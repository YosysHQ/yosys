/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2020  Marcelina Kościelnicka <mwk@0x04.net>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/ff.h"
#include "passes/opt/dff/opt_dff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Bit-parallel random simulation used as a cheap pre-filter for equivalence
struct BitSim {
	Module *module;
	SigMap &sigmap;
	ModWalker &modwalker;
	dict<SigBit, uint64_t> sim_vals;
	uint64_t rng_state;
	int max_depth;
	int evals_left;

	BitSim(Module *m, SigMap &sm, ModWalker &mw)
		: module(m), sigmap(sm), modwalker(mw), rng_state(1337)
	{
		max_depth = module->design->scratchpad_get_int("opt_dff.sim_depth", 10000);
		evals_left = module->design->scratchpad_get_int("opt_dff.sim_evals", 1000000);
	}

	uint64_t next_rand() {
		uint32_t lo = mkhash_xorshift((uint32_t)rng_state);
		uint32_t hi = mkhash_xorshift((uint32_t)(rng_state >> 32) ^ lo);
		rng_state = ((uint64_t)hi << 32) | lo;
		return rng_state;
	}

	uint64_t eval_bit(SigBit b, int depth = 0) {
		SigBit mapped = sigmap(b);
		if (mapped == State::S0) return 0ULL;
		if (mapped == State::S1) return ~0ULL;
		if (mapped == State::Sx || mapped == State::Sz) return 0ULL;

		auto it = sim_vals.find(mapped);
		if (it != sim_vals.end()) return it->second;

		// Failsafe for huge designs
		if (depth >= max_depth || evals_left <= 0) {
			uint64_t r = next_rand();
			sim_vals[mapped] = r;
			return r;
		}
		evals_left--;

		// pre-seed to break combinational loops
		sim_vals[mapped] = 0;
		uint64_t res = 0;

		auto drv = modwalker.signal_drivers.find(mapped);
		if (drv == modwalker.signal_drivers.end() || drv->second.empty()) {
			res = next_rand();
		} else {
			auto driver = *drv->second.begin();
			Cell *cell = driver.cell;

			if (cell->is_builtin_ff()) {
				res = next_rand();
			} else if (cell->type == ID($_AND_)) {
				res = eval_bit(cell->getPort(ID::A)[0], depth+1) & eval_bit(cell->getPort(ID::B)[0], depth+1);
			} else if (cell->type == ID($_OR_)) {
				res = eval_bit(cell->getPort(ID::A)[0], depth+1) | eval_bit(cell->getPort(ID::B)[0], depth+1);
			} else if (cell->type == ID($_XOR_)) {
				res = eval_bit(cell->getPort(ID::A)[0], depth+1) ^ eval_bit(cell->getPort(ID::B)[0], depth+1);
			} else if (cell->type == ID($_NOT_)) {
				res = ~eval_bit(cell->getPort(ID::A)[0], depth+1);
			} else if (cell->type == ID($_MUX_)) {
				uint64_t s = eval_bit(cell->getPort(ID::S)[0], depth+1);
				uint64_t a = eval_bit(cell->getPort(ID::A)[0], depth+1);
				uint64_t b = eval_bit(cell->getPort(ID::B)[0], depth+1);
				res = (a & ~s) | (b & s);
			} else if (cell->type == ID($mux)) {
				uint64_t s = eval_bit(cell->getPort(ID::S)[0], depth+1);
				uint64_t a = eval_bit(cell->getPort(ID::A)[driver.offset], depth+1);
				uint64_t b = eval_bit(cell->getPort(ID::B)[driver.offset], depth+1);
				res = (a & ~s) | (b & s);
			} else {
				res = next_rand();
			}
		}

		sim_vals[mapped] = res;
		return res;
	}
};

// concrete 0/1 bit, as opposed to x/z
bool is_def(State s) {
	return s == State::S0 || s == State::S1;
}

struct EqBitsContext
{
	OptDffWorker &worker;

	EqBitsContext(OptDffWorker &worker) : worker(worker) { }

	struct EqBit {
		Cell *cell;
		int idx;
		SigBit q;
	};

	// NOTE: This intentionally duplicates a subset of FfData, as flattening just the
	// fields that matter for merging into a single comparable/hashable key is cheaper
	struct SigKey {
		enum Flag : uint16_t {
			InitOne     = 1u << 0,
			InitX       = 1u << 1,
			PolClk      = 1u << 2,
			PolCe       = 1u << 3,
			PolSrst     = 1u << 4,
			PolArst     = 1u << 5,
			PolAload    = 1u << 6,
			PolClr      = 1u << 7,
			PolSet      = 1u << 8,
			CeOverSrst  = 1u << 9,
		};

		SigBit clk, ce, srst, arst, aload, clr, set;
		IdString cell_type;  // for SR
		uint16_t flags;

		bool operator==(const SigKey &o) const {
			return flags == o.flags && clk == o.clk && ce == o.ce && srst == o.srst && arst == o.arst
				&& aload == o.aload && clr == o.clr && set == o.set && cell_type == o.cell_type;
		}

		Hasher hash_into(Hasher h) const {
			h.eat(flags);
			h.eat(clk);
			h.eat(ce);
			h.eat(srst);
			h.eat(arst);
			h.eat(aload);
			h.eat(clr);
			h.eat(set);
			h.eat(cell_type);
			return h;
		}
	};

	struct EqCandidates {
		std::vector<EqBit> bits;
		dict<Cell *, FfData> ffs;
		std::vector<std::vector<int>> classes;
	};

	EqCandidates gather_initial_eq_classes()
	{
		EqCandidates cand;
		std::vector<SigKey> keys;

		// Collect FF bits eligible for merging
		for (auto cell : worker.module->selected_cells()) {
			if (!cell->is_builtin_ff())
				continue;

			FfData ff(&worker.initvals, cell);
			if (!ff.has_clk && !ff.has_gclk)
				continue;

			cand.ffs.emplace(cell, ff);

			for (int i = 0; i < ff.width; i++) {
				// Skip bits whose reset value is undefined (x)
				if (ff.has_srst && !is_def(ff.val_srst[i])) continue;
				if (ff.has_arst && !is_def(ff.val_arst[i])) continue;

				// Class members are assumed equal in the current cycle and proven equal in the next, which needs
				// a base case anchoring them to a common known value
				bool def_init = is_def(ff.val_init[i]);
				if (!def_init && !ff.has_srst && !ff.has_arst)
					continue;

				SigKey k = {};

				// Flags
				if (def_init && ff.val_init[i] == State::S1)
					k.flags |= SigKey::InitOne;
				else if (!def_init)
					k.flags |= SigKey::InitX;

				if (ff.has_clk) {
					k.clk = ff.sig_clk;
					if (ff.pol_clk) k.flags |= SigKey::PolClk;
				}
				if (ff.has_ce) {
					k.ce = ff.sig_ce;
					if (ff.pol_ce) k.flags |= SigKey::PolCe;
				}
				if (ff.has_srst) {
					k.srst = ff.sig_srst;
					if (ff.pol_srst) k.flags |= SigKey::PolSrst;
					if (ff.ce_over_srst) k.flags |= SigKey::CeOverSrst;
				}
				if (ff.has_arst) {
					k.arst = ff.sig_arst;
					if (ff.pol_arst) k.flags |= SigKey::PolArst;
				}
				if (ff.has_aload) {
					k.aload = ff.sig_aload;
					if (ff.pol_aload) k.flags |= SigKey::PolAload;
				}
				if (ff.has_sr) {
					k.clr = ff.sig_clr[i];
					k.set = ff.sig_set[i];
					k.cell_type = cell->type;
					if (ff.pol_clr) k.flags |= SigKey::PolClr;
					if (ff.pol_set) k.flags |= SigKey::PolSet;
				}

				cand.bits.push_back({cell, i, ff.sig_q[i]});
				keys.push_back(k);
			}
		}

		dict<SigKey, std::vector<int>> buckets;
		for (int i = 0; i < GetSize(cand.bits); i++)
			buckets[keys[i]].push_back(i);

		for (auto &kv : buckets)
			if (GetSize(kv.second) >= 2)
				cand.classes.push_back(std::move(kv.second));

		return cand;
	}

	void filter_classes_sim(EqCandidates &cand)
	{
		BitSim sim(worker.module, worker.sigmap, worker.get_modwalker());

		// Assume same class
		for (auto &cls : cand.classes) {
			uint64_t class_q_val = sim.next_rand();
			for (int idx : cls) {
				sim.sim_vals[worker.sigmap(cand.bits[idx].q)] = class_q_val;
			}
		}

		std::vector<std::vector<int>> refined_classes;
		for (auto &cls : cand.classes) {
			dict<uint64_t, std::vector<int>> sim_buckets;
			for (int idx : cls) {
				const EqBit &eb = cand.bits[idx];
				const FfData &ff = cand.ffs.at(eb.cell);
				uint64_t n_val = sim.eval_bit(ff.sig_d[eb.idx]);

				if (ff.has_aload) {
					uint64_t al = sim.eval_bit(ff.sig_aload);
					if (!ff.pol_aload) al = ~al;
					uint64_t ad = sim.eval_bit(ff.sig_ad[eb.idx]);
					n_val = (n_val & ~al) | (ad & al);
				}
				if (ff.has_arst) {
					uint64_t ar = sim.eval_bit(ff.sig_arst);
					if (!ff.pol_arst) ar = ~ar;
					uint64_t ar_val = (ff.val_arst[eb.idx] == State::S1) ? ~0ULL : 0ULL;
					n_val = (n_val & ~ar) | (ar_val & ar);
				}
				if (ff.has_sr) {
					uint64_t clr = sim.eval_bit(ff.sig_clr[eb.idx]);
					if (!ff.pol_clr) clr = ~clr;
					uint64_t set = sim.eval_bit(ff.sig_set[eb.idx]);
					if (!ff.pol_set) set = ~set;
					n_val = ~clr & (set | n_val);
				}
				if (ff.has_srst) {
					uint64_t srst = sim.eval_bit(ff.sig_srst);
					if (!ff.pol_srst) srst = ~srst;
					uint64_t srst_val = (ff.val_srst[eb.idx] == State::S1) ? ~0ULL : 0ULL;
					n_val = (n_val & ~srst) | (srst_val & srst);
				}

				sim_buckets[n_val].push_back(idx);
			}

			for (auto &kv : sim_buckets)
				if (GetSize(kv.second) >= 2)
					refined_classes.push_back(std::move(kv.second));
		}

		cand.classes = std::move(refined_classes);
	}

	void drop_all_classes(EqCandidates &cand)
	{
		log("opt_dff -sat: skipping all equivalent-flip-flop merges in module %s (solver effort budget "
				"exhausted before the equivalences could be proven).\n", log_id(worker.module));
		cand.classes.clear();
	}

	void filter_classes_sat(EqCandidates &cand)
	{
		auto &classes = cand.classes;
		auto &bits = cand.bits;
		QuickConeSat qcsat(worker.get_modwalker());
		std::vector<int> q_lit(bits.size(), -1);
		std::vector<int> n_lit(bits.size(), -1);

		// Build the next-state function n_lit[idx] of every candidate bit by
		// folding the FF's control logic on top of the D input (-> next value)
		int64_t cells_charged = 0;

		// Two bits are equivalent if their next states always agree whenever their
		// current states (and those of every other candidate pair) agree
		for (auto &cls : classes) {
			if (worker.warn_if_budget_spent())
				return drop_all_classes(cand);
			for (int idx : cls) {
				const EqBit &eb = bits[idx];
				const FfData &ff = cand.ffs.at(eb.cell);
				q_lit[idx] = qcsat.importSigBit(eb.q);
				int n = qcsat.importSigBit(ff.sig_d[eb.idx]);

				if (ff.has_aload) {
					int al = qcsat.importSigBit(ff.sig_aload);
					if (!ff.pol_aload) al = qcsat.ez->NOT(al);
					n = qcsat.ez->ITE(al, qcsat.importSigBit(ff.sig_ad[eb.idx]), n);
				}
				if (ff.has_arst) {
					int ar = qcsat.importSigBit(ff.sig_arst);
					if (!ff.pol_arst) ar = qcsat.ez->NOT(ar);
					n = qcsat.ez->ITE(ar, qcsat.ez->value(ff.val_arst[eb.idx] == State::S1), n);
				}
				if (ff.has_sr) {
					int clr = qcsat.importSigBit(ff.sig_clr[eb.idx]);
					if (!ff.pol_clr) clr = qcsat.ez->NOT(clr);
					int set = qcsat.importSigBit(ff.sig_set[eb.idx]);
					if (!ff.pol_set) set = qcsat.ez->NOT(set);
					n = qcsat.ez->AND(qcsat.ez->NOT(clr), qcsat.ez->OR(set, n));
				}
				if (ff.has_srst) {
					int srst = qcsat.importSigBit(ff.sig_srst);
					if (!ff.pol_srst) srst = qcsat.ez->NOT(srst);
					n = qcsat.ez->ITE(srst, qcsat.ez->value(ff.val_srst[eb.idx] == State::S1), n);
				}

				n_lit[idx] = n;
			}
			qcsat.prepare();
			cells_charged = worker.sat_budget.charge_import(qcsat, cells_charged);
		}

		// Assume the induction hypo (that every current class is internally equal in the present cycle), and try
		// to prove that the members of each class therefore also agree in the next cycle

		// A class survives only if no counterexample exists under that hypo, so combined with the common init/reset
		// value that every class shares, this makes the equality an inductive invariant -> bits are eq and safe to merge
		std::vector<int> worklist;
		std::vector<bool> in_worklist(GetSize(classes), true);

		for (int i = 0; i < GetSize(classes); i++)
			worklist.push_back(i);

		while (!worklist.empty()) {
			int cls_idx = worklist.back();
			worklist.pop_back();
			in_worklist[cls_idx] = false;

			auto &cls = classes[cls_idx];
			if (GetSize(cls) < 2) continue;

			// Induction hypo: assume every candidate class is equal
			std::vector<int> assumptions;
			for (auto &c : classes) {
				if (GetSize(c) < 2) continue;
				int rep = c[0];
				for (int k = 1; k < GetSize(c); k++)
					assumptions.push_back(qcsat.ez->IFF(q_lit[rep], q_lit[c[k]]));
			}

			// Scan the class members against the representative and issue a query per pair,
			// stopping early at the first counterexample, which is reused to split the entire
			// class at once
			int rep = cls[0];
			for (int i = 1; i < GetSize(cls); i++) {
				if (n_lit[rep] == n_lit[cls[i]])
					continue;

				if (worker.warn_if_budget_spent())
					return drop_all_classes(cand);

				// Can the next state of the rep and this member ever differ?
				int query = qcsat.ez->XOR(n_lit[rep], n_lit[cls[i]]);
				// Capture every member's next-state value in that model so one counterexample
				// partitions the whole class
				std::vector<int> modelExprs;
				for (int b : cls)
					modelExprs.push_back(n_lit[b]);

				std::vector<bool> modelVals;
				assumptions.push_back(query);

				auto res = worker.sat_budget.solve(qcsat, 0, modelExprs, modelVals, assumptions);

				if (res == SatEffortBudget::Result::LimitReached) {
					worker.warn_if_budget_spent();
					return drop_all_classes(cand);
				}

				if (res == SatEffortBudget::Result::Sat) {
					// SAT -> partition entire class
					std::vector<int> sub0;
					std::vector<int> sub1;

					for (int b_idx = 0; b_idx < GetSize(cls); b_idx++) {
						if (modelVals[b_idx])
							sub1.push_back(cls[b_idx]);
						else
							sub0.push_back(cls[b_idx]);
					}

					classes[cls_idx] = std::move(sub0);
					classes.push_back(std::move(sub1));
					in_worklist.push_back(false);

					// Partition was split -> the induction hypo weakened
					for (int j = 0; j < GetSize(classes); j++) {
						if (GetSize(classes[j]) >= 2 && !in_worklist[j]) {
							worklist.push_back(j);
							in_worklist[j] = true;
						}
					}

					break; // Process new splits
				}

				assumptions.pop_back(); // Remove query for the next pairwise check if UNSAT
			}
		}
	}

	bool apply_eq_merges(const EqCandidates &cand)
	{
		bool any_change = false;
		dict<Cell *, pool<int>> remove_bits;

		// Drive every non-rep Q from its class rep, drop merged bits from their FFs
		for (auto &cls : cand.classes) {
			if (GetSize(cls) < 2)
				continue;
			SigBit rep_q = cand.bits[cls[0]].q;
			any_change = true;
			for (int k = 1; k < GetSize(cls); k++) {
				const EqBit &eb = cand.bits[cls[k]];
				worker.initvals.remove_init(eb.q);
				worker.module->connect(eb.q, rep_q);
				remove_bits[eb.cell].insert(eb.idx);
			}
		}

		for (auto &[cell, drop] : remove_bits)
			worker.remove_ff_bits(cell, drop);

		return any_change;
	}

	bool run_eqbits()
	{
		EqCandidates cand = gather_initial_eq_classes();
		if (cand.classes.empty())
			return false;

		// Simulation prepass
		filter_classes_sim(cand);
		if (cand.classes.empty())
			return false;

		// SAT prove
		filter_classes_sat(cand);
		if (cand.classes.empty())
			return false;

		return apply_eq_merges(cand);
	}
};

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN

bool OptDffWorker::run_eqbits()
{
	return EqBitsContext(*this).run_eqbits();
}

YOSYS_NAMESPACE_END
