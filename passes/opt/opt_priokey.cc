/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Akash Levy        <akash@silimate.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/rewrite_utils.h"

// ---------------------------------------------------------------------------
// opt_priokey: priority-by-key deduplication ("taken" accumulator) rewrite.
//
// RTL that resolves conflicts between several sources that each carry a small
// key is often written as a serial scan over a wide one-hot "set" accumulator
// indexed by the key:
//
//   taken = '0;
//   for (i = 0; i < P; i++)
//     if (act[i] && !taken[key[i]]) begin   // this source wins its key
//       taken[key[i]] = 1'b1;               // claim the key
//       ...use win[i]...
//     end
//
// This elaborates into a serial chain of dynamic-index reads (taken[key[i]] =
// $shiftx into an S-bit vector) and dynamic-index writes (taken | 1<<key[i],
// muxed by the winner). Each dynamic access is an O(log S) wide mux, so the
// critical path grows with both P and S even though the underlying decision
// only needs pairwise key comparisons:
//
//   taken[key[j]] (at step j)  ==  OR over i<j of ( win_guard[i] & key[i]==key[j] )
//
// The pass identifies the accumulator chain, then replaces each dynamic read
// with the equivalent pairwise-key-compare reduction, eliminating the wide
// dynamic indexing entirely. Correctness of every rewrite is validated by a
// ConstEval fingerprint (the read output vs. the compare reduction, over the
// free key/guard signals) before it is applied. For non-power-of-two S the
// rewrite is equivalent over the reachable key range [0,S), which the
// fingerprint sweeps.
// ---------------------------------------------------------------------------

struct OptPrioKeyWorker {
	Module *module;
	SigMap sigmap;
	Cell *cell = nullptr;

	dict<SigBit, Cell *> bit_to_driver;

	int max_slots = 1 << 14;   // maximum accumulator width S
	int max_chain = 256;       // maximum number of sources P
	int fp_trials = 256;       // ConstEval validation vectors
	bool strict = false;       // validate over the full key range, not [0,S)

	int regions_rewritten = 0;
	int cells_added = 0;

	OptPrioKeyWorker(Module *m) : module(m), sigmap(m) { build_index(); }

	void build_index() {
		for (auto c : module->cells())
			for (auto &conn : c->connections())
				if (c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire) bit_to_driver[bit] = c;
	}

	Cell *sole_driver(const SigSpec &s) {
		SigSpec ss = sigmap(s);
		Cell *d = nullptr;
		for (auto bit : ss) {
			if (!bit.wire) return nullptr;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) return nullptr;
			if (d && d != it->second) return nullptr;
			d = it->second;
		}
		return d;
	}

	bool is_all_zero(const SigSpec &s) {
		for (auto bit : s)
			if (bit != SigBit(State::S0)) return false;
		return true;
	}

	bool is_const_one(const SigSpec &s) {
		SigSpec ss = sigmap(s);
		if (!ss.is_fully_const()) return false;
		return ss.as_const().as_int() == 1;
	}

	// Recover the index bus `key` from a one-hot set-mask (1 << key), spelled
	// as $shl(1, key) or $shift(1, -key).
	SigSpec decode_onehot_key(const SigSpec &mask) {
		Cell *d = sole_driver(mask);
		if (!d) return SigSpec();
		if ((d->type == ID($shl) || d->type == ID($sshl)) &&
		    is_const_one(d->getPort(ID::A)))
			return sigmap(d->getPort(ID::B));
		if (d->type == ID($shift) && is_const_one(d->getPort(ID::A))) {
			Cell *neg = sole_driver(d->getPort(ID::B));
			if (neg && neg->type == ID($neg))
				return sigmap(neg->getPort(ID::A));
		}
		return SigSpec();
	}

	// A set-arm is `taken_prev` with one bit (1 << key) OR'ed in. After opt it
	// appears either as the raw one-hot (prev was 0) or as an $or whose two
	// operands are the one-hot mask and the (masked) previous state. Return the
	// key bus of the one-hot mask.
	SigSpec extract_key_from_setarm(const SigSpec &arm) {
		SigSpec k = decode_onehot_key(arm);
		if (GetSize(k)) return k;
		Cell *d = sole_driver(arm);
		if (d && d->type == ID($or)) {
			k = decode_onehot_key(d->getPort(ID::A));
			if (GetSize(k)) return k;
			k = decode_onehot_key(d->getPort(ID::B));
			if (GetSize(k)) return k;
		}
		return SigSpec();
	}

	// One guarded "set key" applied to the accumulator (guard may be const-1
	// for an unconditional set).
	struct SetStep {
		SigBit guard;
		SigSpec key;
	};

	// Cache of trace results: chained reads share accumulator prefixes (read j
	// indexes the state produced by sets 0..j-1), so without memoization the
	// same chain is re-walked once per read -> O(P^2 * S). The cache makes the
	// total walk O(P * S).
	dict<SigSpec, std::pair<bool, vector<SetStep>>> acc_memo;

	// Walk an accumulator value back to constant zero, collecting the guarded
	// key-sets that produced it. Returns false (leaving `steps` unchanged) if it
	// is not a pure set-only accumulator (mux/or of prev with a one-hot key)
	// rooted at 0.
	bool trace_acc(SigSpec acc, vector<SetStep> &steps, int depth) {
		acc = sigmap(acc);
		auto mit = acc_memo.find(acc);
		if (mit != acc_memo.end()) {
			if (mit->second.first)
				steps.insert(steps.end(), mit->second.second.begin(),
				             mit->second.second.end());
			return mit->second.first;
		}
		int start = GetSize(steps);
		bool ok = trace_acc_uncached(acc, steps, depth);
		if (ok) {
			acc_memo[acc] = {true, vector<SetStep>(steps.begin() + start,
			                                       steps.end())};
		} else {
			steps.resize(start);   // discard any partial trace
			acc_memo[acc] = {false, {}};
		}
		return ok;
	}

	bool trace_acc_uncached(SigSpec acc, vector<SetStep> &steps, int depth) {
		if (is_all_zero(acc))
			return true;
		if (depth > max_chain)
			return false;
		Cell *d = sole_driver(acc);
		if (!d)
			return false;
		if (d->type == ID($mux)) {
			SigSpec s = sigmap(d->getPort(ID::S));
			if (GetSize(s) != 1)
				return false;
			if (!trace_acc(d->getPort(ID::A), steps, depth + 1))
				return false;
			SigSpec key = extract_key_from_setarm(d->getPort(ID::B));
			if (GetSize(key) == 0)
				return false;
			steps.push_back(SetStep{s[0], key});
			return true;
		}
		if (d->type == ID($or)) {
			SigSpec a = d->getPort(ID::A), b = d->getPort(ID::B);
			SigSpec ka = decode_onehot_key(a), kb = decode_onehot_key(b);
			if (GetSize(ka) && trace_acc(b, steps, depth + 1)) {
				steps.push_back(SetStep{SigBit(State::S1), ka});
				return true;
			}
			if (GetSize(kb) && trace_acc(a, steps, depth + 1)) {
				steps.push_back(SetStep{SigBit(State::S1), kb});
				return true;
			}
		}
		return false;
	}

	// A dynamic read of the accumulator: the 1-bit read cell, the accumulator
	// value it indexes (with any out-of-range x-padding stripped) and the index.
	struct Read {
		Cell *cell;
		SigSpec acc;
		SigSpec key;
	};

	// Recognize a 1-bit dynamic read of a vector: either $shiftx(A=acc, B=key)
	// or $bmux(A={x.., acc}, S=key). Returns false otherwise.
	bool match_read(Cell *c, Read &r) {
		if (c->type == ID($shiftx)) {
			if (GetSize(c->getPort(ID::Y)) != 1)
				return false;
			r.cell = c;
			r.acc = sigmap(c->getPort(ID::A));
			r.key = sigmap(c->getPort(ID::B));
			return GetSize(r.acc) >= 2;
		}
		if (c->type == ID($bmux)) {
			if (c->getParam(ID::WIDTH).as_int() != 1)
				return false;
			SigSpec a = sigmap(c->getPort(ID::A));
			// Strip the high x-padding to recover the real accumulator bits.
			int w = 0;
			while (w < GetSize(a) && a[w] != SigBit(State::Sx))
				w++;
			if (w < 2)
				return false;
			r.cell = c;
			r.acc = a.extract(0, w);
			r.key = sigmap(c->getPort(ID::S));
			return true;
		}
		return false;
	}

	// Prove read == OR over steps of ( guard & key == read_key ) by ConstEval
	// fingerprinting over the reachable key range [0,S). Guards and key buses
	// (which are disjoint sel slices) are driven as free inputs.
	bool validate_read(const Read &rd, const vector<SetStep> &steps, int S) {
		Cell *read = rd.cell;
		SigSpec read_key = rd.key;
		// In strict mode sweep the full key range so the rewrite is proven for
		// every value the index bus can take (out-of-range reads included);
		// otherwise sweep only the reachable slots [0,S).
		int kw = GetSize(read_key);
		uint64_t range = (uint64_t)S;
		if (strict) {
			int cap = kw < 30 ? kw : 30;
			range = 1ULL << cap;
		}
		ConstEval ce(module);
		// Deterministic seed (not a Cell*): ASLR made uintptr_t seeding flake
		// across runs, so -strict could miss the OOR counterexample.
		uint64_t lfsr = 0x9e3779b97f4a7c15ULL ^ ((uint64_t)S << 1) ^
		                ((uint64_t)kw << 17) ^ (uint64_t)GetSize(steps);
		auto rnd = [&]() {
			lfsr ^= lfsr << 13; lfsr ^= lfsr >> 7; lfsr ^= lfsr << 17;
			return lfsr;
		};
		auto trial = [&](int rk, const vector<int> &kv, const vector<int> &gv) -> bool {
			ce.push();
			ce.set(read_key, Const(rk, GetSize(read_key)));
			for (int i = 0; i < GetSize(steps); i++) {
				ce.set(steps[i].key, Const(kv[i], GetSize(steps[i].key)));
				if (steps[i].guard != State::S1)
					ce.set(SigSpec(steps[i].guard), Const(gv[i], 1));
			}
			SigSpec out(read->getPort(ID::Y));
			SigSpec undef;
			bool ok = ce.eval(out, undef) && out.is_fully_const();
			int actual = ok ? (out.as_const().as_int() & 1) : -1;
			int expect = 0;
			for (int i = 0; i < GetSize(steps); i++)
				if (gv[i] && kv[i] == rk) { expect = 1; break; }
			ce.pop();
			return ok && actual == expect;
		};
		// Strict + non-pow2 S: force OOR key collisions the rewrite would accept
		// but the S-bit accumulator cannot store (taken[key>=S] is not a set bit).
		if (strict && range > (uint64_t)S && !steps.empty()) {
			int oor_n = (int)(range - (uint64_t)S);
			int forced = oor_n < 16 ? oor_n : 16;
			for (int f = 0; f < forced; f++) {
				int rk = S + f;
				vector<int> kv(GetSize(steps), 0);
				vector<int> gv(GetSize(steps), 0);
				kv[0] = rk;
				gv[0] = 1;
				for (int i = 1; i < GetSize(steps); i++) {
					kv[i] = (int)(rnd() % range);
					gv[i] = steps[i].guard == State::S1 ? 1 : (int)(rnd() & 1);
				}
				if (!trial(rk, kv, gv))
					return false;
			}
		}
		for (int t = 0; t < fp_trials; t++) {
			int rk = (int)(rnd() % range);
			vector<int> kv(GetSize(steps));
			vector<int> gv(GetSize(steps));
			for (int i = 0; i < GetSize(steps); i++) {
				kv[i] = (int)(rnd() % range);
				if (steps[i].guard == State::S1)
					gv[i] = 1;
				else
					gv[i] = (int)(rnd() & 1);
			}
			if (!trial(rk, kv, gv))
				return false;
		}
		return true;
	}

	void rewrite_read(const Read &rd, const vector<SetStep> &steps) {
		Cell *read = rd.cell;
		cell = read;
		SigSpec read_key = rd.key;
		SigSpec new_r;
		if (steps.empty()) {
			new_r = SigSpec(State::S0);
		} else {
			SigSpec terms;
			for (auto &st : steps) {
				SigSpec eq = module->Eq(NEW_ID2_SUFFIX("priokey_eq"),
				                        st.key, read_key, false, cell_src(read));
				cells_added++;
				SigSpec g = module->And(NEW_ID2_SUFFIX("priokey_and"),
				                        SigSpec(st.guard), eq, false, cell_src(read));
				cells_added++;
				terms.append(g);
			}
			new_r = module->ReduceOr(NEW_ID2_SUFFIX("priokey_or"), terms,
			                        false, cell_src(read));
			cells_added++;
		}
		// Tag wire so the rewrite is externally observable, then detach the old
		// dynamic read and drive its consumers from the reduction.
		Wire *tag = module->addWire(NEW_ID2_SUFFIX("priokey_read"), 1);
		module->connect(SigSpec(tag), new_r);
		SigSpec old_y = sigmap(read->getPort(ID::Y));
		Wire *dangling = module->addWire(NEW_ID2_SUFFIX("priokey_dangling"),
		                                 GetSize(read->getPort(ID::Y)));
		read->setPort(ID::Y, dangling);
		module->connect(old_y, SigSpec(tag));
		regions_rewritten++;
	}

	void run() {
		vector<Read> reads;
		for (auto c : module->cells()) {
			Read r;
			if (!match_read(c, r))
				continue;
			if (GetSize(r.acc) > max_slots)
				continue;
			reads.push_back(r);
		}

		int max_sources = 0;
		int accum_width = 0;
		vector<Read> zero_reads;   // read of the all-zero head (== 0)
		for (auto &rd : reads) {
			int S = GetSize(rd.acc);
			vector<SetStep> steps;
			if (!trace_acc(rd.acc, steps, 0))
				continue;
			// The all-zero head read is only rewritten (to 0) once we know the
			// pattern is really present in this module.
			if (steps.empty()) {
				zero_reads.push_back(rd);
				continue;
			}
			if (!validate_read(rd, steps, S))
				continue;
			rewrite_read(rd, steps);
			max_sources = std::max(max_sources, GetSize(steps) + 1);
			accum_width = S;
		}
		if (regions_rewritten)
			for (auto &rd : zero_reads)
				rewrite_read(rd, {});

		if (regions_rewritten)
			log("  %s: priority-by-key dedup, up to %d source(s), "
			    "%d-slot accumulator\n",
			    log_id(module), max_sources, accum_width);
	}
};

struct OptPrioKeyPass : public Pass {
	OptPrioKeyPass() : Pass("opt_priokey",
		"detect and rewrite priority-by-key deduplication accumulators") {}

	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_priokey [options] [selection]\n");
		log("\n");
		log("This pass detects a serial 'set accumulator' that resolves conflicts\n");
		log("between several sources that each carry a small key:\n");
		log("\n");
		log("    taken = '0;\n");
		log("    for (i = 0; i < P; i++)\n");
		log("      if (act[i] && !taken[key[i]]) begin taken[key[i]] = 1; ... end\n");
		log("\n");
		log("Such RTL elaborates into a chain of dynamic-index reads/writes into a\n");
		log("wide one-hot vector ($shiftx / $shift), whose depth grows with both the\n");
		log("number of sources and the accumulator width. Each dynamic read\n");
		log("taken[key[j]] is provably equal to\n");
		log("\n");
		log("    OR over i<j of ( set_guard[i] & key[i] == key[j] )\n");
		log("\n");
		log("so the pass replaces every read with that pairwise-key-compare\n");
		log("reduction, removing the wide dynamic indexing. Each rewrite is\n");
		log("validated by a ConstEval fingerprint before being applied; for\n");
		log("non-power-of-two accumulator widths the rewrite holds over the\n");
		log("reachable key range [0,S).\n");
		log("\n");
		log("    -max-slots N\n");
		log("        maximum accumulator width to consider (default 16384).\n");
		log("\n");
		log("    -max-sources N\n");
		log("        maximum number of chained sources to consider (default 256).\n");
		log("\n");
		log("    -strict\n");
		log("        validate every rewrite over the full index range instead of\n");
		log("        only the reachable slots [0,S). Rewrites that hold merely by\n");
		log("        out-of-range don't-care freedom are then rejected (use this\n");
		log("        under equiv_opt -assert / formal flows).\n");
		log("\n");
		log("This pass is not invoked by the default 'opt' script; users opt in.\n");
		log("After rewriting, the dead accumulator chain is removed by the trailing\n");
		log("'clean -purge'.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_PRIOKEY pass (priority-by-key dedup).\n");

		int max_slots = 1 << 14;
		int max_sources = 256;
		bool strict = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max-slots" && argidx + 1 < args.size()) {
				max_slots = std::stoi(args[++argidx]); continue;
			}
			if (args[argidx] == "-max-sources" && argidx + 1 < args.size()) {
				max_sources = std::stoi(args[++argidx]); continue;
			}
			if (args[argidx] == "-strict") {
				strict = true; continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0, total_cells = 0;
		for (auto module : design->selected_modules()) {
			OptPrioKeyWorker worker(module);
			worker.max_slots = max_slots;
			worker.max_chain = max_sources;
			worker.strict = strict;
			worker.run();
			total_regions += worker.regions_rewritten;
			total_cells += worker.cells_added;
		}

		log("Rewrote %d dynamic key-read(s); emitted %d new cell(s).\n",
		    total_regions, total_cells);

		if (total_regions)
			Yosys::run_pass("clean -purge");
	}
} OptPrioKeyPass;

PRIVATE_NAMESPACE_END
