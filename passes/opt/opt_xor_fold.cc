/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.     <akash@silimate.com>
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
#include <algorithm>
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/cut_region.h"

// opt_xor_fold: flatten an in-place XOR fold over dynamically indexed bits of
// a vector into a balanced masked-XOR tree.
//
// RTL of the form
//
//   v = src;
//   for (i = 0; i < W; i++)
//     if (active(i))
//       for (j = 0; j < J; j++)
//         if (j < count) v[i] = v[i] ^ v[i + j*stride];
//
// elaborates into a read-modify-write chain per written bit:
//
//   a_0; a_{k+1} = g_k ? (a_k ^ bmux(sel_k, tbl_k)) : a_k
//
// where tbl_k is the *running* vector, so it holds the accumulator itself at
// slot i and the already-written bits at slots < i. Those back-references make
// the chain serial across steps and across written bits (W*J levels), even
// though the strides are such that only slots > i are ever read.
//
// The rewrite recovers that: the chain result is consumed under an activation
// guard G, so every table slot that no G-satisfying control assignment selects
// is a don't-care and is pruned to 0. Once the self/back-reference slots are
// gone the recurrence is affine with no feedback and collapses to
//
//   a_K = a_0 ^ XOR_k (g_k & bmux(sel_k, pruned tbl_k))
//
// emitted as a balanced tree (log depth). Reachability is decided by
// exhaustively enumerating the control cone (sel/g/G share a small support:
// the stride and count ports), and every rewrite is additionally checked by
// ConstEval fingerprinting against the original chain.
//
// The pruning uses don't-care freedom, so -strict (used in formal mode, where
// equiv_opt -assert cannot see the guard) disables the pass.
struct OptXorFoldWorker : CutRegionWorker
{
	// One `a_{k+1} = g ? (a_k ^ bmux(sel, tbl)) : a_k` link of a fold chain.
	struct Step {
		Cell *xor_cell = nullptr;
		Cell *mux_cell = nullptr; // guard mux; null when the step is unguarded
		Cell *tbl_cell = nullptr; // $bmux/$mux supplying the indexed read
		SigBit acc_in, acc_out, term;
		SigBit guard = State::S1;
		bool guard_inv = false;
		SigSpec sel;
		vector<SigBit> table;
		pool<int> reach; // table slots some guard-satisfying control selects
	};

	struct Chain {
		vector<Step> steps;
		SigBit start;      // a_0
		SigBit out;        // a_K
		Cell *sink = nullptr;
		SigBit guard;      // G, the activation guard on the chain result
		bool guard_inv = false;
	};

	// Tunables (see Pass::execute).
	int min_steps = 2;
	int max_steps = 64;
	int max_ctrl_bits = 12;
	int max_table_bits = 8192;
	int verify_vectors = 4;
	bool strict = false;

	int chains_rewritten = 0;
	int steps_rewritten = 0;
	int cells_added = 0;

	dict<SigBit, pool<Cell *>> bit_consumers;
	pool<Cell *> used_cells;
	Cell *anchor = nullptr;
	uint64_t rng_state = 0x9e3779b97f4a7c15ULL;

	OptXorFoldWorker(Module *module) : CutRegionWorker(module)
	{
		// Every cell, selected or not: an unselected consumer still keeps a
		// bit from being sole-consumed by the chain.
		for (auto c : module->cells())
			for (auto &conn : c->connections())
				if (!c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							bit_consumers[bit].insert(c);
	}

	uint64_t next_rand()
	{
		rng_state ^= rng_state << 13;
		rng_state ^= rng_state >> 7;
		rng_state ^= rng_state << 17;
		return rng_state;
	}

	// ---------------------------------------------------------------- emit
	SigBit emit_xor(SigBit a, SigBit b)
	{
		if (a == State::S0)
			return b;
		if (b == State::S0)
			return a;
		Cell *cell = anchor;
		cells_added++;
		return module->Xor(NEW_ID2_SUFFIX("xorfold_xor"), a, b, false, cell_src(anchor))[0];
	}

	SigBit emit_and(SigBit a, SigBit b)
	{
		if (a == State::S1)
			return b;
		if (b == State::S1)
			return a;
		if (a == State::S0 || b == State::S0)
			return State::S0;
		Cell *cell = anchor;
		cells_added++;
		return module->And(NEW_ID2_SUFFIX("xorfold_and"), a, b, false, cell_src(anchor))[0];
	}

	SigBit emit_not(SigBit a)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Not(NEW_ID2_SUFFIX("xorfold_not"), a, false, cell_src(anchor))[0];
	}

	SigBit emit_xor_tree(vector<SigBit> terms)
	{
		vector<SigBit> live;
		bool parity = false;
		for (auto t : terms) {
			if (t == State::S0)
				continue;
			if (t == State::S1) {
				parity = !parity;
				continue;
			}
			live.push_back(t);
		}
		if (live.empty())
			return parity ? State::S1 : State::S0;
		while (GetSize(live) > 1) {
			vector<SigBit> next;
			for (int i = 0; i + 1 < GetSize(live); i += 2)
				next.push_back(emit_xor(live[i], live[i + 1]));
			if (GetSize(live) % 2)
				next.push_back(live.back());
			live.swap(next);
		}
		return parity ? emit_not(live[0]) : live[0];
	}

	// Indexed read restricted to the reachable slots; unreachable ones are
	// don't-care and become 0 so the mux tree const-folds away.
	SigBit emit_pruned_read(const Step &st)
	{
		if (st.reach.empty())
			return State::S0;
		bool uniform = true;
		SigBit first;
		bool have_first = false;
		for (int p : st.reach) {
			if (!have_first) {
				first = st.table[p];
				have_first = true;
			} else if (st.table[p] != first) {
				uniform = false;
				break;
			}
		}
		if (uniform)
			return first;

		SigSpec tbl(State::S0, GetSize(st.table));
		for (int p : st.reach)
			tbl[p] = st.table[p];
		Cell *cell = anchor;
		cells_added++;
		return module->Bmux(NEW_ID2_SUFFIX("xorfold_read"), tbl, st.sel, cell_src(anchor))[0];
	}

	// ------------------------------------------------------------ matching
	SigBit only_bit(Cell *c, IdString port)
	{
		SigSpec s = sigmap(c->getPort(port));
		return GetSize(s) == 1 ? s[0] : SigBit();
	}

	// Table of the cell driving `term`, LSB slot first, plus its select.
	bool read_table(SigBit term, Cell *&tbl_cell, SigSpec &sel, vector<SigBit> &table)
	{
		Cell *drv = bit_to_driver.at(term, nullptr);
		if (drv == nullptr)
			return false;
		if (drv->type == ID($bmux)) {
			if (drv->parameters.at(ID::WIDTH).as_int() != 1)
				return false;
			sel = sigmap(drv->getPort(ID::S));
			SigSpec a = sigmap(drv->getPort(ID::A));
			if (GetSize(a) != (1 << GetSize(sel)))
				return false;
			table.clear();
			for (int i = 0; i < GetSize(a); i++)
				table.push_back(a[i]);
			tbl_cell = drv;
			return true;
		}
		if (drv->type == ID($mux)) {
			SigSpec y = sigmap(drv->getPort(ID::Y));
			int q = -1;
			for (int i = 0; i < GetSize(y); i++)
				if (y[i] == term) {
					q = i;
					break;
				}
			if (q < 0)
				return false;
			sel = sigmap(drv->getPort(ID::S));
			if (GetSize(sel) != 1)
				return false;
			table.clear();
			table.push_back(sigmap(drv->getPort(ID::A))[q]);
			table.push_back(sigmap(drv->getPort(ID::B))[q]);
			tbl_cell = drv;
			return true;
		}
		return false;
	}

	Cell *sole_consumer(SigBit bit)
	{
		auto it = bit_consumers.find(bit);
		if (it == bit_consumers.end() || GetSize(it->second) != 1)
			return nullptr;
		return *it->second.begin();
	}

	// Recognize one fold step anchored on a 1-bit $xor. The guard mux (when
	// present) resolves which $xor input is the accumulator.
	bool make_step(Cell *xor_cell, Step &st)
	{
		if (xor_cell->type != ID($xor) || used_cells.count(xor_cell))
			return false;
		SigSpec xa = sigmap(xor_cell->getPort(ID::A));
		SigSpec xb = sigmap(xor_cell->getPort(ID::B));
		SigSpec xy = sigmap(xor_cell->getPort(ID::Y));
		if (GetSize(xa) != 1 || GetSize(xb) != 1 || GetSize(xy) != 1)
			return false;
		if (!xy[0].wire)
			return false;

		SigBit acc, term;
		Cell *mux = sole_consumer(xy[0]);
		if (mux != nullptr && mux->type == ID($mux) && !used_cells.count(mux)) {
			SigSpec ma = sigmap(mux->getPort(ID::A));
			SigSpec mb = sigmap(mux->getPort(ID::B));
			SigSpec my = sigmap(mux->getPort(ID::Y));
			SigSpec ms = sigmap(mux->getPort(ID::S));
			for (int q = 0; q < GetSize(my) && st.mux_cell == nullptr; q++) {
				bool on_b = (mb[q] == xy[0]);
				bool on_a = (ma[q] == xy[0]);
				if (!on_a && !on_b)
					continue;
				SigBit pass = on_b ? ma[q] : mb[q];
				if (pass != xa[0] && pass != xb[0])
					continue;
				st.mux_cell = mux;
				st.guard = ms[0];
				st.guard_inv = on_a; // Y = S ? B : A, so A-side means ~S
				st.acc_out = my[q];
				acc = pass;
				term = (pass == xa[0]) ? xb[0] : xa[0];
			}
		}
		if (st.mux_cell == nullptr) {
			// Unguarded step: the accumulator is the input that is not the
			// indexed read, so it must be unambiguous.
			Cell *da = bit_to_driver.at(xa[0], nullptr);
			Cell *db = bit_to_driver.at(xb[0], nullptr);
			bool a_is_read = da && da->type.in(ID($bmux), ID($mux));
			bool b_is_read = db && db->type.in(ID($bmux), ID($mux));
			if (a_is_read == b_is_read)
				return false;
			acc = a_is_read ? xb[0] : xa[0];
			term = a_is_read ? xa[0] : xb[0];
			st.acc_out = xy[0];
		}
		if (!st.acc_out.wire)
			return false;

		st.xor_cell = xor_cell;
		st.acc_in = acc;
		st.term = term;
		if (!read_table(term, st.tbl_cell, st.sel, st.table))
			return false;
		// The indexed read must be private to this step, otherwise pruning it
		// would need a rebuild for every other consumer too.
		if (sole_consumer(term) != xor_cell)
			return false;
		return true;
	}

	// -------------------------------------------------------------- verify
	// Exhaustively enumerate the control support and record, for every
	// assignment that activates the chain, which table slot each step reads.
	bool analyze_reach(Chain &ch, const vector<SigBit> &ctrl_bits,
	                   vector<std::pair<uint64_t, vector<int>>> &live_cfgs)
	{
		SigSpec ctrl_sig;
		for (auto b : ctrl_bits)
			ctrl_sig.append(b);
		int n = GetSize(ctrl_bits);
		ConstEval &ce = shared_ce();

		for (uint64_t v = 0; v < (1ULL << n); v++) {
			charge_eval(GetSize(ch.steps) + 4);
			if (eval_exhausted())
				return false;
			ce.push();
			if (n > 0)
				ce.set(ctrl_sig, const_u64(v, n));

			SigSpec gs(ch.guard), undef;
			bool ok = ce.eval(gs, undef) && gs.is_fully_const();
			if (!ok) {
				ce.pop();
				return false;
			}
			bool active = (gs.as_bool() != ch.guard_inv);
			if (!active) {
				ce.pop();
				continue;
			}

			// -1 marks a step whose guard is low: it contributes no term.
			vector<int> slots(GetSize(ch.steps), -1);
			for (int k = 0; k < GetSize(ch.steps) && ok; k++) {
				Step &st = ch.steps[k];
				if (st.guard != State::S1) {
					SigSpec gk(st.guard);
					ok = ce.eval(gk, undef) && gk.is_fully_const();
					if (!ok)
						break;
					if (gk.as_bool() == st.guard_inv)
						continue;
				}
				SigSpec sk = st.sel;
				ok = ce.eval(sk, undef) && sk.is_fully_const();
				if (!ok)
					break;
				int slot = sk.as_int(false);
				if (slot < 0 || slot >= GetSize(st.table)) {
					ok = false;
					break;
				}
				st.reach.insert(slot);
				slots[k] = slot;
			}
			ce.pop();
			if (!ok)
				return false;
			live_cfgs.push_back(std::make_pair(v, slots));
		}
		return !live_cfgs.empty();
	}

	// Fingerprint the flattened model against the original chain: force the
	// control assignment plus random values on every table entry and a_0, then
	// compare ConstEval on the old chain output with the predicted parity.
	bool verify_model(Chain &ch, const vector<SigBit> &ctrl_bits,
	                  const vector<std::pair<uint64_t, vector<int>>> &live_cfgs,
	                  const pool<Cell *> &ctrl_cells, const pool<SigBit> &chain_bits)
	{
		dict<SigBit, int> ctrl_idx;
		for (int i = 0; i < GetSize(ctrl_bits); i++)
			ctrl_idx[ctrl_bits[i]] = i;

		vector<SigBit> data_bits;
		dict<SigBit, int> data_idx;
		// The chain's own accumulators must stay computed, not forced, or the
		// reference evaluation would be cut at every back-reference slot.
		auto add_data = [&](SigBit b) {
			if (!b.wire || data_idx.count(b) || ctrl_idx.count(b) || chain_bits.count(b))
				return true;
			// A forced bit driven from inside the control cone would be
			// clobbered when ConstEval evaluates that driver.
			if (ctrl_cells.count(bit_to_driver.at(b, nullptr)))
				return false;
			data_idx[b] = GetSize(data_bits);
			data_bits.push_back(b);
			return true;
		};
		if (!add_data(ch.start))
			return false;
		for (auto &st : ch.steps)
			for (auto b : st.table)
				if (!add_data(b))
					return false;
		if (GetSize(data_bits) > 1024)
			return false;

		SigSpec ctrl_sig;
		for (auto b : ctrl_bits)
			ctrl_sig.append(b);
		SigSpec data_sig;
		for (auto b : data_bits)
			data_sig.append(b);
		int nd = GetSize(data_bits);
		int nc = GetSize(ctrl_bits);
		ConstEval &ce = shared_ce();
		vector<State> dv(nd, State::S0);

		// Bits shared with the control support take their value from the
		// enumerated assignment, not from the random data vector.
		auto bit_value = [&](SigBit b, uint64_t cfg, bool &ok) {
			if (!b.wire)
				return b == State::S1;
			auto ci = ctrl_idx.find(b);
			if (ci != ctrl_idx.end())
				return ((cfg >> ci->second) & 1ULL) != 0;
			auto di = data_idx.find(b);
			if (di == data_idx.end()) {
				ok = false;
				return false;
			}
			return dv[di->second] == State::S1;
		};

		for (auto &cfg : live_cfgs) {
			for (int t = 0; t < verify_vectors; t++) {
				charge_eval(nd + GetSize(ch.steps) * 4);
				if (eval_exhausted())
					return false;

				for (int i = 0; i < nd; i++)
					dv[i] = (next_rand() & 1) ? State::S1 : State::S0;

				ce.push();
				if (nc > 0)
					ce.set(ctrl_sig, const_u64(cfg.first, nc));
				if (nd > 0)
					ce.set(data_sig, Const(dv));
				SigSpec out(ch.out), undef;
				bool ok = ce.eval(out, undef) && out.is_fully_const();
				ce.pop();
				if (!ok)
					return false;

				bool have = true;
				bool want = bit_value(ch.start, cfg.first, have);
				for (int k = 0; k < GetSize(ch.steps); k++) {
					int slot = cfg.second[k];
					if (slot < 0)
						continue;
					want ^= bit_value(ch.steps[k].table[slot], cfg.first, have);
				}
				if (!have || out.as_bool() != want)
					return false;
			}
		}
		return true;
	}

	// --------------------------------------------------------------- drive
	bool reject(const char *why)
	{
		log_debug("    reject: %s\n", why);
		return false;
	}

	bool try_chain(Chain &ch)
	{
		log_debug("  chain of %d step(s) out=%s\n", GetSize(ch.steps), log_signal(ch.out));
		if (GetSize(ch.steps) < min_steps || GetSize(ch.steps) > max_steps)
			return reject("chain length out of range");

		int64_t table_bits = 0;
		for (auto &st : ch.steps)
			table_bits += GetSize(st.table);
		if (table_bits > max_table_bits)
			return reject("table too large");

		// The activation guard is what makes the back-reference slots
		// don't-care, so a chain result with any other use is out of scope.
		if (ch.out.wire && ch.out.wire->port_output)
			return reject("chain result is a module output");
		ch.sink = sole_consumer(ch.out);
		if (ch.sink == nullptr || ch.sink->type != ID($mux))
			return reject("chain result is not consumed by a single guard mux");
		// Applying the fold rewires the guard mux's data port, so it has to be
		// in the selection too -- the consumer index spans every cell.
		if (!module->design->selected(module, ch.sink))
			return reject("guard mux is not selected");
		SigSpec sa = sigmap(ch.sink->getPort(ID::A));
		SigSpec sb = sigmap(ch.sink->getPort(ID::B));
		SigSpec ss = sigmap(ch.sink->getPort(ID::S));
		int q = -1;
		bool on_a = false;
		for (int i = 0; i < GetSize(sa); i++) {
			if (sb[i] == ch.out) {
				q = i;
				break;
			}
			if (sa[i] == ch.out) {
				q = i;
				on_a = true;
				break;
			}
		}
		if (q < 0)
			return reject("chain result not found on a guard mux data port");
		ch.guard = ss[0];
		ch.guard_inv = on_a;

		// Intermediate accumulators must be chain-private, otherwise the
		// original serial chain stays alive next to the emitted tree.
		for (int k = 1; k < GetSize(ch.steps); k++) {
			Step &st = ch.steps[k];
			auto it = bit_consumers.find(st.acc_in);
			if (it == bit_consumers.end())
				return reject("intermediate accumulator has no consumer");
			for (auto c : it->second)
				if (c != st.xor_cell && c != st.mux_cell && c != st.tbl_cell)
					return reject("intermediate accumulator escapes the chain");
		}

		// Control support: everything the guards and the read indices depend
		// on. Small by construction for stride/count-driven folds.
		SigSpec ctrl_probe(ch.guard);
		for (auto &st : ch.steps) {
			ctrl_probe.append(st.sel);
			if (st.guard != State::S1)
				ctrl_probe.append(st.guard);
		}
		pool<Cell *> ctrl_cells;
		pool<SigBit> ctrl_leaves;
		if (!get_cone(ctrl_probe, ctrl_cells, ctrl_leaves, 4096, max_ctrl_bits))
			return reject("control cone too large to enumerate");
		for (auto &st : ch.steps)
			if (ctrl_cells.count(st.xor_cell) || ctrl_cells.count(st.tbl_cell))
				return reject("control cone depends on the chain itself");
		vector<SigBit> ctrl_bits(ctrl_leaves.begin(), ctrl_leaves.end());
		std::sort(ctrl_bits.begin(), ctrl_bits.end());
		if (GetSize(ctrl_bits) > max_ctrl_bits)
			return reject("control support too wide");

		vector<std::pair<uint64_t, vector<int>>> live_cfgs;
		if (!analyze_reach(ch, ctrl_bits, live_cfgs))
			return reject("control enumeration failed or guard never active");

		// Every remaining back-reference keeps the chain serial, so bail
		// instead of emitting something no shallower than the original.
		pool<SigBit> chain_bits;
		for (auto &st : ch.steps)
			chain_bits.insert(st.acc_out);
		int live_slots = 0;
		for (auto &st : ch.steps) {
			for (int p : st.reach) {
				if (st.table[p] == st.acc_in || chain_bits.count(st.table[p]))
					return reject("reachable slot still back-references the chain");
				live_slots++;
			}
		}
		if (live_slots == 0)
			return reject("no reachable slot");
		// A surviving entry computed from the chain itself would keep the
		// serial dependency even though it is not literally an accumulator.
		pool<Cell *> entry_cells;
		pool<SigBit> entry_leaves;
		SigSpec entry_probe;
		for (auto &st : ch.steps)
			for (int p : st.reach)
				entry_probe.append(st.table[p]);
		if (!get_cone(entry_probe, entry_cells, entry_leaves, 20000, 4096))
			return reject("read-entry cone too large");
		for (auto &st : ch.steps)
			if (entry_cells.count(st.xor_cell) ||
			    (st.mux_cell && entry_cells.count(st.mux_cell)))
				return reject("reachable entry is computed from the chain");

		if (!verify_model(ch, ctrl_bits, live_cfgs, ctrl_cells, chain_bits))
			return reject("ConstEval fingerprint mismatch");

		// Emit: a_K = a_0 ^ XOR_k (g_k & pruned_read_k)
		anchor = ch.steps.front().xor_cell;
		vector<SigBit> terms;
		terms.push_back(ch.start);
		for (auto &st : ch.steps) {
			SigBit read = emit_pruned_read(st);
			SigBit g = st.guard;
			if (g != State::S1 && st.guard_inv)
				g = emit_not(g);
			terms.push_back(emit_and(read, g));
		}
		SigBit rebuilt = emit_xor_tree(terms);

		SigSpec new_port = ch.sink->getPort(on_a ? ID::A : ID::B);
		new_port[q] = rebuilt;
		ch.sink->setPort(on_a ? ID::A : ID::B, new_port);

		for (auto &st : ch.steps) {
			used_cells.insert(st.xor_cell);
			if (st.mux_cell)
				used_cells.insert(st.mux_cell);
		}
		chains_rewritten++;
		steps_rewritten += GetSize(ch.steps);
		log_debug("  rewrote fold chain of %d step(s) into %s (%d live slot(s))\n",
		          GetSize(ch.steps), log_signal(rebuilt), live_slots);
		return true;
	}

	void run()
	{
		if (strict)
			return;

		vector<Step> steps;
		dict<SigBit, int> step_by_out;
		pool<SigBit> is_acc_in;
		// Only the match seed is filtered by the selection; bit_consumers
		// still indexes every cell so the sole_consumer checks stay exact.
		for (auto c : module->selected_cells()) {
			Step st;
			if (!make_step(c, st))
				continue;
			if (step_by_out.count(st.acc_out))
				continue;
			step_by_out[st.acc_out] = GetSize(steps);
			is_acc_in.insert(st.acc_in);
			steps.push_back(st);
		}

		log_debug("module %s: %d candidate fold step(s)\n", log_id(module), GetSize(steps));

		// Chain tails are steps whose result does not feed another step.
		vector<int> tails;
		for (int i = 0; i < GetSize(steps); i++)
			if (!is_acc_in.count(steps[i].acc_out))
				tails.push_back(i);

		for (int tail : tails) {
			if (walk_exhausted() || eval_exhausted())
				break;
			Chain ch;
			int cur = tail;
			pool<int> seen;
			while (true) {
				if (!seen.insert(cur).second)
					break;
				if (used_cells.count(steps[cur].xor_cell))
					break;
				ch.steps.push_back(steps[cur]);
				charge_walk(1);
				auto it = step_by_out.find(steps[cur].acc_in);
				if (it == step_by_out.end() || GetSize(ch.steps) >= max_steps)
					break;
				cur = it->second;
			}
			std::reverse(ch.steps.begin(), ch.steps.end());
			if (ch.steps.empty())
				continue;
			ch.start = ch.steps.front().acc_in;
			ch.out = ch.steps.back().acc_out;
			try_chain(ch);
		}
	}
};

// analyze_reach enumerates 1ULL << max_ctrl_bits assignments, so the option
// needs a ceiling that keeps the shift defined; the eval budget bails out long
// before this many anyway.
static const int max_ctrl_bits_limit = 24;

struct OptXorFoldPass : public Pass
{
	OptXorFoldPass() : Pass("opt_xor_fold",
		"flatten in-place XOR folds over dynamically indexed vector bits") {}

	void help() override
	{
		log("\n");
		log("    opt_xor_fold [options] [selection]\n");
		log("\n");
		log("Detect an in-place XOR accumulation over dynamically indexed bits of a\n");
		log("vector, e.g.\n");
		log("\n");
		log("    for (j = 0; j < J; j++)\n");
		log("      if (j < count) v[i] = v[i] ^ v[i + j*stride];\n");
		log("\n");
		log("Elaboration turns each such statement into a read-modify-write chain\n");
		log("whose indexed read table still holds the running accumulator (and the\n");
		log("already-written bits), so the chain is serial across both the inner\n");
		log("loop and the written bits. Since the chain result is only consumed\n");
		log("under an activation guard, the table slots that no guard-satisfying\n");
		log("control assignment can select are don't-cares; pruning them removes the\n");
		log("feedback and the chain collapses to a balanced masked-XOR tree:\n");
		log("\n");
		log("    a_K = a_0 ^ XOR_k (g_k & read_k)\n");
		log("\n");
		log("Reachability is decided by exhaustively enumerating the control cone\n");
		log("shared by the guards and the read indices (stride/count ports), and\n");
		log("every rewrite is checked by ConstEval fingerprinting against the\n");
		log("original chain before it is applied.\n");
		log("\n");
		log("    -strict\n");
		log("        disable the pass. The rewrite relies on don't-care freedom in\n");
		log("        the unreachable table slots, which equiv_opt -assert cannot\n");
		log("        see, so formal mode runs with -strict.\n");
		log("\n");
		log("    -min-steps N, -min_steps N\n");
		log("        minimum chain length to consider (default 2).\n");
		log("\n");
		log("    -max-steps N, -max_steps N\n");
		log("        maximum chain length to consider (default 64).\n");
		log("\n");
		log("    -max-ctrl-bits N, -max_ctrl_bits N\n");
		log("        maximum control support to enumerate, in bits (default 12,\n");
		log("        ceiling %d). Chains with a wider control cone are skipped.\n",
		    max_ctrl_bits_limit);
		log("\n");
		log("    -max-table-bits N, -max_table_bits N\n");
		log("        maximum total indexed-read table size per chain (default 8192).\n");
		log("\n");
		log("    -verify-vectors N, -verify_vectors N\n");
		log("        fingerprint vectors per control assignment (default 4).\n");
		log("\n");
		log("    -walk-budget N, -eval-budget N\n");
		log("        per-module work limits for the search (defaults 20000000).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_XOR_FOLD pass (flatten in-place XOR folds).\n");

		bool strict = false;
		int min_steps = 2, max_steps = 64, max_ctrl_bits = 12;
		int max_table_bits = 8192, verify_vectors = 4;
		int64_t walk_budget = -1, eval_budget = -1;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-strict") {
				strict = true;
				continue;
			}
			if ((args[argidx] == "-min-steps" || args[argidx] == "-min_steps") &&
			    argidx + 1 < args.size()) {
				min_steps = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-steps" || args[argidx] == "-max_steps") &&
			    argidx + 1 < args.size()) {
				max_steps = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-ctrl-bits" || args[argidx] == "-max_ctrl_bits") &&
			    argidx + 1 < args.size()) {
				max_ctrl_bits = std::stoi(args[++argidx]);
				if (max_ctrl_bits < 0 || max_ctrl_bits > max_ctrl_bits_limit)
					log_cmd_error("-max-ctrl-bits must be in 0..%d.\n",
					              max_ctrl_bits_limit);
				continue;
			}
			if ((args[argidx] == "-max-table-bits" || args[argidx] == "-max_table_bits") &&
			    argidx + 1 < args.size()) {
				max_table_bits = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-verify-vectors" || args[argidx] == "-verify_vectors") &&
			    argidx + 1 < args.size()) {
				verify_vectors = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-walk-budget" || args[argidx] == "-walk_budget") &&
			    argidx + 1 < args.size()) {
				walk_budget = std::stoll(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-eval-budget" || args[argidx] == "-eval_budget") &&
			    argidx + 1 < args.size()) {
				eval_budget = std::stoll(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_chains = 0, total_steps = 0, total_cells = 0;
		for (auto module : design->selected_modules()) {
			OptXorFoldWorker worker(module);
			worker.strict = strict;
			worker.min_steps = min_steps;
			worker.max_steps = max_steps;
			worker.max_ctrl_bits = max_ctrl_bits;
			worker.max_table_bits = max_table_bits;
			worker.verify_vectors = verify_vectors;
			if (walk_budget > 0)
				worker.walk_budget = walk_budget;
			if (eval_budget > 0)
				worker.eval_budget = eval_budget;
			worker.run();
			total_chains += worker.chains_rewritten;
			total_steps += worker.steps_rewritten;
			total_cells += worker.cells_added;
		}

		log("Rewrote %d XOR fold chain(s) covering %d step(s); emitted %d new cell(s).\n",
		    total_chains, total_steps, total_cells);

		if (total_chains)
			Yosys::run_pass("clean -purge");
	}
} OptXorFoldPass;

PRIVATE_NAMESPACE_END
