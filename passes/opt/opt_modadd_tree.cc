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
#include <algorithm>
#include <functional>
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/cut_region.h"

// opt_modadd_tree: rebalance a serial narrow-state accumulate cascade into a
// log-depth tree.
//
// Loops of the form
//
//     acc = acc0;
//     for (i = 0; i < N; i++) acc = step(acc, digit_i);
//
// (mod-M digit sums, running remainders, small saturating counters, ...)
// synthesize to a linear cascade of N steps, so logic depth grows with N.
// Whatever `step` is, the cascade is a composition of the state-to-state
// transfer functions T_{digit_i}, and function composition is associative, so
// the cascade can always be re-bracketed as a balanced tree. Two emit shapes:
//
//   1. associative tree - when every transfer function is faithfully
//      identified by the state it produces from one seed state s0 (exactly
//      the condition "step is associative", which real (acc + d) mod M
//      satisfies for any M), a partial result is a single w-bit state and
//      tree nodes combine two of them with a proven 2w->w const table, or
//      better, with a copy of the cascade's own step logic when a step is
//      proven to already compute that table. This is the cheap shape and the
//      one mod-M RTL wants.
//
//   2. transfer-function tree - otherwise carry the whole state->state map
//      (2^w slots of w bits) and compose slot-wise. Always sound, but it
//      needs 2^w copies of the step logic, so it is gated on width, chain
//      length and clone-count budgets.
//
// Both shapes are derived from the netlist itself (cloned step cones, and for
// shape 1 a ConstEval-proven table), so the pass never assumes a particular
// spelling of the reduction and never relies on don't-care freedom. Only the
// state has to flow serially: the addends may come from anywhere, including
// pre-logic shared by every step (a barrel shifter, a mux tree, ...), which
// the rewrite leaves in place and the tree leaves read unchanged.
struct OptModAddTreeWorker : CutRegionWorker
{
	// Tunables (see Pass::execute).
	int max_state_bits = 4;
	int min_state_bits = 2;
	int min_nodes = 4;
	int max_nodes = 64;
	int max_cone_cells = 512;
	int max_leaf_bits = 512;
	int max_digit_bits = 10;
	int max_clones = 1024;
	int min_serial_depth = 32;
	int min_depth_gain = 2;

	int table_regions = 0;
	int vector_regions = 0;
	int cells_added = 0;

	dict<SigBit, pool<Cell *>> bit_to_sinks;
	pool<SigBit> output_port_bits;

	// Emit anchor (drives NEW_ID2_SUFFIX / src attribution).
	Cell *anchor = nullptr;

	struct Chain {
		SigSpec tail;
		int w = 0;
		// Finest valid cut sequence; grouping picks a subset of these.
		vector<SigSpec> fine_cuts;
		vector<pool<Cell *>> fine_nodes;
		vector<int> fine_depth;

		int head_min = 0;                 // node 0 must cover fine nodes 0..head_min

		vector<SigSpec> cuts;             // cuts[i] = state after node i
		vector<pool<Cell *>> state_cells; // cells of node i that depend on cuts[i-1]
		pool<Cell *> head_cells;          // node 0: produces the initial state
		pool<Cell *> cone;
	};

	OptModAddTreeWorker(Module *module) : CutRegionWorker(module)
	{
		for (auto c : module->cells())
			for (auto &conn : c->connections())
				if (c->input(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							bit_to_sinks[bit].insert(c);

		for (auto w : module->wires())
			if (w->port_output)
				for (auto bit : sigmap(SigSpec(w)))
					if (bit.wire)
						output_port_bits.insert(bit);
	}

	// ------------------------------------------------------------ detection

	// A cut splits the tail cone in two: no cascade state produced upstream of
	// X may reach a cell downstream of X other than through X itself.
	// `state_free` cells carry no state (shared addend pre-logic such as a
	// barrel shifter feeding every digit); the rewrite leaves their value
	// untouched, so they may fan out to any step. Escaping fanout to cells
	// outside the tail cone is fine (shared pre-logic stays in place).
	bool is_cut(const SigSpec &x, const pool<Cell *> &cx, const pool<Cell *> &cone,
	            const pool<Cell *> &state_free)
	{
		pool<SigBit> xbits = sig_bit_pool(x);
		for (auto c : cx) {
			if (state_free.count(c))
				continue;
			charge_walk(1);
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire || xbits.count(bit))
						continue;
					for (auto sink : bit_to_sinks.at(bit, pool<Cell *>()))
						if (cone.count(sink) && !cx.count(sink))
							return false;
				}
			}
		}
		return true;
	}

	// True when a non-tail output of `c` is read from outside the region (or
	// is a module output). Such a cell survives the rewrite, so cloning it
	// leaves the serial chain alive next to its tree.
	bool cell_escapes(Cell *c, const pool<Cell *> &cone, const pool<SigBit> &tail_bits)
	{
		charge_walk(1);
		for (auto &conn : c->connections()) {
			if (!c->output(conn.first))
				continue;
			for (auto bit : sigmap(conn.second)) {
				if (!bit.wire || tail_bits.count(bit))
					continue;
				if (output_port_bits.count(bit))
					return true;
				for (auto sink : bit_to_sinks.at(bit, pool<Cell *>()))
					if (!cone.count(sink))
						return true;
			}
		}
		return false;
	}

	// Intermediate states must die with the old cascade, else the rewrite
	// only adds area.
	bool cut_is_internal(const SigSpec &x, const pool<Cell *> &cone)
	{
		for (auto bit : sigmap(x)) {
			if (!bit.wire || output_port_bits.count(bit))
				return false;
			for (auto sink : bit_to_sinks.at(bit, pool<Cell *>()))
				if (!cone.count(sink))
					return false;
		}
		return true;
	}

	// Cells of `region` reachable forward from `from`; the rest of the region
	// is state-independent and does not need to be cloned per slot.
	pool<Cell *> forward_cells(const SigSpec &from, const pool<Cell *> &region)
	{
		pool<Cell *> reached;
		std::queue<Cell *> work;
		for (auto bit : sigmap(from))
			if (bit.wire)
				for (auto sink : bit_to_sinks.at(bit, pool<Cell *>()))
					if (region.count(sink) && reached.insert(sink).second)
						work.push(sink);

		while (!work.empty()) {
			Cell *c = work.front();
			work.pop();
			charge_walk(1);
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second))
					if (bit.wire)
						for (auto sink : bit_to_sinks.at(bit, pool<Cell *>()))
							if (region.count(sink) && reached.insert(sink).second)
								work.push(sink);
			}
		}
		return reached;
	}

	// Rough post-techmap depth of a cell, so a wide adder is not counted as
	// one level next to a mux.
	static int cell_depth(Cell *c)
	{
		int w = 1;
		for (auto port : {ID::A, ID::B})
			if (c->hasPort(port))
				w = std::max(w, GetSize(c->getPort(port)));
		if (c->type.in(ID($add), ID($sub), ID($neg), ID($lt), ID($le), ID($gt), ID($ge),
		               ID($eq), ID($ne), ID($eqx), ID($nex)))
			return clog2_int(w) + 1;
		if (c->type.in(ID($mul), ID($div), ID($mod), ID($shl), ID($shr), ID($sshl),
		               ID($sshr), ID($shift), ID($shiftx)))
			return 2 * clog2_int(w) + 1;
		if (c->type == ID($bmux))
			return GetSize(c->getPort(ID::S));
		if (c->type == ID($pmux))
			return clog2_int(GetSize(c->getPort(ID::S))) + 1;
		return 1;
	}

	// Longest weighted path inside `cells`, used to balance leaf depth against
	// the depth one tree level costs.
	int region_depth(const pool<Cell *> &cells)
	{
		vector<std::pair<int, Cell *>> order;
		for (auto &it : compute_cone_depths(cells))
			order.push_back({it.second, it.first});
		std::sort(order.begin(), order.end(),
		          [](const std::pair<int, Cell *> &a, const std::pair<int, Cell *> &b) {
		              return a.first != b.first ? a.first < b.first
		                                        : a.second->name.str() < b.second->name.str();
		          });

		dict<SigBit, int> arrival;
		int best = 0;
		for (auto &e : order) {
			Cell *c = e.second;
			int in = 0;
			for (auto &conn : c->connections())
				if (c->input(conn.first))
					for (auto bit : sigmap(conn.second))
						in = std::max(in, arrival.at(bit, 0));
			int out = in + cell_depth(c);
			for (auto &conn : c->connections())
				if (c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						arrival[bit] = out;
			best = std::max(best, out);
		}
		return best;
	}

	bool find_chain(const SigSpec &tail, Chain &ch)
	{
		int w = GetSize(tail);
		pool<Cell *> cone;
		pool<SigBit> leaves;
		if (!get_cone(tail, cone, leaves, max_cone_cells, max_leaf_bits))
			return false;
		if (GetSize(cone) < min_nodes)
			return false;

		// Candidate cuts: same-width output buses produced inside the cone.
		vector<SigSpec> cands;
		pool<SigSpec> seen;
		for (auto c : cone)
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first) || GetSize(conn.second) != w)
					continue;
				SigSpec sig = sigmap(conn.second);
				if (sig == sigmap(tail) || !sig_bus_ok(sig))
					continue;
				if (seen.insert(sig).second)
					cands.push_back(sig);
			}
		if (GetSize(cands) + 1 < min_nodes)
			return false;

		// A cell that neither produces nor can reach a candidate state computes
		// an addend: the rewrite leaves its value alone, so it may feed any
		// number of steps. One forward walk over every candidate keeps this
		// conservative whichever cuts the chain ends up using.
		SigSpec cand_bits;
		for (auto &sig : cands)
			cand_bits.append(sig);
		pool<Cell *> downstream = forward_cells(cand_bits, cone);
		pool<Cell *> state_free;
		for (auto c : cone)
			if (!downstream.count(c))
				state_free.insert(c);
		// A cell producing a candidate is a state producer even though no
		// candidate reaches it, so it must not be treated as pre-logic.
		for (auto bit : sigmap(cand_bits)) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr)
				state_free.erase(drv);
		}

		// Keep the valid cuts, ordered by how much of the cone they cover.
		vector<std::pair<int, int>> ranked;
		vector<pool<Cell *>> cand_cones(GetSize(cands));
		for (int i = 0; i < GetSize(cands); i++) {
			if (walk_exhausted())
				return false;
			pool<SigBit> sub_leaves;
			if (!get_cone(cands[i], cand_cones[i], sub_leaves, max_cone_cells, max_leaf_bits))
				continue;
			if (!cut_is_internal(cands[i], cone))
				continue;
			if (!is_cut(cands[i], cand_cones[i], cone, state_free))
				continue;
			ranked.push_back({GetSize(cand_cones[i]), i});
		}
		std::sort(ranked.begin(), ranked.end());

		// Valid cuts nest; drop any that does not extend the previous one.
		vector<SigSpec> fine_cuts;
		vector<pool<Cell *>> fine_nodes;
		pool<Cell *> covered;
		for (auto &r : ranked) {
			const pool<Cell *> &cx = cand_cones[r.second];
			if (GetSize(cx) <= GetSize(covered))
				continue;
			bool nests = true;
			for (auto c : covered)
				if (!cx.count(c)) {
					nests = false;
					break;
				}
			if (!nests)
				continue;
			pool<Cell *> node;
			for (auto c : cx)
				if (!covered.count(c))
					node.insert(c);
			fine_cuts.push_back(cands[r.second]);
			fine_nodes.push_back(node);
			covered = cx;
		}
		{
			pool<Cell *> node;
			for (auto c : cone)
				if (!covered.count(c))
					node.insert(c);
			if (node.empty() && !fine_cuts.empty()) {
				fine_cuts.pop_back();
				fine_nodes.pop_back();
			}
			fine_cuts.push_back(sigmap(tail));
			fine_nodes.push_back(node);
		}
		if (GetSize(fine_cuts) < min_nodes)
			return false;

		ch.tail = sigmap(tail);
		ch.w = w;
		ch.cone = cone;
		ch.fine_cuts = fine_cuts;
		ch.fine_nodes = fine_nodes;

		// A node clones exactly what its incoming cut reaches, and node 0 is
		// left in place, so an escaping cell is tolerable only if node 0 grows
		// to cover it. The same walk bounds the state path and spots the
		// ripple, killing most non-cascades before the grouping sweep.
		pool<SigBit> tail_bits = sig_bit_pool(tail);
		ch.head_min = 0;
		int serial = 0;
		bool ripple = false;
		for (int i = 1; i < GetSize(fine_nodes); i++) {
			pool<Cell *> fwd = forward_cells(fine_cuts[i - 1], fine_nodes[i]);
			serial += region_depth(fwd);
			for (auto c : fwd) {
				ripple |= cell_depth(c) > 1;
				if (cell_escapes(c, cone, tail_bits))
					ch.head_min = std::max(ch.head_min, i);
			}
		}
		if (GetSize(fine_cuts) - ch.head_min < min_nodes) {
			log_debug("  skipping cascade at %s: state escapes up to fine node %d "
			          "of %d\n", log_signal(tail), ch.head_min, GetSize(fine_cuts));
			return false;
		}
		if (!ripple || serial < min_serial_depth) {
			log_debug("  skipping cascade at %s: serial depth at most %d, %s\n",
			          log_signal(tail), serial,
			          ripple ? "below the minimum" : "pure bitwise logic");
			return false;
		}

		ch.fine_depth.clear();
		for (auto &node : fine_nodes)
			ch.fine_depth.push_back(region_depth(node));
		log_debug("  chain at %s: %d fine cut(s), serial depth at most %d\n",
		          log_signal(tail), GetSize(ch.fine_cuts), serial);
		return true;
	}

	// Group `stride` consecutive steps per tree leaf (the first leaf takes
	// `first_len`). A tree level costs about a 2w-input lookup, so leaves that
	// deep are free; the phase matters because only some cut positions are the
	// cascade's real accumulator.
	bool apply_grouping(Chain &ch, int stride, int first_len)
	{
		int nfine = GetSize(ch.fine_nodes);
		vector<int> keep;
		for (int i = std::max(first_len - 1, ch.head_min); i < nfine;
		     i += (GetSize(keep) ? stride : 1))
			keep.push_back(i);
		if (keep.empty() || keep.back() != nfine - 1)
			keep.push_back(nfine - 1);
		if (GetSize(keep) < min_nodes || GetSize(keep) > max_nodes)
			return false;

		ch.cuts.clear();
		ch.state_cells.clear();
		ch.head_cells.clear();
		int lo = 0;
		for (int k = 0; k < GetSize(keep); k++) {
			pool<Cell *> group;
			for (int i = lo; i <= keep[k]; i++)
				for (auto c : ch.fine_nodes[i])
					group.insert(c);
			lo = keep[k] + 1;
			ch.cuts.push_back(ch.fine_cuts[keep[k]]);
			if (k == 0) {
				ch.head_cells = group;
				ch.state_cells.push_back(pool<Cell *>());
			} else {
				ch.state_cells.push_back(forward_cells(ch.cuts[k - 1], group));
			}
		}

		// Node 0 must be state-free and every later node must actually
		// consume the previous state, else this is not a cascade.
		for (int i = 1; i < GetSize(ch.cuts); i++)
			if (ch.state_cells[i].empty())
				return false;
		return true;
	}

	int default_stride(const Chain &ch)
	{
		int total = 0;
		for (int d : ch.fine_depth)
			total += d;
		if (total <= 0)
			return 1;
		int nfine = GetSize(ch.fine_depth);
		return std::max(1, (2 * ch.w * nfine + total / 2) / total);
	}

	// -------------------------------------------------------------- cloning

	// Deterministic cell order, so digit bit numbering and emitted names do
	// not depend on pool iteration order.
	vector<Cell *> ordered_cells(const pool<Cell *> &cells)
	{
		vector<Cell *> out(cells.begin(), cells.end());
		std::sort(out.begin(), out.end(),
		          [](Cell *a, Cell *b) { return a->name.str() < b->name.str(); });
		return out;
	}

	// Rebuild node `i`'s state-dependent cells with `subst` applied to their
	// inputs; everything not substituted keeps reading the original signals.
	SigSpec clone_node(const Chain &ch, int i, dict<SigBit, SigBit> subst)
	{
		vector<Cell *> cells = ordered_cells(ch.state_cells[i]);
		for (auto c : cells)
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				SigSpec o = sigmap(conn.second);
				Cell *cell = c;
				Wire *nw = module->addWire(NEW_ID2_SUFFIX("modadd_slot"), GetSize(o));
				for (int b = 0; b < GetSize(o); b++)
					if (o[b].wire)
						subst[o[b]] = SigBit(nw, b);
			}

		auto lookup = [&](const SigSpec &sig) {
			SigSpec out;
			for (auto bit : sigmap(sig))
				out.append(subst.count(bit) ? subst.at(bit) : bit);
			return out;
		};

		for (auto c : cells) {
			Cell *cell = c;
			Cell *nc = module->addCell(NEW_ID2_SUFFIX("modadd_step"), c->type);
			nc->parameters = c->parameters;
			nc->attributes = c->attributes;
			for (auto &conn : c->connections())
				nc->setPort(conn.first, lookup(conn.second));
			cells_added++;
		}

		return lookup(ch.cuts[i]);
	}

	dict<SigBit, SigBit> const_subst(const SigSpec &sig, int value)
	{
		dict<SigBit, SigBit> subst;
		for (int b = 0; b < GetSize(sig); b++)
			if (sig[b].wire)
				subst[sig[b]] = ((value >> b) & 1) ? State::S1 : State::S0;
		return subst;
	}

	dict<SigBit, SigBit> sig_subst(const SigSpec &from, const SigSpec &to)
	{
		dict<SigBit, SigBit> subst;
		for (int b = 0; b < GetSize(from); b++)
			if (from[b].wire)
				subst[from[b]] = to[b];
		return subst;
	}

	// ----------------------------------------------------------------- emit

	SigSpec emit_bmux(const SigSpec &data, const SigSpec &sel, int width)
	{
		Cell *cell = anchor;
		Wire *y = module->addWire(NEW_ID2_SUFFIX("modadd_lut"), width);
		module->addBmux(NEW_ID2_SUFFIX("modadd_lut_cell"), data, sel, y, cell_src(anchor));
		cells_added++;
		return SigSpec(y);
	}

	// A partial result: either one state value (const-table shape, or a
	// transfer map that turned out to be constant across slots) or the full
	// per-slot map.
	struct Vec {
		bool uniform = false;
		SigSpec val;
		vector<SigSpec> slots;
	};

	// out[s] = b[a[s]] : apply `a` first, then `b`.
	Vec compose(const Vec &a, const Vec &b, int w)
	{
		Vec out;
		if (b.uniform) {
			out.uniform = true;
			out.val = b.val;
			return out;
		}
		SigSpec data;
		for (auto &slot : b.slots)
			data.append(slot);
		if (a.uniform) {
			out.uniform = true;
			out.val = emit_bmux(data, a.val, w);
			return out;
		}
		out.slots.reserve(GetSize(a.slots));
		for (auto &slot : a.slots)
			out.slots.push_back(emit_bmux(data, slot, w));
		return out;
	}

	Vec build_vector_tree(vector<Vec> &leaves, int lo, int hi, int w)
	{
		if (hi - lo == 1)
			return leaves[lo];
		int mid = lo + (hi - lo) / 2;
		Vec a = build_vector_tree(leaves, lo, mid, w);
		Vec b = build_vector_tree(leaves, mid, hi, w);
		return compose(a, b, w);
	}

	// Combine two partial results into one. Either the cascade's own step
	// logic (when find_combiner proved one) or the const table.
	struct Combiner {
		const Chain *ch = nullptr;
		int node = -1;
		SigSpec digit;
		SigSpec table;
	};

	SigSpec emit_combine(const Combiner &cb, const SigSpec &a, const SigSpec &b, int w)
	{
		if (cb.node < 0) {
			SigSpec sel = a;
			sel.append(b);
			return emit_bmux(cb.table, sel, w);
		}
		dict<SigBit, SigBit> subst = sig_subst(cb.ch->cuts[cb.node - 1], a);
		for (auto &it : sig_subst(cb.digit, b))
			subst[it.first] = it.second;
		return clone_node(*cb.ch, cb.node, subst);
	}

	SigSpec build_table_tree(vector<SigSpec> &leaves, int lo, int hi, const Combiner &cb, int w)
	{
		if (hi - lo == 1)
			return leaves[lo];
		int mid = lo + (hi - lo) / 2;
		SigSpec a = build_table_tree(leaves, lo, mid, cb, w);
		SigSpec b = build_table_tree(leaves, mid, hi, cb, w);
		return emit_combine(cb, a, b, w);
	}

	// ------------------------------------------------------- const-table tier

	// A region's free input bits, in cell/port/bit order so that a digit of
	// state width lines up with the state's own bit numbering. The addend may
	// be driven by anything (port bits, a shifter, a mux, ...), but forcing a
	// driven bit is only safe when ConstEval never evaluates its driver, so
	// the region's cone must close on state+digit with no forced bit produced
	// inside it.
	bool region_digit(const pool<Cell *> &cells, const SigSpec &state, const SigSpec &out,
	                  SigSpec &digit)
	{
		pool<SigBit> state_bits = sig_bit_pool(state);
		pool<SigBit> internal;
		for (auto c : cells)
			for (auto &conn : c->connections())
				if (c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							internal.insert(bit);

		pool<SigBit> seen;
		bool any_driven = false;
		digit = SigSpec();
		for (auto c : ordered_cells(cells)) {
			vector<IdString> ports;
			for (auto &conn : c->connections())
				if (c->input(conn.first))
					ports.push_back(conn.first);
			std::sort(ports.begin(), ports.end(),
			          [](IdString a, IdString b) { return a.str() < b.str(); });
			for (auto port : ports)
				for (auto bit : sigmap(c->getPort(port))) {
					if (!bit.wire || state_bits.count(bit) || internal.count(bit))
						continue;
					if (seen.insert(bit).second) {
						digit.append(bit);
						if (GetSize(digit) > max_digit_bits)
							return false;
						any_driven |= bit_to_driver.at(bit, nullptr) != nullptr;
					}
				}
		}
		if (!any_driven)
			return true;
		pool<SigBit> forced = seen;
		for (auto bit : state_bits)
			forced.insert(bit);
		return cut_cone_walk(out, forced, max_cone_cells, nullptr, nullptr, &forced);
	}

	bool node_digit(const Chain &ch, int i, SigSpec &digit)
	{
		return region_digit(ch.state_cells[i], ch.cuts[i - 1], ch.cuts[i], digit);
	}

	// Exhaustive transfer function of node `i`, indexed [digit][state].
	bool node_transfers(const Chain &ch, int i, vector<vector<int>> &tables)
	{
		SigSpec digit;
		if (!node_digit(ch, i, digit))
			return false;

		int nstates = 1 << ch.w;
		int ndigits = 1 << GetSize(digit);
		tables.assign(ndigits, vector<int>(nstates, 0));
		ConstEval &ce = shared_ce();
		for (int d = 0; d < ndigits; d++)
			for (int s = 0; s < nstates; s++) {
				vector<std::pair<SigSpec, Const>> sets;
				sets.push_back({ch.cuts[i - 1], const_u64(s, ch.w)});
				if (!digit.empty())
					sets.push_back({digit, const_u64(d, GetSize(digit))});
				uint64_t out = 0;
				if (eval_exhausted() ||
				    !eval_with(ce, sets, ch.cuts[i], out, GetSize(ch.state_cells[i])))
					return false;
				tables[d][s] = int(out);
			}
		return true;
	}

	// States the cascade can actually be in. Transfer functions only have to
	// agree here, which is what makes e.g. a mod-9 accumulator in a 4-bit
	// register associative even though the spare codes 9..15 are not.
	vector<int> reachable_states(const Chain &ch, const vector<vector<int>> &transfers)
	{
		int nstates = 1 << ch.w;
		vector<bool> in(nstates, false);
		vector<int> work;

		SigSpec digit;
		ConstEval &ce = shared_ce();
		bool seeded = region_digit(ch.head_cells, SigSpec(), ch.cuts[0], digit);
		if (seeded) {
			int ndigits = 1 << GetSize(digit);
			for (int d = 0; d < ndigits && seeded; d++) {
				vector<std::pair<SigSpec, Const>> sets;
				if (!digit.empty())
					sets.push_back({digit, const_u64(d, GetSize(digit))});
				uint64_t out = 0;
				if (eval_exhausted() ||
				    !eval_with(ce, sets, ch.cuts[0], out, GetSize(ch.head_cells)))
					seeded = false;
				else if (!in[int(out)]) {
					in[int(out)] = true;
					work.push_back(int(out));
				}
			}
		}
		if (!seeded) {
			work.clear();
			for (int s = 0; s < nstates; s++) {
				in[s] = true;
				work.push_back(s);
			}
		}

		for (int head = 0; head < GetSize(work); head++)
			for (auto &t : transfers) {
				int next = t[work[head]];
				if (!in[next]) {
					in[next] = true;
					work.push_back(next);
				}
			}

		std::sort(work.begin(), work.end());
		return work;
	}

	// Try to represent every reachable transfer function by the single state
	// it produces from some seed s0; that succeeds exactly when composing two
	// steps is itself a step, i.e. when the step operator is associative.
	// Returns the resulting 2w->w combine table and which representatives can
	// actually reach a tree node (the rest of the table is don't-care).
	bool prove_table(const Chain &ch, vector<int> &combine, vector<bool> &live,
	                 vector<int> &reach, int &seed)
	{
		int nstates = 1 << ch.w;
		vector<vector<int>> transfers;
		for (int i = 1; i < GetSize(ch.cuts); i++) {
			vector<vector<int>> tables;
			if (!node_transfers(ch, i, tables)) {
				log_debug("    not associative: step %d is not exhaustively evaluable\n", i);
				return false;
			}
			for (auto &t : tables)
				transfers.push_back(t);
		}
		if (transfers.empty())
			return false;

		reach = reachable_states(ch, transfers);
		int nreach = GetSize(reach);

		// Two transfer functions are the same element if they agree on every
		// reachable state; unreachable codes are don't-care.
		auto key_of = [&](const vector<int> &f) {
			std::string k;
			for (int s : reach)
				k += char('0' + f[s]);
			return k;
		};
		vector<vector<int>> monoid;
		pool<std::string> known;
		for (auto &t : transfers)
			if (known.insert(key_of(t)).second) {
				monoid.push_back(t);
				if (GetSize(monoid) > nreach) {
					log_debug("    not associative: >%d distinct step function(s)\n", nreach);
					return false;
				}
			}

		// Close under composition; more elements than reachable states can
		// never be told apart by a single state representative.
		for (int head = 0; head < GetSize(monoid); head++)
			for (int g = 0, ng = GetSize(monoid); g < ng; g++) {
				vector<int> prod(nstates, 0);
				for (int s : reach)
					prod[s] = monoid[g][monoid[head][s]];
				if (known.insert(key_of(prod)).second) {
					monoid.push_back(prod);
					if (GetSize(monoid) > nreach) {
						log_debug("    not associative: composition closure exceeds "
						          "%d reachable state(s)\n", nreach);
						return false;
					}
				}
			}

		for (int cand : reach) {
			vector<int> rep(nstates, -1);
			bool ok = true;
			for (int m = 0; m < GetSize(monoid) && ok; m++) {
				int r = monoid[m][cand];
				if (rep[r] != -1)
					ok = false;
				else
					rep[r] = m;
			}
			if (!ok)
				continue;
			seed = cand;
			// combine[a | (b << w)] = (the element represented by b)(a)
			combine.assign(nstates * nstates, 0);
			live.assign(nstates, false);
			for (int b = 0; b < nstates; b++) {
				live[b] = rep[b] != -1;
				for (int a = 0; a < nstates; a++)
					combine[a | (b << ch.w)] = rep[b] == -1 ? a : monoid[rep[b]][a];
			}
			return true;
		}
		log_debug("    not associative: no seed state distinguishes all %d element(s)\n",
		          GetSize(monoid));
		return false;
	}

	// A step whose digit is exactly as wide as the state already computes the
	// combine table, so the tree can reuse the cascade's own logic instead of
	// a 2w-input lookup. Verified exhaustively before it is used, and only
	// taken when it is no deeper than the lookup it replaces.
	bool find_combiner(const Chain &ch, const vector<int> &combine, const vector<bool> &live,
	                   const vector<int> &reach, int &node, SigSpec &digit)
	{
		int nstates = 1 << ch.w;
		ConstEval &ce = shared_ce();
		for (int i = 1; i < GetSize(ch.cuts); i++) {
			SigSpec d;
			if (!node_digit(ch, i, d) || GetSize(d) != ch.w)
				continue;
			if (region_depth(ch.state_cells[i]) > 2 * ch.w)
				continue;
			bool ok = true;
			for (int b = 0; b < nstates && ok; b++) {
				if (!live[b])
					continue;
				for (int a : reach) {
					if (!ok)
						break;
					vector<std::pair<SigSpec, Const>> sets = {
						{ch.cuts[i - 1], const_u64(a, ch.w)},
						{d, const_u64(b, ch.w)}};
					uint64_t out = 0;
					if (eval_exhausted() ||
					    !eval_with(ce, sets, ch.cuts[i], out, GetSize(ch.state_cells[i])) ||
					    int(out) != combine[a | (b << ch.w)])
						ok = false;
				}
			}
			if (ok) {
				node = i;
				digit = d;
				return true;
			}
		}
		return false;
	}

	// ------------------------------------------------------------- rewriting

	bool rewrite(Chain &ch)
	{
		int nstates = 1 << ch.w;
		find_anchor_driver(ch.tail, anchor);

		vector<int> combine, reach;
		vector<bool> live;
		int seed = 0;
		bool as_table = false;

		// Only some grouping phases cut at the cascade's real accumulator; a
		// phase that cuts mid-step sees a wider state and cannot be proven
		// associative, so try a few before giving up on the cheap shape.
		int k0 = default_stride(ch);
		for (int k : {k0, k0 + 1, std::max(1, k0 - 1)}) {
			for (int phase = 1; phase <= k && !as_table; phase++)
				if (apply_grouping(ch, k, phase)) {
					log_debug("  try %s: stride %d phase %d, %d node(s)\n",
					          log_signal(ch.tail), k, phase, GetSize(ch.cuts));
					as_table = prove_table(ch, combine, live, reach, seed);
				}
			if (as_table)
				break;
		}
		if (!as_table && !apply_grouping(ch, k0, k0))
			return false;

		int n = GetSize(ch.cuts);
		Combiner cb;
		if (as_table) {
			cb.ch = &ch;
			if (!find_combiner(ch, combine, live, reach, cb.node, cb.digit))
				for (int v : combine)
					cb.table.append(const_u64(v, ch.w));
		}

		// The transfer-function tier copies the step cone once per state, which
		// only pays off when the state is too wide to rebalance associatively.
		// A 1-bit accumulator is a boolean chain that tree balancing flattens
		// for free, so cloning its cone just buys area.
		if (!as_table && ch.w < min_state_bits) {
			log_debug("  skipping general cascade at %s: state width %d below %d\n",
			          log_signal(ch.tail), ch.w, min_state_bits);
			return false;
		}

		int clones = 0;
		for (int i = 1; i < n; i++)
			clones += GetSize(ch.state_cells[i]) * (as_table ? 1 : nstates);
		if (cb.node >= 0)
			clones += GetSize(ch.state_cells[cb.node]) * (n - 1);
		if (clones > max_clones) {
			log_debug("  skipping %s cascade at %s: %d clone(s) exceeds budget %d\n",
			          as_table ? "associative" : "general", log_signal(ch.tail), clones,
			          max_clones);
			return false;
		}

		// Only pay for the rewrite where the tree is a clear win. Compare like
		// with like: the rewrite rebuilds the state path only, so node 0 and
		// each step's addend logic must not count on either side.
		int serial = 0, leaf = 0;
		bool ripple = false;
		for (int i = 1; i < n; i++) {
			int d = region_depth(ch.state_cells[i]);
			serial += d;
			leaf = std::max(leaf, d);
			for (auto c : ch.state_cells[i])
				ripple |= cell_depth(c) > 1;
		}
		// Counting cells only tracks real depth where the step carries a
		// ripple (an add, a compare, a wide select). A step built purely from
		// bitwise gates is restructured downstream anyway, so replicating it
		// buys area, not levels.
		if (!ripple) {
			log_debug("  skipping %s cascade at %s: step is pure bitwise logic\n",
			          as_table ? "associative" : "general", log_signal(ch.tail));
			return false;
		}
		// One tree level costs what emit_combine will actually build: a cloned
		// step, or a lookup selected by 2w (table) / w (per-slot) bits.
		int level = cb.node >= 0 ? region_depth(ch.state_cells[cb.node])
		                         : (as_table ? 2 * ch.w : ch.w);
		int tree = leaf + clog2_int(n) * level;
		if (serial < min_serial_depth || min_depth_gain * tree > serial) {
			log_debug("  skipping %s cascade at %s: serial depth %d vs tree depth %d\n",
			          as_table ? "associative" : "general", log_signal(ch.tail), serial, tree);
			return false;
		}

		log_debug("  %s cascade at %s: %d node(s), state width %d, %d clone(s), "
		          "serial depth %d -> tree depth %d%s\n",
		          as_table ? "associative" : "general", log_signal(ch.tail), n, ch.w, clones,
		          serial, tree, cb.node >= 0 ? ", reusing step logic as combiner" : "");

		SigSpec result;
		if (as_table) {
			vector<SigSpec> leaves;
			for (int i = 1; i < n; i++)
				leaves.push_back(clone_node(ch, i, const_subst(ch.cuts[i - 1], seed)));
			SigSpec root = build_table_tree(leaves, 0, GetSize(leaves), cb, ch.w);
			result = emit_combine(cb, ch.cuts[0], root, ch.w);
		} else {
			vector<Vec> leaves(n);
			leaves[0].uniform = true;
			leaves[0].val = ch.cuts[0];
			for (int i = 1; i < n; i++) {
				leaves[i].slots.reserve(nstates);
				for (int s = 0; s < nstates; s++)
					leaves[i].slots.push_back(
						clone_node(ch, i, const_subst(ch.cuts[i - 1], s)));
			}
			Vec root = build_vector_tree(leaves, 0, n, ch.w);
			log_assert(root.uniform);
			result = root.val;
		}

		disconnect_root(ch.tail, anchor, "modadd_old");
		module->connect(ch.tail, result);
		claim_region(ch.tail, ch.cone);
		// The shared ConstEval indexes drivers at construction time, so it
		// must be rebuilt now that the netlist changed.
		shared_ce_ptr.reset();
		if (as_table)
			table_regions++;
		else
			vector_regions++;
		return true;
	}

	void run()
	{
		auto width_ok = [&](int w) { return w >= 1 && w <= max_state_bits; };
		auto interesting = [&](const pool<Cell *> &cells) { return GetSize(cells) >= min_nodes; };
		auto roots = collect_root_candidates(width_ok, interesting, true,
		                                     max_cone_cells, max_leaf_bits);

		int skipped = 0;
		for (auto &root : roots) {
			if (walk_exhausted()) {
				skipped++;
				continue;
			}
			if (root_claimed(root.sig) || !sig_fully_driven(root.sig))
				continue;
			pool<SigBit> unique_bits;
			if (!sig_bits_unique(root.sig, unique_bits))
				continue;
			Chain ch;
			if (!find_chain(root.sig, ch))
				continue;
			rewrite(ch);
		}
		note_budget("opt_modadd_tree", skipped);
	}
};

struct OptModAddTreePass : public Pass {
	OptModAddTreePass() : Pass("opt_modadd_tree", "serial narrow-state accumulate cascades to trees") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_modadd_tree [options] [selection]\n");
		log("\n");
		log("Rebalance a serial cascade of narrow-state accumulate steps, e.g. the\n");
		log("mod-M digit sum\n");
		log("\n");
		log("    acc = 0; for (i...) begin acc = acc + d[i];\n");
		log("                              if (acc >= M) acc = acc - M; end\n");
		log("\n");
		log("into a log-depth tree. The cascade composes per-digit state transfer\n");
		log("functions, and composition is associative, so it can always be\n");
		log("re-bracketed. Two shapes are emitted:\n");
		log("\n");
		log("  - when the step operator is associative (proven by ConstEval over the\n");
		log("    whole state/digit space, as real (acc + d) mod M is for any M), a\n");
		log("    partial result is one state value and tree nodes combine two of them\n");
		log("    with a proven const table, or with a copy of the cascade's own step\n");
		log("    logic when a step is proven to already compute that table;\n");
		log("\n");
		log("  - otherwise partial results carry the full state->state map and tree\n");
		log("    nodes compose it slot-wise. This costs 2^w copies of the step logic,\n");
		log("    so it is bounded by -max-state-bits / -max-clones.\n");
		log("\n");
		log("Both shapes are built from the cascade's own cells, so the pass is\n");
		log("agnostic to how the reduction was spelled and never relies on don't-care\n");
		log("freedom. Only the state has to flow serially; the addends may be driven\n");
		log("by anything, including pre-logic shared by every step.\n");
		log("\n");
		log("    -max-state-bits N, -max_state_bits N\n");
		log("        maximum accumulator width to consider (default 4).\n");
		log("\n");
		log("    -min-state-bits N, -min_state_bits N\n");
		log("        minimum accumulator width for the general shape (default 2).\n");
		log("        Narrower states are boolean chains that tree balancing\n");
		log("        already flattens, so cloning their step cones only costs area.\n");
		log("\n");
		log("    -min-nodes N, -min_nodes N\n");
		log("        minimum cascade length to rebalance (default 4).\n");
		log("\n");
		log("    -max-nodes N, -max_nodes N\n");
		log("        maximum cascade length to rebalance (default 64).\n");
		log("\n");
		log("    -max-digit-bits N, -max_digit_bits N\n");
		log("        maximum per-step digit width for the associativity proof\n");
		log("        (default 10). Wider steps fall back to the general shape.\n");
		log("\n");
		log("    -max-clones N, -max_clones N\n");
		log("        maximum number of step cells the rewrite may replicate\n");
		log("        (default 1024). Wider states and longer chains bail out here\n");
		log("        instead of exploding area.\n");
		log("\n");
		log("    -min-serial-depth N, -min_serial_depth N\n");
		log("        minimum estimated depth of the original cascade (default 32).\n");
		log("\n");
		log("    -min-depth-gain N, -min_depth_gain N\n");
		log("        require the cascade to be at least N times deeper than the tree\n");
		log("        that replaces it (default 2), so short narrow-state chains are\n");
		log("        not replicated for a level or two.\n");
		log("\n");
		log("    -walk-budget N, -eval-budget N, -attempt-budget N\n");
		log("        per-module work limits for the candidate search (defaults\n");
		log("        20000000 / 20000000 / 65536).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MODADD_TREE pass (serial accumulate cascades to trees).\n");

		int max_state_bits = 4;
		int min_state_bits = 2;
		int min_nodes = 4;
		int max_nodes = 64;
		int max_digit_bits = 10;
		int max_clones = 1024;
		int min_serial_depth = 32;
		int min_depth_gain = 2;
		int64_t walk_budget = -1, eval_budget = -1, attempt_budget = -1;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if ((args[argidx] == "-max-state-bits" || args[argidx] == "-max_state_bits") &&
			    argidx + 1 < args.size()) {
				max_state_bits = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-min-state-bits" || args[argidx] == "-min_state_bits") &&
			    argidx + 1 < args.size()) {
				min_state_bits = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-min-nodes" || args[argidx] == "-min_nodes") &&
			    argidx + 1 < args.size()) {
				min_nodes = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-nodes" || args[argidx] == "-max_nodes") &&
			    argidx + 1 < args.size()) {
				max_nodes = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-digit-bits" || args[argidx] == "-max_digit_bits") &&
			    argidx + 1 < args.size()) {
				max_digit_bits = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-clones" || args[argidx] == "-max_clones") &&
			    argidx + 1 < args.size()) {
				max_clones = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-min-serial-depth" || args[argidx] == "-min_serial_depth") &&
			    argidx + 1 < args.size()) {
				min_serial_depth = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-min-depth-gain" || args[argidx] == "-min_depth_gain") &&
			    argidx + 1 < args.size()) {
				min_depth_gain = std::stoi(args[++argidx]);
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
			if ((args[argidx] == "-attempt-budget" || args[argidx] == "-attempt_budget") &&
			    argidx + 1 < args.size()) {
				attempt_budget = std::stoll(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_tables = 0, total_vectors = 0, total_cells = 0;
		for (auto module : design->selected_modules()) {
			OptModAddTreeWorker worker(module);
			worker.max_state_bits = max_state_bits;
			worker.min_state_bits = min_state_bits;
			worker.min_nodes = min_nodes;
			worker.max_nodes = max_nodes;
			worker.max_digit_bits = max_digit_bits;
			worker.max_clones = max_clones;
			worker.min_serial_depth = min_serial_depth;
			worker.min_depth_gain = min_depth_gain;
			if (walk_budget > 0)
				worker.walk_budget = walk_budget;
			if (eval_budget > 0)
				worker.eval_budget = eval_budget;
			if (attempt_budget > 0)
				worker.attempt_budget = attempt_budget;
			worker.run();
			total_tables += worker.table_regions;
			total_vectors += worker.vector_regions;
			total_cells += worker.cells_added;
		}

		log("Rewrote %d associative cascade(s) as balanced tree(s), %d cascade(s) as "
		    "transfer-function tree(s); emitted %d new cell(s).\n",
		    total_tables, total_vectors, total_cells);

		if (total_tables || total_vectors)
			Yosys::run_pass("clean -purge");
	}
} OptModAddTreePass;

PRIVATE_NAMESPACE_END
