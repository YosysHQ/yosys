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
#include <memory>
#include <queue>
#include <utility>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/cut_region.h"

// opt_modred: re-emit reductions modulo a Mersenne number C = 2^k - 1 as an
// end-around-carry carry-save tree, and push the reduction back through the
// arithmetic that produced its input.
//
// Two properties of C = 2^k - 1 drive everything here:
//
//   1. 2^k == 1 (mod C), so multiplying a residue by 2^j is a left rotate of
//      its k bits -- free rewiring. That makes k-bit digits interchangeable
//      and makes every "times a power of two" correction cost nothing.
//
//   2. Therefore a full adder is already a mod-C compressor: for residues
//      a, b, c we have a + b + c == (a^b^c) + 2*maj(a,b,c), and the doubling
//      is that free rotate. Three residues collapse to two in one FA level,
//      with no reduction step and no normalization -- the redundant encoding
//      simply allows 2^k-1 as a second spelling of zero.
//
// RTL spells these reductions as a tree of k-bit "add two digits mod C" nodes,
// each of which maps to several levels of complex gates. A Wallace tree of
// end-around-carry compressors is both shallower and much smaller, because an
// FA level is cheaper than a mod-C add and there are fewer of them.
//
// On top of that, res_C is a ring homomorphism, so it commutes with the
// producers of its input:
//
//     res(mux(s, a, b))     == mux(s, res(a), res(b))
//     res((a + b) mod 2^n)  == res(a) + res(b) - 2^(n mod k) * carry_out
//     res(x >> s)           == rotl_{-s mod k}( res(x) - res(x & mask(s)) )
//
// The add rule is the valuable one: it takes the carry-propagate adder off the
// reduction's path entirely, since only the single carry-out bit still needs
// it, and that bit has the whole tree's worth of slack. The shift rule is what
// makes the add rule reachable -- a barrel shifter in front of the tree both
// costs its own depth and flattens the adder's per-bit arrival profile.
//
// Matching never assumes a spelling. Candidate reduction nodes are cut out of
// the netlist and proven exhaustively with ConstEval over the cut, so a proof
// covers every value the cut can carry, including the 2^k-1 encoding of zero
// that a normalizer in the source RTL would otherwise leave as a don't-care.

struct OptModRedWorker : CutRegionWorker {
	// Tunables (see Pass::execute).
	int min_mod_bits = 2;
	int max_mod_bits = 6;
	int max_cut_bits = 14;
	int max_cut_retries = 3;
	int max_prune_rounds = 64;
	// Cells a digit's bound may pull in looking for a cut it can sweep. Sized for a
	// digit's own table, not for the design behind it; see budget_cone.
	int max_bound_cells = 256;
	int max_region_cells = 4096;
	int max_region_leaves = 1024;
	int min_terms = 4;
	int max_terms = 512;
	int max_internal_roots = 256;
	int max_push_depth = 6;
	int min_push_add_width = 8;
	int max_shift_sel_bits = 6;
	int max_fn_slots = 4;
	// Widest leaf group -sink-shift will take, in bits. The leaf-identity check
	// sweeps 2^g vectors per leaf, and a leaf of a fold reads one narrow field.
	int max_sink_group_bits = 10;
	int max_sink_sel_bits = 8;
	// Levels the sink has to buy to be worth it: it trades a barrel over the
	// whole amount for a g-way shift and a mask, and breaking even is a loss
	// because the mask is a fixed cell the Boolean optimizer cannot fold away.
	int min_sink_gain = 2;
	// Largest cone the bit-level evaluator will walk. A whole fold level is a
	// few hundred cells once the frontend has vectorized it, and the walk is
	// the only way to see through the cell-level loops it leaves behind.
	int max_bits_eval_cells = 256;
	// Largest cone the value-range prover will sweep, in leaf bits. A leaf digit
	// of a fold reads one narrow field, so a handful of bits covers the shape
	// this is for while keeping the sweep to a few thousand evaluations.
	int max_bound_bits = 12;
	bool fit_fn = true;
	bool push_shift_sub = false;
	bool opaque_digits = false;
	bool div_cells = false;
	bool sink_shift_en = false;

	int k = 0;      // modulus width
	int mod_c = 0;  // 2^k - 1
	Cell *anchor = nullptr;

	int regions = 0;
	int fn_regions = 0;
	int cells_added = 0;
	int pushed_adds = 0;
	int pushed_muxes = 0;
	int pushed_shifts = 0;
	int pushed_norms = 0;
	int pushed_concats = 0;
	int sunk_shifts = 0;
	bool dirty = false;

	OptModRedWorker(Module *module) : CutRegionWorker(module) {}

	// ---------------------------------------------------------------- proof

	// A proven reduction: root == (sum of weight[bit] * bit) mod C. Weights are
	// arbitrary residues, not just powers of two, because a rotated combine or a
	// doubled operand contributes a scaled digit.
	struct Proof {
		dict<SigBit, int> weights;
		pool<Cell *> region;
		// Largest value seen over the whole (exhaustive) proof, so a node above
		// this one knows the range its input can actually take.
		int maxval = 0;
		// Largest weighted sum the terms can actually reach, or -1 to price it
		// from `weights` alone. Only an opaque digit needs the distinction: its
		// k bits carry weights summing to coeff*(2^k-1), but its proven bound
		// caps the value it can really take. Set once anything below rests on
		// such a bound, and propagated upward so a parent prices its slots by
		// range too rather than re-inflating them. See cannot_wrap().
		int reach = -1;
	};

	dict<SigSpec, int> prove_memo_ok;
	// Roots whose proof is on the stack, and how many times one was re-entered.
	pool<SigSpec> prove_active;
	int64_t reentries = 0;
	dict<SigSpec, dict<SigBit, int>> prove_memo;
	dict<SigSpec, int> prove_memo_max;
	dict<SigSpec, int> prove_memo_reach;
	dict<SigSpec, pool<Cell *>> prove_memo_region;

	// Candidate places to cut a reduction cone, in two flavours.
	//
	// A cell output exactly k bits wide is a candidate *residue*: it becomes one
	// slot and its own proof is discharged by recursion, which is what keeps each
	// exhaustive check down to a handful of slots.
	//
	// Every bit of a wider cell output is a candidate leaf. That is how the cut
	// stops at the adder or shifter feeding the tree instead of running on to the
	// primary inputs. Whole outputs only: a partial slice would leave its siblings
	// to be reached around the cut, through the very cell the cut stands in for,
	// and the two would then be forced to inconsistent values.
	void collect_cut_buses(const pool<Cell *> &cone, vector<SigSpec> &buses,
	                       pool<SigBit> &wide_bits)
	{
		pool<SigSpec> seen;
		pool<SigBit> cone_bits;
		vector<SigSpec> port_buses;
		for (auto c : cone)
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				SigSpec sig = sigmap(conn.second);
				for (auto bit : sig)
					cone_bits.insert(bit);
				pool<SigBit> uniq;
				if (sig.is_fully_const() || !sig_bits_unique(sig, uniq))
					continue;
				if (GetSize(sig) == k) {
					if (seen.insert(sig).second)
						port_buses.push_back(sig);
				} else if (GetSize(sig) > k) {
					for (auto bit : sig)
						if (bit.wire)
							wide_bits.insert(bit);
				}
			}

		// Named wires first, then cell ports. A slot's value depends on its bit
		// order, and only a named wire carries the order the RTL meant: a
		// vectorizing frontend leaves the same k bits on a cell port in an
		// arbitrary order, and a permutation of a digit is not linear mod C, so
		// cutting on the port spelling loses the proof. The port order stays as
		// a fallback for buses that never got a name.
		//
		// Residues are often assembled a bit at a time, so the bus exists only
		// as a named wire and never as one cell's output.
		for (auto &sig : wire_buses()) {
			bool inside = true;
			for (auto bit : sig)
				if (!cone_bits.count(bit))
					inside = false;
			if (inside && seen.insert(sig).second)
				buses.push_back(sig);
		}
		for (auto &sig : port_buses)
			buses.push_back(sig);
	}

	// A cut is only meaningful if its points are independent. When one point
	// feeds another -- a normalizer's data output cut shallow while its select
	// path runs on to the raw bits -- forcing both demands a combination the
	// circuit cannot produce, and the sweep proves nothing about it.
	//
	// Retire the shallow end of every such pair, so the next walk runs past it.
	// Pushing the whole cut outward instead would also retire the deep points
	// that were already fine, and the cut would slide without ever settling.
	//
	// One walk answers this for the whole cut. Backward from every point at
	// once, recording each edge as it is crossed, then forward along those
	// edges from the points: a point the forward pass arrives at has another
	// point in its fanin. Asking point by point instead re-explored the same
	// fanin once per point, since they all sit in the same region.
	//
	// Both directions run over the interned cone graph, since this is the
	// hottest walk in the pass: every retry and every prune round re-runs it
	// on the same cone, and a hashed SigBit BFS that re-sigmaps the fanin and
	// allocates a successor vector per bit costs an order of magnitude more
	// than the integer walk. An uncut cone over the interning cap has no graph
	// and keeps the cut walk hashed, so keep a hashed prune for that case:
	// skipping it there would let an unpruned cut through to the sweep.
	bool prune_covered_cuts(const SigSpec &root, const pool<SigBit> &hit,
	                        pool<SigBit> &excluded)
	{
		const ConeGraph *gp = cone_graph(root);
		if (gp == nullptr)
			return prune_covered_cuts_hashed(hit, excluded);
		const ConeGraph &g = *gp;
		next_pc_gen(GetSize(g.bits), GetSize(g.cells));

		// Intern the points once: each is asked about four times below, and
		// the hash lookup is all that is left of the old walk's cost.
		pc_ids.clear();
		for (auto bit : hit) {
			auto it = g.bit_id.find(bit);
			if (it == g.bit_id.end())
				continue;
			pc_ids.push_back(it->second);
			pc_hit[it->second] = pc_gen;
		}

		// Backward from every point at once. The edges are kept per cell
		// rather than per bit pair: a wide cell would otherwise contribute
		// fanin*driven edges, and that product, not the cone, is what made
		// this walk expensive.
		pc_queue.clear();
		pc_fan_cell.clear();
		pc_fan_next.clear();
		pc_out_bit.clear();
		pc_out_next.clear();
		for (auto id : pc_ids)
			if (g.bit_drv[id] >= 0 && pc_seen[id] != pc_gen) {
				pc_seen[id] = pc_gen;
				pc_queue.push_back(id);
			}
		for (int head = 0; head < GetSize(pc_queue) && !walk_exhausted(); head++) {
			int id = pc_queue[head];
			int cid = g.bit_drv[id];
			if (cid < 0)
				continue;
			charge_walk(1);
			bool first = pc_cell_gen[cid] != pc_gen;
			if (first) {
				pc_cell_gen[cid] = pc_gen;
				pc_out_head[cid] = -1;
			}
			pc_out_bit.push_back(id);
			pc_out_next.push_back(pc_out_head[cid]);
			pc_out_head[cid] = GetSize(pc_out_bit) - 1;
			// The fanin only has to be crossed once per cell: a later bit
			// of the same cell finds every fanin bit already seeded or
			// already a point, so the queue and the seen set come out the
			// same as crossing it once per bit did.
			if (!first)
				continue;
			for (int e = g.in_off[cid]; e < g.in_off[cid + 1]; e++) {
				int in_id = g.in_bits[e];
				if (pc_fan_gen[in_id] != pc_gen) {
					pc_fan_gen[in_id] = pc_gen;
					pc_fan_head[in_id] = -1;
				}
				pc_fan_cell.push_back(cid);
				pc_fan_next.push_back(pc_fan_head[in_id]);
				pc_fan_head[in_id] = GetSize(pc_fan_cell) - 1;
				// A point is not walked through, only seeded, so the
				// edges collected stay the ones a per-point walk saw.
				if (pc_hit[in_id] != pc_gen && pc_seen[in_id] != pc_gen) {
					pc_seen[in_id] = pc_gen;
					pc_queue.push_back(in_id);
				}
			}
		}

		// Forward from the points, but starting one edge out so that a point
		// is not reported as covering itself. Each cell's driven bits are
		// handed out once, which is what keeps this pass linear.
		pc_fwd_queue.clear();
		auto push_succs = [&](int id) {
			if (pc_fan_gen[id] != pc_gen)
				return;
			for (int e = pc_fan_head[id]; e != -1; e = pc_fan_next[e]) {
				int cid = pc_fan_cell[e];
				if (pc_cell_done[cid] == pc_gen)
					continue;
				pc_cell_done[cid] = pc_gen;
				for (int f = pc_out_head[cid]; f != -1; f = pc_out_next[f]) {
					int next = pc_out_bit[f];
					if (pc_reached[next] != pc_gen) {
						pc_reached[next] = pc_gen;
						pc_fwd_queue.push_back(next);
					}
				}
			}
		};
		for (auto id : pc_ids)
			push_succs(id);
		for (int head = 0; head < GetSize(pc_fwd_queue); head++)
			push_succs(pc_fwd_queue[head]);

		bool grew = false;
		for (auto bit : hit) {
			auto it = g.bit_id.find(bit);
			if (it != g.bit_id.end() && pc_reached[it->second] == pc_gen &&
			    excluded.insert(bit).second)
				grew = true;
		}
		return grew;
	}

	// Same walk over hashed signal bits, for a cone too large to intern.
	bool prune_covered_cuts_hashed(const pool<SigBit> &hit, pool<SigBit> &excluded)
	{
		dict<SigBit, vector<SigBit>> fwd;  // a bit -> the bits it feeds
		pool<SigBit> seen;
		std::queue<SigBit> queue;
		for (auto bit : hit)
			if (bit_to_driver.at(bit, nullptr) != nullptr && seen.insert(bit).second)
				queue.push(bit);
		while (!queue.empty() && !walk_exhausted()) {
			SigBit bit = queue.front();
			queue.pop();
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr)
				continue;
			charge_walk(1);
			for (auto in_bit : cell_fanin(drv)) {
				fwd[in_bit].push_back(bit);
				// A point is not walked through, only seeded, so the
				// edges collected stay the ones a per-point walk saw.
				if (!hit.count(in_bit) && seen.insert(in_bit).second)
					queue.push(in_bit);
			}
		}

		pool<SigBit> reached;
		std::queue<SigBit> fq;  // the backward queue may have been cut short
		auto push_succs = [&](const SigBit &b) {
			auto it = fwd.find(b);
			if (it == fwd.end())
				return;
			for (auto next : it->second)
				if (reached.insert(next).second)
					fq.push(next);
		};
		for (auto bit : hit)
			push_succs(bit);
		while (!fq.empty()) {
			SigBit bit = fq.front();
			fq.pop();
			push_succs(bit);
		}

		bool grew = false;
		for (auto bit : hit)
			if (reached.count(bit) && excluded.insert(bit).second)
				grew = true;
		return grew;
	}

	// Scratch for prune_covered_cuts, kept across probes so a probe allocates
	// nothing. Stamps are generation-counted rather than cleared; the edge
	// lists are rebuilt per probe but keep their capacity.
	vector<int> pc_queue, pc_fwd_queue, pc_ids;
	vector<int> pc_fan_head, pc_fan_cell, pc_fan_next;  // bit -> cells it feeds
	vector<int> pc_out_head, pc_out_bit, pc_out_next;   // cell -> bits it drove
	vector<uint32_t> pc_seen, pc_hit, pc_reached, pc_fan_gen;
	vector<uint32_t> pc_cell_gen, pc_cell_done;
	uint32_t pc_gen = 0;

	// Open a generation, growing the stamps to cover the graph. Growing must
	// not disturb the counter: the bit and cell stamps grow independently, so
	// restarting it would let a stamp left over from an earlier generation
	// alias the current one. A new entry reads as generation 0, which no live
	// generation ever uses.
	void next_pc_gen(int nbits, int ncells)
	{
		if (GetSize(pc_seen) < nbits) {
			pc_seen.resize(nbits, 0);
			pc_hit.resize(nbits, 0);
			pc_reached.resize(nbits, 0);
			pc_fan_gen.resize(nbits, 0);
			pc_fan_head.resize(nbits, -1);
		}
		if (GetSize(pc_cell_gen) < ncells) {
			pc_cell_gen.resize(ncells, 0);
			pc_cell_done.resize(ncells, 0);
			pc_out_head.resize(ncells, -1);
		}
		if (++pc_gen == 0) {  // wrapped, so every stamp is stale
			std::fill(pc_seen.begin(), pc_seen.end(), 0);
			std::fill(pc_hit.begin(), pc_hit.end(), 0);
			std::fill(pc_reached.begin(), pc_reached.end(), 0);
			std::fill(pc_fan_gen.begin(), pc_fan_gen.end(), 0);
			std::fill(pc_cell_gen.begin(), pc_cell_gen.end(), 0);
			std::fill(pc_cell_done.begin(), pc_cell_done.end(), 0);
			pc_gen = 1;
		}
	}

	// Module wires exactly k bits wide, indexed by k so the sweep is paid once
	// per modulus rather than once per proof.
	dict<int, vector<SigSpec>> wire_buses_by_k;

	const vector<SigSpec> &wire_buses()
	{
		if (!wire_buses_by_k.count(k)) {
			vector<SigSpec> v;
			for (auto w : module->wires()) {
				if (GetSize(w) != k)
					continue;
				SigSpec sig = sigmap(SigSpec(w));
				pool<SigBit> uniq;
				if (sig.is_fully_const() || !sig_bits_unique(sig, uniq))
					continue;
				v.push_back(sig);
			}
			wire_buses_by_k[k] = v;
		}
		return wire_buses_by_k.at(k);
	}

	// Exhaustively evaluate `root` over every assignment of the cut slots and
	// check it is the residue Sum(coeff_i * slot_i) mod C. Exhaustive is what
	// makes this sound: it also pins down the value the cut carries for the
	// 2^k-1 spelling of zero, which a normalizer leaves free.
	//
	// `slot_max` bounds each slot, which is what makes the check affordable on
	// the upper levels of a tree. It also makes it *correct* for the common
	// one-hot spelling of a fold, whose table only decodes canonical residues
	// and answers zero for the 2^k-1 input a lower level can never produce.
	bool check_linear(const SigSpec &root, const vector<SigSpec> &slots,
	                  const vector<int> &slot_max, const pool<Cell *> &region, bool allow_bits,
	                  vector<int> &coeffs, int &maxval)
	{
		int region_cells = GetSize(region);
		// Overflow here would silently shrink the domain and "prove" a cut that
		// was never checked, so the product is bounded as it is built.
		const int64_t limit = int64_t(1) << max_cut_bits;
		int64_t combos = 1;
		if (slots.empty())
			return false;
		for (int i = 0; i < GetSize(slots); i++) {
			int64_t range = int64_t(slot_max[i]) + 1;
			if (range < 1 || combos > limit / range)
				return false;
			combos *= range;
		}

		ConstEval &ce = shared_ce();
		// One-way switch: a cone ConstEval cannot resolve stays unresolvable
		// for every vector, so pay the probe once rather than per vector.
		bool bits_mode = false;
		// Ordered on the first probe, since most cuts are rejected by the
		// coefficient reads above and never reach the sweep.
		vector<Cell *> order;
		bool ordered = false;
		// Rewritten in place per probe: the slots and their widths do not
		// change, and a fresh assignment list costs an allocation per slot at
		// every one of thousands of probes.
		vector<std::pair<SigSpec, Const>> sets;
		for (auto &s : slots)
			sets.push_back({s, Const(State::S0, GetSize(s))});
		auto eval_at = [&](const vector<int> &vals, uint64_t &out) {
			for (int i = 0; i < GetSize(slots); i++)
				set_const_u64(sets[i].second, vals[i]);
			if (eval_exhausted())
				return false;
			if (!bits_mode) {
				if (!ordered) {
					compute_cone_depths(region, &order);
					ordered = true;
				}
				if (eval_with(ce, sets, root, out, region_cells, &order))
					return true;
				if (!allow_bits)
					return false;
				bits_mode = true;
			}
			return eval_with_bits(sets, root, out, region_cells);
		};

		// Zero must map to zero, and each slot's coefficient is read off the
		// evaluation with that slot at one.
		vector<int> vals(GetSize(slots), 0);
		uint64_t out = 0;
		if (!eval_at(vals, out)) {
			log_debug("      zero eval failed (eval budget %s)\n",
			          eval_exhausted() ? "out" : "ok");
			return false;
		}
		if ((out % mod_c) != 0) {
			log_debug("      zero eval gave %d\n", int(out));
			return false;
		}
		coeffs.clear();
		for (int i = 0; i < GetSize(slots); i++) {
			vals.assign(GetSize(slots), 0);
			vals[i] = 1;
			if (!eval_at(vals, out))
				return false;
			coeffs.push_back(int(out % mod_c));
		}

		// Verify over the whole cut, in mixed radix so each slot only spans the
		// values it can actually take.
		maxval = 0;
		for (int64_t c = 0; c < combos; c++) {
			int64_t rest = c;
			int64_t want = 0;
			for (int i = 0; i < GetSize(slots); i++) {
				int v = int(rest % (int64_t(slot_max[i]) + 1));
				rest /= int64_t(slot_max[i]) + 1;
				vals[i] = v;
				want += int64_t(coeffs[i]) * v;
			}
			if (!eval_at(vals, out))
				return false;
			if ((out % mod_c) != uint64_t(want % mod_c))
				return false;
			maxval = std::max(maxval, int(out));
		}
		return true;
	}

	// Largest value `sig` can take, or -1 when that cannot be shown cheaply.
	// Keyed on the signal alone and independent of k, since it only asks what the
	// producer can emit.
	dict<SigSpec, int> bound_memo;

	// Sweep `sig`'s own cone exhaustively for its largest reachable value.
	//
	// A k-bit signal that never reaches 2^k-1 only ever carries a canonical
	// residue, and that is exactly what makes the level above it linear: a fold
	// spelled as a one-hot table decodes 0..C-1 and answers 0 for the 2^k-1 input
	// its producer cannot emit, so over the full k-bit domain the table reads as
	// non-linear and the whole tree above it is lost.
	static int cell_out_bits(Cell *c)
	{
		int n = 0;
		for (auto &conn : c->connections())
			if (c->output(conn.first))
				n += GetSize(conn.second);
		return n;
	}

	// Cone of `sig` with a wide producer's output taken as a leaf instead of
	// walked into. A digit that samples one narrow field of a barrel shifter is a
	// function of that field, while its true cone is the whole shifter -- tens of
	// bits, far past any sweep. Cutting at the producer leaves those bits free,
	// which can only add reachable values, so the largest value over the cut is
	// still an upper bound, and an upper bound is all the opaque-digit test asks.
	bool sampled_cone(const SigSpec &sig, int max_bits, pool<Cell *> &cone, SigSpec &cut)
	{
		pool<SigBit> visited, leaves;
		std::queue<SigBit> work;
		for (auto bit : sigmap(sig))
			if (bit.wire != nullptr && visited.insert(bit).second)
				work.push(bit);

		while (!work.empty()) {
			SigBit bit = work.front();
			work.pop();
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr || is_sequential(drv) || cell_out_bits(drv) > max_bits) {
				leaves.insert(bit);
				if (GetSize(leaves) > max_bits)
					return false;
				continue;
			}
			if (!cone.insert(drv).second)
				continue;
			charge_walk(1);
			if (GetSize(cone) > max_region_cells)
				return false;
			for (auto &conn : drv->connections())
				if (drv->input(conn.first))
					for (auto b : sigmap(conn.second))
						if (b.wire != nullptr && visited.insert(b).second)
							work.push(b);
		}
		for (auto bit : leaves)
			cut.append(bit);
		return GetSize(cut) > 0;
	}

	// Cone of `sig` grown as deep as a `max_bits`-wide cut allows, with the bits it
	// still reads as the cut. `get_cone` gives up when the true cone needs more free
	// bits than the sweep can cover, and `sampled_cone` only stops at a producer wide
	// enough to recognise from its output width, which a barrel shifter already
	// lowered to a mesh of two-bit muxes is not -- so on a flattened design both run
	// past the digit into every primary input behind it. What the sweep needs is not
	// the narrowest cut but the deepest one that fits: the digit's own table then
	// lands inside the cone and the narrow field it samples becomes the cut, which is
	// the boundary a module port used to hand us for free. Growing the cone only
	// removes reachable values, so the sweep's maximum stays an upper bound.
	bool budget_cone(const SigSpec &sig, int max_bits, pool<Cell *> &cone, SigSpec &cut)
	{
		// Bits the cone reads but does not drive, i.e. the cut if we stop here.
		pool<SigBit> frontier;
		for (auto bit : sigmap(sig))
			if (bit.wire != nullptr)
				frontier.insert(bit);
		if (frontier.empty() || GetSize(frontier) > max_bits)
			return false;

		// The frontier that pulling `bit`'s driver in would leave, or -1 if that
		// driver cannot come in at all. Its outputs stop being cut points and its
		// inputs become ones, except those the cone already drives -- which is also
		// what keeps the cut clear of the whole-cell caching conflict ConstEval
		// would otherwise hit.
		auto weigh = [&](SigBit bit, pool<SigBit> *out) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr || is_sequential(drv) || cone.count(drv))
				return -1;
			pool<SigBit> next = frontier;
			for (auto &conn : drv->connections())
				if (drv->output(conn.first))
					for (auto b : sigmap(conn.second))
						next.erase(b);
			for (auto &conn : drv->connections())
				if (drv->input(conn.first))
					for (auto b : sigmap(conn.second)) {
						if (b.wire == nullptr)
							continue;
						Cell *up = bit_to_driver.at(b, nullptr);
						if (up != nullptr && cone.count(up))
							continue;
						next.insert(b);
					}
			if (out != nullptr)
				*out = next;
			return GetSize(next);
		};

		// `max_bits` bounds the cut we keep, not the search: the way into a digit's
		// table runs through a frontier wider than the field the table reads, so
		// refusing to ever exceed the cap strands the walk partway inside the table
		// with some of the clamping still outside the sweep. Grow past it and keep
		// the deepest frontier that fits instead.
		pool<Cell *> best_cone;
		pool<SigBit> best_cut;
		while (true) {
			if (GetSize(frontier) <= max_bits && GetSize(cone) > GetSize(best_cone)) {
				best_cone = cone;
				best_cut = frontier;
			}
			// Tested after the cone is weighed, not before growing it, so a cone of
			// exactly the budget still gets its turn as the best while the budget
			// stays the number of cells walked.
			if (GetSize(cone) >= max_bound_cells)
				break;
			// Sorted so the cone a digit bounds against does not depend on set
			// iteration order, and narrowest-first so the walk finishes the table
			// it is inside before starting on whatever feeds it.
			vector<SigBit> cands(frontier.begin(), frontier.end());
			std::sort(cands.begin(), cands.end());
			SigBit pick;
			pool<SigBit> picked;
			int best = -1;
			for (auto bit : cands) {
				pool<SigBit> next;
				int w = weigh(bit, &next);
				if (w < 0)
					continue;
				if (best < 0 || w < best) {
					best = w;
					pick = bit;
					picked.swap(next);
				}
			}
			if (best < 0)
				break;
			cone.insert(bit_to_driver.at(pick, nullptr));
			charge_walk(1);
			frontier.swap(picked);
		}

		// An empty cone means nothing could be pulled in and the cut is the digit
		// itself, which bounds it to its own width and tells us nothing.
		if (best_cone.empty())
			return false;
		cone = best_cone;
		for (auto bit : best_cut)
			cut.append(bit);
		return GetSize(cut) > 0;
	}

	int value_bound(const SigSpec &sig)
	{
		if (bound_memo.count(sig))
			return bound_memo.at(sig);
		bound_memo[sig] = -1;  // pessimistic unless the sweep below completes

		if (!sig_fully_driven(sig))
			return -1;

		pool<Cell *> cone;
		pool<SigBit> leaves;
		SigSpec leafsig;
		// The true cone first, so a digit that already bounded keeps the bound it had
		// and only a digit that could not bound at all pays for a cut.
		int cap = std::min(max_bound_bits, max_cut_bits);
		bool have = false;
		if (get_cone(sig, cone, leaves, max_region_cells, max_bound_bits)) {
			for (auto bit : leaves)
				leafsig.append(bit);
			have = GetSize(leafsig) <= max_cut_bits;
		}
		// budget_cone before sampled_cone: both cut short of the true cone, but the
		// one that captures more of the logic bounds the digit more tightly, and a
		// digit that bounds loosely is a digit the tree above it cannot use.
		for (auto cut_at : {&OptModRedWorker::budget_cone, &OptModRedWorker::sampled_cone}) {
			if (have)
				break;
			cone.clear();
			leafsig = SigSpec();
			have = (this->*cut_at)(sig, cap, cone, leafsig) &&
			       GetSize(leafsig) <= max_cut_bits;
		}
		if (!have) {
			log_debug("      bound %s: no cut (cap %d)\n", log_signal(sig), cap);
			return -1;
		}
		log_debug("      bound %s: cut %d bit(s) over %d cell(s)\n", log_signal(sig),
		          GetSize(leafsig), GetSize(cone));
		// Compared before the shift, not after: max_bound_bits is a user option,
		// and a cone that wide would shift past the width of the count itself.
		if (GetSize(leafsig) > max_cut_bits)
			return -1;
		int64_t combos = int64_t(1) << GetSize(leafsig);

		ConstEval &ce = shared_ce();
		vector<Cell *> order;
		compute_cone_depths(cone, &order);
		vector<std::pair<SigSpec, Const>> sets{{leafsig, Const(State::S0, GetSize(leafsig))}};
		int cells = GetSize(cone);
		// Same one-way switch as check_linear: a vectorized fold leaves cells
		// that each need a bit of another's output, which ConstEval cannot
		// resolve whole even though the cone is acyclic bit by bit.
		bool allow_bits = cells <= max_bits_eval_cells && cone_has_cell_loop(cone);
		bool bits_mode = false;
		int bound = 0;
		for (int64_t v = 0; v < combos; v++) {
			set_const_u64(sets[0].second, uint64_t(v));
			uint64_t out = 0;
			if (eval_exhausted())
				return -1;
			if (!bits_mode) {
				if (eval_with(ce, sets, sig, out, cells, &order)) {
					bound = std::max(bound, int(out));
					continue;
				}
				if (!allow_bits)
					return -1;
				bits_mode = true;
			}
			if (!eval_with_bits(sets, sig, out, cells))
				return -1;
			bound = std::max(bound, int(out));
		}
		bound_memo[sig] = bound;
		return bound;
	}

	// Prove that `root` is a mod-C reduction, returning the weight of every raw
	// bit that feeds it. Cuts are pushed outward on failure: a normalizer sitting
	// between two tree levels makes the inner cut unprovable (7 maps to 0 there,
	// which is not linear) while the cut one level out is fine.
	bool prove(const SigSpec &root_in, Proof &out, int depth)
	{
		SigSpec root = sigmap(root_in);
		if (GetSize(root) != k || depth > 16 || walk_exhausted() || eval_exhausted()) {
			log_debug("%*s%s: early out (width %d, depth %d, walk %d, eval %d)\n",
			          2 * depth + 4, "", log_signal(root), GetSize(root), depth,
			          walk_exhausted() ? 1 : 0, eval_exhausted() ? 1 : 0);
			return false;
		}
		if (prove_memo_ok.count(root)) {
			if (!prove_memo_ok.at(root))
				return false;
			out.weights = prove_memo.at(root);
			out.maxval = prove_memo_max.at(root);
			out.reach = prove_memo_reach.at(root, -1);
			out.region = prove_memo_region.at(root);
			return true;
		}
		// Re-entry means a bit-level cycle through `root`, which this cannot
		// prove -- but only because of where the walk started, so the failure
		// it forces on the callers above it is not theirs to remember.
		if (!prove_active.insert(root).second) {
			reentries++;
			return false;
		}
		int64_t reentry_mark = reentries;
		bool ok = prove_uncached(root, out, depth);
		prove_active.erase(root);
		if (!ok && reentries == reentry_mark)
			prove_memo_ok[root] = 0;
		return ok;
	}

	// The divisor's width when it is a constant 2^k-1, else 0. Read bitwise:
	// as_int() would truncate a divisor wider than an int.
	int mersenne_divisor_bits(Cell *cell)
	{
		if (!cell->type.in(ID($mod), ID($modfloor)) || !cell->hasPort(ID::Y))
			return 0;
		// Unsigned only: signed `%` truncates toward zero and can go negative,
		// and $modfloor takes the divisor's sign, neither of which is a residue.
		if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
			return 0;
		SigSpec b = sigmap(cell->getPort(ID::B));
		if (!b.is_fully_const())
			return 0;
		Const bc = b.as_const();
		if (!bc.is_fully_def())
			return 0;
		int bits = 0;
		while (bits < GetSize(bc) && bc[bits] == State::S1)
			bits++;
		for (int i = bits; i < GetSize(bc); i++)
			if (bc[i] != State::S0)
				return 0;
		return bits;
	}

	// Roots the candidate walk cannot offer. A lone `$mod` is a single cell, so
	// its residue is neither a named wire the walk seeds on nor part of a cone
	// big enough to look interesting, and it is never even proposed. Offer the
	// low k bits of the output, which is the whole residue: `A % C` < C < 2^k.
	void collect_div_roots(vector<RootCand> &roots)
	{
		for (auto cell : module->cells()) {
			int bits = mersenne_divisor_bits(cell);
			if (bits < min_mod_bits || bits > max_mod_bits)
				continue;
			SigSpec y = sigmap(cell->getPort(ID::Y));
			if (GetSize(y) < bits)
				continue;
			RootCand cand;
			cand.sig = y.extract(0, bits);
			cand.name = log_signal(cand.sig);
			roots.push_back(cand);
		}
	}

	// Bits read by any cell, port or connection in the module. Built once, and
	// only when a divider match asks: nothing else here needs fanout.
	pool<SigBit> read_bits;
	bool read_bits_ready = false;
	bool bit_is_read(const SigBit &bit)
	{
		if (!read_bits_ready) {
			for (auto cell : module->cells())
				for (auto &conn : cell->connections())
					if (!cell->output(conn.first))
						for (auto b : sigmap(conn.second))
							read_bits.insert(b);
			for (auto wire : module->wires())
				if (wire->port_output || wire->get_bool_attribute(ID::keep))
					for (auto b : sigmap(SigSpec(wire)))
						read_bits.insert(b);
			for (auto &conn : module->connections())
				for (auto b : sigmap(conn.second))
					read_bits.insert(b);
			read_bits_ready = true;
		}
		return read_bits.count(sigmap(bit)) != 0;
	}

	// A `$mod` by a constant C = 2^k-1 is a reduction by construction: 2^k == 1
	// (mod C), so bit i of A is worth 2^(i mod k) and the weight map is exact
	// without evaluating anything. The exhaustive prover cannot reach this
	// spelling at all -- its only cut is the whole operand, which is far past
	// max_cut_bits -- yet it is the one that needs the rewrite most, since the
	// divider it stands for is far deeper than the tree replacing it.
	bool prove_div_cell(const SigSpec &root, Proof &out)
	{
		Cell *drv = nullptr;
		for (auto bit : root) {
			Cell *d = bit.wire ? bit_to_driver.at(bit, nullptr) : nullptr;
			if (d == nullptr || (drv != nullptr && d != drv))
				return false;
			drv = d;
		}
		if (drv == nullptr || mersenne_divisor_bits(drv) != k)
			return false;
		// The residue is the low k bits of the output: `A % C` < C < 2^k leaves
		// the bits above it constant zero, so the root need not span the port.
		SigSpec y = sigmap(drv->getPort(ID::Y));
		if (GetSize(y) < k)
			return false;
		for (int i = 0; i < k; i++)
			if (y[i] != root[i])
				return false;
		// Those high zero bits still have to be dead, or the divider survives
		// the rewrite and the tree is built beside it instead of replacing it.
		for (int i = k; i < GetSize(y); i++)
			if (y[i].wire && bit_is_read(y[i]))
				return false;

		SigSpec a = sigmap(drv->getPort(ID::A));
		dict<SigBit, int> weights;
		for (int i = 0; i < GetSize(a); i++) {
			SigBit bit = a[i];
			if (!bit.wire) {
				// Zero padding drops out; a constant one is an offset the
				// weight map has nowhere to put.
				if (bit == State::S0)
					continue;
				return false;
			}
			// A repeated bit accumulates, as a rotated combine would.
			weights[bit] = int((int64_t(weights.at(bit, 0)) + (int64_t(1) << (i % k))) %
			                   mod_c);
		}
		for (auto it = weights.begin(); it != weights.end();)
			it = (it->second == 0) ? weights.erase(it) : ++it;

		out.weights = weights;
		out.region = pool<Cell *>({drv});
		out.maxval = mod_c - 1;  // `A % C` is already canonical
		log_debug("    %s: $mod by %d proves as mod-%d over %d bit(s)\n", log_signal(root),
		          mod_c, mod_c, GetSize(weights));
		return true;
	}

	bool prove_uncached(const SigSpec &root, Proof &out, int depth)
	{
		if (div_cells && prove_div_cell(root, out))
			return true;

		pool<Cell *> cone;
		pool<SigBit> leaves;
		if (!sig_fully_driven(root) ||
		    !get_cone(root, cone, leaves, max_region_cells, max_region_leaves)) {
			log_debug("%*s%s: not fully driven or cone too big\n", 2 * depth + 4, "",
			          log_signal(root));
			return false;
		}
		out.region = cone;

		vector<SigSpec> buses;
		pool<SigBit> wide_bits;
		collect_cut_buses(cone, buses, wide_bits);
		log_debug("%*s%s: cone %d cell(s) %d leaf/leaves, %d bus(es) %d wide bit(s)\n",
		          2 * depth + 4, "", log_signal(root), GetSize(cone), GetSize(leaves),
		          GetSize(buses), GetSize(wide_bits));

		// Two passes, deepest cut first. Without the k-bit buses the walk runs
		// all the way to the wide signal feeding the tree, and those weights are
		// the ones the push can move; offering the buses as well lets the walk
		// stop on a tree level instead, which only pays when the deep cut is too
		// wide to sweep. Trying the shallow one first also mixes the two -- one
		// path stops on a level, another runs on past it -- and the cut is then
		// no antichain no matter how many points are retired.
		for (int mode = 0; mode < 2; mode++) {
			if (prove_cut(root, cone, leaves, mode ? buses : vector<SigSpec>(),
			              wide_bits, out, depth))
				return true;
		}
		return false;
	}

	bool prove_cut(const SigSpec &root, const pool<Cell *> &cone, const pool<SigBit> &leaves,
	               const vector<SigSpec> &buses, const pool<SigBit> &wide_bits, Proof &out,
	               int depth)
	{
		pool<SigBit> excluded;
		out.region = cone;
		// Asking a SigSpec whether it holds a bit unpacks it, which allocates;
		// every offered cut point is asked, once per retry.
		pool<SigBit> root_bits(root.begin(), root.end());

		// Retiring a covered cut point and pushing the cut outward are separate
		// moves and get separate budgets: the first converges on the antichain
		// the second one keeps sliding past.
		for (int retries = 0, prunes = 0;
		     retries <= max_cut_retries && prunes <= max_prune_rounds;) {
			pool<SigBit> allowed = leaves;
			vector<SigSpec> live_buses;
			for (auto &b : buses) {
				bool skip = false;
				for (auto bit : b)
					if (excluded.count(bit) || root_bits.count(bit))
						skip = true;
				if (skip)
					continue;
				live_buses.push_back(b);
				for (auto bit : b)
					allowed.insert(bit);
			}
			for (auto bit : wide_bits)
				if (!excluded.count(bit) && !root_bits.count(bit))
					allowed.insert(bit);

			pool<SigBit> hit;
			pool<Cell *> cut_cells;
			pool<SigBit> conflicts;
			if (!cut_cone_walk(root, allowed, max_region_cells, &hit, &cut_cells, nullptr,
			                   nullptr, nullptr, &conflicts)) {
				log_debug("%*s%s: cut walk failed (%s, %d conflict(s))\n",
				          2 * depth + 4, "", log_signal(root), last_cut_fail.c_str(),
				          GetSize(conflicts));
				// A cut point the cone also reaches around cannot close the cut,
				// but the rest of the offer is still good: retire just those and
				// walk again. Dropping every bus and wide bit instead lands the
				// cut on the primary inputs, tens of slots past anything the
				// sweep can cover.
				bool grew = false;
				for (auto bit : conflicts)
					if (excluded.insert(bit).second)
						grew = true;
				if (!grew)
					return false;
				prunes++;
				continue;
			}

			// Nothing to decompose against, so a cut too wide to sweep is the
			// end of this pass rather than something more retries can fix.
			if (buses.empty() && GetSize(hit) > max_cut_bits)
				return false;

			if (prune_covered_cuts(root, hit, excluded)) {
				prunes++;
				continue;
			}

			// Group the cut into k-bit slots where a whole candidate bus was hit,
			// and single-bit slots for everything else.
			vector<SigSpec> slots;
			vector<int> bus_slot;  // index into live_buses, or -1 for a raw bit
			pool<SigBit> taken;
			for (int i = 0; i < GetSize(live_buses); i++) {
				bool all = true;
				for (auto bit : live_buses[i])
					if (!hit.count(bit) || taken.count(bit))
						all = false;
				if (!all)
					continue;
				for (auto bit : live_buses[i])
					taken.insert(bit);
				slots.push_back(live_buses[i]);
				bus_slot.push_back(i);
			}
			for (auto bit : hit)
				if (!taken.count(bit)) {
					slots.push_back(SigSpec(bit));
					bus_slot.push_back(-1);
				}

			// Resolve the residue slots first: their own proofs bound the values
			// this level has to cover, and an unproven one has to be assumed to
			// span its full width.
			vector<int> slot_max(GetSize(slots), 1);
			vector<Proof> sub(GetSize(slots));
			vector<bool> sub_ok(GetSize(slots), false);
			// Unproven slots that still only ever carry a canonical residue, so
			// they can ride in as opaque digits (see the lin branch below).
			vector<bool> opaque(GetSize(slots), false);
			for (int i = 0; i < GetSize(slots); i++) {
				if (bus_slot[i] < 0)
					continue;
				sub_ok[i] = prove(slots[i], sub[i], depth + 1);
				if (sub_ok[i]) {
					slot_max[i] = sub[i].maxval;
					continue;
				}
				int bound = opaque_digits ? value_bound(slots[i]) : -1;
				opaque[i] = bound >= 0 && bound < mod_c;
				slot_max[i] = opaque[i] ? bound : (1 << k) - 1;
			}

			vector<int> coeffs;
			int maxval = 0;
			// The bit-level evaluator is only worth its cost on the
			// small cones ConstEval cannot resolve structurally.
			bool allow_bits = GetSize(cut_cells) <= max_bits_eval_cells &&
			                  cone_has_cell_loop(cut_cells);
			bool lin = check_linear(root, slots, slot_max, cut_cells, allow_bits, coeffs,
			                        maxval);
			log_debug("%*stry %s: %d slot(s), %d cut cell(s) -> %s\n", 2 * depth + 4, "",
			          log_signal(root), GetSize(slots), GetSize(cut_cells),
			          lin ? "linear" : "not linear");
			if (ys_debug() && GetSize(slots) <= 16)
				for (int i = 0; i < GetSize(slots); i++)
					log_debug("%*s  slot %s max %d coeff %d%s\n", 2 * depth + 4, "",
					          log_signal(slots[i]), slot_max[i],
					          i < GetSize(coeffs) ? coeffs[i] : -1,
					          opaque[i] ? " (opaque digit)" : "");
			if (lin) {
				bool ok = true;
				bool any_opaque = false;
				dict<SigBit, int> weights;
				// Every slot priced by the range it can actually take, which
				// for a proven slot is its own maxval and for an opaque digit
				// is its bound. Only used once something below is opaque.
				int64_t reach = 0;
				// Cells the rewrite would replace: everything between the root
				// and the cut, plus whatever each proven slot covers.
				pool<Cell *> claimed = cut_cells;
				for (int i = 0; ok && i < GetSize(slots); i++) {
					if (coeffs[i] == 0)
						continue;
					reach += int64_t(coeffs[i]) * slot_max[i];
					if (bus_slot[i] < 0) {
						SigBit bit = slots[i][0];
						weights[bit] = (weights.at(bit, 0) + coeffs[i]) % mod_c;
						continue;
					}
					if (!sub_ok[i]) {
						if (!opaque[i]) {
							ok = false;
							break;
						}
						// slot == sum of 2^j * bit_j holds for any bus, so an
						// opaque digit needs no proof of its own -- only the
						// bound above, which is what the linearity check just
						// covered. The tree then reads the digit where it is
						// instead of pushing past it.
						for (int j = 0; j < k; j++)
							weights[slots[i][j]] =
							    int((int64_t(weights.at(slots[i][j], 0)) +
							         int64_t(coeffs[i]) * (1 << j)) % mod_c);
						any_opaque = true;
						continue;
					}
					// A slot whose own proof rests on a bound taints this one:
					// its inflated bit weights would otherwise reappear here as
					// reach the design cannot actually produce.
					if (sub[i].reach >= 0)
						any_opaque = true;
					for (auto &it : sub[i].weights)
						weights[it.first] =
						    int((int64_t(weights.at(it.first, 0)) +
						         int64_t(coeffs[i]) * it.second) % mod_c);
					for (auto c : sub[i].region)
						out.region.insert(c);
					for (auto c : sub[i].region)
						claimed.insert(c);
				}
				// The cone behind an opaque digit survives the rewrite, so it
				// must not count toward the depth the tree claims to save.
				if (ok && any_opaque)
					out.region = claimed;
				if (ok) {
					for (auto it = weights.begin(); it != weights.end();)
						it = (it->second == 0) ? weights.erase(it) : ++it;
					// Only opaque digits make the weight sum an overestimate,
					// so leave `reach` unset otherwise and keep the plain
					// pricing (and its results) exactly as they were.
					int r = any_opaque ? int(std::min<int64_t>(reach, mod_c)) : -1;
					prove_memo_ok[root] = 1;
					prove_memo[root] = weights;
					prove_memo_max[root] = maxval;
					prove_memo_reach[root] = r;
					prove_memo_region[root] = out.region;
					out.weights = weights;
					out.maxval = maxval;
					out.reach = r;
					return true;
				}
			}

			// Push the cut one layer outward past whatever it stopped on and
			// retry. Only bits a cell drives can be pushed past; stopping on a
			// true leaf is as far out as the cut goes.
			bool grew = false;
			for (auto bit : hit)
				if (bit_to_driver.at(bit, nullptr) != nullptr && excluded.insert(bit).second)
					grew = true;
			if (!grew)
				return false;
			retries++;
		}
		log_debug("%*s%s: out of cut retries\n", 2 * depth + 4, "", log_signal(root));
		return false;
	}

	// ----------------------------------------------------------------- emit

	std::string src;
	IdString cell_name;  // names everything emitted for the region (NEW_ID3_SUFFIX)

	SigSpec rotl(const SigSpec &x, int j)
	{
		SigSpec r;
		for (int i = 0; i < k; i++)
			r.append(x[((i - j) % k + k) % k]);
		return r;
	}

	// One full-adder level over three residues. The carry is worth 2x, and 2x
	// mod (2^k-1) is a left rotate, so the level costs exactly one FA row.
	std::pair<SigSpec, SigSpec> emit_csa(const SigSpec &a, const SigSpec &b, const SigSpec &c)
	{
		SigSpec s = module->Xor(NEW_ID3_SUFFIX("modred_s"), module->Xor(NEW_ID, a, b, false, src),
		                        c, false, src);
		SigSpec cy = module->Or(
		    NEW_ID3_SUFFIX("modred_c"),
		    module->Or(NEW_ID, module->And(NEW_ID, a, b, false, src),
		               module->And(NEW_ID, b, c, false, src), false, src),
		    module->And(NEW_ID, a, c, false, src), false, src);
		cells_added += 6;
		return {s, rotl(cy, 1)};
	}

	// Collapse two redundant residues into one, end-around carry. The result may
	// be 2^k-1, which is a valid second encoding of zero; callers that need the
	// canonical form must normalize.
	SigSpec emit_eac(const SigSpec &a, const SigSpec &b)
	{
		Wire *t = module->addWire(NEW_ID3_SUFFIX("modred_eac_t"), k + 1);
		module->addAdd(NEW_ID3_SUFFIX("modred_eac_add"), a, b, t, false, src);
		Wire *y = module->addWire(NEW_ID3_SUFFIX("modred_eac"), k);
		module->addAdd(NEW_ID3_SUFFIX("modred_eac_fold"), SigSpec(t).extract(0, k),
		               SigSpec(t)[k], y, false, src);
		cells_added += 2;
		return SigSpec(y);
	}

	// Wallace tree of end-around-carry compressors down to a redundant pair.
	// Leftovers ride to the back of the next level, so the operands listed last
	// -- by convention the ones that arrive latest -- are consumed shallowest.
	std::pair<SigSpec, SigSpec> emit_tree(vector<SigSpec> terms)
	{
		while (GetSize(terms) < 2)
			terms.push_back(SigSpec(State::S0, k));
		while (GetSize(terms) > 2) {
			vector<SigSpec> next;
			int i = 0;
			for (; i + 3 <= GetSize(terms); i += 3) {
				auto p = emit_csa(terms[i], terms[i + 1], terms[i + 2]);
				next.push_back(p.first);
				next.push_back(p.second);
			}
			for (; i < GetSize(terms); i++)
				next.push_back(terms[i]);
			terms.swap(next);
		}
		return {terms[0], terms[1]};
	}

	// Pack (bit, position) contributions into as few k-bit residues as possible:
	// one bit per position per residue, so the count is the tallest column.
	void pack_terms(const vector<std::pair<SigBit, int>> &raw, vector<SigSpec> &out)
	{
		vector<vector<SigBit>> col(k);
		for (auto &t : raw)
			col[t.second].push_back(t.first);
		size_t rows = 0;
		for (int p = 0; p < k; p++)
			rows = std::max(rows, col[p].size());
		for (size_t r = 0; r < rows; r++) {
			SigSpec v;
			for (int p = 0; p < k; p++)
				v.append(r < col[p].size() ? col[p][r] : SigBit(State::S0));
			out.push_back(v);
		}
	}

	// Split a signal into k-bit digits. Every digit of a k-aligned split carries
	// the same weight, so a single rotation covers the whole signal.
	void add_digits(const SigSpec &sig_in, int rot, vector<std::pair<SigBit, int>> &out)
	{
		SigSpec sig = sigmap(sig_in);
		for (int off = 0; off < GetSize(sig); off += k)
			for (int p = 0; p < k && off + p < GetSize(sig); p++) {
				SigBit b = sig[off + p];
				if (b == State::S0)
					continue;
				out.push_back({b, (p + rot) % k});
			}
	}

	// A constant residue scaled by one bit costs no gates: each set bit of the
	// constant becomes that bit at the matching position.
	void add_const_scaled(SigBit b, int value, int rot, vector<std::pair<SigBit, int>> &out)
	{
		for (int p = 0; p < k; p++)
			if ((value >> p) & 1)
				out.push_back({b, (p + rot) % k});
	}

	// ----------------------------------------------------------------- push

	Cell *sole_driver(const SigSpec &sig_in, IdString port, SigSpec &whole)
	{
		SigSpec sig = sigmap(sig_in);
		Cell *drv = nullptr;
		for (auto bit : sig) {
			Cell *d = bit_to_driver.at(bit, nullptr);
			if (d == nullptr || (drv != nullptr && d != drv))
				return nullptr;
			drv = d;
		}
		if (drv == nullptr || !drv->hasPort(port))
			return nullptr;
		whole = sigmap(drv->getPort(port));
		// Only push when the reduction consumes the producer's output whole.
		if (GetSize(whole) != GetSize(sig))
			return nullptr;
		for (int i = 0; i < GetSize(sig); i++)
			if (whole[i] != sig[i])
				return nullptr;
		return drv;
	}

	// Widen an $add in place so its carry-out becomes an ordinary output bit; the
	// original consumers keep reading the low bits through a connection.
	SigBit widen_for_carry(Cell *cell)
	{
		int n = GetSize(sigmap(cell->getPort(ID::Y)));
		Wire *wide = module->addWire(NEW_ID3_SUFFIX("modred_cout"), n + 1);
		SigSpec old_y = cell->getPort(ID::Y);
		cell->setPort(ID::A, {State::S0, cell->getPort(ID::A)});
		cell->setPort(ID::B, {State::S0, cell->getPort(ID::B)});
		cell->setParam(ID::A_WIDTH, GetSize(cell->getPort(ID::A)));
		cell->setParam(ID::B_WIDTH, GetSize(cell->getPort(ID::B)));
		cell->setPort(ID::Y, wide);
		cell->setParam(ID::Y_WIDTH, n + 1);
		module->connect(old_y, SigSpec(wide).extract(0, n));
		dirty = true;
		return SigBit(wide, n);
	}

	// Read a k-bit group out of a weight map: exactly k bits, with bit j worth
	// 2^((j+r) mod k) for the given r. Every r admits an assignment, so r is the
	// caller's choice and only the resulting bit order differs.
	bool weights_as_digit(const dict<SigBit, int> &weights, int r, SigSpec &digit)
	{
		if (GetSize(weights) != k)
			return false;
		vector<SigBit> slot(k);
		vector<bool> filled(k, false);
		for (auto &it : weights) {
			int p = -1;
			for (int j = 0; j < k; j++)
				if (it.second == (1 << ((j + r) % k)))
					p = j;
			if (p < 0 || filled[p])
				return false;
			slot[p] = it.first;
			filled[p] = true;
		}
		digit = SigSpec();
		for (int j = 0; j < k; j++)
			digit.append(slot[j]);
		return true;
	}

	// Maximal ranges of `sig` that are one cell's whole output, in order. Anything
	// else is left to the caller as raw bits.
	void driver_runs(const SigSpec &sig, vector<std::pair<int, int>> &runs)
	{
		int n = GetSize(sig);
		for (int start = 0; start < n;) {
			Cell *drv = bit_to_driver.at(sig[start], nullptr);
			int end = start + 1;
			while (end < n && bit_to_driver.at(sig[end], nullptr) == drv)
				end++;
			SigSpec whole;
			if (drv != nullptr && sole_driver(sig.extract(start, end - start), ID::Y, whole))
				runs.push_back({start, end - start});
			start = end;
		}
	}

	// How much of `sig` a push could actually walk into, used to break the tie
	// between the k rotations a digit-wise map can be read at.
	int pushable_bits(const SigSpec &sig)
	{
		vector<std::pair<int, int>> runs;
		driver_runs(sig, runs);
		int total = 0;
		for (auto &r : runs)
			total += r.second;
		return total;
	}

	// A digit-wise normalizer -- every k-aligned digit independently replaced by
	// some value congruent to it -- leaves res_C alone, so the reduction can be
	// read off whatever feeds the normalizer. Proven one digit at a time, since
	// the map as a whole is far too wide to enumerate.
	bool as_digitwise_map(const SigSpec &sig, SigSpec &in, int &rot_delta)
	{
		int n = GetSize(sig);
		if (n % k != 0 || n / k < 2)
			return false;
		// A digit that does not prove -- a zero-extension's constant padding, most
		// often -- is simply left where it is. Only the digits that do prove move.
		vector<dict<SigBit, int>> digit_weights(n / k);
		for (int off = 0; off < n; off += k) {
			Proof sub;
			if (prove(sig.extract(off, k), sub, 1))
				digit_weights[off / k] = sub.weights;
		}

		int best = -1;
		for (int r = 0; r < k; r++) {
			SigSpec cand;
			for (int d = 0; d < n / k; d++) {
				SigSpec digit;
				if (!weights_as_digit(digit_weights[d], r, digit))
					digit = sig.extract(d * k, k);
				cand.append(digit);
			}
			if (sigmap(cand) == sig)
				continue;
			int score = pushable_bits(cand);
			if (score > best) {
				best = score;
				in = cand;
				rot_delta = r;
			}
		}
		return best > 0;
	}

	// Accumulate the terms of rotl_rot(res_C(sig)), pushing res_C back through
	// the producers of `sig` wherever the homomorphism lets it commute.
	void collect(const SigSpec &sig, int rot, vector<std::pair<SigBit, int>> &out, int depth)
	{
		SigSpec whole;
		Cell *drv = depth < max_push_depth ? sole_driver(sig, ID::Y, whole) : nullptr;
		int n = GetSize(sigmap(sig));
		log_debug("%*scollect %s (%d bit(s), rot %d) drv=%s\n", 2 * depth + 6, "",
		          log_signal(sig), n, rot, drv ? log_id(drv->type) : "-");

		if (drv != nullptr && drv->type == ID($add) && !drv->getParam(ID::A_SIGNED).as_bool() &&
		    n >= min_push_add_width) {
			// res((a+b) mod 2^n) = res(a) + res(b) - 2^(n mod k) * cout. Only the
			// one carry bit still needs the carry chain.
			SigSpec a = drv->getPort(ID::A), b = drv->getPort(ID::B);
			if (GetSize(a) <= n && GetSize(b) <= n) {
				SigBit cout = widen_for_carry(drv);
				collect(a, rot, out, depth + 1);
				collect(b, rot, out, depth + 1);
				int wrap = int((int64_t(mod_c) - (int64_t(1) << (n % k)) % mod_c) % mod_c);
				add_const_scaled(cout, wrap, rot, out);
				pushed_adds++;
				return;
			}
		}

		if (drv != nullptr && drv->type == ID($mux)) {
			// res(mux(s,a,b)) = mux(s, res(a), res(b)); each arm has to be folded
			// to a definite pair first, so this costs one mux level on 2k bits.
			vector<std::pair<SigBit, int>> ta, tb;
			collect(drv->getPort(ID::A), 0, ta, depth + 1);
			collect(drv->getPort(ID::B), 0, tb, depth + 1);
			vector<SigSpec> va, vb;
			pack_terms(ta, va);
			pack_terms(tb, vb);
			auto pa = emit_tree(va);
			auto pb = emit_tree(vb);
			SigSpec s = drv->getPort(ID::S);
			SigSpec mu = module->Mux(NEW_ID3_SUFFIX("modred_arm"), pa.first, pb.first, s, src);
			SigSpec mv = module->Mux(NEW_ID3_SUFFIX("modred_arm"), pa.second, pb.second, s, src);
			cells_added += 2;
			add_digits(rotl(mu, rot), 0, out);
			add_digits(rotl(mv, rot), 0, out);
			pushed_muxes++;
			return;
		}

		// A dynamic shift anywhere along the chain, not just under the root: the
		// rotate it leaves behind is dynamic, so the terms so far have to be
		// folded to a pair here and rejoin as two ordinary digits.
		if (drv != nullptr && is_dyn_shift(drv)) {
			vector<SigSpec> terms;
			SigSpec sel;
			if (emit_shifted(drv, 0, terms, sel, depth + 1)) {
				auto p = emit_tree(terms);
				add_digits(rotl(rotl_dyn(p.first, sel), rot), 0, out);
				add_digits(rotl(rotl_dyn(p.second, sel), rot), 0, out);
				return;
			}
		}

		// Past the cells the homomorphism commutes with outright: a normalizer
		// that preserves the residue, then the pieces of a concatenation.
		SigSpec in;
		int rot_delta = 0;
		if (depth < max_push_depth && drv == nullptr &&
		    as_digitwise_map(sigmap(sig), in, rot_delta)) {
			collect(in, (rot + rot_delta) % k, out, depth + 1);
			pushed_norms++;
			return;
		}

		if (depth < max_push_depth && drv == nullptr) {
			vector<std::pair<int, int>> runs;
			SigSpec s = sigmap(sig);
			driver_runs(s, runs);
			if (!runs.empty() && !(GetSize(runs) == 1 && runs[0].second == n)) {
				int at = 0;
				for (auto &r : runs) {
					add_digits(s.extract(at, r.first - at), (at + rot) % k, out);
					collect(s.extract(r.first, r.second), (r.first + rot) % k, out,
					        depth + 1);
					at = r.first + r.second;
				}
				add_digits(s.extract(at, n - at), (at + rot) % k, out);
				pushed_concats++;
				return;
			}
		}

		add_digits(sig, rot, out);
	}

	bool is_dyn_shift(Cell *cell)
	{
		return (cell->type == ID($shr) || cell->type == ID($shiftx) ||
		        cell->type == ID($shift)) &&
		       !sigmap(cell->getPort(ID::B)).is_fully_const();
	}

	// res(x >> s) = rotl_{-s mod k}(res(x & ~mask(s))): clearing the discarded
	// low bits leaves H * 2^s, whose residue is res(H) rotated by s.
	//
	// The alternative, res(x) - res(x & mask(s)), keeps `x` whole and so keeps
	// its producer pushable -- but it pays for a second tree, a complement and
	// two extra digits, and the push it preserves only helps when the producer's
	// operands are shallower than the producer. Masking is the cheaper default;
	// `-push-shift-sub` asks for the other spelling.
	bool emit_shifted(Cell *shr, int rot, vector<SigSpec> &terms, SigSpec &dyn_sel, int depth)
	{
		SigSpec a = sigmap(shr->getPort(ID::A)), b = sigmap(shr->getPort(ID::B));
		int n = GetSize(sigmap(shr->getPort(ID::Y)));
		int sb = GetSize(b);
		if (GetSize(a) != n || sb < 1 || sb > max_shift_sel_bits ||
		    shr->getParam(ID::A_SIGNED).as_bool() || shr->getParam(ID::B_SIGNED).as_bool())
			return false;

		// Thermometer mask over the bits the shift can discard, as one constant
		// table read: a per-bit comparison against s would cost a comparator row.
		vector<std::pair<SigBit, int>> hi;
		int nlow = std::min(n, (1 << sb) - 1);
		if (nlow > 0 && !push_shift_sub) {
			Const table;
			for (int v = 0; v < (1 << sb); v++)
				for (int m = 0; m < nlow; m++)
					table.bits().push_back(m < v ? State::S0 : State::S1);
			SigSpec keep = module->Bmux(NEW_ID3_SUFFIX("modred_keepmask"), table, b, src);
			SigSpec masked = module->And(NEW_ID3_SUFFIX("modred_keep"), a.extract(0, nlow),
			                             keep, false, src);
			cells_added += 2;
			masked.append(a.extract(nlow, n - nlow));
			add_digits(masked, rot, hi);
			pack_terms(hi, terms);
		} else if (nlow > 0) {
			Const table;
			for (int v = 0; v < (1 << sb); v++)
				for (int m = 0; m < nlow; m++)
					table.bits().push_back(m < v ? State::S1 : State::S0);
			SigSpec mask = module->Bmux(NEW_ID3_SUFFIX("modred_lowmask"), table, b, src);
			SigSpec low = module->And(NEW_ID3_SUFFIX("modred_low"), a.extract(0, nlow),
			                          mask, false, src);
			cells_added += 2;
			vector<std::pair<SigBit, int>> lt;
			add_digits(low, rot, lt);
			vector<SigSpec> lv;
			pack_terms(lt, lv);
			auto lp = emit_tree(lv);
			collect(a, rot, hi, depth);
			pack_terms(hi, terms);
			terms.push_back(module->Not(NEW_ID3_SUFFIX("modred_sub"), lp.first, false, src));
			terms.push_back(module->Not(NEW_ID3_SUFFIX("modred_sub"), lp.second, false, src));
			cells_added += 2;
		} else {
			collect(a, rot, hi, depth);
			pack_terms(hi, terms);
		}

		// Rotate select: (-s) mod k, as a constant table read off the shift amount.
		int selw = std::max(1, clog2_int(k));
		Const sel;
		for (int v = 0; v < (1 << sb); v++) {
			int j = (k - (v % k)) % k;
			for (int i = 0; i < selw; i++)
				sel.bits().push_back((j >> i) & 1 ? State::S1 : State::S0);
		}
		dyn_sel = module->Bmux(NEW_ID3_SUFFIX("modred_rotsel"), sel, b, src);
		cells_added++;
		pushed_shifts++;
		return true;
	}

	SigSpec rotl_dyn(const SigSpec &x, const SigSpec &sel)
	{
		int selw = GetSize(sel);
		Const idx;
		SigSpec data;
		for (int j = 0; j < (1 << selw); j++)
			data.append(rotl(x, j % k));
		(void)idx;
		cells_added++;
		return module->Bmux(NEW_ID3_SUFFIX("modred_rot"), data, sel, src);
	}

	// -------------------------------------------------------------- rewrite

	// Turn a proven weight map into the residues to compress.
	//
	// A run of consecutive bits of one wire whose weights follow the canonical
	// 2^((offset+r) mod k) progression is rotl_r(res_C(slice)) of a value in the
	// netlist, so the homomorphism push applies to it -- and moving those terms
	// to earlier signals is the whole point of the pass. Requiring instead that
	// the entire map be one cell's output gives up on the common case, where the
	// reduction reads a bus a normalizer wrote a digit at a time. Anything not in
	// such a run rides in as its own scaled constant.
	bool weight_terms(const dict<SigBit, int> &weights, vector<SigSpec> &terms)
	{
		vector<std::pair<SigBit, int>> raw;
		dict<SigSpec, vector<std::pair<int, int>>> by_host;  // index, weight
		for (auto &it : weights) {
			if (it.first.wire == nullptr) {
				add_const_scaled(it.first, it.second, 0, raw);
				continue;
			}
			SigSpec host;
			int index = 0;
			host_of(it.first, host, index);
			by_host[host].push_back({index, it.second});
		}

		for (auto &h : by_host) {
			auto &v = h.second;
			std::sort(v.begin(), v.end());
			for (size_t i = 0; i < v.size();) {
				int r = canonical_rot(v[i].first, v[i].second);
				size_t j = i + 1;
				if (r >= 0)
					while (j < v.size() && v[j].first == v[j - 1].first + 1 &&
					       canonical_rot(v[j].first, v[j].second) == r)
						j++;
				// One digit is the least that can carry a push; below that the
				// walk costs more than the terms it could move.
				if (r >= 0 && int(j - i) >= k)
					collect(h.first.extract(v[i].first, int(j - i)),
					        (v[i].first + r) % k, raw, 0);
				else
					for (size_t t = i; t < j; t++)
						add_const_scaled(h.first[v[t].first], v[t].second, 0, raw);
				i = j;
			}
		}
		pack_terms(raw, terms);
		return !terms.empty();
	}

	// The signal a weighted bit was produced on, and its position there. A
	// producer's whole output when the bit has one, so a run split across
	// several named wires still reads as one run -- Verific routinely spreads
	// one operator's result over unrelated wire names, and grouping by wire
	// then hides the very slice the push has to walk into.
	void host_of(SigBit bit, SigSpec &host, int &index)
	{
		Cell *drv = bit_to_driver.at(bit, nullptr);
		if (drv != nullptr && drv->hasPort(ID::Y)) {
			SigSpec y = sigmap(drv->getPort(ID::Y));
			pool<SigBit> uniq;
			// A repeated bit makes the position ambiguous, so that output
			// cannot host a run.
			if (sig_bits_unique(y, uniq))
				for (int i = 0; i < GetSize(y); i++)
					if (y[i] == bit) {
						host = y;
						index = i;
						return;
					}
		}
		host = sigmap(SigSpec(bit.wire));
		index = bit.offset;
	}

	// The rotation that makes `weight` the canonical weight of a bit at `offset`,
	// or -1 when the weight is not a power of two.
	int canonical_rot(int offset, int weight) const
	{
		for (int t = 0; t < k; t++)
			if (weight == (1 << ((offset + t) % k)))
				return t;
		return -1;
	}

	int tree_levels(int terms) const
	{
		int lv = 0;
		while (terms > 2) {
			terms = terms - terms / 3;
			lv++;
		}
		return lv;
	}

	// Logic depth one cell stands for. Everything counts as a single level
	// except the divider class: `$div`/`$mod` become a shift-subtract chain with
	// a stage per quotient bit, so one cell can hide more depth than the entire
	// tree that would replace it, and counting it as 1 makes every rewrite of a
	// bare `A % C` look like a loss. The operand width is a floor on that chain.
	int cell_depth_cost(Cell *cell) const
	{
		if (!div_cells || cell == nullptr)
			return 1;
		if (!cell->type.in(ID($div), ID($mod), ID($divfloor), ID($modfloor)))
			return 1;
		return std::max(1, cell->getParam(ID::A_WIDTH).as_int());
	}

	// Longest path through `region`, weighting each cell by the depth it stands
	// for. Same recurrence as compute_cone_depths, run over the topological
	// order that walk hands back; a cell in a cell-level loop is in neither, so
	// `covered` reports how many the walk reached for callers that check.
	int weighted_region_depth(const pool<Cell *> &region, int *covered = nullptr)
	{
		vector<Cell *> order;
		auto unit = compute_cone_depths(region, &order);
		if (covered != nullptr)
			*covered = GetSize(unit);
		if (!div_cells) {
			int worst = 0;
			for (auto &it : unit)
				worst = std::max(worst, it.second);
			return worst;
		}
		dict<Cell *, int> depth;
		int worst = 0;
		for (auto cell : order) {
			int in = 0;
			for (auto &conn : cell->connections()) {
				if (!cell->input(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire)
						continue;
					Cell *drv = bit_to_driver.at(bit, nullptr);
					if (drv != nullptr && drv != cell && region.count(drv))
						in = std::max(in, depth.at(drv, 0));
				}
			}
			depth[cell] = in + cell_depth_cost(cell);
			worst = std::max(worst, depth.at(cell));
		}
		return worst;
	}

	// Longest combinational level of a bit, counting from flops and inputs.
	// Cone-local depth says how deep the matched logic is, not when its terms
	// arrive: a tree over terms that are themselves late is a loss even when it
	// is locally much shallower than what it replaces. Iterative, and it treats
	// a back edge as level 0, because a vectorizing frontend leaves cell-level
	// loops that are perfectly acyclic bit by bit.
	dict<SigBit, int> level_memo;
	int bit_level(const SigBit &root_bit)
	{
		if (!root_bit.wire)
			return 0;
		if (level_memo.count(root_bit))
			return level_memo.at(root_bit);

		vector<std::pair<SigBit, bool>> stack;
		pool<SigBit> on_stack;
		stack.push_back({root_bit, false});
		while (!stack.empty()) {
			SigBit bit = stack.back().first;
			bool expanded = stack.back().second;
			Cell *drv = bit.wire ? bit_to_driver.at(bit, nullptr) : nullptr;
			if (level_memo.count(bit) || drv == nullptr || is_sequential(drv)) {
				if (!level_memo.count(bit))
					level_memo[bit] = 0;
				on_stack.erase(bit);
				stack.pop_back();
				continue;
			}
			if (!expanded) {
				stack.back().second = true;
				on_stack.insert(bit);
				for (auto &conn : drv->connections())
					if (drv->input(conn.first))
						for (auto b : sigmap(conn.second))
							if (b.wire && !level_memo.count(b) &&
							    !on_stack.count(b))
								stack.push_back({b, false});
				continue;
			}
			int lv = 0;
			int cost = cell_depth_cost(drv);
			for (auto &conn : drv->connections())
				if (drv->input(conn.first))
					for (auto b : sigmap(conn.second))
						if (b.wire)
							lv = std::max(lv, level_memo.at(b, 0) + cost);
			level_memo[bit] = lv;
			on_stack.erase(bit);
			stack.pop_back();
		}
		return level_memo.at(root_bit);
	}

	// True when the weighted bits cannot sum past the modulus, so nothing ever
	// wraps and res_C over them is the identity: a plain weighted sum that
	// merely lands in as many bits as a residue. An n-input popcount reads as
	// mod-(2^n-1) for exactly that reason. There is no reduction on the path to
	// take off it, and re-spelling the adder tree as a carry-save fold only
	// adds the end-around wrap and the normalizer behind it.
	//
	// Measured before the push, which can only widen the reach: a run the push
	// would explode already contributes a full C here, as its digits are the
	// powers of two. A reach of exactly C does wrap, at the one point where
	// every term is set, and is left to the profitability guards below.
	//
	// `reach` overrides the weight sum for a proof carrying opaque digits, whose
	// bit weights add up to a full C no matter how narrow the digit's proven
	// range is -- which would otherwise retire this guard for every such proof.
	bool cannot_wrap(const dict<SigBit, int> &weights, int reach = -1) const
	{
		int64_t total = reach;
		if (reach < 0) {
			total = 0;
			for (auto &it : weights)
				total += it.second;  // each weighted bit is worth at most its weight
		}
		return total < mod_c;
	}

	// True when a tree over `terms` would not land enough earlier than `root`
	// does now. Breaking even on levels is still a loss: the emitted tree is a
	// fixed structure that the Boolean optimizer can no longer fold into its
	// surroundings, so a rewrite has to buy a real margin to be worth it.
	static constexpr int min_arrival_gain = 2;
	bool arrival_no_better(const SigSpec &root, const vector<SigSpec> &terms, int slack)
	{
		int tree = tree_levels(GetSize(terms)) + slack;
		int span = term_to_root_levels(root, terms);
		log_debug("    arrival: tree %d + gain %d vs %d level(s) of matched logic\n", tree,
		          min_arrival_gain, span);
		return tree + min_arrival_gain > span;
	}

	// Levels of logic the rewrite would actually replace: how much later the
	// root lands than the terms it is a function of.
	int term_to_root_levels(const SigSpec &root, const vector<SigSpec> &terms)
	{
		int term_level = 0;
		for (auto &t : terms)
			for (auto bit : t)
				term_level = std::max(term_level, bit_level(bit));
		int root_level = 0;
		for (auto bit : root)
			root_level = std::max(root_level, bit_level(bit));
		return root_level - term_level;
	}

	// ----------------------------------------------------------- shift sink

	// A variable right shift the sink can move: unsigned, as wide out as in,
	// and zero-filling. $shiftx fills with x, which a mask cannot reproduce.
	bool is_sink_shift(Cell *cell)
	{
		if (cell->type != ID($shr) && cell->type != ID($shift))
			return false;
		if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
			return false;
		SigSpec b = sigmap(cell->getPort(ID::B));
		if (b.is_fully_const())
			return false;
		return GetSize(b) >= 1 && GetSize(b) <= max_sink_sel_bits;
	}

	// Recover the reduction's digits from a proof: k consecutive bits of one wire
	// carrying weights coeff*2^j. One coeff shared by every digit is what makes
	// them interchangeable, which is the property the sink rests on.
	bool proof_digits(const Proof &pf, vector<SigSpec> &digits, int &coeff)
	{
		dict<Wire *, dict<int, int>> by_wire;
		for (auto &it : pf.weights) {
			if (it.first.wire == nullptr)
				return false;
			by_wire[it.first.wire][it.first.offset] = it.second;
		}

		coeff = -1;
		for (auto &w : by_wire) {
			vector<int> offs;
			for (auto &it : w.second)
				offs.push_back(it.first);
			std::sort(offs.begin(), offs.end());
			for (int at = 0; at < GetSize(offs); at += k) {
				// The digit's low bit fixes coeff; the rest must follow 2^j off it.
				int base = offs[at];
				int c = w.second.at(base);
				if (c == 0)
					return false;
				for (int j = 0; j < k; j++) {
					if (at + j >= GetSize(offs) || offs[at + j] != base + j)
						return false;
					if (w.second.at(base + j) != int((int64_t(c) << j) % mod_c))
						return false;
				}
				if (coeff < 0)
					coeff = c;
				else if (coeff != c)
					return false;
				digits.push_back(SigSpec(w.first, base, k));
			}
		}
		return coeff > 0 && GetSize(digits) >= 2;
	}

	// Walk back from `sig` and record which bits of `stop` it reads. Fails as
	// soon as the walk escapes `stop`, which is what pins each leaf to one group
	// of the shifted word rather than to the word plus something else.
	bool reads_through(const SigSpec &sig, const pool<SigBit> &stop, pool<SigBit> &reached,
	                   pool<Cell *> &cells, int max_cells)
	{
		pool<SigBit> visited;
		std::queue<SigBit> work;
		for (auto bit : sigmap(sig))
			if (bit.wire != nullptr && visited.insert(bit).second)
				work.push(bit);

		while (!work.empty()) {
			SigBit bit = work.front();
			work.pop();
			if (stop.count(bit)) {
				reached.insert(bit);
				continue;
			}
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr || is_sequential(drv))
				return false;
			if (!cells.insert(drv).second)
				continue;
			charge_walk(1);
			if (GetSize(cells) > max_cells)
				return false;
			for (auto &conn : drv->connections())
				if (drv->input(conn.first))
					for (auto b : sigmap(conn.second))
						if (b.wire != nullptr && visited.insert(b).second)
							work.push(b);
		}
		return true;
	}

	// Nearest variable shift behind `from`: BFS order, so the one the leaves
	// read rather than one further back behind the amount's own decode.
	Cell *nearest_sink_shift(const SigSpec &from)
	{
		pool<SigBit> seen;
		std::queue<SigBit> work;
		for (auto bit : sigmap(from))
			if (bit.wire != nullptr && seen.insert(bit).second)
				work.push(bit);
		int steps = 0;
		while (!work.empty() && steps++ <= max_region_cells) {
			SigBit bit = work.front();
			work.pop();
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr || is_sequential(drv))
				continue;
			if (is_sink_shift(drv))
				return drv;
			charge_walk(1);
			for (auto &conn : drv->connections())
				if (drv->input(conn.first))
					for (auto b : sigmap(conn.second))
						if (b.wire != nullptr && seen.insert(b).second)
							work.push(b);
		}
		return nullptr;
	}

	// Sink a variable right shift out of a reduction whose leaves read fixed,
	// equal-width groups of the shifted word.
	//
	// A shift by g*u moves whole groups, and a reduction that weights every leaf
	// residue alike is invariant under permuting them, so
	//
	//   F(X >> (g*u + w))  ===  F((X >> w) & keep_u)
	//
	// with keep_u clearing the u low groups: both spellings hand F the same
	// multiset of groups, one padded with L(0) where the other dropped what the
	// shift discarded. Only the g-way shift and the mask stay on the data path,
	// and both tables read the amount alone -- so an amount that arrives before
	// the data takes the whole barrel off the path.
	//
	// Unlike emit_shifted this needs no canonical residue at the shift, which is
	// what lets it reach a barrel sitting *below* opaque leaves.
	// Does each digit read exactly one aligned g-bit group of `word`, each group
	// once, with every leaf computing the same function? That last part is what
	// makes the groups interchangeable, and so what lets the sink permute and drop
	// them. This is the whole of the sink's match that lives on the reduction's
	// side of the shift, so the inliner can ask it of a submodule across a port
	// before deciding to pull the module in.
	// The sink masks the word where it stands, so the reduction has to be all that
	// reads it -- anything else would see the masked value. `skip` is the shift
	// itself; a child reached through a port has none, and asks with nullptr.
	// Shared with port_group_width because that runs a module early, to decide
	// whether inlining is worth a flatten that nothing undoes.
	// Every bit the sink alters. Not just the word: each leaf comes to read a
	// different group, so every digit and partial sum under the root moves with
	// it, and only the root itself is left equal. The rename below wants the same
	// set, for the same reason.
	void sink_changed_bits(const SigSpec &word, const pool<Cell *> &leaf_cells,
	                       const pool<Cell *> &region, const pool<SigBit> &rootbits,
	                       pool<SigBit> &changed)
	{
		for (auto bit : sigmap(word))
			if (bit.wire != nullptr)
				changed.insert(bit);
		for (auto cells : {&leaf_cells, &region})
			for (auto c : *cells)
				for (auto &conn : c->connections())
					if (c->output(conn.first))
						for (auto bit : sigmap(conn.second))
							if (bit.wire != nullptr && !rootbits.count(bit))
								changed.insert(bit);
	}

	// The sink rewrites in place, so anything outside the reduction that reads a
	// bit it changes would silently read the new value. Only the root survives the
	// rewrite equal, so the root is the only thing the outside may hold on to.
	// Shared with port_group_width, which has to reach this verdict a module early
	// to keep the inliner from flattening for a sink that then declines.
	bool changed_bits_are_private(const pool<SigBit> &changed, const pool<Cell *> &leaf_cells,
	                              const pool<Cell *> &region, Cell *skip, const char *&why)
	{
		for (auto w : module->wires())
			if (w->port_output || w->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(SigSpec(w)))
					if (changed.count(bit)) {
						why = "reduction's own signal is a port or kept";
						return false;
					}
		for (auto c : module->cells()) {
			if (c == skip || leaf_cells.count(c) || region.count(c))
				continue;
			for (auto &conn : c->connections())
				if (!c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (changed.count(bit)) {
							why = "reduction's own signal has another reader";
							return false;
						}
		}
		return true;
	}

	bool digit_groups(const SigSpec &word, const vector<SigSpec> &digits, int g,
	                  dict<SigBit, int> &ypos, vector<int> &group_of,
	                  vector<pool<Cell *>> &cones, pool<Cell *> &leaf_cells,
	                  const char *&why)
	{
		int m = GetSize(digits), n = GetSize(word);
		auto no = [&](const char *reason) {
			why = reason;
			return false;
		};

		// Positions of the word, so a leaf's reads can be tested for being one
		// aligned group. A repeated or constant bit has no position.
		pool<SigBit> ybits;
		for (int i = 0; i < n; i++) {
			if (word[i].wire == nullptr || !ypos.emplace(word[i], i).second)
				return no("shifted word has a constant or repeated bit");
			ybits.insert(word[i]);
		}

		group_of.assign(m, -1);
		cones.assign(m, pool<Cell *>());
		pool<int> used;
		for (int i = 0; i < m; i++) {
			pool<SigBit> reached;
			if (!reads_through(digits[i], ybits, reached, cones[i], max_region_cells))
				return no("digit cone does not reach the shifted word");
			if (GetSize(reached) != g)
				return no("digit does not read a whole group");
			int lo = n;
			for (auto bit : reached)
				lo = std::min(lo, ypos.at(bit));
			if (lo % g != 0)
				return no("digit's group is not aligned");
			for (auto bit : reached)
				if (ypos.at(bit) < lo || ypos.at(bit) >= lo + g)
					return no("digit straddles two groups");
			if (!used.insert(lo / g).second)
				return no("two digits read the same group");
			group_of[i] = lo / g;
			for (auto c : cones[i])
				leaf_cells.insert(c);
		}

		// One shared leaf function, settled over all 2^g vectors of a group.
		if (g > max_sink_group_bits || eval_exhausted())
			return no("out of eval budget");
		ConstEval &ce = shared_ce();
		vector<uint64_t> ref(size_t(1) << g, 0);
		for (int i = 0; i < m; i++) {
			SigSpec grp = word.extract(g * group_of[i], g);
			int cells = GetSize(cones[i]);
			// Same one-way switch as value_bound and check_linear: a vectorized
			// leaf leaves cells that each need a bit of another's output, which
			// ConstEval cannot resolve whole even though the cone is acyclic bit
			// by bit. A flattened design reaches the sink in exactly that shape.
			bool allow_bits = cells <= max_bits_eval_cells && cone_has_cell_loop(cones[i]);
			bool bits_mode = false;
			for (int v = 0; v < (1 << g); v++) {
				uint64_t out = 0;
				vector<std::pair<SigSpec, Const>> sets{{grp, Const(v, g)}};
				if (!bits_mode) {
					if (eval_with(ce, sets, digits[i], out, cells)) {
						if (i == 0)
							ref[v] = out;
						else if (ref[v] != out)
							return no("leaves compute different functions");
						continue;
					}
					if (!allow_bits)
						return no("leaf would not evaluate");
					bits_mode = true;
				}
				if (!eval_with_bits(sets, digits[i], out, cells))
					return no("leaf would not evaluate bitwise");
				if (i == 0)
					ref[v] = out;
				else if (ref[v] != out)
					return no("leaves compute different functions");
			}
			if (eval_exhausted())
				return no("out of eval budget");
		}
		return true;
	}

	// Group width at which some reduction here reads `word` as interchangeable
	// aligned groups, or 0 if none does. Lets the inliner price a submodule's
	// reduction from the parent, where the shift is, without inlining it first.
	int port_group_width(const SigSpec &word)
	{
		auto width_ok = [&](int w) { return w >= min_mod_bits && w <= max_mod_bits; };
		auto interesting = [&](const pool<Cell *> &cells) { return GetSize(cells) >= 4; };
		auto any_width = [&](int) { return true; };
		auto roots = collect_root_candidates(width_ok, interesting, true, max_region_cells,
		                                     max_region_leaves, max_internal_roots, any_width);
		int n = GetSize(word);
		for (auto &root : roots) {
			if (walk_exhausted() || eval_exhausted())
				break;
			SigSpec sig = sigmap(root.sig);
			pool<SigBit> uniq;
			if (!sig_fully_driven(sig) || !sig_bits_unique(sig, uniq))
				continue;
			k = GetSize(sig);
			mod_c = (1 << k) - 1;
			Proof pf;
			if (!prove(sig, pf, 0))
				continue;
			vector<SigSpec> digits;
			int coeff = 0;
			if (!proof_digits(pf, digits, coeff))
				continue;
			int m = GetSize(digits);
			if (m < 2 || n % m != 0)
				continue;
			int g = n / m;
			if (g < 1 || g > max_sink_group_bits)
				continue;
			dict<SigBit, int> ypos;
			vector<int> group_of;
			vector<pool<Cell *>> cones;
			pool<Cell *> leaf_cells;
			const char *why = nullptr;
			if (digit_groups(word, digits, g, ypos, group_of, cones, leaf_cells, why)) {
				// No shift to skip: in the child the word arrives on a port.
				pool<SigBit> rootbits(sig.begin(), sig.end());
				pool<SigBit> changed;
				sink_changed_bits(word, leaf_cells, pf.region, rootbits, changed);
				if (changed_bits_are_private(changed, leaf_cells, pf.region, nullptr,
				                             why))
					return g;
			}
			log_debug("  port group %s under %s: %s\n", log_signal(word),
			          log_signal(sig), why);
		}
		return 0;
	}

	bool sink_shift(const SigSpec &root, Proof &pf)
	{
		auto no = [&](const char *why) {
			log_debug("  sink %s: %s\n", log_signal(root), why);
			return false;
		};
		vector<SigSpec> digits;
		int coeff = 0;
		if (!proof_digits(pf, digits, coeff))
			return no("no digits");
		int m = GetSize(digits);

		Cell *sh = nearest_sink_shift(digits[0]);
		if (sh == nullptr)
			return no("no shift behind the digits");

		SigSpec sy = sigmap(sh->getPort(ID::Y));
		SigSpec sa = sigmap(sh->getPort(ID::A));
		SigSpec sb = sigmap(sh->getPort(ID::B));
		int n = GetSize(sy), selb = GetSize(sb);
		if (GetSize(sa) != n || n == 0 || n % m != 0)
			return no("width not a whole number of digits");
		int g = n / m;
		if (g < 1 || g > max_sink_group_bits)
			return no("group width out of range");
		int wb = std::max(1, clog2_int(g));
		// A barrel over selb bits for a g-way shift plus one mask level.
		if (selb - wb - 1 < min_sink_gain)
			return no("gain below -min-sink-gain");

		dict<SigBit, int> ypos;
		vector<int> group_of;
		vector<pool<Cell *>> cones;
		pool<Cell *> leaf_cells;
		const char *why = nullptr;
		if (!digit_groups(sy, digits, g, ypos, group_of, cones, leaf_cells, why))
			return no(why);

		pool<SigBit> rootbits(root.begin(), root.end());
		pool<SigBit> changed;
		sink_changed_bits(sy, leaf_cells, pf.region, rootbits, changed);
		if (!changed_bits_are_private(changed, leaf_cells, pf.region, sh, why))
			return no(why);


		// The tables hang off the amount alone, so the sink only pays when the
		// amount is not itself the late input: otherwise the barrel comes off the
		// data path and reappears on the amount's.
		int alevel = 0, blevel = 0;
		for (auto bit : sa)
			alevel = std::max(alevel, bit_level(bit));
		for (auto bit : sb)
			blevel = std::max(blevel, bit_level(bit));
		// Both sides meet again at the mask, so what the sink is worth is the depth
		// to that point, not the amount's arrival on its own. The barrel costs a
		// level per amount bit whichever input is late; afterwards the data only
		// pays the g-way shift, but the amount pays a 2^selb-entry table, which is
		// just as deep as the barrel was. So the sink pays exactly when the data is
		// the late input by more than the table costs -- with both arriving
		// together it lands the old barrel's depth back on the amount and adds the
		// mask on top, which is how it reads as a win locally and loses on the path.
		int before = std::max(alevel, blevel) + selb;
		int after = std::max(blevel + selb, alevel + wb) + 1;
		if (before - after < min_sink_gain) {
			log_debug("  sink %s: depth %d -> %d, data at %d, amount at %d\n",
			          log_signal(sy), before, after, alevel, blevel);
			return false;
		}

		log_debug("  sink %s under %s: %d leaf group(s) of %d bit(s), amount %d bits\n",
		          log_signal(sy), log_signal(root), m, g, selb);

		src = cell_src(sh);
		cell_name = sh->name;

		// w = amount mod g and the group-keep mask, both as one constant table
		// read: a divider and per-group comparators would cost more and buy
		// nothing, since the amount is only selb bits wide. The mask stays its own
		// level: folding it into a per-group select costs the barrel's sharing
		// across bits, which is worth more than the level it saves.
		Const wtab, ktab;
		for (int v = 0; v < (1 << selb); v++) {
			int u = v / g, w = v % g;
			for (int i = 0; i < wb; i++)
				wtab.bits().push_back((w >> i) & 1 ? State::S1 : State::S0);
			for (int i = 0; i < n; i++)
				ktab.bits().push_back(i / g >= u ? State::S1 : State::S0);
		}
		SigSpec amt = module->Bmux(NEW_ID3_SUFFIX("modsink_amt"), wtab, sb, src);
		SigSpec keep = module->Bmux(NEW_ID3_SUFFIX("modsink_keep"), ktab, sb, src);
		SigSpec small = module->Shr(NEW_ID3_SUFFIX("modsink_shr"), sa, amt, false, src);
		SigSpec masked = module->And(NEW_ID3_SUFFIX("modsink_masked"), small, keep, false, src);
		cells_added += 4;

		disconnect_root(sy, sh, "modsink_old");
		module->connect(sy, masked);
		pool<Cell *> dead;
		dead.insert(sh);
		sweep_dead(dead);

		// The sink is the one rewrite here that does not preserve what it
		// rewrites. The word is meant to differ, and so is every digit and
		// partial sum below the root, since each leaf now reads a different
		// group; only the root comes out the same. A public name is what an
		// equivalence checker pairs gold to gate by, so leaving the RTL's names
		// on those asks it to prove away the very difference the rewrite exists
		// to make -- which is how equiv_opt fails a sink that is correct. Take
		// the names off and the proof lands on the outputs, where it belongs.
		// One changed bit is enough to disqualify the whole wire as an anchor, even
		// where the wire also carries root bits that did survive: the name pairs
		// gold to gate bit for bit, so the changed bits come along and take the
		// root's own bits down with them. Nothing is lost by dropping such a
		// mixed name -- the root is still anchored wherever it is named alone, and
		// at the outputs. No port can reach here to have its name taken: the check
		// above refuses the sink outright if a port carries a changed bit.
		vector<Wire *> unname;
		for (auto w : module->wires()) {
			if (!w->name.isPublic())
				continue;
			for (auto bit : sigmap(SigSpec(w)))
				if (changed.count(bit)) {
					unname.push_back(w);
					break;
				}
		}
		for (auto w : unname)
			module->rename(w, module->uniquify("$modsink$" + w->name.str().substr(1)));

		sunk_shifts++;
		dirty = true;
		return true;
	}

	bool rewrite(const SigSpec &root, Proof &pf)
	{
		if (GetSize(pf.weights) < min_terms || GetSize(pf.weights) > max_terms)
			return false;
		if (cannot_wrap(pf.weights, pf.reach)) {
			log_debug("  %s: terms cannot reach the modulus\n", log_signal(root));
			return false;
		}
		if (!find_anchor_driver(root, anchor))
			return false;
		src = cell_src(anchor);
		cell_name = anchor->name;
		// The push proves normalizers as it walks, and the memo is keyed on the
		// signal alone, so it cannot outlive the k it was filled for.
		prove_memo_ok.clear();
		prove_memo.clear();
		prove_memo_reach.clear();
		bound_memo.clear();

		vector<SigSpec> terms;
		if (!weight_terms(pf.weights, terms) || GetSize(terms) > max_terms)
			return false;

		int walked = 0;
		int region_depth = weighted_region_depth(pf.region, &walked);
		// A const-table fold vectorizes into cells that each want a bit of
		// another's output, and the topological walk above never brings those
		// ready, so a cone hundreds of levels deep measures as two. The bit
		// walk treats a back edge as level 0 and does see through it.
		if (opaque_digits && walked < GetSize(pf.region))
			region_depth = std::max(region_depth, term_to_root_levels(root, terms));

		// Profitability: the emitted tree is one FA level per Wallace stage plus
		// the final fold, against the matched region's own depth. Measured after
		// the push, whose whole purpose is to move the terms to earlier signals.
		log_debug("  rewrite %s: region depth %d vs tree depth %d\n", log_signal(root),
		          region_depth, tree_levels(GetSize(terms)) + 2);
		if (region_depth <= tree_levels(GetSize(terms)) + 2)
			return false;
		if (arrival_no_better(root, terms, 2))
			return false;

		auto pair = emit_tree(terms);
		SigSpec result = emit_eac(pair.first, pair.second);

		// The fold can produce 2^k-1 where the original produced 0, so canonicalize
		// before handing the value back to logic that may compare it.
		SigSpec all_ones = module->ReduceAnd(NEW_ID3_SUFFIX("modred_ones"), result, false, src);
		result = module->Mux(NEW_ID3_SUFFIX("modred_norm"), result, SigSpec(State::S0, k),
		                     all_ones, src);
		cells_added += 2;

		disconnect_root(root, anchor, "modred_old");
		module->connect(root, result);
		claim_region(root, pf.region);
		sweep_dead(pf.region);  // rebuilds the indexes, dropping the caches
		mark_emitted_out(root);
		regions++;
		dirty = true;
		return true;
	}

	// Drop what the rewrite orphaned. Correctness does not need it -- opt_clean
	// would get there -- but the disconnected tree still computes the same
	// residue, so the next round matches it and builds a second tree beside the
	// one that replaced it.
	void sweep_dead(const pool<Cell *> &region)
	{
		pool<Cell *> cand = region;
		while (!cand.empty()) {
			pool<SigBit> used;
			for (auto c : module->cells())
				for (auto &conn : c->connections())
					if (!c->output(conn.first))
						for (auto bit : sigmap(conn.second))
							used.insert(bit);
			for (auto w : module->wires())
				if (w->port_output || w->get_bool_attribute(ID::keep))
					for (auto bit : sigmap(SigSpec(w)))
						used.insert(bit);
			for (auto &conn : module->connections())
				for (auto bit : sigmap(conn.second))
					used.insert(bit);

			pool<Cell *> next;
			for (auto c : cand) {
				if (c->get_bool_attribute(ID::keep) || is_sequential(c))
					continue;
				bool dead = true;
				for (auto &conn : c->connections())
					if (c->output(conn.first))
						for (auto bit : sigmap(conn.second))
							if (bit.wire != nullptr && used.count(bit))
								dead = false;
				if (!dead)
					continue;
				for (auto &conn : c->connections())
					if (!c->output(conn.first))
						for (auto bit : sigmap(conn.second))
							if (Cell *d = bit_to_driver.at(bit, nullptr))
								if (d != c)
									next.insert(d);
				module->remove(c);
			}
			if (next.empty())
				break;
			cand.swap(next);
		}
		build_indexes_again();
	}

	// The sweep invalidates every driver and cell the worker cached, and the fn
	// match still has candidates to walk after a plain rewrite declines.
	void build_indexes_again()
	{
		clear_cell_caches();
		bit_to_driver.clear();
		input_port_bits.clear();
		build_indexes();
	}

	// ------------------------------------------------- function of a residue

	// A residue is rarely consumed as a number. It gets compared, decoded, or
	// -- once the dead bits of a fold tree's top are swept -- read one bit at a
	// time in whatever order the one-hot spelling happened to leave them. All of
	// those are g(res_C(x)) for some g, so insisting the rewritten signal *be*
	// the residue gives up on the top of nearly every real reduction tree, which
	// is exactly the node whose terms reach furthest back. Match g instead: the
	// tree computes the residue and a 2^k-entry table computes g.
	struct FnMatch {
		vector<SigSpec> group;  // the proven residues the cone reads
		vector<int> coeff;      // always powers of two: trees combine by rotation
		pool<Cell *> cone;
		SigSpec outs;         // the cone bits that are a function of the residue
		vector<Const> table;  // g, indexed by the combined residue
	};

	dict<SigBit, pool<Cell *>> bit_to_consumers;
	bool consumers_built = false;

	void build_consumers()
	{
		if (consumers_built)
			return;
		consumers_built = true;
		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				if (!cell->input(conn.first))
					continue;
				for (auto bit : sigmap(conn.second))
					if (bit.wire)
						bit_to_consumers[bit].insert(cell);
			}
	}

	// Two residues can only be forced to independent values if neither is
	// computed from the other; otherwise the sweep below covers combinations the
	// circuit cannot produce *and* misses the constraint that ties them.
	bool residues_independent(const SigSpec &a, const SigSpec &b,
	                          const dict<SigSpec, Proof> &proofs)
	{
		for (int pass = 0; pass < 2; pass++) {
			const SigSpec &from = pass ? b : a, &to = pass ? a : b;
			auto it = proofs.find(from);
			if (it == proofs.end())
				return false;
			for (auto c : it->second.region)
				for (auto &conn : c->connections()) {
					if (!c->output(conn.first))
						continue;
					for (auto bit : sigmap(conn.second))
						if (to.extract(bit).size() != 0)
							return false;
				}
		}
		return true;
	}

	// Grow the largest cone above `seed` whose every non-constant input is a
	// proven residue. A cell reading anything else is refused, which is what
	// makes the sweep sound: nothing inside the cone can be reached around the
	// residues the sweep drives.
	void grow_fn_cone(const SigSpec &seed, const dict<SigBit, SigSpec> &residue_of,
	                  const dict<SigSpec, Proof> &proofs, vector<SigSpec> &group,
	                  pool<Cell *> &cone)
	{
		build_consumers();
		group.push_back(seed);
		pool<SigSpec> in_group;
		pool<SigBit> covered;
		in_group.insert(seed);
		for (auto bit : seed)
			covered.insert(bit);

		for (bool grew = true; grew && !walk_exhausted();) {
			grew = false;
			pool<Cell *> frontier;
			for (auto bit : covered)
				for (auto c : bit_to_consumers[bit])
					if (!cone.count(c))
						frontier.insert(c);

			for (auto c : by_name(frontier)) {
				charge_walk(1);
				if (!c->hasPort(ID::Y) || is_sequential(c))
					continue;
				vector<SigSpec> add;
				bool ok = true;
				for (auto &conn : c->connections()) {
					if (!ok)
						break;
					if (!c->input(conn.first))
						continue;
					for (auto bit : sigmap(conn.second)) {
						if (!bit.wire || covered.count(bit))
							continue;
						auto it = residue_of.find(bit);
						if (it == residue_of.end()) {
							ok = false;
							break;
						}
						if (!in_group.count(it->second))
							add.push_back(it->second);
					}
				}
				if (!ok || GetSize(group) + GetSize(add) > max_fn_slots)
					continue;
				for (auto &r : add)
					for (auto &g : group)
						if (!residues_independent(r, g, proofs))
							ok = false;
				if (!ok)
					continue;

				for (auto &r : add)
					if (in_group.insert(r).second) {
						group.push_back(r);
						for (auto bit : r)
							covered.insert(bit);
					}
				cone.insert(c);
				for (auto bit : sigmap(c->getPort(ID::Y)))
					if (bit.wire)
						covered.insert(bit);
				grew = true;
			}

			if (!grew)
				grew = grow_fn_cone_cycle(frontier, residue_of, proofs, group, in_group,
				                          covered, cone);
		}
	}

	// Admitting one cell at a time stalls on a cell-level combinational loop: a
	// vectorizing frontend leaves two wide cells each needing a bit of the
	// other's output, so neither is ever admissible alone even though the pair
	// is. Shrink the frontier to the largest set whose uncovered inputs are all
	// either proven residues or driven from inside the set, and take it whole.
	bool grow_fn_cone_cycle(const pool<Cell *> &frontier, const dict<SigBit, SigSpec> &residue_of,
	                        const dict<SigSpec, Proof> &proofs, vector<SigSpec> &group,
	                        pool<SigSpec> &in_group, pool<SigBit> &covered, pool<Cell *> &cone)
	{
		pool<Cell *> cand;
		for (auto c : frontier)
			if (c->hasPort(ID::Y) && !is_sequential(c))
				cand.insert(c);
		if (GetSize(cand) < 2)
			return false;

		// Drop cells that need something no candidate produces, until stable.
		for (bool shrank = true; shrank;) {
			shrank = false;
			pool<SigBit> inside;
			for (auto c : cand)
				for (auto &conn : c->connections())
					if (c->output(conn.first))
						for (auto bit : sigmap(conn.second))
							inside.insert(bit);
			for (auto c : by_name(cand)) {
				charge_walk(1);
				if (walk_exhausted())
					return false;
				bool ok = true;
				for (auto &conn : c->connections()) {
					if (!c->input(conn.first) || !ok)
						continue;
					for (auto bit : sigmap(conn.second)) {
						if (!bit.wire || covered.count(bit) || inside.count(bit))
							continue;
						if (!residue_of.count(bit)) {
							ok = false;
							break;
						}
					}
				}
				if (!ok) {
					cand.erase(c);
					shrank = true;
					break;
				}
			}
		}
		if (GetSize(cand) < 2)
			return false;

		// Every residue the set reads has to join the group, and they must stay
		// mutually independent for the sweep to cover their combinations.
		vector<SigSpec> add;
		pool<SigSpec> add_seen;
		for (auto c : by_name(cand))
			for (auto &conn : c->connections()) {
				if (!c->input(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire || covered.count(bit))
						continue;
					auto it = residue_of.find(bit);
					if (it != residue_of.end() && !in_group.count(it->second) &&
					    add_seen.insert(it->second).second)
						add.push_back(it->second);
				}
			}
		if (GetSize(group) + GetSize(add) > max_fn_slots)
			return false;
		for (auto &r : add) {
			for (auto &g : group)
				if (!residues_independent(r, g, proofs))
					return false;
			for (auto &o : add)
				if (o != r && !residues_independent(r, o, proofs))
					return false;
		}

		for (auto &r : add)
			if (in_group.insert(r).second) {
				group.push_back(r);
				for (auto bit : r)
					covered.insert(bit);
			}
		for (auto c : cand) {
			charge_walk(1);
			cone.insert(c);
			for (auto bit : sigmap(c->getPort(ID::Y)))
				if (bit.wire)
					covered.insert(bit);
		}
		log_debug("      fn grow: admitted %d mutually dependent cell(s)\n", GetSize(cand));
		return true;
	}

	// Iterating a pool of pointers follows allocator addresses, which differ
	// between platforms and runs. Anything whose order reaches the emitted
	// netlist has to go by name instead, or the pass is not reproducible.
	static vector<Cell *> by_name(const pool<Cell *> &cells)
	{
		vector<Cell *> out(cells.begin(), cells.end());
		std::sort(out.begin(), out.end(),
		          [](Cell *a, Cell *b) { return a->name.str() < b->name.str(); });
		return out;
	}

	static bool bit_before(const SigBit &a, const SigBit &b)
	{
		if (a.wire == nullptr || b.wire == nullptr)
			return (a.wire == nullptr) < (b.wire == nullptr);
		if (a.wire != b.wire)
			return a.wire->name.str() < b.wire->name.str();
		return a.offset < b.offset;
	}

	// Bits the cone drives that something outside it reads.
	void cone_outputs(const pool<Cell *> &cone, SigSpec &outs)
	{
		pool<SigBit> seen;
		vector<SigBit> found;
		for (auto c : by_name(cone))
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire || !seen.insert(bit).second)
						continue;
					for (auto u : bit_to_consumers[bit])
						if (!cone.count(u)) {
							found.push_back(bit);
							break;
						}
				}
			}
		// The table the fit builds is indexed by position in `outs`, so the
		// order has to be the same everywhere the pass runs.
		std::sort(found.begin(), found.end(), bit_before);
		for (auto &bit : found)
			outs.append(bit);
	}

	// Sweep the group over every value each residue can take, then look for the
	// rotation weights that make each output bit a function of the combined
	// residue. Exhaustive over a superset of the reachable combinations, so a
	// bit that survives really is a function of the residue alone.
	bool fit_function(FnMatch &m, const dict<SigSpec, Proof> &proofs, int cells, bool allow_bits)
	{
		int s = GetSize(m.group);
		if (s < 1 || GetSize(m.outs) < 1 || GetSize(m.outs) > 63)
			return false;

		const int64_t limit = int64_t(1) << max_cut_bits;
		int64_t combos = 1;
		vector<int> maxv;
		for (auto &r : m.group) {
			int64_t range = int64_t(proofs.at(r).maxval) + 1;
			if (range < 2 || combos > limit / range)
				return false;
			maxv.push_back(int(range - 1));
			combos *= range;
		}

		ConstEval &ce = shared_ce();
		vector<uint64_t> tab(combos);
		vector<int> vals(s);
		// Bits every vector resolved. A cone output the group does not
		// determine is not a function of it, so it drops out here rather
		// than sinking the whole match.
		uint64_t all = GetSize(m.outs) == 64 ? ~uint64_t(0)
		                                     : (uint64_t(1) << GetSize(m.outs)) - 1;
		// Rewritten in place per vector; see check_linear.
		vector<std::pair<SigSpec, Const>> sets;
		for (auto &r : m.group)
			sets.push_back({r, Const(State::S0, GetSize(r))});
		for (int64_t c = 0; c < combos; c++) {
			int64_t rest = c;
			for (int i = 0; i < s; i++) {
				vals[i] = int(rest % (int64_t(maxv[i]) + 1));
				rest /= int64_t(maxv[i]) + 1;
				set_const_u64(sets[i].second, vals[i]);
			}
			if (eval_exhausted())
				return false;
			uint64_t ok_mask = 0;
			eval_masked(ce, sets, m.outs, tab[c], ok_mask, cells);
			// ConstEval gives up a whole cell at a time, so on a cone with
			// cell-level loops it can resolve nothing; the bit walk may.
			if (allow_bits && (~ok_mask & all) != 0) {
				uint64_t bval = 0, bmask = 0;
				eval_masked_bits(sets, m.outs, bval, bmask, cells);
				tab[c] = (tab[c] & ok_mask) | (bval & ~ok_mask);
				ok_mask |= bmask;
			}
			all &= ok_mask;
			if (all == 0) {
				log_debug("      fn: nothing resolvable at vector %lld\n", (long long)c);
				return false;
			}
		}
		log_debug("      fn: %d of %d out bit(s) resolvable\n", __builtin_popcountll(all),
		          GetSize(m.outs));

		// Only rotations: a reduction tree scales a residue by doubling it, and
		// opening the search to every coefficient would fit noise.
		// A bit that never moves is a constant, not a reduction of anything.
		uint64_t varies = 0;
		for (int64_t c = 1; c < combos; c++)
			varies |= (tab[c] ^ tab[0]) & all;

		uint64_t best_fit = 0;
		int64_t combs = 1;
		for (int i = 0; i < s; i++)
			combs *= k;
		for (int64_t ci = 0; ci < combs; ci++) {
			vector<int> coeff(s);
			int64_t rest = ci;
			for (int i = 0; i < s; i++) {
				coeff[i] = 1 << int(rest % k);
				rest /= k;
			}
			vector<uint64_t> seen(mod_c, 0);
			vector<bool> have(mod_c, false);
			uint64_t bad = 0;
			for (int64_t c = 0; c < combos; c++) {
				int64_t rest2 = c;
				int t = 0;
				for (int i = 0; i < s; i++) {
					int v = int(rest2 % (int64_t(maxv[i]) + 1));
					rest2 /= int64_t(maxv[i]) + 1;
					t = (t + coeff[i] * v) % mod_c;
				}
				if (have[t])
					bad |= (seen[t] ^ tab[c]) & all;
				have[t] = true;
				seen[t] = tab[c];
			}
			uint64_t fit = ~bad & varies & all;
			if (__builtin_popcountll(fit) > __builtin_popcountll(best_fit)) {
				best_fit = fit;
				m.coeff = coeff;
			}
		}
		log_debug("      fn: %d bit(s) vary, %d fit as f(residue)\n",
		          __builtin_popcountll(varies & all), __builtin_popcountll(best_fit));
		if (best_fit == 0)
			return false;

		// Rebuild the table over the surviving bits only.
		SigSpec keep;
		vector<int> keep_idx;
		for (int i = 0; i < GetSize(m.outs); i++)
			if ((best_fit >> i) & 1) {
				keep.append(m.outs[i]);
				keep_idx.push_back(i);
			}
		vector<int> entry(mod_c, -1);
		for (int64_t c = 0; c < combos; c++) {
			int64_t rest = c;
			int t = 0;
			for (int i = 0; i < s; i++) {
				int v = int(rest % (int64_t(maxv[i]) + 1));
				rest /= int64_t(maxv[i]) + 1;
				t = (t + m.coeff[i] * v) % mod_c;
			}
			int packed = 0;
			for (int j = 0; j < GetSize(keep_idx); j++)
				if ((tab[c] >> keep_idx[j]) & 1)
					packed |= 1 << j;
			entry[t] = packed;
		}
		// The fold hands back 2^k-1 where the tree meant zero, so the table has
		// to answer the same thing at both spellings. Unreachable residues are
		// don't-care and ride along on zero's answer.
		m.table.clear();
		for (int t = 0; t < (1 << k); t++) {
			int idx = t % mod_c;
			m.table.push_back(Const(entry[idx] < 0 ? std::max(entry[0], 0) : entry[idx],
			                        GetSize(keep)));
		}
		m.outs = keep;
		return true;
	}

	// Combined weights of the group under the fitted coefficients: the residue
	// the table is going to read. `reach` follows the same combination, and
	// stays -1 unless some member priced an opaque digit below its bit weights.
	void fn_weights(const FnMatch &m, const dict<SigSpec, Proof> &proofs,
	                dict<SigBit, int> &weights, int *reach = nullptr)
	{
		int64_t total = 0;
		bool any_reach = false;
		for (int i = 0; i < GetSize(m.group); i++) {
			const Proof &p = proofs.at(m.group[i]);
			for (auto &it : p.weights)
				weights[it.first] = int((int64_t(weights.at(it.first, 0)) +
				                         int64_t(m.coeff[i]) * it.second) %
				                        mod_c);
			// Each group member reads as a residue, so its range is what it
			// contributes -- but only price it that way once some member rests
			// on a bound, to leave the plain path's pricing untouched.
			total += int64_t(m.coeff[i]) * p.maxval;
			any_reach |= p.reach >= 0;
		}
		for (auto it = weights.begin(); it != weights.end();)
			it = (it->second == 0) ? weights.erase(it) : ++it;
		if (reach)
			*reach = any_reach ? int(std::min<int64_t>(total, mod_c)) : -1;
	}

	bool rewrite_fn(FnMatch &m, const dict<SigSpec, Proof> &proofs)
	{
		dict<SigBit, int> weights;
		int reach = -1;
		fn_weights(m, proofs, weights, &reach);
		if (GetSize(weights) < min_terms || GetSize(weights) > max_terms)
			return false;
		if (cannot_wrap(weights, reach)) {
			log_debug("  fn %s: terms cannot reach the modulus\n", log_signal(m.outs));
			return false;
		}
		if (!find_anchor_driver(m.outs, anchor))
			return false;
		src = cell_src(anchor);
		cell_name = anchor->name;
		prove_memo_ok.clear();
		prove_memo.clear();
		prove_memo_reach.clear();
		bound_memo.clear();

		pool<Cell *> region = m.cone;
		for (auto &r : m.group)
			for (auto c : proofs.at(r).region)
				region.insert(c);
		int region_depth = weighted_region_depth(region);

		vector<SigSpec> terms;
		if (!weight_terms(weights, terms) || GetSize(terms) > max_terms)
			return false;

		// The table read costs about as much as the final fold, so it counts as
		// one more level on top of the tree.
		log_debug("  rewrite fn over %d residue(s) -> %s: region depth %d vs tree depth %d\n",
		          GetSize(m.group), log_signal(m.outs), region_depth,
		          tree_levels(GetSize(terms)) + 3);
		if (region_depth <= tree_levels(GetSize(terms)) + 3)
			return false;
		if (arrival_no_better(m.outs, terms, 3))
			return false;

		auto pair = emit_tree(terms);
		SigSpec res = emit_eac(pair.first, pair.second);
		Const table;
		for (auto &e : m.table)
			table.bits().insert(table.bits().end(), e.bits().begin(), e.bits().end());
		SigSpec out = module->Bmux(NEW_ID3_SUFFIX("modred_fn"), table, res, src);
		cells_added++;

		disconnect_root(m.outs, anchor, "modred_old");
		module->connect(m.outs, out);
		claim_region(m.outs, region);
		build_indexes_again();  // the connect moved the drivers it caches
		mark_emitted_out(m.outs);
		regions++;
		fn_regions++;
		dirty = true;
		return true;
	}

	// Try every proven residue as the seed of a function cone, widest first, and
	// take the first one that pays. Each seed carries its whole tree with it, so
	// there is nothing to gain from a second match in the same round.
	bool rewrite_widest_fn(const vector<std::pair<int, SigSpec>> &cands,
	                       const dict<SigSpec, Proof> &proofs, const pool<SigSpec> &done)
	{
		dict<SigBit, SigSpec> residue_of;
		for (auto &c : cands)
			for (auto bit : c.second)
				residue_of[bit] = c.second;

		// What the widest plain rewrite would reach. A table over a group that
		// covers less than that trades the deepest terms for a lookup, which is
		// backwards: the fn match exists to get *past* logic above a residue,
		// not to settle for a shallower one. Roots already rewritten do not
		// count: the plain path will not touch them again.
		int widest = 0;
		for (auto &c : cands)
			if (!done.count(c.second))
				widest = std::max(widest, c.first);

		for (auto &c : cands) {
			if (walk_exhausted() || eval_exhausted() || root_claimed(c.second))
				continue;
			k = GetSize(c.second);
			mod_c = (1 << k) - 1;

			FnMatch m;
			grow_fn_cone(c.second, residue_of, proofs, m.group, m.cone);
			if (m.cone.empty()) {
				log_debug("  fn seed %s: empty cone\n", log_signal(c.second));
				continue;
			}
			// The group may include trees this pass emitted, but the cone it
			// replaces must not: rewriting our own output stacks a table on
			// a tree that already computes the same residue.
			bool own = false;
			for (auto cell : m.cone)
				if (cell->has_attribute(emitted_attr()))
					own = true;
			if (own) {
				log_debug("  fn seed %s: cone contains emitted logic\n",
				          log_signal(c.second));
				continue;
			}
			pool<SigBit> covered;
			for (auto &g : m.group)
				for (auto &it : proofs.at(g).weights)
					covered.insert(it.first);
			if (GetSize(covered) < widest) {
				log_debug("  fn seed %s: covers %d bit(s) < widest %d\n",
				          log_signal(c.second), GetSize(covered), widest);
				continue;
			}
			cone_outputs(m.cone, m.outs);
			if (!fit_function(m, proofs, GetSize(m.cone),
			                  GetSize(m.cone) <= max_bits_eval_cells &&
			                          cone_has_cell_loop(m.cone))) {
				log_debug("  fn seed %s: %d group, %d cone cell(s), %d out bit(s) -> no fit\n",
				          log_signal(c.second), GetSize(m.group), GetSize(m.cone),
				          GetSize(m.outs));
				continue;
			}
			log_debug("  fn fit: %d residue(s), %d cone cell(s) -> %s\n", GetSize(m.group),
			          GetSize(m.cone), log_signal(m.outs));
			if (rewrite_fn(m, proofs))
				return true;
		}
		return false;
	}

	// Marks a cell this pass emitted. The tree it builds is itself a residue of
	// the same terms, so without this the next round matches the pass's own
	// output and stacks a second tree on top of the first.
	static IdString emitted_attr() { return IdString("\\modred_emitted"); }

	// Marks the cell driving what a rewrite handed back, as opposed to the tree
	// behind it. Only the handed-back signal is worth looking at again: a
	// function match over a top-level fold has to see the halves already
	// rewritten, while the levels inside a tree are already the form this pass
	// emits, so proving them can only cost.
	static IdString emitted_out_attr() { return IdString("\\modred_out"); }

	bool driver_has(const SigSpec &sig, IdString attr)
	{
		for (auto bit : sig) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr && drv->has_attribute(attr))
				return true;
		}
		return false;
	}

	// Call once the rewrite's result is connected and the indexes are rebuilt.
	void mark_emitted_out(const SigSpec &sig)
	{
		for (auto bit : sigmap(sig))
			if (Cell *drv = bit_to_driver.at(bit, nullptr))
				drv->set_bool_attribute(emitted_out_attr());
	}

	void run()
	{
		pool<Cell *> before;
		for (auto c : module->cells())
			before.insert(c);

		run_once();

		for (auto c : module->cells())
			if (!before.count(c))
				c->set_bool_attribute(emitted_attr());
	}

	void run_once()
	{
		auto width_ok = [&](int w) { return w >= min_mod_bits && w <= max_mod_bits; };
		auto interesting = [&](const pool<Cell *> &cells) { return GetSize(cells) >= 4; };
		// Seeds of any width: a residue is narrow, but it is usually consumed bit
		// by bit into control logic, so the flop that anchors its cone is often a
		// single bit and would filter itself out.
		auto any_width = [&](int) { return true; };
		auto roots = collect_root_candidates(width_ok, interesting, true, max_region_cells,
		                                     max_region_leaves, max_internal_roots, any_width);
		// Named wires first. A vectorizing frontend packs the bits of several
		// unrelated k-bit results into one cell port in whatever order suited
		// it, and each of those orders is a separate root that costs a full
		// exhaustive sweep to reject -- enough of them to spend the whole walk
		// budget before the residue the RTL actually named is ever reached.
		std::stable_sort(roots.begin(), roots.end(),
		                 [](const RootCand &a, const RootCand &b) {
			                 return a.whole_wire && !b.whole_wire;
		                 });
		// Ahead of all of them: a divider root costs no sweep to prove, so it
		// should not be the candidate the walk budget ran out before reaching.
		if (div_cells) {
			vector<RootCand> div_roots;
			collect_div_roots(div_roots);
			roots.insert(roots.begin(), div_roots.begin(), div_roots.end());
		}
		log_debug("opt_modred: %d root candidate(s) in %s\n", GetSize(roots), log_id(module));
		for (auto &r : roots)
			log_debug("  root %s = %s\n", r.name.c_str(), log_signal(r.sig));

		// Prove first, rewrite widest-first: a reduction tree proves at every
		// level, and only the topmost one is worth rewriting.
		vector<std::pair<int, SigSpec>> cands;
		dict<SigSpec, Proof> proofs;
		// What a rewrite handed back is still a residue, and the logic *above*
		// it has not been touched. Proving it anyway is what lets a function
		// match see both halves of a top-level fold at once, since the two
		// halves are rewritten in different rounds. Only the plain re-emit has
		// to skip these, or it stacks a tree on its own output.
		pool<SigSpec> done;
		int skipped = 0;
		for (auto &root : roots) {
			if (walk_exhausted() || eval_exhausted()) {
				skipped++;
				continue;
			}
			SigSpec sig = sigmap(root.sig);
			pool<SigBit> uniq;
			// A root that repeats a bit is a residue only vacuously (x + 2x is
			// 0 mod 3), and proving it wastes the budget the real roots need.
			if (proofs.count(sig) || !sig_fully_driven(sig) || !sig_bits_unique(sig, uniq))
				continue;
			if (driver_has(sig, emitted_attr())) {
				// A level inside a tree this pass emitted. It proves,
				// but the proof can only ever re-emit the same tree,
				// and a module with several of them offers hundreds of
				// these -- each one a cone, a cut and a sweep, and
				// enough of them to cost more than the real roots do.
				if (!driver_has(sig, emitted_out_attr()))
					continue;
				done.insert(sig);
			}
			k = GetSize(sig);
			mod_c = (1 << k) - 1;
			// The memo carries over between roots: k is fixed by the root's
			// own width, and nothing is rewritten until all of them are
			// proven. A tree's levels are each a root and each other's cut
			// slots, so nearly every proof here is one already done.
			Proof pf;
			if (!prove(sig, pf, 0)) {
				log_debug("  no mod-%d proof for %s\n", mod_c, log_signal(sig));
				continue;
			}
			if (GetSize(pf.weights) < min_terms)
				continue;
			log_debug("  proved %s as mod-%d over %d bit(s)\n", log_signal(sig), mod_c,
			          GetSize(pf.weights));
			proofs[sig] = pf;
			cands.push_back({GetSize(pf.weights), sig});
		}
		// Stable: the comparator only ranks width, and most candidates tie, so
		// an unstable sort would pick a different seed on a different standard
		// library. The order it falls back on is the root order, which is the
		// module's own cell and wire order.
		std::stable_sort(cands.begin(), cands.end(),
		                 [](const std::pair<int, SigSpec> &a,
		                    const std::pair<int, SigSpec> &b) { return a.first > b.first; });

		// Sinking a shift out from under the leaves first: it leaves the reduction
		// itself alone, so whatever the other rewrites would have done to it they
		// can still do on the next round, now over a shallower producer.
		if (sink_shift_en)
			for (auto &c : cands) {
				if (root_claimed(c.second))
					continue;
				k = GetSize(c.second);
				mod_c = (1 << k) - 1;
				if (sink_shift(c.second, proofs.at(c.second)))
					return;  // the rewrite moved a producer, so re-index
			}

		// The logic above a reduction tree first: its terms reach the furthest
		// back, and it subsumes every residue underneath it.
		if (fit_fn && rewrite_widest_fn(cands, proofs, done))
			return;

		for (auto &c : cands) {
			if (root_claimed(c.second) || done.count(c.second))
				continue;
			k = GetSize(c.second);
			mod_c = (1 << k) - 1;
			if (rewrite(c.second, proofs.at(c.second)))
				break;  // the push mutates producers, so re-index before the next one
		}
		note_budget("opt_modred", skipped);
	}
};

struct OptModRedPass : public Pass {
	OptModRedPass() : Pass("opt_modred", "mod-(2^k-1) reductions to carry-save trees") {}

	// A submodule that compresses one wide combinational port down to a few bits,
	// fed by a variable shift the parent owns, is a reduction whose shift the sink
	// could move -- except the two sit on opposite sides of a port, and the pass
	// works a module at a time. Inline just those instances. Flattening the design
	// instead would reach the same reductions, but at the cost of every other
	// hierarchy the rest of the flow still wants.
	int inline_sink_submodules(RTLIL::Design *design, int min_sink_gain,
	                           std::function<void(OptModRedWorker &)> configure)
	{
		vector<std::pair<RTLIL::Module *, RTLIL::Cell *>> victims;
		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			// The parent's own worker, so the shifts admitted here are exactly the
			// ones its sink will match -- a looser filter flattens for nothing, and
			// the flatten is not undone. It also answers the level queries below.
			OptModRedWorker parent(module);
			configure(parent);
			SigMap &sigmap = parent.sigmap;

			// Bits each shift candidate drives, and every bit the module reads.
			dict<SigBit, RTLIL::Cell *> shifted;
			for (auto cell : module->cells()) {
				if (!cell->hasPort(ID::Y) || !parent.is_sink_shift(cell))
					continue;
				SigSpec y = sigmap(cell->getPort(ID::Y));
				if (GetSize(y) != GetSize(sigmap(cell->getPort(ID::A))))
					continue;
				for (auto bit : y)
					if (bit.wire != nullptr)
						shifted[bit] = cell;
			}
			if (shifted.empty())
				continue;

			// A shift qualifies only if one submodule port reads all of it and
			// nothing else does, so inlining is what puts the two in one module.
			dict<RTLIL::Cell *, pool<RTLIL::Cell *>> readers;
			pool<RTLIL::Cell *> shared;
			for (auto cell : module->cells())
				for (auto &conn : cell->connections()) {
					if (cell->output(conn.first))
						continue;
					for (auto bit : sigmap(conn.second)) {
						auto it = shifted.find(bit);
						if (it == shifted.end())
							continue;
						readers[it->second].insert(cell);
					}
				}
			for (auto w : module->wires())
				if (w->port_output || w->get_bool_attribute(ID::keep))
					for (auto bit : sigmap(SigSpec(w)))
						if (shifted.count(bit))
							shared.insert(shifted.at(bit));

			for (auto &it : readers) {
				if (shared.count(it.first) || GetSize(it.second) != 1)
					continue;
				RTLIL::Cell *sink = *it.second.begin();
				RTLIL::Module *sub = design->module(sink->type);
				if (sub == nullptr || sub->get_blackbox_attribute() ||
				    sub->has_processes_warn())
					continue;
				// Combinational, and narrow out of a wide port that divides
				// evenly into digits: what a group reduction looks like from
				// outside. Anything else is not worth flattening for.
				bool seq = false;
				for (auto c : sub->cells())
					if (StaticCellTypes::categories.is_ff(c->type) ||
					    c->type.in(ID($mem), ID($mem_v2), ID($memrd), ID($memwr)))
						seq = true;
				if (seq)
					continue;
				// Which port takes the shift whole, in order: only then does
				// bit i inside the child mean bit i of the shifted word.
				SigSpec y = sigmap(it.first->getPort(ID::Y));
				RTLIL::Wire *port = nullptr;
				for (auto &conn : sink->connections())
					if (!sink->output(conn.first) && sigmap(conn.second) == y)
						port = sub->wire(conn.first);
				if (port == nullptr || GetSize(port) != GetSize(y))
					continue;

				// Ask the child at what group width its reduction reads that
				// port. This is the sink's own match run across the port, so a
				// module answering 0 is one the sink would decline anyway --
				// which is the whole reason not to inline it.
				OptModRedWorker child(sub);
				configure(child);
				int g = child.port_group_width(SigSpec(port));
				if (g == 0)
					continue;

				// With g known the gain model of sink_shift applies exactly: the
				// barrel's selb levels become a g-way shift plus a mask, but the
				// amount now pays a 2^selb table, so the sink only pays when the
				// data is the late input by more than that table costs.
				int alevel = 0, blevel = 0, selb = GetSize(sigmap(it.first->getPort(ID::B)));
				int wb = std::max(1, clog2_int(g));
				for (auto bit : sigmap(it.first->getPort(ID::A)))
					alevel = std::max(alevel, parent.bit_level(bit));
				for (auto bit : sigmap(it.first->getPort(ID::B)))
					blevel = std::max(blevel, parent.bit_level(bit));
				int before = std::max(alevel, blevel) + selb;
				int after = std::max(blevel + selb, alevel + wb) + 1;
				if (selb - wb - 1 < min_sink_gain || before - after < min_sink_gain) {
					log_debug("  inline %s: group %d, depth %d -> %d, declined\n",
					          log_id(sink), g, before, after);
					continue;
				}
				log_debug("  inline %s: group %d, depth %d -> %d\n", log_id(sink), g,
				          before, after);
				victims.emplace_back(module, sink);
			}
		}

		for (auto &v : victims) {
			log_debug("opt_modred: inlining %s in %s to reach the shift feeding it\n",
			          log_id(v.second->name), log_id(v.first->name));
			RTLIL::Selection sel(false);
			sel.select(v.first, v.second);
			design->push_selection(sel);
			Pass::call(design, "flatten -noscopeinfo");
			design->pop_selection();
		}
		return GetSize(victims);
	}

	void help() override
	{
		log("\n");
		log("    opt_modred [options] [selection]\n");
		log("\n");
		log("Re-emit reductions modulo a Mersenne number C = 2^k-1 as an end-around-carry\n");
		log("carry-save tree, and push the reduction back through the arithmetic feeding it.\n");
		log("\n");
		log("Because 2^k == 1 (mod C), doubling a residue is a free rotate, so a full adder\n");
		log("is already a mod-C compressor: three residues become two in one FA level, with\n");
		log("no reduction step and no normalization. That is both shallower and smaller than\n");
		log("the tree of k-bit mod-C adders the RTL spells out.\n");
		log("\n");
		log("res_C is also a ring homomorphism, so it commutes with its input's producers:\n");
		log("mux distributes, (a+b) mod 2^n costs one carry-out correction, and x >> s is a\n");
		log("rotate of the reduction of x with its low bits masked off. Pushing through the\n");
		log("add is the point: it takes the carry-propagate adder off the reduction's path.\n");
		log("\n");
		log("Candidate reductions are cut out of the netlist and proven exhaustively over the\n");
		log("cut with ConstEval, so no spelling is assumed and no don't-care is relied on.\n");
		log("\n");
		log("A proof whose terms cannot sum past C is left alone: nothing wraps there, so the\n");
		log("node is a plain weighted sum -- an n-input popcount proves as mod-(2^n-1) this\n");
		log("way -- and it has no reduction to take off the path.\n");
		log("\n");
		log("    -min-mod-bits N, -max-mod-bits N\n");
		log("        modulus width k to consider, in 1..30 (default 2 to 6).\n");
		log("\n");
		log("    -max-cut-bits N\n");
		log("        largest cut to verify exhaustively, in bits (default 14).\n");
		log("\n");
		log("    -min-terms N, -max-terms N\n");
		log("        reduction width, in k-bit residues, worth rewriting (default 4 to 512).\n");
		log("\n");
		log("    -max-push-depth N\n");
		log("        how far to push the reduction through producers (default 6).\n");
		log("\n");
		log("    -min-push-add-width N\n");
		log("        narrowest adder worth taking off the path (default 8).\n");
		log("\n");
		log("    -max-bits-eval-cells N\n");
		log("        largest cone to fall back to bit-at-a-time evaluation on, in cells\n");
		log("        (default 256). A vectorizing frontend leaves wide cells that each\n");
		log("        need a bit of the other's output: acyclic per bit, deadlocked per\n");
		log("        cell, which is all ConstEval can see. 0 disables the fallback.\n");
		log("\n");
		log("    -no-push\n");
		log("        only re-emit the tree; do not touch the producers.\n");
		log("\n");
		log("    -push-shift-sub\n");
		log("        take a dynamic shift as res(x) - res(x & mask(s)) rather than\n");
		log("        res(x & ~mask(s)). Costs a second tree and a complement, and buys\n");
		log("        a push into x's producer, which only pays when that producer's\n");
		log("        operands are shallower than the producer itself.\n");
		log("\n");
		log("    -opaque-digits\n");
		log("        let a cut slot that is not itself a provable reduction still ride\n");
		log("        into the tree as one digit, when its own cone is swept and shown\n");
		log("        never to reach 2^k-1. That is what a leaf of a const-table fold is:\n");
		log("        a field map answering 0..C-1 only, so the mod-C adds stacked above\n");
		log("        it are a real reduction even though the leaf is not. Without this\n");
		log("        the leaf's full k-bit domain includes the 2^k-1 the table sends to\n");
		log("        zero, every level reads as non-linear, and the tree is not matched.\n");
		log("\n");
		log("    -max-bound-bits N\n");
		log("        largest cone the -opaque-digits sweep will bound, in leaf bits\n");
		log("        (default 12).\n");
		log("\n");
		log("    -max-bound-cells N\n");
		log("        cells a digit's bound may pull in looking for a cut narrow enough\n");
		log("        to sweep (default 256). A digit reading one field of a lowered\n");
		log("        barrel has no cut until its own table is inside the cone, which is\n");
		log("        deeper than the first cut that fits.\n");
		log("\n");
		log("    -sink-shift\n");
		log("        move a variable right shift out from under a matched reduction\n");
		log("        whose leaves read fixed, equal-width groups of the shifted word:\n");
		log("          F(x >> (g*u + w))  ===>  F((x >> w) & keep_u)\n");
		log("        where g is the leaf group width and keep_u clears the u low\n");
		log("        groups. A shift by g*u moves whole groups, and a reduction that\n");
		log("        weights every leaf alike does not care which leaf sees which\n");
		log("        group, so both spellings hand F the same multiset of groups. Only\n");
		log("        the g-way shift and the mask are left on the data path; the two\n");
		log("        tables read the amount alone, so an amount arriving before the\n");
		log("        data takes the whole barrel off the path. Unlike the -push rules\n");
		log("        this needs no canonical residue at the shift, which is what lets\n");
		log("        it reach a barrel below -opaque-digits leaves. Requires every\n");
		log("        leaf to compute one function (checked over all 2^g inputs) and\n");
		log("        the reduction to be the only reader of the shift.\n");
		log("\n");
		log("    -max-sink-group-bits N\n");
		log("        widest leaf group -sink-shift will take (default 10). The leaf\n");
		log("        identity check sweeps 2^N vectors per leaf.\n");
		log("\n");
		log("    -min-sink-gain N\n");
		log("        levels -sink-shift has to save to fire (default 2), counted as\n");
		log("        the amount's width less the g-way shift's and the mask's.\n");
		log("\n");
		log("    -div-cells\n");
		log("        also match a bare `A %% C` cell, and count the divider class at\n");
		log("        its true depth when weighing a rewrite. `$mod` by a constant\n");
		log("        C = 2^k-1 needs no sweep -- bit i of A is worth 2^(i mod k) by\n");
		log("        construction -- but the exhaustive prover never reaches it, since\n");
		log("        its only cut is the whole operand. Off by default: it rewrites a\n");
		log("        cell the rest of the flow may still be relying on.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MODRED pass (mod-(2^k-1) reductions to carry-save "
		                   "trees).\n");
		int min_mod_bits = 2, max_mod_bits = 6, max_cut_bits = 14;
		int min_terms = 4, max_terms = 512, max_push_depth = 6, min_push_add_width = 8;
		int max_bits_eval_cells = 256, max_bound_bits = 12, max_bound_cells = 256;
		int max_sink_group_bits = 10, min_sink_gain = 2;
		bool push_shift_sub = false, opaque_digits = false, div_cells = false;
		bool sink_shift_en = false;

		// 2^k-1 lives in an int all through the prover, and the residue table is
		// 2^k entries long, so a wider modulus has neither a representable value
		// to reduce against nor a table that fits in memory.
		const int mod_bits_limit = 30;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if ((args[argidx] == "-min-mod-bits" || args[argidx] == "-min_mod_bits") &&
			    argidx + 1 < args.size()) {
				min_mod_bits = std::stoi(args[++argidx]);
				// A 0-bit modulus would be 2^0-1 == 0, and every weight is taken
				// mod that.
				if (min_mod_bits < 1 || min_mod_bits > mod_bits_limit)
					log_cmd_error("-min-mod-bits must be in 1..%d\n", mod_bits_limit);
				continue;
			}
			if ((args[argidx] == "-max-mod-bits" || args[argidx] == "-max_mod_bits") &&
			    argidx + 1 < args.size()) {
				max_mod_bits = std::stoi(args[++argidx]);
				if (max_mod_bits < 1 || max_mod_bits > mod_bits_limit)
					log_cmd_error("-max-mod-bits must be in 1..%d\n", mod_bits_limit);
				continue;
			}
			if ((args[argidx] == "-max-cut-bits" || args[argidx] == "-max_cut_bits") &&
			    argidx + 1 < args.size()) {
				max_cut_bits = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-min-terms" || args[argidx] == "-min_terms") &&
			    argidx + 1 < args.size()) {
				min_terms = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-terms" || args[argidx] == "-max_terms") &&
			    argidx + 1 < args.size()) {
				max_terms = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-push-depth" || args[argidx] == "-max_push_depth") &&
			    argidx + 1 < args.size()) {
				max_push_depth = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-min-push-add-width" ||
			     args[argidx] == "-min_push_add_width") &&
			    argidx + 1 < args.size()) {
				min_push_add_width = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-bits-eval-cells" ||
			     args[argidx] == "-max_bits_eval_cells") &&
			    argidx + 1 < args.size()) {
				max_bits_eval_cells = std::stoi(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-no-push") {
				max_push_depth = 0;
				continue;
			}
			if (args[argidx] == "-push-shift-sub") {
				push_shift_sub = true;
				continue;
			}
			if (args[argidx] == "-div-cells" || args[argidx] == "-div_cells") {
				div_cells = true;
				continue;
			}
			if (args[argidx] == "-sink-shift" || args[argidx] == "-sink_shift") {
				sink_shift_en = true;
				continue;
			}
			if ((args[argidx] == "-max-sink-group-bits" ||
			     args[argidx] == "-max_sink_group_bits") &&
			    argidx + 1 < args.size()) {
				max_sink_group_bits = std::stoi(args[++argidx]);
				// The leaf-identity sweep indexes a 2^N table with an int.
				if (max_sink_group_bits < 1 || max_sink_group_bits > 20)
					log_cmd_error("-max-sink-group-bits must be in 1..20\n");
				continue;
			}
			if ((args[argidx] == "-min-sink-gain" || args[argidx] == "-min_sink_gain") &&
			    argidx + 1 < args.size()) {
				min_sink_gain = std::stoi(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-opaque-digits" || args[argidx] == "-opaque_digits") {
				opaque_digits = true;
				continue;
			}
			if ((args[argidx] == "-max-bound-bits" || args[argidx] == "-max_bound_bits") &&
			    argidx + 1 < args.size()) {
				max_bound_bits = std::stoi(args[++argidx]);
				// The sweep counts combinations in an int64_t, so a wider cone
				// than that has no representable iteration count.
				if (max_bound_bits < 0 || max_bound_bits > 62)
					log_cmd_error("-max-bound-bits must be in 0..62\n");
				continue;
			}
			if ((args[argidx] == "-max-bound-cells" || args[argidx] == "-max_bound_cells") &&
			    argidx + 1 < args.size()) {
				max_bound_cells = std::stoi(args[++argidx]);
				if (max_bound_cells < 0)
					log_cmd_error("-max-bound-cells must not be negative\n");
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0, total_cells = 0, total_adds = 0, total_muxes = 0, total_shifts = 0;
		int total_norms = 0, total_concats = 0, total_sunk = 0, total_inlined = 0;
		if (sink_shift_en)
			total_inlined = inline_sink_submodules(
			    design, min_sink_gain,
			    [&](OptModRedWorker &w) {
				    w.min_mod_bits = min_mod_bits;
				    w.max_mod_bits = max_mod_bits;
				    w.max_cut_bits = max_cut_bits;
				    w.min_terms = min_terms;
				    w.max_terms = max_terms;
				    w.max_bits_eval_cells = max_bits_eval_cells;
				    w.max_bound_bits = max_bound_bits;
				    w.max_bound_cells = max_bound_cells;
				    w.opaque_digits = opaque_digits;
				    w.max_sink_group_bits = max_sink_group_bits;
			    });
		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			// The push rewires producers, so the worker's index is stale after a
			// rewrite; re-index and look again until the module settles.
			for (int round = 0; round < 8; round++) {
				OptModRedWorker worker(module);
				worker.min_mod_bits = min_mod_bits;
				worker.max_mod_bits = max_mod_bits;
				worker.max_cut_bits = max_cut_bits;
				worker.min_terms = min_terms;
				worker.max_terms = max_terms;
				worker.max_push_depth = max_push_depth;
				worker.min_push_add_width = min_push_add_width;
				worker.push_shift_sub = push_shift_sub;
				worker.max_bits_eval_cells = max_bits_eval_cells;
				worker.max_bound_bits = max_bound_bits;
				worker.max_bound_cells = max_bound_cells;
				worker.opaque_digits = opaque_digits;
				worker.div_cells = div_cells;
				worker.sink_shift_en = sink_shift_en;
				worker.max_sink_group_bits = max_sink_group_bits;
				worker.min_sink_gain = min_sink_gain;
				worker.run();
				total_regions += worker.regions;
				total_sunk += worker.sunk_shifts;
				total_cells += worker.cells_added;
				total_adds += worker.pushed_adds;
				total_muxes += worker.pushed_muxes;
				total_shifts += worker.pushed_shifts;
				total_norms += worker.pushed_norms;
				total_concats += worker.pushed_concats;
				if (worker.regions == 0 && worker.sunk_shifts == 0)
					break;
			}
		}

		log("Rewrote %d mod-(2^k-1) reduction(s) as carry-save tree(s); pushed through %d "
		    "add(s), %d mux(es), %d shift(s), %d normalizer(s), %d concat(s); inlined %d "
		    "submodule(s) and sank %d shift(s) under a reduction; emitted %d new cell(s).\n",
		    total_regions, total_adds, total_muxes, total_shifts, total_norms, total_concats,
		    total_inlined, total_sunk, total_cells);
		if (total_regions > 0 || total_sunk > 0)
			Yosys::run_pass("clean -purge");
	}
} OptModRedPass;

PRIVATE_NAMESPACE_END
