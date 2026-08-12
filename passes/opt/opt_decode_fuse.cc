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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/rewrite_utils.h"

// opt_decode_fuse: collapse an encode/decode round trip on a narrow code.
//
// RTL that classifies a format/mode code usually re-encodes it at every stage,
// then decodes it again at the next one:
//
//     always @* case (fmt_q)                          // remap a few codes
//                7'd0: fmt_m = tbl0[smp_sel];         //   -> 0, 32, 33, 34
//                7'd1: fmt_m = tbl1[smp_sel];         //   -> 1, 35, 36, 37
//                default: fmt_m = fmt_q;
//              endcase
//     wire [6:0] fmt_e = edge_q ? 7'd62 : fmt_m;      // override
//     wire [6:0] fmt_c = (fmt_e == 7'd25) ? 7'd2 : fmt_e;
//     always @* if (buf_q || fmt_c == 7'd0 || fmt_c == 7'd32 || ...) cls = 3'd0;
//               else if (...) cls = 3'd1; ...         // classify
//     wire [2:0] sy = (cls == 3'd0) ? 3'd3 : ...;     // and use the class
//
// The classifier cannot start until the select network above it has produced a
// code, so the decode sits in series with the network even though every value
// the network can produce is known at compile time. What the classification then
// picks is usually something the datapath wants early -- here a shift amount
// ahead of a 40-bit adder -- which puts the whole round trip in front of it.
//
// Pushing the test down to the network's leaves fixes that. The unit that gets
// pushed is a *membership test*, not one equality: a class is a set of codes, and
// it is the set that collapses. Under `fmt_q == 0` above, all four codes the
// sample select can produce are in class 0, so the whole smp_sel subtree folds to
// 1 -- while `fmt_c == 32` on its own would keep every level of it. What survives
// is a decode of the leaves alone.
//
// Soundness is structural: mux(s, a, b) in S is exactly mux(s, a in S, b in S),
// and the same holds slice-wise for $pmux, so this is a re-bracketing of the same
// function. No don't-care freedom is involved and the rewrite survives a
// node-matching equivalence check, so unlike the ODC passes it needs no -strict.
//
// Three conditions make it a win rather than duplicated logic:
//
//   1. The code must die. Every live reader of the network output has to be one
//      of these constant compares. A code that also feeds the datapath keeps its
//      wide network, and the push would only add the 1-bit copies next to it.
//
//   2. The fold must pay for itself. Along any single path the push is depth
//      neutral -- leaf, network, test becomes leaf, test, network -- so all of the
//      win comes from levels that fold away, and a push that folds nothing just
//      buys a copy of the network per test. The group is therefore costed before
//      anything is touched, in combinational levels from start points, over the
//      shape the emit would really build.
//
//   3. It must not grow the design. The 1-bit cells the push emits have to fit in
//      the bit count of the network and wide compares it deletes. Cell counts do
//      still rise -- many 1-bit cells replacing a few wide ones -- while bit
//      counts fall, which is the trade this pass exists to make.
//
// Eligibility has to be recomputed after each batch: a stage's own select is
// often a compare on the stage below it (`fmt_e == 25` above), and that compare
// is only the last reader of that stage once the stage above it is gone.

// dict::at(key, defval) hands back a reference to defval, and a range-for does
// not extend that temporary's lifetime before C++23, so the empty fallback for a
// reader lookup has to outlive the loop that walks it.
static const pool<Cell *> no_readers;

// Cells that test a value against a constant. opt_expr has usually rewritten the
// tests against 0 and ~0 into reductions by the time this pass runs, and those
// are the same test: $logic_not is "== 0", $reduce_bool/$reduce_or is "!= 0",
// $reduce_and is "== ~0".
static bool is_cmp_type(Cell *c)
{
	return c->type.in(ID($eq), ID($ne), ID($logic_not), ID($reduce_bool),
	                  ID($reduce_or), ID($reduce_and));
}

// Cells that OR their inputs together, which is how a set of codes is spelled.
static bool is_or_type(Cell *c)
{
	return c->type.in(ID($or), ID($logic_or), ID($reduce_or), ID($reduce_bool));
}

struct OptDecodeFuseWorker
{
	Module *module;
	SigMap sigmap;

	// Indexed over every cell, not just the selected ones: the "code must die"
	// test is only sound with a complete view of the readers.
	dict<SigBit, Cell *> drivers;
	dict<SigBit, pool<Cell *>> readers;
	pool<SigBit> output_port_bits;

	// Cells the rewrite orphaned. They stay in the netlist until clean -purge
	// collects them, so reader tests have to skip them explicitly.
	pool<Cell *> dead;

	// Tunables (see Pass::execute).
	int max_nodes = 64;
	int max_depth = 16;
	int max_var_leaves = 4;
	int max_emit_cells = 512;
	int max_rounds = 8;

	int regions = 0;
	int tests_pushed = 0;
	int cells_added = 0;

	OptDecodeFuseWorker(Module *module) : module(module), sigmap(module) { }

	void index()
	{
		drivers.clear();
		readers.clear();
		levels_of.clear();
		active.clear();
		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				bool is_out = cell->output(conn.first);
				for (auto bit : sigmap(conn.second))
					if (bit.wire) {
						if (is_out)
							drivers[bit] = cell;
						else
							readers[bit].insert(cell);
					}
			}

		output_port_bits.clear();
		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(SigSpec(wire)))
					if (bit.wire)
						output_port_bits.insert(bit);
	}

	// Live readers of a bit: the husks left by an earlier rewrite are still in
	// the netlist but no longer observe anything.
	vector<Cell *> live_readers(SigBit bit)
	{
		vector<Cell *> out;
		for (auto rd : readers.at(sigmap(bit), no_readers))
			if (!dead.count(rd))
				out.push_back(rd);
		std::sort(out.begin(), out.end(), RTLIL::sort_by_name_id<Cell>());
		return out;
	}

	// --------------------------------------------------------------- levels

	// Combinational level of a bit, counted back from start points: port inputs,
	// register outputs, undriven bits. This is the unit the depth comparison is
	// made in, so a leaf sitting behind logic gets costed by it rather than
	// refused.
	//
	// Walked on demand instead of relaxed over the whole module, because only the
	// cone the costing reaches is ever needed -- and a module holding no decode
	// network reaches none of it. Two-phase explicit stack (expand, then
	// finalize) as in opt_timing_balance, so a deep cone cannot overflow the C++
	// stack. A bit reached through itself is a combinational loop and counts 0,
	// which understates a depth the profit test then refuses anyway.
	dict<SigBit, int> levels_of;
	pool<SigBit> active;

	int level(SigBit bit)
	{
		SigBit start = sigmap(bit);
		vector<pair<SigBit, bool>> stack = {{start, false}};
		while (!stack.empty()) {
			auto [b, finalize] = stack.back();
			stack.pop_back();
			if (!b.wire || levels_of.count(b))
				continue;
			Cell *drv = drivers.at(b, nullptr);
			if (drv == nullptr || is_sequential(drv)) {
				levels_of[b] = 0;
				continue;
			}
			if (!finalize) {
				// Already expanded further down the path: its finalize entry is
				// still below us and will set the level.
				if (!active.insert(b).second)
					continue;
				stack.push_back({b, true});
				for (auto &conn : drv->connections())
					if (!drv->output(conn.first))
						for (auto in : sigmap(conn.second))
							if (in.wire && !levels_of.count(in) && !active.count(in))
								stack.push_back({in, false});
				continue;
			}
			int depth = 0;
			for (auto &conn : drv->connections())
				if (!drv->output(conn.first))
					for (auto in : sigmap(conn.second))
						depth = std::max(depth, levels_of.at(in, 0));
			levels_of[b] = depth + 1;
			active.erase(b);
		}
		return levels_of.at(start, 0);
	}

	int level(const SigSpec &v)
	{
		int depth = 0;
		for (auto bit : sigmap(v))
			depth = std::max(depth, level(bit));
		return depth;
	}

	// Levels a membership test costs: a bitwise compare per code feeding a
	// reduction, then an OR across the codes. Charged on both sides of the
	// comparison, so what it decides is where the test sits, not its size.
	int test_levels(int width, int codes)
	{
		return clog2_int(std::max(width, 1)) + 1 + clog2_int(std::max(codes, 1));
	}

	// ------------------------------------------------------------ detection

	// The select node producing all of `v` through its Y port. Anything else --
	// a partial driver, a slice of a wider mux, a non-select cell -- makes `v` a
	// leaf, which keeps the recursion below honest about what it can rebuild. A
	// $shiftx over a constant table is the same shape in RTL, but its windows
	// only line up with the table entries when the index is scaled by the entry
	// width, so it is left to peepopt's shiftpow2 rule to turn into a $bmux.
	Cell *net_node(const SigSpec &v)
	{
		if (v.empty() || !v[0].wire)
			return nullptr;
		Cell *drv = drivers.at(sigmap(v[0]), nullptr);
		if (drv == nullptr || !drv->type.in(ID($mux), ID($pmux), ID($bmux)) ||
		    dead.count(drv))
			return nullptr;
		if (drv->get_bool_attribute(ID::keep) || !module->design->selected(module, drv))
			return nullptr;
		return sigmap(drv->getPort(ID::Y)) == sigmap(v) ? drv : nullptr;
	}

	// Arms of a select node, in the order the emitted 1-bit copy has to keep:
	// every A slice for $bmux, otherwise A and then each B slice. A case over a
	// constant table survives to here as a $bmux, which is the shape that folds
	// hardest -- every arm is a constant, so the whole node can collapse. Empty
	// when the node carries more than `limit` arms, counted before they are
	// materialized: a $bmux holds 2**|S| of them.
	vector<SigSpec> node_arms(Cell *node, int limit = INT_MAX)
	{
		int w = std::max(GetSize(node->getPort(ID::Y)), 1);
		bool wide = node->type == ID($bmux);
		SigSpec slices = wide ? node->getPort(ID::A) : node->getPort(ID::B);
		if (GetSize(slices) / w + (wide ? 0 : 1) > limit)
			return {};
		vector<SigSpec> arms;
		if (!wide)
			arms.push_back(node->getPort(ID::A));
		for (int i = 0; i + w <= GetSize(slices); i += w)
			arms.push_back(slices.extract(i, w));
		return arms;
	}

	// A reader that tests the whole of `v` against one constant.
	bool is_const_cmp(Cell *c, const SigSpec &v, Const &k, bool &negate, bool &is_signed)
	{
		if (!is_cmp_type(c) || c->get_bool_attribute(ID::keep))
			return false;
		if (!module->design->selected(module, c))
			return false;
		is_signed = false;

		if (c->type.in(ID($logic_not), ID($reduce_bool), ID($reduce_or), ID($reduce_and))) {
			if (sigmap(c->getPort(ID::A)) != sigmap(v))
				return false;
			k = Const(c->type == ID($reduce_and) ? State::S1 : State::S0, GetSize(v));
			negate = c->type.in(ID($reduce_bool), ID($reduce_or));
			return true;
		}

		// Mixed signedness would need the compare's own extension rules
		// replayed at every leaf; the shapes this targets are all unsigned.
		if (c->getParam(ID::A_SIGNED).as_bool() != c->getParam(ID::B_SIGNED).as_bool())
			return false;
		SigSpec a = sigmap(c->getPort(ID::A)), b = sigmap(c->getPort(ID::B));
		if (a == sigmap(v) && b.is_fully_const())
			k = b.as_const();
		else if (b == sigmap(v) && a.is_fully_const())
			k = a.as_const();
		else
			return false;
		negate = c->type == ID($ne);
		is_signed = c->getParam(ID::A_SIGNED).as_bool();
		return true;
	}

	// (leaf in codes) for a fully defined constant leaf, else -1 (emit a test).
	int const_test(const SigSpec &leaf, const vector<pair<Const, bool>> &codes)
	{
		if (!leaf.is_fully_const() || !leaf.is_fully_def())
			return -1;
		for (auto &[k, is_signed] : codes) {
			if (!k.is_fully_def())
				return -1;
			SigSpec a = leaf, b = k;
			int w = std::max(GetSize(a), GetSize(b));
			a.extend_u0(w, is_signed);
			b.extend_u0(w, is_signed);
			if (a.as_const() == b.as_const())
				return 1;
		}
		return 0;
	}

	// ---------------------------------------------------------------- groups

	// One group of readers to replace together. A classifier tests membership in
	// a set of codes, and it is the set that folds: a select node whose arms all
	// land inside the set collapses, where each arm on its own would not. `kept`
	// carries the inputs of that OR which are not compares on this value -- a
	// bypass ORed in beside the decode -- and they stay where they are.
	struct Target {
		Cell *root = nullptr;    // cell whose output the pushed test replaces
		bool negate = false;     // test is "not in set"
		vector<Cell *> consumed; // compares and OR nodes that die with it
		SigSpec kept;            // OR inputs to keep beside the pushed test

		// Constants the value is tested against, each carrying the signedness of
		// the compare it came from. One flag for the set would not do: against a
		// wider constant an unsigned compare zero-extends where a signed one
		// sign-extends, so sharing a flag across a mixed OR tree would silently
		// change the tests it did not come from.
		vector<pair<Const, bool>> codes;
	};

	// Climb to the topmost OR cell that still only exists to combine `c`'s
	// result with others: one reader, and that reader is an OR.
	Cell *or_root(Cell *c)
	{
		while (true) {
			SigSpec y = c->getPort(ID::Y);
			if (GetSize(y) != 1)
				return c;
			vector<Cell *> rd = live_readers(y[0]);
			if (GetSize(rd) != 1 || !is_or_type(rd[0]) || dead.count(rd[0]))
				return c;
			if (output_port_bits.count(sigmap(y[0])))
				return c;
			c = rd[0];
		}
	}

	// Collect the OR tree under `root` into `t`: compare-on-`v` leaves become
	// codes, everything else is kept. Interior cells must have this tree as
	// their only reader, or they would survive the rewrite and be duplicated.
	bool grow_or_tree(Cell *root, const SigSpec &v, Target &t, pool<Cell *> &claimed)
	{
		vector<Cell *> queue = {root};
		for (int head = 0; head < GetSize(queue); head++) {
			Cell *c = queue[head];
			for (auto &conn : c->connections()) {
				if (c->output(conn.first))
					continue;
				for (auto bit : conn.second) {
					if (!bit.wire) {
						// A constant OR input decides the whole tree; leave
						// such degenerate shapes to opt_expr.
						if (bit != State::S0)
							return false;
						continue;
					}
					Cell *drv = drivers.at(sigmap(bit), nullptr);
					bool sole = drv != nullptr && !dead.count(drv) &&
					            GetSize(live_readers(bit)) == 1;
					Const k;
					bool negate = false, is_signed = false;
					if (sole && !claimed.count(drv) && is_or_type(drv) &&
					    GetSize(drv->getPort(ID::Y)) == 1) {
						queue.push_back(drv);
						t.consumed.push_back(drv);
						continue;
					}
					if (sole && !claimed.count(drv) &&
					    is_const_cmp(drv, v, k, negate, is_signed) && !negate) {
						t.codes.push_back({k, is_signed});
						t.consumed.push_back(drv);
						continue;
					}
					t.kept.append(bit);
				}
			}
		}
		if (t.codes.empty())
			return false;
		for (auto c : t.consumed)
			claimed.insert(c);
		claimed.insert(root);
		return true;
	}

	// Group every reader of `v` into tests to push. Fails when a reader is not a
	// constant compare at all, since then the code survives the rewrite.
	bool collect_targets(const SigSpec &v, vector<Target> &targets)
	{
		vector<Cell *> cmps;
		pool<Cell *> seen;
		for (auto bit : sigmap(v)) {
			if (output_port_bits.count(bit))
				return false;
			for (auto rd : live_readers(bit)) {
				if (!seen.insert(rd).second)
					continue;
				Const k;
				bool negate = false, is_signed = false;
				if (!is_const_cmp(rd, v, k, negate, is_signed))
					return false;
				cmps.push_back(rd);
			}
		}
		std::sort(cmps.begin(), cmps.end(), RTLIL::sort_by_name_id<Cell>());

		pool<Cell *> claimed;
		for (auto cmp : cmps) {
			if (claimed.count(cmp))
				continue;
			Target t;
			t.root = or_root(cmp);
			if (t.root != cmp && grow_or_tree(t.root, v, t, claimed)) {
				targets.push_back(t);
				continue;
			}
			// Not part of an OR of codes: push this one compare on its own.
			Target one;
			one.root = cmp;
			Const k;
			bool negate = false, is_signed = false;
			is_const_cmp(cmp, v, k, negate, is_signed);
			one.codes.push_back({k, is_signed});
			one.negate = negate;
			claimed.insert(cmp);
			targets.push_back(one);
		}
		for (auto &t : targets)
			log_debug("    target %s (%s): %d code(s), %d kept, %d consumed\n",
			          log_id(t.root), log_id(t.root->type), GetSize(t.codes),
			          GetSize(t.kept), GetSize(t.consumed));
		return !targets.empty();
	}

	// ------------------------------------------------------------- planning

	// Shape of the network under one candidate, measured once per candidate.
	// Memoized by signal, so a subtree feeding two arms is one node and one leaf
	// -- which is what the cost model has to charge for, since deleting the
	// network deletes each cell once.
	dict<SigSpec, int> plan_memo;
	int plan_nodes = 0, plan_consts = 0, plan_vars = 0;
	const char *plan_fail = nullptr;

	// Level `v` arrives at today: leaves at their own level, each select node one
	// above the later of its arms and its select. False when a budget is hit, so
	// the emit below can never run out of budget half way through a network.
	bool plan(const SigSpec &v, int depth, int &levels)
	{
		auto it = plan_memo.find(v);
		if (it != plan_memo.end()) {
			levels = it->second;
			return true;
		}

		Cell *node = net_node(v);
		if (node == nullptr) {
			levels = level(v);
			if (v.is_fully_const())
				plan_consts++;
			else if (++plan_vars > max_var_leaves) {
				plan_fail = "more value leaves than -max-var-leaves allows";
				return false;
			}
		} else {
			if (depth >= max_depth) {
				plan_fail = "network deeper than -max-depth";
				return false;
			}
			if (++plan_nodes > max_nodes) {
				plan_fail = "more select nodes than -max-nodes allows";
				return false;
			}
			// A $bmux is 2**|S| arms wide, so its arm count is what bounds the
			// walk rather than the node count.
			vector<SigSpec> arms = node_arms(node, max_nodes);
			if (arms.empty()) {
				plan_fail = "select node with more arms than -max-nodes allows";
				return false;
			}
			levels = level(node->getPort(ID::S));
			for (auto &arm : arms) {
				int sub = 0;
				if (!plan(arm, depth + 1, sub))
					return false;
				levels = std::max(levels, sub);
			}
			levels++;
		}
		plan_memo[v] = levels;
		return true;
	}

	// ------------------------------------------------------------- costing

	// What push() would produce for one test, without touching the netlist:
	// `id` identifies a pushed value (S0, S1, or a distinct piece of logic) so
	// the fold test here is exactly the one push() applies, and `depth` is the
	// level count that survives folding.
	struct Est {
		int id, depth;
	};
	static const int ID_S0 = -2, ID_S1 = -1;

	dict<SigSpec, Est> est_memo;
	int est_next_id = 0, est_sel_cells = 0, est_test_bits = 0;

	Est estimate(const SigSpec &v, const Target &t)
	{
		auto it = est_memo.find(v);
		if (it != est_memo.end())
			return it->second;

		Est r;
		Cell *node = net_node(v);
		if (node == nullptr) {
			int folded = const_test(v, t.codes);
			if (folded >= 0)
				r = Est{folded ? ID_S1 : ID_S0, 0};
			else {
				int width = GetSize(v);
				for (auto &code : t.codes)
					width = std::max(width, GetSize(code.first));
				est_test_bits += width * GetSize(t.codes);
				r = Est{est_next_id++,
				        level(v) + test_levels(width, GetSize(t.codes))};
			}
		} else {
			vector<Est> arms;
			int depth = level(node->getPort(ID::S));
			for (auto &arm : node_arms(node)) {
				arms.push_back(estimate(arm, t));
				depth = std::max(depth, arms.back().depth);
			}
			bool uniform = true;
			for (auto &a : arms)
				uniform &= a.id == arms[0].id;
			if (uniform)
				r = arms[0];
			else {
				est_sel_cells++;
				r = Est{est_next_id++, depth + 1};
			}
		}
		est_memo[v] = r;
		return r;
	}

	// ----------------------------------------------------------------- emit

	// Memo for one test's push, so identical subtrees share a cell and the
	// folding matches what estimate() costed.
	dict<SigSpec, SigBit> push_memo;

	// (v in t.codes), rebuilt at the leaves. Constant leaves fold to a constant,
	// and a node whose arms all agree folds with them -- that collapse is where
	// the depth the pass is after comes from.
	SigBit push(const SigSpec &v, const Target &t, Cell *anchor)
	{
		auto it = push_memo.find(v);
		if (it != push_memo.end())
			return it->second;

		SigBit r;
		Cell *node = net_node(v);
		if (node == nullptr) {
			int folded = const_test(v, t.codes);
			if (folded >= 0)
				r = folded ? State::S1 : State::S0;
			else
				r = emit_test(v, t, anchor);
		} else {
			SigSpec arms;
			for (auto &arm : node_arms(node))
				arms.append(push(arm, t, anchor));

			bool uniform = true;
			for (auto bit : arms)
				uniform &= bit == arms[0];
			if (uniform)
				r = arms[0];
			else {
				Cell *cell = node;
				cells_added++;
				if (node->type == ID($bmux))
					r = module->Bmux(NEW_ID2_SUFFIX("decode_fuse_sel"), arms,
					                 node->getPort(ID::S), cell_src(node))[0];
				else if (node->type == ID($mux))
					r = module->Mux(NEW_ID2_SUFFIX("decode_fuse_sel"), arms[0],
					                arms[1], node->getPort(ID::S),
					                cell_src(node))[0];
				else
					r = module->Pmux(NEW_ID2_SUFFIX("decode_fuse_sel"), arms[0],
					                 arms.extract(1, GetSize(arms) - 1),
					                 node->getPort(ID::S), cell_src(node))[0];
			}
		}
		push_memo[v] = r;
		return r;
	}

	// (leaf in t.codes) as logic: one compare per code, ORed together.
	SigBit emit_test(const SigSpec &leaf, const Target &t, Cell *anchor)
	{
		Cell *cell = anchor;
		SigSpec hits;
		for (auto &[k, is_signed] : t.codes) {
			cells_added++;
			hits.append(module->Eq(NEW_ID2_SUFFIX("decode_fuse_cmp"), leaf, k,
			                       is_signed, cell_src(anchor))[0]);
		}
		if (GetSize(hits) == 1)
			return hits[0];
		cells_added++;
		return module->ReduceOr(NEW_ID2_SUFFIX("decode_fuse_any"), hits, false,
		                        cell_src(anchor))[0];
	}

	// Point `c`'s output at a fresh wire and hand back the signal it used to
	// drive, so the replacement can take it over without a second driver.
	// clean -purge collects the husk.
	SigSpec release_output(Cell *c)
	{
		SigSpec y = c->getPort(ID::Y);
		Cell *cell = c;
		c->setPort(ID::Y, module->addWire(NEW_ID2_SUFFIX("decode_fuse_old"), GetSize(y)));
		return y;
	}

	// ------------------------------------------------------------- rewriting

	bool fuse(const SigSpec &v)
	{
		Cell *node = net_node(v);
		if (node == nullptr)
			return false;

		vector<Target> targets;
		if (!collect_targets(v, targets))
			return false;

		plan_memo.clear();
		plan_nodes = plan_consts = plan_vars = 0;
		plan_fail = nullptr;
		int levels = 0;
		if (!plan(v, 0, levels)) {
			log_debug("  skipping %s: %s\n", log_signal(v), plan_fail);
			return false;
		}

		// Cost the whole group before touching anything. The pushed form has to
		// be strictly shallower -- otherwise the tests merely move below the
		// network and each one pays for a copy of it -- and it has to fit in the
		// bit budget of the network and wide compares it deletes, so a fold that
		// does not really collapse cannot buy depth with unbounded area.
		int width = GetSize(v), before = 0, after = 0, born = 0, codes = 0;
		for (auto &t : targets) {
			est_memo.clear();
			est_sel_cells = est_test_bits = 0;
			after = std::max(after, estimate(v, t).depth);
			before = std::max(before,
			                  levels + test_levels(width, GetSize(t.codes)));
			born += est_sel_cells + est_test_bits + (t.negate ? 1 : 0);
			codes += GetSize(t.codes);
			if (born > max_emit_cells) {
				log_debug("  skipping %s: emit exceeds budget %d\n", log_signal(v),
				          max_emit_cells);
				return false;
			}
		}
		int dies = (plan_nodes + codes) * width;
		if (after >= before) {
			log_debug("  skipping %s: %d level(s) pushed vs %d now, no depth win\n",
			          log_signal(v), after, before);
			return false;
		}
		if (born > dies) {
			log_debug("  skipping %s: %d bit-cell(s) emitted against %d removed\n",
			          log_signal(v), born, dies);
			return false;
		}

		log_debug("  fusing %s: %d test(s) over %d code(s) through %d select "
		          "node(s) (%d constant, %d value leaf/leaves), depth %d -> %d, "
		          "%d bit-cell(s) for %d\n",
		          log_signal(v), GetSize(targets), codes, plan_nodes, plan_consts,
		          plan_vars, before, after, born, dies);

		for (auto &t : targets) {
			push_memo.clear();
			SigBit r = push(v, t, t.root);
			Cell *cell = t.root;
			if (t.negate) {
				cells_added++;
				r = module->Not(NEW_ID2_SUFFIX("decode_fuse_inv"), r, false,
				                cell_src(t.root))[0];
			}
			if (!t.kept.empty()) {
				cells_added++;
				SigSpec any = t.kept;
				any.append(r);
				r = module->ReduceOr(NEW_ID2_SUFFIX("decode_fuse_or"), any, false,
				                     cell_src(t.root))[0];
			}
			// wreduce can leave a test wider than one bit; the extra bits are
			// zero either way.
			SigSpec y = release_output(t.root);
			SigSpec result = r;
			result.append(Const(State::S0, GetSize(y) - 1));
			module->connect(y, result);

			dead.insert(t.root);
			for (auto c : t.consumed)
				dead.insert(c);
			tests_pushed++;
		}

		// Every reader of `v` is now dead, so the network root is too. Cells
		// deeper in the network may still be read by a select compare, which is
		// what the next round picks up.
		dead.insert(node);
		regions++;
		return true;
	}

	// Every value that a constant compare reads out of a select network. Kept as
	// signals rather than cells because all the tests on one value are rewritten
	// together, and together is what makes the network die.
	vector<SigSpec> candidates()
	{
		vector<SigSpec> out;
		pool<SigSpec> seen;
		for (auto cell : module->selected_cells()) {
			if (dead.count(cell) || !is_cmp_type(cell))
				continue;
			for (auto port : {ID::A, ID::B}) {
				if (!cell->hasPort(port))
					continue;
				SigSpec v = sigmap(cell->getPort(port));
				if (v.is_fully_const() || net_node(v) == nullptr)
					continue;
				if (seen.insert(v).second)
					out.push_back(v);
			}
		}
		return out;
	}

	void run()
	{
		// A stage only becomes eligible once the stage above it is gone, so keep
		// re-deriving candidates until a whole round finds nothing.
		for (int round = 0; round < max_rounds; round++) {
			index();
			int before = regions;
			for (auto &v : candidates())
				fuse(v);
			if (regions == before)
				break;
		}
	}
};

struct OptDecodeFusePass : public Pass {
	OptDecodeFusePass() : Pass("opt_decode_fuse", "collapse encode/decode round trips") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_decode_fuse [options] [selection]\n");
		log("\n");
		log("Push constant tests down through the select network that produces the value\n");
		log("they read, collapsing an encode/decode round trip:\n");
		log("\n");
		log("    wire [6:0] code = sel ? 7'd62 : remap(mode);       // encode\n");
		log("    wire       cls0 = code == 7'd0 || code == 7'd32;   // decode\n");
		log("\n");
		log("becomes a decode of `mode` alone. The unit that is pushed is a membership\n");
		log("test, not one equality: a class is a set of codes, and it is the set that\n");
		log("collapses. If every code some subtree can produce is in the set, that whole\n");
		log("subtree folds to 1, where any one equality would have kept all of it.\n");
		log("\n");
		log("The rewrite is exact -- mux(s, a, b) in S is mux(s, a in S, b in S), and\n");
		log("slice-wise the same for $pmux -- so it is a re-bracketing of the same\n");
		log("function, not an observability don't-care, and it holds under a\n");
		log("node-matching equivalence check. Chains of stages collapse together, since\n");
		log("a stage's own select is typically the next test to become eligible.\n");
		log("\n");
		log("$logic_not, $reduce_bool, $reduce_or and $reduce_and count as compares: by\n");
		log("the time this runs, opt_expr has usually rewritten the tests against 0 and\n");
		log("~0 into those. OR inputs that are not compares on the value (a bypass ORed\n");
		log("in beside the decode) are left where they are.\n");
		log("\n");
		log("Only applied when it wins on depth without growing the design:\n");
		log("\n");
		log("  - every reader of the value must be one of these constant compares, so\n");
		log("    the wide network dies instead of surviving next to its 1-bit copies;\n");
		log("  - the pushed form must be strictly shallower, measured in combinational\n");
		log("    levels from start points over the shape the emit would build. Along a\n");
		log("    single path the push is depth neutral, so every level of win comes\n");
		log("    from folding;\n");
		log("  - the 1-bit cells it emits must fit in the bit count of the network and\n");
		log("    wide compares it deletes. Cell counts still rise (many 1-bit cells for\n");
		log("    a few wide ones) while bit counts fall.\n");
		log("\n");
		log("    -max-nodes N, -max_nodes N\n");
		log("        maximum select nodes in one network (default 64).\n");
		log("\n");
		log("    -max-depth N, -max_depth N\n");
		log("        maximum select network depth to walk (default 16).\n");
		log("\n");
		log("    -max-var-leaves N, -max_var_leaves N\n");
		log("        maximum non-constant leaves (default 4). Each one keeps a real\n");
		log("        test per pushed reader, so a network of mostly live values buys\n");
		log("        little and costs area.\n");
		log("\n");
		log("    -max-emit-cells N, -max_emit_cells N\n");
		log("        maximum bit-cells one network may emit (default 512). A hard\n");
		log("        runtime bound; the budget that normally decides is the count of\n");
		log("        bit-cells the rewrite removes.\n");
		log("\n");
		log("    -max-rounds N, -max_rounds N\n");
		log("        how many times to re-derive candidates per module (default 8).\n");
		log("        Each round exposes the select compare of the stage below.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_DECODE_FUSE pass (collapse encode/decode round trips).\n");

		int max_nodes = 64;
		int max_depth = 16;
		int max_var_leaves = 4;
		int max_emit_cells = 512;
		int max_rounds = 8;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if ((args[argidx] == "-max-nodes" || args[argidx] == "-max_nodes") &&
			    argidx + 1 < args.size()) {
				max_nodes = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-depth" || args[argidx] == "-max_depth") &&
			    argidx + 1 < args.size()) {
				max_depth = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-var-leaves" || args[argidx] == "-max_var_leaves") &&
			    argidx + 1 < args.size()) {
				max_var_leaves = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-emit-cells" || args[argidx] == "-max_emit_cells") &&
			    argidx + 1 < args.size()) {
				max_emit_cells = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-rounds" || args[argidx] == "-max_rounds") &&
			    argidx + 1 < args.size()) {
				max_rounds = std::stoi(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0, total_tests = 0, total_cells = 0;
		for (auto module : design->selected_modules()) {
			// The index is built from cells, so logic still held in a process is
			// invisible to it -- and the reader test needs a complete view.
			if (!module->processes.empty()) {
				log("Skipping module %s because it contains processes "
				    "(run proc first).\n", log_id(module));
				continue;
			}
			OptDecodeFuseWorker worker(module);
			worker.max_nodes = max_nodes;
			worker.max_depth = max_depth;
			worker.max_var_leaves = max_var_leaves;
			worker.max_emit_cells = max_emit_cells;
			worker.max_rounds = max_rounds;
			worker.run();
			total_regions += worker.regions;
			total_tests += worker.tests_pushed;
			total_cells += worker.cells_added;
		}

		log("Fused %d decode network(s) covering %d test(s); emitted %d new cell(s).\n",
		    total_regions, total_tests, total_cells);

		// Pass::call rather than run_pass: the latter goes to the global design,
		// which is not the one handed to us when Yosys is driven from pyosys, and
		// the husks left behind by the rewrite would survive.
		if (total_regions) {
			Pass::call(design, "opt_expr -full");
			Pass::call(design, "clean -purge");
		}
	}
} OptDecodeFusePass;

PRIVATE_NAMESPACE_END
