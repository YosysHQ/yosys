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
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include <vector>
#include "kernel/celltypes.h"
#include <cmath>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/rewrite_utils.h"
#include "passes/silimate/unit_delay.h"

// opt_addcmp: fuse an adder into the comparator it feeds.
//
// A bound check spelled `a + b <cmp> c` costs a full carry-propagate adder
// followed by a comparator, but the sum itself is never needed -- only its
// order against c. Adding one carry-save level in front of the comparator
// removes the adder from that path:
//
//     (a + b) >= c   <=>   s >= ~d       with  s = a ^ b ^ ~c
//     (a + b) >  c   <=>   s >  ~d             v = maj(a, b, ~c)
//                                              d = v << 1
//
// Both operands are widened to W = max(|a|,|b|,|c|) + 1 first, so a and b
// carry a zero in the top bit and the carry out of that column, which the
// shift drops, is maj(0, 0, x) = 0. Working one bit wider is what makes the
// identity exact rather than modular; see below for why a truncating add is
// rejected outright.
//
// Derivation, at width W with a + b < 2**W:
//
//     a + b >= c  <=>  a + b + ~c + 1 >= 2**W          (~c = 2**W-1 - c)
//                 <=>  s + d + 1 >= 2**W               (a + b + ~c = s + d)
//                 <=>  s >= 2**W-1 - d = ~d
//
// and the strict form drops the +1, which turns >= into >. The other two
// relations are these two inverted, and a sum on the comparator's right-hand
// side is the mirror image, so all four ordering cell types are handled by
// choosing a relation and an inversion.
//
// Equality comes off the same pair: a + b == c iff a + b + ~c == 2**W-1, i.e.
// s + d == 2**W-1, and two values summing to all-ones can share no set bit (it
// would carry and clear one), so that is exactly s == ~d.
//
// A whole tree of adds collapses into one comparison the same way, since
// run_csa() reduces n summands to the two the identity expects. Only a child
// add its parent solely reads is absorbed, so every adder the walk takes in is
// dead afterwards.
//
// Soundness conditions, all structural:
//
//   1. No truncation. The comparator must see the mathematical sum, so the
//      add's Y must be at least max(|a|,|b|) + 1 bits and the comparator must
//      read all of it. An add that wraps compares its residue, which the
//      carry-save form does not reproduce.
//
//   2. Unsigned. Both the add and the comparator must be unsigned; a signed
//      compare orders the same bits differently.
//
// $sub is deliberately not matched. No width condition makes an unsigned
// subtract exact the way one does an add: a - b wraps whenever a < b, and
// ruling that out needs a value range the pass cannot establish locally.
//
// Profitability. When the sum feeds nothing but this comparator the adder
// disappears, so the rewrite is a strict win in both area and depth and fires
// unconditionally. When the sum has other readers the adder stays and the
// carry-save level is added area, so that case needs -timing: it fires only
// where the comparator sits on the module's longest path in the shared
// unit-delay model, which is where trading ~2 gates per bit for a carry chain
// pays.
// Relation the rewrite emits for `sum <rel> other`; the other comparisons are
// these inverted.
enum class Rel { Ge, Gt, Eq };

inline bool is_cmp_type(IdString type)
{
	return type.in(ID($lt), ID($le), ID($gt), ID($ge), ID($eq), ID($ne));
}

struct OptAddCmpWorker : UnitDelayTiming
{
	pool<SigBit> output_bits;

	// Tunables (see Pass::execute).
	int min_width = 8;
	bool timing_guard = false;
	int slack_margin = 0;

	int fused_exclusive = 0, fused_shared = 0, fused_wide = 0;
	int skipped_slack = 0, skipped_narrow = 0;

	OptAddCmpWorker(Module *module) : UnitDelayTiming(module)
	{
		// Port bits are collected by wire, not by testing port_output on a
		// sigmap representative: `assign out = sum` merges the two wires and
		// the representative can be either one.
		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					output_bits.insert(bit);

		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				bool is_out = cell->output(conn.first);
				for (auto bit : sigmap(conn.second)) {
					if (bit.wire == nullptr)
						continue;
					if (!is_out)
						consumer_map[bit].push_back(cell);
					// A bit with more than one driver ends a path instead of
					// electing one of them.
					else if (!driver_map.count(bit))
						driver_map[bit] = cell;
					else if (driver_map.at(bit) != cell)
						driver_map[bit] = nullptr;
				}
			}
	}

	// The unsigned non-truncating $add whose Y makes up all of `operand`, else
	// null. Zero padding above Y is fine (a widened use of the sum); anything
	// narrower would compare a residue the carry-save form does not reproduce.
	Cell *sum_driver(const SigSpec &operand)
	{
		SigSpec sig = sigmap(operand);
		if (sig.empty() || sig[0].wire == nullptr)
			return nullptr;

		auto it = driver_map.find(sig[0]);
		Cell *add = it == driver_map.end() ? nullptr : it->second;
		if (add == nullptr || add->type != ID($add))
			return nullptr;
		if (add->getParam(ID::A_SIGNED).as_bool() || add->getParam(ID::B_SIGNED).as_bool())
			return nullptr;

		int wa = add->getParam(ID::A_WIDTH).as_int();
		int wb = add->getParam(ID::B_WIDTH).as_int();
		int wy = add->getParam(ID::Y_WIDTH).as_int();
		if (wy < std::max(wa, wb) + 1)
			return nullptr;

		SigSpec y = sigmap(add->getPort(ID::Y));
		if (GetSize(sig) < GetSize(y))
			return nullptr;
		for (int i = 0; i < GetSize(sig); i++) {
			if (i < GetSize(y)) {
				if (sig[i] != y[i])
					return nullptr;
			} else if (sig[i] != SigBit(State::S0)) {
				return nullptr;
			}
		}
		return add;
	}

	// Is `sig` read by anything other than `reader`?
	bool escapes(const SigSpec &sig, Cell *reader)
	{
		for (auto bit : sigmap(sig)) {
			if (bit.wire == nullptr)
				continue;
			if (output_bits.count(bit))
				return true;
			auto it = consumer_map.find(bit);
			if (it == consumer_map.end())
				continue;
			for (auto cons : it->second)
				if (cons != reader)
					return true;
		}
		return false;
	}

	// Flatten an add tree into its summands, descending into a child add only
	// when the parent is its sole reader, so every adder the walk absorbs dies.
	// A child that truncates is left as an operand: its wrapped result is a
	// different value from the exact sum of its own operands.
	void collect_operands(Cell *add, std::vector<SigSpec> &operands, pool<Cell *> &tree)
	{
		tree.insert(add);
		for (IdString port : {ID::A, ID::B}) {
			SigSpec operand = add->getPort(port);
			Cell *child = sum_driver(operand);
			if (child != nullptr && !tree.count(child) && !escapes(child->getPort(ID::Y), add) &&
					GetSize(tree) + 1 < max_summands)
				collect_operands(child, operands, tree);
			else
				operands.push_back(operand);
		}
	}

	// Absorbing one adder adds one summand, so the tree ends with tree+1 of them.
	// Past a handful the carry-save levels cost more than the adders they remove.
	static const int max_summands = 6;

	// Does anything but `cmp` read the sum? If not, the adder dies with it.
	bool sum_is_shared(Cell *add, Cell *cmp) { return escapes(add->getPort(ID::Y), cmp); }

	// One 3:2 carry-save level: x + y + z == sum + (carry << 1), exactly, as long
	// as the shift keeps the top carry bit. `run_csa` establishes that.
	void csa_level(Cell *cell, const SigSpec &x, const SigSpec &y, const SigSpec &z,
			SigSpec &sum, SigSpec &carry)
	{
		std::string src = cell_src(cell);
		int width = GetSize(x);
		SigSpec xxy = module->Xor(NEW_ID2_SUFFIX("addcmp_cx"), x, y, false, src);
		sum = module->Xor(NEW_ID2_SUFFIX("addcmp_cs"), xxy, z, false, src);
		SigSpec c = module->Or(NEW_ID2_SUFFIX("addcmp_cv"),
		                       module->And(NEW_ID2_SUFFIX("addcmp_cxy"), x, y, false, src),
		                       module->And(NEW_ID2_SUFFIX("addcmp_cxz"), xxy, z, false, src),
		                       false, src);
		carry = SigSpec(State::S0);
		carry.append(c.extract(0, width - 1));
	}

	// Reduce n >= 3 operands to the two that sum to the same value, so the
	// comparator identity below sees its usual pair.
	//
	// Everything runs at width W = max(|o_i|) + ceil(log2 n), which makes the
	// total T = sum(o_i) < 2**W. Every level replaces x, y, z with s and 2c
	// where s + 2c == x + y + z, so the multiset total stays T; since the values
	// are non-negative and sum to T < 2**W, each one is itself below 2**W, so
	// 2c < 2**W and the shift never drops a set bit. That is what keeps the
	// reduction exact instead of modular.
	void run_csa(Cell *cell, std::vector<SigSpec> operands, SigSpec &s, SigSpec &d)
	{
		int width = 0;
		for (auto &o : operands)
			width = std::max(width, GetSize(o));
		width += log2p1_int(GetSize(operands) - 1); // ceil(log2 n) for n >= 2
		for (auto &o : operands)
			o.extend_u0(width, false);

		while (GetSize(operands) > 2) {
			SigSpec x = operands.back(); operands.pop_back();
			SigSpec y = operands.back(); operands.pop_back();
			SigSpec z = operands.back(); operands.pop_back();
			SigSpec sum, carry;
			csa_level(cell, x, y, z, sum, carry);
			operands.push_back(sum);
			operands.push_back(carry);
		}
		s = operands[0];
		d = operands[1];
	}

	// (a + b) >= c, or the strict form: one carry-save level plus one compare.
	// `cell` is the comparator being replaced; NEW_ID2_SUFFIX names after it.
	SigSpec emit_fused(Cell *cell, SigSpec a, SigSpec b, SigSpec c, Rel rel)
	{
		int width = std::max({GetSize(a), GetSize(b), GetSize(c)}) + 1;
		a.extend_u0(width, false);
		b.extend_u0(width, false);
		c.extend_u0(width, false);
		std::string src = cell_src(cell);

		SigSpec nc = module->Not(NEW_ID2_SUFFIX("addcmp_nc"), c, false, src);
		SigSpec axb = module->Xor(NEW_ID2_SUFFIX("addcmp_axb"), a, b, false, src);
		SigSpec sum = module->Xor(NEW_ID2_SUFFIX("addcmp_s"), axb, nc, false, src);
		SigSpec carry = module->Or(NEW_ID2_SUFFIX("addcmp_v"),
		                           module->And(NEW_ID2_SUFFIX("addcmp_ab"), a, b, false, src),
		                           module->And(NEW_ID2_SUFFIX("addcmp_xc"), axb, nc, false, src),
		                           false, src);

		// ~(carry << 1), spelled directly: the shifted-in zero inverts to one,
		// and the top carry bit is provably zero because a and b were widened.
		SigSpec ncarry(State::S1);
		ncarry.append(module->Not(NEW_ID2_SUFFIX("addcmp_nv"),
		                          carry.extract(0, width - 1), false, src));

		// Equality needs no ordering: sum + d == 2**W-1 holds only when the two
		// are bit-complements, since a shared set bit would carry and clear one.
		if (rel == Rel::Eq)
			return module->Eq(NEW_ID2_SUFFIX("addcmp_eq"), sum, ncarry, false, src);
		return rel == Rel::Gt ? module->Gt(NEW_ID2_SUFFIX("addcmp_gt"), sum, ncarry, false, src)
		                      : module->Ge(NEW_ID2_SUFFIX("addcmp_ge"), sum, ncarry, false, src);
	}

	void fuse(Cell *cell, const std::vector<SigSpec> &operands, bool sum_on_a)
	{
		// Relation to emit for `sum <rel> other`, and whether to invert it.
		// With the sum on the right the comparison is read backwards, which
		// swaps >= against > and flips the inversion with it; equality reads the
		// same either way.
		IdString t = cell->type;
		Rel rel = t.in(ID($eq), ID($ne)) ? Rel::Eq
		        : (sum_on_a ? t.in(ID($gt), ID($le)) : t.in(ID($lt), ID($ge))) ? Rel::Gt
		        : Rel::Ge;
		bool invert = t == ID($ne) ||
				(sum_on_a ? t.in(ID($lt), ID($le)) : t.in(ID($gt), ID($ge)));

		// More than two summands reduce to two first, which is the pair the
		// identity below expects
		SigSpec a = operands[0], b = operands[1];
		if (GetSize(operands) > 2)
			run_csa(cell, operands, a, b);

		SigSpec other = cell->getPort(sum_on_a ? ID::B : ID::A);
		SigSpec y = emit_fused(cell, a, b, other, rel);
		if (invert)
			y = module->Not(NEW_ID2_SUFFIX("addcmp_inv"), y, false, cell_src(cell));

		SigSpec cmp_y = cell->getPort(ID::Y);
		y.extend_u0(GetSize(cmp_y), false);
		module->remove(cell);
		module->connect(cmp_y, y);
	}

	int run()
	{
		std::vector<std::tuple<Cell *, std::vector<SigSpec>, bool>> hits;
		for (auto cmp : module->selected_cells()) {
			if (!is_cmp_type(cmp->type))
				continue;
			if (cmp->getParam(ID::A_SIGNED).as_bool() || cmp->getParam(ID::B_SIGNED).as_bool())
				continue;

			for (int side = 0; side < 2; side++) {
				bool sum_on_a = side == 0;
				Cell *add = sum_driver(cmp->getPort(sum_on_a ? ID::A : ID::B));
				if (add == nullptr)
					continue;

				// A narrow adder is cheaper than the carry-save level plus the
				// wider compare it would leave behind, and the boolean mapper
				// flattens it anyway.
				if (add->getParam(ID::Y_WIDTH).as_int() < min_width) {
					skipped_narrow++;
					continue;
				}

				bool exclusive = !sum_is_shared(add, cmp);
				if (!exclusive) {
					if (!timing_guard)
						continue;
					int depth = path_depth(cmp->getPort(ID::Y));
					if (depth < longest_path() - slack_margin) {
						log_debug("  %s: off-critical (depth %d of %d)\n",
						          log_id(cmp), depth, longest_path());
						skipped_slack++;
						continue;
					}
				}

				std::vector<SigSpec> operands;
				pool<Cell *> tree;
				collect_operands(add, operands, tree);

				log_debug("  %s: fusing %s (%d summand(s) from %d add(s), %s)\n",
				          log_id(cmp), log_id(add), GetSize(operands), GetSize(tree),
				          exclusive ? "sole reader" : "critical");
				hits.emplace_back(cmp, operands, sum_on_a);
				(exclusive ? fused_exclusive : fused_shared)++;
				if (GetSize(operands) > 2)
					fused_wide++;
				break;
			}
		}

		for (auto &[cmp, operands, sum_on_a] : hits)
			fuse(cmp, operands, sum_on_a);

		if (skipped_narrow || skipped_slack)
			log_debug("  %s: skipped %d narrow adder(s), %d off-critical comparator(s).\n",
			          log_id(module), skipped_narrow, skipped_slack);
		return GetSize(hits);
	}
};

struct OptAddCmpPass : public Pass {
	OptAddCmpPass() : Pass("opt_addcmp", "fuse an adder into the comparator it feeds") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_addcmp [options] [selection]\n");
		log("\n");
		log("Replace a comparison against a sum with a carry-save comparison, so the\n");
		log("adder no longer sits between its own operands and the comparator:\n");
		log("\n");
		log("    (a + b) >= c    ->    s >= ~(v << 1)      s = a ^ b ^ ~c\n");
		log("    (a + b) >  c    ->    s >  ~(v << 1)      v = maj(a, b, ~c)\n");
		log("\n");
		log("Bound checks (address range, credit, overflow) ask for the order of a sum\n");
		log("and never for the sum itself, but the RTL spells them as an adder feeding\n");
		log("a comparator, which puts a full carry-propagate network ahead of the\n");
		log("comparator's own. One carry-save level replaces it: the operands are\n");
		log("reduced to a sum and a carry vector in constant depth, and the single\n");
		log("remaining carry chain is the comparator's.\n");
		log("\n");
		log("Operands are first widened to max(|a|,|b|,|c|) + 1 bits. That makes the\n");
		log("identity exact -- the carry out of the top column is maj(0, 0, x) = 0, so\n");
		log("the shift drops nothing -- and it is why an add whose result is narrower\n");
		log("than its operands (comparing a residue) is rejected instead. The other\n");
		log("two relations are these two inverted, and a sum on the comparator's\n");
		log("right-hand side is the mirror image, so all four orderings are handled.\n");
		log("\n");
		log("$eq and $ne fuse off the same pair, since a sum and a carry vector adding\n");
		log("to all-ones must be bit-complements. A tree of adds is flattened into one\n");
		log("carry-save reduction, absorbing only child adders their parent solely\n");
		log("reads so that each one absorbed is dead afterwards.\n");
		log("\n");
		log("Signed adds and signed comparisons are rejected: the carry-save identity\n");
		log("is an unsigned one. $sub is rejected too -- an unsigned subtract wraps\n");
		log("whenever a < b, which no width condition rules out.\n");
		log("\n");
		log("When the comparator is the sum's only reader the adder is dead after the\n");
		log("rewrite, so the fusion is a strict win and always taken. When the sum has\n");
		log("other readers the adder stays and the carry-save level is added area,\n");
		log("which only pays on a critical comparator -- that case needs -timing.\n");
		log("\n");
		log("    -timing\n");
		log("        also fuse when the sum has other readers, provided the comparator\n");
		log("        lies on the module's longest unit-delay path.\n");
		log("\n");
		log("    -slack-margin <int>\n");
		log("        levels below the module depth still counted as critical for\n");
		log("        -timing (default: 0)\n");
		log("\n");
		log("    -min-width <n>\n");
		log("        skip adders narrower than this many result bits (default: 8).\n");
		log("        Below it the adder is cheaper than the logic that would replace\n");
		log("        it, and the boolean mapper flattens it regardless.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_ADDCMP pass (fuse adder into comparator).\n");

		int min_width = 8, slack_margin = 0;
		bool timing_guard = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-timing") {
				timing_guard = true;
				continue;
			}
			if (args[argidx] == "-slack-margin" && argidx + 1 < args.size()) {
				slack_margin = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min-width" && argidx + 1 < args.size()) {
				min_width = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total = 0, exclusive = 0, wide = 0;
		for (auto module : design->selected_modules()) {
			// The worker indexes every bit in the module, so check there is
			// something to match before paying for it
			bool candidate = false;
			for (auto cell : module->selected_cells())
				if (is_cmp_type(cell->type)) {
					candidate = true;
					break;
				}
			if (!candidate)
				continue;

			OptAddCmpWorker worker(module);
			worker.min_width = min_width;
			worker.timing_guard = timing_guard;
			worker.slack_margin = slack_margin;
			total += worker.run();
			exclusive += worker.fused_exclusive;
			wide += worker.fused_wide;
		}

		if (total)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Fused %d add-compare region(s); %d left the adder dead, %d flattened "
		    "more than two summands.\n", total, exclusive, wide);
	}
} OptAddCmpPass;

PRIVATE_NAMESPACE_END
