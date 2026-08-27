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
// side is the mirror image, so all four cell types are handled by choosing a
// relation and an inversion.
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
// Profitability. When the sum feeds nothing but this comparator the adder
// disappears, so the rewrite is a strict win in both area and depth and fires
// unconditionally. When the sum has other readers the adder stays and the
// carry-save level is added area, so that case needs -timing: it fires only
// where the comparator sits on the module's longest path in the shared
// unit-delay model, which is where trading ~2 gates per bit for a carry chain
// pays.
struct OptAddCmpWorker : UnitDelayTiming
{
	pool<SigBit> output_bits;

	// Tunables (see Pass::execute).
	int min_width = 8;
	bool timing_guard = false;
	int slack_margin = 0;

	int fused_exclusive = 0, fused_shared = 0;
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

	// Does anything but `cmp` read the sum? If not, the adder dies with it.
	bool sum_is_shared(Cell *add, Cell *cmp)
	{
		for (auto bit : sigmap(add->getPort(ID::Y))) {
			if (bit.wire == nullptr)
				continue;
			if (output_bits.count(bit))
				return true; // escapes the module, so the adder survives
			auto it = consumer_map.find(bit);
			if (it == consumer_map.end())
				continue;
			for (auto cons : it->second)
				if (cons != cmp)
					return true;
		}
		return false;
	}

	// (a + b) >= c, or the strict form: one carry-save level plus one compare.
	// `cell` is the comparator being replaced; NEW_ID2_SUFFIX names after it.
	SigSpec emit_fused(Cell *cell, SigSpec a, SigSpec b, SigSpec c, bool strict)
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

		return strict ? module->Gt(NEW_ID2_SUFFIX("addcmp_gt"), sum, ncarry, false, src)
		              : module->Ge(NEW_ID2_SUFFIX("addcmp_ge"), sum, ncarry, false, src);
	}

	void fuse(Cell *cell, Cell *add, bool sum_on_a)
	{
		// Relation to emit for `sum <rel> other`, and whether to invert it.
		// With the sum on the right the comparison is read backwards, which
		// swaps >= against > and flips the inversion with it.
		IdString t = cell->type;
		bool strict = sum_on_a ? t.in(ID($gt), ID($le)) : t.in(ID($lt), ID($ge));
		bool invert = sum_on_a ? t.in(ID($lt), ID($le)) : t.in(ID($gt), ID($ge));

		SigSpec other = cell->getPort(sum_on_a ? ID::B : ID::A);
		SigSpec y = emit_fused(cell, add->getPort(ID::A), add->getPort(ID::B), other, strict);
		if (invert)
			y = module->Not(NEW_ID2_SUFFIX("addcmp_inv"), y, false, cell_src(cell));

		SigSpec cmp_y = cell->getPort(ID::Y);
		y.extend_u0(GetSize(cmp_y), false);
		module->remove(cell);
		module->connect(cmp_y, y);
	}

	int run()
	{
		std::vector<std::tuple<Cell *, Cell *, bool>> hits;
		for (auto cmp : module->selected_cells()) {
			if (!cmp->type.in(ID($lt), ID($le), ID($gt), ID($ge)))
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

				log_debug("  %s: fusing %s %s (%s)\n", log_id(cmp), log_id(add->type),
				          log_id(add), exclusive ? "sole reader" : "critical");
				hits.emplace_back(cmp, add, sum_on_a);
				(exclusive ? fused_exclusive : fused_shared)++;
				break;
			}
		}

		for (auto &[cmp, add, sum_on_a] : hits)
			fuse(cmp, add, sum_on_a);

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
		log("right-hand side is the mirror image, so all four cell types are handled.\n");
		log("\n");
		log("Signed adds and signed comparisons are rejected: the carry-save identity\n");
		log("is an unsigned one.\n");
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

		int total = 0, exclusive = 0;
		for (auto module : design->selected_modules()) {
			OptAddCmpWorker worker(module);
			worker.min_width = min_width;
			worker.timing_guard = timing_guard;
			worker.slack_margin = slack_margin;
			total += worker.run();
			exclusive += worker.fused_exclusive;
		}

		if (total)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Fused %d add-compare region(s); %d left the adder dead.\n", total, exclusive);
	}
} OptAddCmpPass;

PRIVATE_NAMESPACE_END
