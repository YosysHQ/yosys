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
#include "kernel/consteval.h"
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/cut_region.h"

struct OptDisjointAddWorker : CutRegionWorker
{
	struct Rewrite {
		Cell *add;
		SigSpec shifted;  // operand whose low `amount` bits are zero
		SigSpec addend;   // operand proven to fit below that window
		SigSpec y;
		int width;
		int cases;        // enumerated support assignments (for the log)
	};

	// Enumeration is exponential in the joint support, so the cap is the
	// pass's main cost knob: 2^max_support_bits ConstEval sweeps per
	// candidate, each charged against the shared eval budget.
	int max_support_bits = 16;
	int max_cone_cells = 4000;

	vector<Rewrite> rewrites;
	int skipped_roots = 0;

	OptDisjointAddWorker(Module *module) : CutRegionWorker(module)
	{
	}

	// $shl driving `operand`, else null. The shift's own data operand is
	// deliberately not inspected: bit i of (X << s) is zero for every i < s
	// whatever X is, which is the only fact the proof needs.
	Cell *shl_driver(const SigSpec &operand)
	{
		SigSpec sig = sigmap(operand);
		if (sig.empty())
			return nullptr;

		Cell *drv = bit_to_driver.at(sig[0], nullptr);
		if (drv == nullptr || drv->type != ID($shl))
			return nullptr;

		// Every operand bit must come from that $shl's Y, in order, from bit
		// 0 up; trailing zero padding is fine (a widened use of the shift).
		SigSpec y = sigmap(drv->getPort(ID::Y));
		for (int i = 0; i < GetSize(sig); i++) {
			if (i < GetSize(y)) {
				if (sig[i] != y[i])
					return nullptr;
			} else if (sig[i] != SigBit(State::S0)) {
				return nullptr;
			}
		}
		return drv;
	}

	// Shift amount opening the window at the bottom of `operand`: the $shl's
	// amount if one drives it, else the run of literal zero bits there. A
	// constant shift is folded away long before this pass runs, so that form
	// arrives as an operand zero-padded at the bottom rather than as a cell.
	bool window_amount(const SigSpec &operand, SigSpec &amount)
	{
		Cell *shl = shl_driver(operand);
		if (shl != nullptr) {
			if (shl->getParam(ID::B_SIGNED).as_bool())
				return false;
			amount = sigmap(shl->getPort(ID::B));
			return true;
		}

		int zeros = 0;
		while (zeros < GetSize(operand) && operand[zeros] == SigBit(State::S0))
			zeros++;
		if (zeros == 0)
			return false;
		amount = const_u64((uint64_t)zeros, 32);
		return true;
	}

	// True when every bit of `sig` from `from` up is a literal zero.
	static bool zero_above(const SigSpec &sig, int from)
	{
		for (int i = std::max(from, 0); i < GetSize(sig); i++)
			if (sig[i] != SigBit(State::S0))
				return false;
		return true;
	}

	// Leaves of the combinational cone behind `sig`, added to `support`.
	// `cone_size` accumulates cell counts so the sweep can be charged for
	// what a ConstEval pass over these cones actually costs.
	bool collect_support(const SigSpec &sig, pool<SigBit> &support, int &cone_size)
	{
		pool<Cell *> cone_cells;
		pool<SigBit> leaves;
		if (!get_cone(sig, cone_cells, leaves, max_cone_cells, max_support_bits))
			return false;
		for (auto bit : leaves)
			support.insert(bit);
		cone_size += GetSize(cone_cells);
		return GetSize(support) <= max_support_bits;
	}

	// Value of a fully-defined shift amount, clamped to `clamp`. A $shl by
	// more than the operand width zeroes the whole result, so clamping an
	// out-of-int amount stays conservative instead of overflowing.
	static int shift_amount_value(const Const &amount, int clamp)
	{
		for (int i = 30; i < GetSize(amount); i++)
			if (amount[i] == State::S1)
				return clamp;

		int value = 0;
		for (int i = 0; i < GetSize(amount) && i < 30; i++)
			if (amount[i] == State::S1)
				value |= 1 << i;
		return value;
	}

	// Sweep every assignment of `support` and require the addend to stay
	// strictly below the shift window on all of them. Both signals are
	// evaluated under the same assignment, so amounts and magnitudes that
	// share drivers (a shift by f(k) paired with an addend bounded by g(k))
	// are proven jointly rather than by independent per-operand ranges.
	bool prove_disjoint(const SigSpec &amount, const SigSpec &addend,
	                    const pool<SigBit> &support, int cone_size, int &cases)
	{
		SigSpec support_sig;
		for (auto bit : support)
			support_sig.append(bit);

		int n = GetSize(support_sig);
		if (n > max_support_bits || n >= 31)
			return false;

		cases = 1 << n;
		charge_eval((int64_t)cases * std::max(cone_size, 1));
		if (eval_exhausted())
			return false;

		ConstEval &ce = shared_ce();
		for (int v = 0; v < cases; v++) {
			ce.push();
			ce.set(support_sig, const_u64((uint64_t)v, n));

			SigSpec amount_val = amount, addend_val = addend, undef;
			bool ok = ce.eval(amount_val, undef) && ce.eval(addend_val, undef);
			ce.pop();

			// An x bit (or an unresolved one, meaning the support was
			// under-collected) proves nothing about this assignment. Rejecting
			// x keeps the rewrite independent of don't-care freedom.
			if (!ok || !amount_val.is_fully_def() || !addend_val.is_fully_def())
				return false;

			Const addend_const = addend_val.as_const();
			int shift = shift_amount_value(amount_val.as_const(), GetSize(addend_const));
			for (int i = shift; i < GetSize(addend_const); i++)
				if (addend_const[i] != State::S0)
					return false;
		}
		return true;
	}

	void collect(Cell *cell)
	{
		if (cell->type != ID($add))
			return;
		if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
			return;

		int width = cell->getParam(ID::Y_WIDTH).as_int();
		if (width < 2)
			return;

		SigSpec ports[2] = {sigmap(cell->getPort(ID::A)), sigmap(cell->getPort(ID::B))};
		for (int side = 0; side < 2; side++) {
			SigSpec amount;
			if (!window_amount(ports[side], amount))
				continue;
			SigSpec addend = ports[1 - side];

			// A fixed window that the addend structurally fits under needs no
			// sweep, and so carries no bound on the addend's cone either.
			if (amount.is_fully_def() &&
			    zero_above(addend, shift_amount_value(amount.as_const(), GetSize(addend)))) {
				log_debug("  %s: addend is structurally below a fixed window\n", log_id(cell));
				rewrites.push_back({cell, ports[side], addend, sigmap(cell->getPort(ID::Y)),
				                    width, 0});
				return;
			}

			if (walk_exhausted() || eval_exhausted()) {
				skipped_roots++;
				return;
			}

			pool<SigBit> support;
			int cone_size = 0;
			if (!collect_support(amount, support, cone_size) ||
			    !collect_support(addend, support, cone_size)) {
				log_debug("  %s: joint support of %s / %s exceeds %d bits\n",
				          log_id(cell), log_signal(amount), log_signal(addend), max_support_bits);
				continue;
			}

			int cases = 0;
			if (!prove_disjoint(amount, addend, support, cone_size, cases)) {
				log_debug("  %s: operands may overlap (support %d bits)\n",
				          log_id(cell), GetSize(support));
				continue;
			}

			log_debug("  %s: disjoint over %d case(s), %d support bit(s)\n",
			          log_id(cell), cases, GetSize(support));
			rewrites.push_back({cell, ports[side], addend, sigmap(cell->getPort(ID::Y)),
			                    width, cases});
			return;
		}
	}

	void apply(const Rewrite &rewrite)
	{
		Cell *cell = rewrite.add;  // NEW_ID2_SUFFIX names the $or after it

		SigSpec a = rewrite.shifted, b = rewrite.addend;
		a.extend_u0(rewrite.width, false);
		b.extend_u0(rewrite.width, false);

		Cell *or_cell = module->addCell(NEW_ID2_SUFFIX("disjoint_or"), ID($or));
		or_cell->attributes = cell->attributes;
		or_cell->setPort(ID::A, a);
		or_cell->setPort(ID::B, b);
		or_cell->setPort(ID::Y, rewrite.y);
		or_cell->setParam(ID::A_SIGNED, false);
		or_cell->setParam(ID::B_SIGNED, false);
		or_cell->fixup_parameters();

		module->remove(cell);
	}

	int run()
	{
		vector<Cell *> cells;
		for (auto cell : module->selected_cells())
			cells.push_back(cell);
		for (auto cell : cells)
			collect(cell);

		for (auto &rewrite : rewrites)
			apply(rewrite);

		note_budget("opt_disjoint_add", skipped_roots);
		return GetSize(rewrites);
	}
};

struct OptDisjointAddPass : public Pass {
	OptDisjointAddPass() : Pass("opt_disjoint_add", "rewrite non-overlapping adds as bitwise or") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_disjoint_add [options] [selection]\n");
		log("\n");
		log("Replace an $add whose two operands can never hold a 1 in the same bit\n");
		log("position with a plain $or. Such an add carries nowhere, so the adder is a\n");
		log("full carry-propagate network computing a concatenation:\n");
		log("\n");
		log("    (X << s) + b    ->    (X << s) | b        when b < 2**s always\n");
		log("\n");
		log("The idiom shows up in address generation, where a coarse field is scaled\n");
		log("by a run-time shift and a fine field is dropped into the hole underneath\n");
		log("it. Both are usually derived from the same control register, so the two\n");
		log("operands are only provably non-overlapping when the shift amount and the\n");
		log("addend magnitude are considered together -- independent per-operand range\n");
		log("analysis sees the windows touch and gives up.\n");
		log("\n");
		log("The match therefore takes the combinational cone leaves behind the shift\n");
		log("amount and behind the addend, sweeps every assignment of that joint\n");
		log("support with ConstEval, and requires the addend to stay below the shift\n");
		log("window on all of them. The shift's data operand is never inspected: bit i\n");
		log("of (X << s) is zero for all i < s regardless of X, so its cone (typically\n");
		log("the wide datapath) neither has to be enumerated nor bounded.\n");
		log("\n");
		log("A constant shift is folded away before this pass runs, so that case\n");
		log("arrives as an operand carrying literal zeros at the bottom. It is taken\n");
		log("directly from the operand shapes when the addend is short enough, with no\n");
		log("sweep and hence no limit on how wide the addend's cone may be.\n");
		log("\n");
		log("Signed operands, a signed shift amount, and any assignment that ConstEval\n");
		log("cannot resolve are all rejected, as is a joint support wider than\n");
		log("-max-support (the sweep is exponential in it).\n");
		log("\n");
		log("    -max-support <n>\n");
		log("        maximum joint support width to enumerate (default 16, so up to\n");
		log("        65536 sweeps per candidate). Candidates above this are skipped.\n");
		log("\n");
		log("    -max-cone-cells <n>\n");
		log("        maximum cells per collected cone (default 4000).\n");
		log("\n");
		log("    -eval-budget <n>\n");
		log("        per-module ConstEval work budget (default 20000000).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_DISJOINT_ADD pass (non-overlapping add to or).\n");

		int max_support_bits = 16, max_cone_cells = 4000;
		int64_t eval_budget = -1;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max-support" && argidx + 1 < args.size()) {
				max_support_bits = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max-cone-cells" && argidx + 1 < args.size()) {
				max_cone_cells = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-eval-budget" && argidx + 1 < args.size()) {
				eval_budget = std::stoll(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total = 0;
		for (auto module : design->selected_modules()) {
			OptDisjointAddWorker worker(module);
			worker.max_support_bits = max_support_bits;
			worker.max_cone_cells = max_cone_cells;
			if (eval_budget > 0)
				worker.eval_budget = eval_budget;
			total += worker.run();
		}

		if (total)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Rewrote %d non-overlapping add%s into $or.\n", total, total == 1 ? "" : "s");
	}
} OptDisjointAddPass;

PRIVATE_NAMESPACE_END
