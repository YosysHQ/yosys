/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/utils.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool did_something;

// scratchpad configurations for pmgen
int shiftadd_max_ratio;

pool<SigBit> muladd_keep_bits, muladd_mul_bits;
int muladd_min_product_width;
int muladd_max_chain_depth;

struct MuladdLevel {
	Cell *adder;
	IdString port;
	SigSpec product;
};

IdString muladd_other_port(IdString name)
{
	return name == ID::A ? ID::B : ID::A;
}

IdString muladd_width_param(IdString name)
{
	return name == ID::A ? ID::A_WIDTH : ID::B_WIDTH;
}

bool muladd_is_product(Cell *cell)
{
	if (cell == nullptr || cell->type != ID($mul))
		return false;
	int operand_width = GetSize(cell->getPort(ID::A)) + GetSize(cell->getPort(ID::B));
	return operand_width >= muladd_min_product_width;
}

bool muladd_holds_product(const SigSpec &sig)
{
	for (auto bit : sig)
		if (muladd_mul_bits.count(bit))
			return true;
	return false;
}

bool muladd_signal_kept(const SigSpec &sig)
{
	for (auto bit : sig)
		if (muladd_keep_bits.count(bit))
			return true;
	return false;
}

bool muladd_signals_overlap(const SigSpec &lhs, const SigSpec &rhs)
{
	pool<SigBit> lhs_bits(lhs.begin(), lhs.end());
	for (auto bit : rhs)
		if (lhs_bits.count(bit))
			return true;
	return false;
}

// reassociating is only exact when both hold
bool muladd_levels_compatible(Cell *upper, Cell *lower)
{
	if (upper->getParam(ID::Y_WIDTH).as_int() > lower->getParam(ID::Y_WIDTH).as_int())
		return false;
	// the parameter is a bool of any width
	return lower->getParam(ID::A_SIGNED).as_bool() == upper->getParam(ID::A_SIGNED).as_bool();
}

void muladd_rotate(Cell *outer, IdString outer_port, const vector<MuladdLevel> &levels, const SigSpec &addend)
{
	outer->setPort(outer_port, levels.front().product);
	outer->setParam(muladd_width_param(outer_port), GetSize(levels.front().product));

	for (int i = 0; i < GetSize(levels); i++) {
		SigSpec moved = i + 1 < GetSize(levels) ? levels[i + 1].product : addend;
		levels[i].adder->setPort(levels[i].port, moved);
		levels[i].adder->setParam(muladd_width_param(levels[i].port), GetSize(moved));
	}
}

// Helper function, removes LSB 0s
SigSpec remove_bottom_padding(SigSpec sig)
{
	int i = 0;
	for (; i < sig.size() - 1 && sig[i] == State::S0; i++);
	return sig.extract(i, sig.size() - i);
}

#include "passes/opt/peepopt_pm.h"

void collect_muladd_bits(peepopt_pm &pm)
{
	muladd_keep_bits.clear();
	muladd_mul_bits.clear();
	for (auto wire : pm.module->wires())
		if (wire->get_bool_attribute(ID::keep))
			for (auto bit : pm.sigmap(wire))
				muladd_keep_bits.insert(bit);
	for (auto cell : pm.module->cells())
		if (cell->type == ID($mul))
			for (auto bit : pm.sigmap(cell->getPort(ID::Y)))
				muladd_mul_bits.insert(bit);
}

struct PeepoptPass : public Pass {
	PeepoptPass() : Pass("peepopt", "collection of peephole optimizers") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    peepopt [options] [selection]\n");
		log("\n");
		log("This pass applies a collection of peephole optimizers to the current design.\n");
		log("\n");
		log("This pass employs the following rules by default:\n");
		log("\n");
		log("   * muldiv - Replace (A*B)/B with A\n");
		log("\n");
		log("   * muldiv_c - Replace (A*B)/C with A*(B/C) when C is a const divisible by B.\n");
		log("\n");
		log("   * shiftmul - Replace A>>(B*C) with A'>>(B<<K) where C and K are constants\n");
		log("                and A' is derived from A by appropriately inserting padding\n");
		log("                into the signal. (right variant)\n");
		log("\n");
		log("                Analogously, replace A<<(B*C) with appropriate selection of\n");
		log("                output bits from A<<(B<<K). (left variant)\n");
		log("\n");
		log("   * shiftadd - Replace A>>(B+D) with (A'>>D)>>(B) where D is constant and\n");
		log("                A' is derived from A by padding or cutting inaccessible bits.\n");
		log("                Scratchpad: 'peepopt.shiftadd.max_data_multiple' (default: 2)\n");
		log("                limits the amount of padding to a multiple of the data, \n");
		log("                to avoid high resource usage from large temporary MUX trees.\n");
		log("\n");
		log("   * shiftpow2 - Replace A>>(B<<K) with a $bmux word multiplexer when\n");
		log("                the output width is at most the stride 1<<K. This handles\n");
		log("                power-of-two aligned word selects.\n");
		log("                Scratchpad: 'peepopt.shiftpow2.max_data_multiple' (default: 2)\n");
		log("                limits padding for out-of-range select values.\n");
		log("\n");
		log("   * muladd - Replace ((P+A*B)+C*D)+E with ((P+E)+A*B)+C*D, so that DSP\n");
		log("                inference can give both multipliers a post-adder.\n");
		log("                Scratchpad: 'peepopt.muladd.min_product_width' (default: 11)\n");
		log("                is the smallest A_WIDTH+B_WIDTH that counts as a product.\n");
		log("                Scratchpad: 'peepopt.muladd.max_chain_depth' (default: 64,\n");
		log("                max 256) limits how far the operand is sunk.\n");
		log("\n");
		log("If -formalclk is specified it instead employs the following rules:\n");
		log("\n");
		log("   * clockgateff - Replace latch based clock gating patterns with a flip-flop\n");
		log("                   based pattern to prevent combinational paths from the\n");
		log("                   output to the enable input after running clk2fflogic.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing PEEPOPT pass (run peephole optimizers).\n");

		bool formalclk = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-formalclk") {
				formalclk = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// limit the padding from shiftadd to a multiple of the input data
		// during techmap it creates (#data + #padding) * log(shift) $_MUX_ cells
		// 2x implies there is a constant shift larger than the input-data which should be extremely rare
		shiftadd_max_ratio = design->scratchpad_get_int("peepopt.shiftadd.max_data_multiple", 2);

		// 11 is the A_WIDTH+B_WIDTH ice40_dsp asks for
		muladd_min_product_width = design->scratchpad_get_int("peepopt.muladd.min_product_width", 11);
		muladd_max_chain_depth = design->scratchpad_get_int("peepopt.muladd.max_chain_depth", 64);
		// the walk recurses per level, so an unbounded setting overflows the stack
		muladd_max_chain_depth = std::min(muladd_max_chain_depth, 256);

		for (auto module : design->selected_modules())
		{
			did_something = true;

			while (did_something)
			{
				did_something = false;

				peepopt_pm pm(module);

				pm.setup(module->selected_cells());

				if (formalclk) {
					pm.run_formal_clockgateff();
				} else {
					pm.run_shiftadd();
					pm.run_shiftmul_right();
					pm.run_shiftmul_left();
					pm.run_shiftpow2();
					pm.run_muldiv();
					pm.run_muldiv_c();
					if (!did_something) {
						collect_muladd_bits(pm);
						pm.run_muladd();
					}
				}
			}
		}
	}
} PeepoptPass;

PRIVATE_NAMESPACE_END
