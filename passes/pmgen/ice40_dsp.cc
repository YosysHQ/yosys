/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#include "passes/pmgen/ice40_dsp_pm.h"

void create_ice40_dsp(ice40_dsp_pm &pm)
{
	auto &st = pm.st_ice40_dsp;

#if 0
	log("\n");
	log("ffA:   %s\n", log_id(st.ffA, "--"));
	log("ffB:   %s\n", log_id(st.ffB, "--"));
	log("mul:   %s\n", log_id(st.mul, "--"));
	log("ffY:   %s\n", log_id(st.ffY, "--"));
	log("addAB: %s\n", log_id(st.addAB, "--"));
	log("muxAB: %s\n", log_id(st.muxAB, "--"));
	log("ffS:   %s\n", log_id(st.ffS, "--"));
#endif

	log("Checking %s.%s for iCE40 DSP inference.\n", log_id(pm.module), log_id(st.mul));

	if (GetSize(st.sigA) > 16) {
		log("  input A (%s) is too large (%d > 16).\n", log_signal(st.sigA), GetSize(st.sigA));
		return;
	}

	if (GetSize(st.sigB) > 16) {
		log("  input B (%s) is too large (%d > 16).\n", log_signal(st.sigB), GetSize(st.sigB));
		return;
	}

	if (GetSize(st.sigS) > 32) {
		log("  accumulator (%s) is too large (%d > 32).\n", log_signal(st.sigS), GetSize(st.sigS));
		return;
	}

	if (GetSize(st.sigY) > 32) {
		log("  output (%s) is too large (%d > 32).\n", log_signal(st.sigY), GetSize(st.sigY));
		return;
	}

	bool mul_signed = st.mul->getParam("\\A_SIGNED").as_bool();

	if (mul_signed) {
		log("  inference of signed iCE40 DSP arithmetic is currently not supported.\n");
		return;
	}

	log("  replacing $mul with SB_MAC16 cell.\n");

	Cell *cell = pm.module->addCell(NEW_ID, "\\SB_MAC16");
	pm.module->swap_names(cell, st.mul);

	// SB_MAC16 Input Interface

	SigSpec A = st.sigA;
	A.extend_u0(16, mul_signed);

	SigSpec B = st.sigB;
	B.extend_u0(16, mul_signed);

	SigSpec CD;
	if (st.muxA)
		CD = st.muxA->getPort("\\B");
	if (st.muxB)
		CD = st.muxB->getPort("\\A");
	CD.extend_u0(32, mul_signed);

	cell->setPort("\\A", A);
	cell->setPort("\\B", B);
	cell->setPort("\\C", CD.extract(0, 16));
	cell->setPort("\\D", CD.extract(16, 16));

	cell->setParam("\\A_REG", st.ffA ? State::S1 : State::S0);
	cell->setParam("\\B_REG", st.ffB ? State::S1 : State::S0);

	cell->setPort("\\AHOLD", State::S0);
	cell->setPort("\\BHOLD", State::S0);
	cell->setPort("\\CHOLD", State::S0);
	cell->setPort("\\DHOLD", State::S0);

	cell->setPort("\\IRSTTOP", State::S0);
	cell->setPort("\\IRSTBOT", State::S0);

	if (st.clock_vld)
	{
		cell->setPort("\\CLK", st.clock);
		cell->setPort("\\CE", State::S1);
		cell->setParam("\\NEG_TRIGGER", st.clock_pol ? State::S0 : State::S1);

		log("  clock: %s (%s)", log_signal(st.clock), st.clock_pol ? "posedge" : "negedge");

		if (st.ffA)
			log(" ffA:%s", log_id(st.ffA));

		if (st.ffB)
			log(" ffB:%s", log_id(st.ffB));

		if (st.ffY)
			log(" ffY:%s", log_id(st.ffY));

		if (st.ffS)
			log(" ffS:%s", log_id(st.ffS));

		log("\n");
	}
	else
	{
		cell->setPort("\\CLK", State::S0);
		cell->setPort("\\CE", State::S0);
		cell->setParam("\\NEG_TRIGGER", State::S0);
	}

	// SB_MAC16 Cascade Interface

	cell->setPort("\\SIGNEXTIN", State::Sx);
	cell->setPort("\\SIGNEXTOUT", pm.module->addWire(NEW_ID));

	cell->setPort("\\CI", State::Sx);
	cell->setPort("\\CO", pm.module->addWire(NEW_ID));

	cell->setPort("\\ACCUMCI", State::Sx);
	cell->setPort("\\ACCUMCO", pm.module->addWire(NEW_ID));

	// SB_MAC16 Output Interface

	SigSpec O = st.ffS ? st.sigS : st.sigY;
	if (GetSize(O) < 32)
		O.append(pm.module->addWire(NEW_ID, 32-GetSize(O)));

	cell->setPort("\\O", O);

	if (st.addAB) {
		log("  accumulator %s (%s)\n", log_id(st.addAB), log_id(st.addAB->type));
		cell->setPort("\\ADDSUBTOP", st.addAB->type == "$add" ? State::S0 : State::S1);
		cell->setPort("\\ADDSUBBOT", st.addAB->type == "$add" ? State::S0 : State::S1);
	} else {
		cell->setPort("\\ADDSUBTOP", State::S0);
		cell->setPort("\\ADDSUBBOT", State::S0);
	}

	cell->setPort("\\ORSTTOP", State::S0);
	cell->setPort("\\ORSTBOT", State::S0);

	cell->setPort("\\OHOLDTOP", State::S0);
	cell->setPort("\\OHOLDBOT", State::S0);

	SigSpec acc_reset = State::S0;
	if (st.muxA)
		acc_reset = st.muxA->getPort("\\S");
	if (st.muxB)
		acc_reset = pm.module->Not(NEW_ID, st.muxB->getPort("\\S"));

	cell->setPort("\\OLOADTOP", acc_reset);
	cell->setPort("\\OLOADBOT", acc_reset);

	// SB_MAC16 Remaining Parameters

	cell->setParam("\\C_REG", State::S0);
	cell->setParam("\\D_REG", State::S0);

	cell->setParam("\\TOP_8x8_MULT_REG", st.ffY ? State::S1 : State::S0);
	cell->setParam("\\BOT_8x8_MULT_REG", st.ffY ? State::S1 : State::S0);
	cell->setParam("\\PIPELINE_16x16_MULT_REG1", st.ffY ? State::S1 : State::S0);
	cell->setParam("\\PIPELINE_16x16_MULT_REG2", State::S0);

	cell->setParam("\\TOPOUTPUT_SELECT", Const(st.ffS ? 1 : 3, 2));
	cell->setParam("\\TOPADDSUB_LOWERINPUT", Const(2, 2));
	cell->setParam("\\TOPADDSUB_UPPERINPUT", State::S0);
	cell->setParam("\\TOPADDSUB_CARRYSELECT", Const(3, 2));

	cell->setParam("\\BOTOUTPUT_SELECT", Const(st.ffS ? 1 : 3, 2));
	cell->setParam("\\BOTADDSUB_LOWERINPUT", Const(2, 2));
	cell->setParam("\\BOTADDSUB_UPPERINPUT", State::S0);
	cell->setParam("\\BOTADDSUB_CARRYSELECT", Const(0, 2));

	cell->setParam("\\MODE_8x8", State::S0);
	cell->setParam("\\A_SIGNED", mul_signed ? State::S1 : State::S0);
	cell->setParam("\\B_SIGNED", mul_signed ? State::S1 : State::S0);

	pm.autoremove(st.mul);
	pm.autoremove(st.ffY);
	pm.autoremove(st.ffS);
}

struct Ice40DspPass : public Pass {
	Ice40DspPass() : Pass("ice40_dsp", "iCE40: map multipliers") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ice40_dsp [options] [selection]\n");
		log("\n");
		log("Map multipliers and multiply-accumulate blocks to iCE40 DSP resources.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ICE40_DSP pass (map multipliers).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
			ice40_dsp_pm(module, module->selected_cells()).run_ice40_dsp(create_ice40_dsp);
	}
} Ice40DspPass;

PRIVATE_NAMESPACE_END
