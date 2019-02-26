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
#include "passes/pmgen/ice40_dsp_pm.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void create_ice40_dsp(ice40_dsp_pm &pm)
{
#if 0
	log("\n");
	log("ffA:   %s\n", log_id(pm.st.ffA, "--"));
	log("ffB:   %s\n", log_id(pm.st.ffB, "--"));
	log("mul:   %s\n", log_id(pm.st.mul, "--"));
	log("ffY:   %s\n", log_id(pm.st.ffY, "--"));
	log("addAB: %s\n", log_id(pm.st.addAB, "--"));
	log("muxAB: %s\n", log_id(pm.st.muxAB, "--"));
	log("ffS:   %s\n", log_id(pm.st.ffS, "--"));
#endif

	log("Checking %s.%s for iCE40 DSP inference.\n", log_id(pm.module), log_id(pm.st.mul));

	if (GetSize(pm.st.sigA) > 16) {
		log("  input A (%s) is too large (%d > 16).\n", log_signal(pm.st.sigA), GetSize(pm.st.sigA));
		return;
	}

	if (GetSize(pm.st.sigB) > 16) {
		log("  input B (%s) is too large (%d > 16).\n", log_signal(pm.st.sigB), GetSize(pm.st.sigB));
		return;
	}

	if (GetSize(pm.st.sigS) > 32) {
		log("  accumulator (%s) is too large (%d > 32).\n", log_signal(pm.st.sigS), GetSize(pm.st.sigS));
		return;
	}

	if (GetSize(pm.st.sigY) > 32) {
		log("  output (%s) is too large (%d > 32).\n", log_signal(pm.st.sigY), GetSize(pm.st.sigY));
		return;
	}

	bool mul_signed = pm.st.mul->getParam("\\A_SIGNED").as_bool();

	if (mul_signed) {
		log("  inference of signed iCE40 DSP arithmetic is currently not supported.\n");
		return;
	}

	log("  replacing $mul with SB_MAC16 cell.\n");

	Cell *cell = pm.module->addCell(NEW_ID, "\\SB_MAC16");
	pm.module->swap_names(cell, pm.st.mul);

	// SB_MAC16 Input Interface

	SigSpec A = pm.st.sigA;
	A.extend_u0(16, mul_signed);

	SigSpec B = pm.st.sigB;
	B.extend_u0(16, mul_signed);

	SigSpec CD;
	if (pm.st.muxA)
		CD = pm.st.muxA->getPort("\\B");
	if (pm.st.muxB)
		CD = pm.st.muxB->getPort("\\A");
	CD.extend_u0(32, mul_signed);

	cell->setPort("\\A", A);
	cell->setPort("\\B", B);
	cell->setPort("\\C", CD.extract(0, 16));
	cell->setPort("\\D", CD.extract(16, 16));

	cell->setParam("\\A_REG", pm.st.ffA ? State::S1 : State::S0);
	cell->setParam("\\B_REG", pm.st.ffB ? State::S1 : State::S0);

	cell->setPort("\\AHOLD", State::S0);
	cell->setPort("\\BHOLD", State::S0);
	cell->setPort("\\CHOLD", State::S0);
	cell->setPort("\\DHOLD", State::S0);

	cell->setPort("\\IRSTTOP", State::S0);
	cell->setPort("\\IRSTBOT", State::S0);

	if (pm.st.clock_vld)
	{
		cell->setPort("\\CLK", pm.st.clock);
		cell->setPort("\\CE", State::S1);
		cell->setParam("\\NEG_TRIGGER", pm.st.clock_pol ? State::S0 : State::S1);

		log("  clock: %s (%s)", log_signal(pm.st.clock), pm.st.clock_pol ? "posedge" : "negedge");

		if (pm.st.ffA)
			log(" ffA:%s", log_id(pm.st.ffA));

		if (pm.st.ffB)
			log(" ffB:%s", log_id(pm.st.ffB));

		if (pm.st.ffY)
			log(" ffY:%s", log_id(pm.st.ffY));

		if (pm.st.ffS)
			log(" ffS:%s", log_id(pm.st.ffS));

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

	SigSpec O = pm.st.ffS ? pm.st.sigS : pm.st.sigY;
	if (GetSize(O) < 32)
		O.append(pm.module->addWire(NEW_ID, 32-GetSize(O)));

	cell->setPort("\\O", O);

	if (pm.st.addAB) {
		log("  accumulator %s (%s)\n", log_id(pm.st.addAB), log_id(pm.st.addAB->type));
		cell->setPort("\\ADDSUBTOP", pm.st.addAB->type == "$add" ? State::S0 : State::S1);
		cell->setPort("\\ADDSUBBOT", pm.st.addAB->type == "$add" ? State::S0 : State::S1);
	} else {
		cell->setPort("\\ADDSUBTOP", State::S0);
		cell->setPort("\\ADDSUBBOT", State::S0);
	}

	cell->setPort("\\ORSTTOP", State::S0);
	cell->setPort("\\ORSTBOT", State::S0);

	cell->setPort("\\OHOLDTOP", State::S0);
	cell->setPort("\\OHOLDBOT", State::S0);

	SigSpec acc_reset = State::S0;
	if (pm.st.muxA)
		acc_reset = pm.st.muxA->getPort("\\S");
	if (pm.st.muxB)
		acc_reset = pm.module->Not(NEW_ID, pm.st.muxB->getPort("\\S"));

	cell->setPort("\\OLOADTOP", acc_reset);
	cell->setPort("\\OLOADBOT", acc_reset);

	// SB_MAC16 Remaining Parameters

	cell->setParam("\\C_REG", State::S0);
	cell->setParam("\\D_REG", State::S0);

	cell->setParam("\\TOP_8x8_MULT_REG", pm.st.ffY ? State::S1 : State::S0);
	cell->setParam("\\BOT_8x8_MULT_REG", pm.st.ffY ? State::S1 : State::S0);
	cell->setParam("\\PIPELINE_16x16_MULT_REG1", pm.st.ffY ? State::S1 : State::S0);
	cell->setParam("\\PIPELINE_16x16_MULT_REG2", State::S0);

	cell->setParam("\\TOPOUTPUT_SELECT", Const(pm.st.ffS ? 1 : 3, 2));
	cell->setParam("\\TOPADDSUB_LOWERINPUT", Const(2, 2));
	cell->setParam("\\TOPADDSUB_UPPERINPUT", State::S0);
	cell->setParam("\\TOPADDSUB_CARRYSELECT", Const(3, 2));

	cell->setParam("\\BOTOUTPUT_SELECT", Const(pm.st.ffS ? 1 : 3, 2));
	cell->setParam("\\BOTADDSUB_LOWERINPUT", Const(2, 2));
	cell->setParam("\\BOTADDSUB_UPPERINPUT", State::S0);
	cell->setParam("\\BOTADDSUB_CARRYSELECT", Const(0, 2));

	cell->setParam("\\MODE_8x8", State::S0);
	cell->setParam("\\A_SIGNED", mul_signed ? State::S1 : State::S0);
	cell->setParam("\\B_SIGNED", mul_signed ? State::S1 : State::S0);

	pm.autoremove(pm.st.mul);
	pm.autoremove(pm.st.ffY);
	pm.autoremove(pm.st.ffS);
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
			ice40_dsp_pm(module, module->selected_cells()).run(create_ice40_dsp);
	}
} Ice40DspPass;

PRIVATE_NAMESPACE_END
