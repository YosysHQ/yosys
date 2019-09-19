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

#if 1
	log("\n");
	log("ffA:    %s %s %s\n", log_id(st.ffA, "--"), log_id(st.ffAholdmux, "--"), log_id(st.ffArstmux, "--"));
	log("ffB:    %s %s %s\n", log_id(st.ffB, "--"), log_id(st.ffBholdmux, "--"), log_id(st.ffBrstmux, "--"));
	log("ffCD:   %s %s\n", log_id(st.ffCD, "--"), log_id(st.ffCDholdmux, "--"));
	log("mul:    %s\n", log_id(st.mul, "--"));
	log("ffFJKG: %s\n", log_id(st.ffFJKG, "--"));
	log("ffH:    %s\n", log_id(st.ffH, "--"));
	log("add:    %s\n", log_id(st.add, "--"));
	log("mux:    %s\n", log_id(st.mux, "--"));
	log("ffO:    %s %s %s\n", log_id(st.ffO, "--"), log_id(st.ffOholdmux, "--"), log_id(st.ffOrstmux, "--"));
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

	if (GetSize(st.sigO) > 33) {
		log("  adder/accumulator (%s) is too large (%d > 33).\n", log_signal(st.sigO), GetSize(st.sigO));
		return;
	}

	if (GetSize(st.sigH) > 32) {
		log("  output (%s) is too large (%d > 32).\n", log_signal(st.sigH), GetSize(st.sigH));
		return;
	}

	Cell *cell = st.mul;
	if (cell->type == "$mul") {
		log("  replacing %s with SB_MAC16 cell.\n", log_id(st.mul->type));

		cell = pm.module->addCell(NEW_ID, "\\SB_MAC16");
		pm.module->swap_names(cell, st.mul);
	}
	else log_assert(cell->type == "\\SB_MAC16");

	// SB_MAC16 Input Interface
	SigSpec A = st.sigA;
	A.extend_u0(16, st.mul->getParam("\\A_SIGNED").as_bool());
	log_assert(GetSize(A) == 16);

	SigSpec B = st.sigB;
	B.extend_u0(16, st.mul->getParam("\\B_SIGNED").as_bool());
	log_assert(GetSize(B) == 16);

	SigSpec CD = st.sigCD;
	if (CD.empty())
		CD = RTLIL::Const(0, 32);
	else
		log_assert(GetSize(CD) == 32);

	cell->setPort("\\A", A);
	cell->setPort("\\B", B);
	cell->setPort("\\C", CD.extract(16, 16));
	cell->setPort("\\D", CD.extract(0, 16));

	cell->setParam("\\A_REG", st.ffA ? State::S1 : State::S0);
	cell->setParam("\\B_REG", st.ffB ? State::S1 : State::S0);
	cell->setParam("\\C_REG", st.ffCD ? State::S1 : State::S0);
	cell->setParam("\\D_REG", st.ffCD ? State::S1 : State::S0);

	SigSpec AHOLD, BHOLD, CDHOLD;
	if (st.ffAholdmux)
		AHOLD = st.ffAholdpol ? st.ffAholdmux->getPort("\\S") : pm.module->Not(NEW_ID, st.ffAholdmux->getPort("\\S"));
	else
		AHOLD = State::S0;
	if (st.ffBholdmux)
		BHOLD = st.ffBholdpol ? st.ffBholdmux->getPort("\\S") : pm.module->Not(NEW_ID, st.ffBholdmux->getPort("\\S"));
	else
		BHOLD = State::S0;
	if (st.ffCDholdmux)
		CDHOLD = st.ffCDholdpol ? st.ffCDholdmux->getPort("\\S") : pm.module->Not(NEW_ID, st.ffCDholdmux->getPort("\\S"));
	else
		CDHOLD = State::S0;
	cell->setPort("\\AHOLD", AHOLD);
	cell->setPort("\\BHOLD", BHOLD);
	cell->setPort("\\CHOLD", CDHOLD);
	cell->setPort("\\DHOLD", CDHOLD);

	SigSpec IRSTTOP, IRSTBOT;
	if (st.ffArstmux)
		IRSTTOP = st.ffArstpol ? st.ffArstmux->getPort("\\S") : pm.module->Not(NEW_ID, st.ffArstmux->getPort("\\S"));
	else
		IRSTTOP = State::S0;
	if (st.ffBrstmux)
		IRSTBOT = st.ffBrstpol ? st.ffBrstmux->getPort("\\S") : pm.module->Not(NEW_ID, st.ffBrstmux->getPort("\\S"));
	else
		IRSTBOT = State::S0;
	cell->setPort("\\IRSTTOP", IRSTTOP);
	cell->setPort("\\IRSTBOT", IRSTBOT);

	if (st.clock != SigBit())
	{
		cell->setPort("\\CLK", st.clock);
		cell->setPort("\\CE", State::S1);
		cell->setParam("\\NEG_TRIGGER", st.clock_pol ? State::S0 : State::S1);

		log("  clock: %s (%s)", log_signal(st.clock), st.clock_pol ? "posedge" : "negedge");

		if (st.ffA)
			log(" ffA:%s", log_id(st.ffA));

		if (st.ffB)
			log(" ffB:%s", log_id(st.ffB));

		if (st.ffCD)
			log(" ffCD:%s", log_id(st.ffCD));

		if (st.ffFJKG)
			log(" ffFJKG:%s", log_id(st.ffFJKG));

		if (st.ffH)
			log(" ffH:%s", log_id(st.ffH));

		if (st.ffO)
			log(" ffO:%s", log_id(st.ffO));

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

	cell->setPort("\\ACCUMCI", State::Sx);
	cell->setPort("\\ACCUMCO", pm.module->addWire(NEW_ID));

	// SB_MAC16 Output Interface

	SigSpec O = st.sigO;
	int O_width = GetSize(O);
	if (O_width == 33) {
		log_assert(st.add);
		// If we have a signed multiply-add, then perform sign extension
		if (st.add->getParam("\\A_SIGNED").as_bool() && st.add->getParam("\\B_SIGNED").as_bool())
			pm.module->connect(O[32], O[31]);
		else
			cell->setPort("\\CO", O[32]);
		O.remove(O_width-1);
	}
	else
		cell->setPort("\\CO", pm.module->addWire(NEW_ID));
	log_assert(GetSize(O) <= 32);
	if (GetSize(O) < 32)
		O.append(pm.module->addWire(NEW_ID, 32-GetSize(O)));

	cell->setPort("\\O", O);

	bool accum = false;
	if (st.add) {
		accum = (st.ffO && st.add->getPort(st.addAB == "\\A" ? "\\B" : "\\A") == st.sigO);
		if (accum)
			log("  accumulator %s (%s)\n", log_id(st.add), log_id(st.add->type));
		else
			log("  adder %s (%s)\n", log_id(st.add), log_id(st.add->type));
		cell->setPort("\\ADDSUBTOP", st.add->type == "$add" ? State::S0 : State::S1);
		cell->setPort("\\ADDSUBBOT", st.add->type == "$add" ? State::S0 : State::S1);
	} else {
		cell->setPort("\\ADDSUBTOP", State::S0);
		cell->setPort("\\ADDSUBBOT", State::S0);
	}

	SigSpec OHOLD;
	if (st.ffOholdmux)
		OHOLD = st.ffOholdpol ? st.ffOholdmux->getPort("\\S") : pm.module->Not(NEW_ID, st.ffOholdmux->getPort("\\S"));
	else
		OHOLD = State::S0;
	cell->setPort("\\OHOLDTOP", OHOLD);
	cell->setPort("\\OHOLDBOT", OHOLD);

	SigSpec ORST;
	if (st.ffOrstmux)
		ORST = st.ffOrstpol ? st.ffOrstmux->getPort("\\S") : pm.module->Not(NEW_ID, st.ffOrstmux->getPort("\\S"));
	else
		ORST = State::S0;
	cell->setPort("\\ORSTTOP", ORST);
	cell->setPort("\\ORSTBOT", ORST);

	SigSpec acc_reset = State::S0;
	if (st.mux) {
		if (st.muxAB == "\\A")
			acc_reset = st.mux->getPort("\\S");
		else
			acc_reset = pm.module->Not(NEW_ID, st.mux->getPort("\\S"));
	}
	cell->setPort("\\OLOADTOP", acc_reset);
	cell->setPort("\\OLOADBOT", acc_reset);

	// SB_MAC16 Remaining Parameters

	cell->setParam("\\TOP_8x8_MULT_REG", st.ffFJKG ? State::S1 : State::S0);
	cell->setParam("\\BOT_8x8_MULT_REG", st.ffFJKG ? State::S1 : State::S0);
	cell->setParam("\\PIPELINE_16x16_MULT_REG1", st.ffFJKG ? State::S1 : State::S0);
	cell->setParam("\\PIPELINE_16x16_MULT_REG2", st.ffH ? State::S1 : State::S0);

	cell->setParam("\\TOPADDSUB_LOWERINPUT", Const(2, 2));
	cell->setParam("\\TOPADDSUB_UPPERINPUT", accum ? State::S0 : State::S1);
	cell->setParam("\\TOPADDSUB_CARRYSELECT", Const(3, 2));

	cell->setParam("\\BOTADDSUB_LOWERINPUT", Const(2, 2));
	cell->setParam("\\BOTADDSUB_UPPERINPUT", accum ? State::S0 : State::S1);
	cell->setParam("\\BOTADDSUB_CARRYSELECT", Const(0, 2));

	cell->setParam("\\MODE_8x8", State::S0);
	cell->setParam("\\A_SIGNED", st.mul->getParam("\\A_SIGNED").as_bool());
	cell->setParam("\\B_SIGNED", st.mul->getParam("\\B_SIGNED").as_bool());

	if (st.ffO) {
		if (st.o_lo)
			cell->setParam("\\TOPOUTPUT_SELECT", Const(st.add ? 0 : 3, 2));
		else
			cell->setParam("\\TOPOUTPUT_SELECT", Const(1, 2));

		st.ffO->connections_.at("\\Q").replace(O, pm.module->addWire(NEW_ID, GetSize(O)));
		cell->setParam("\\BOTOUTPUT_SELECT", Const(1, 2));
	}
	else {
		cell->setParam("\\TOPOUTPUT_SELECT", Const(st.add ? 0 : 3, 2));
		cell->setParam("\\BOTOUTPUT_SELECT", Const(st.add ? 0 : 3, 2));
	}

	if (cell != st.mul)
		pm.autoremove(st.mul);
	else
		pm.blacklist(st.mul);
	pm.autoremove(st.ffFJKG);
	pm.autoremove(st.add);
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
		log("Currently, only the 16x16 multiply mode is supported and not the 2 x 8x8 mode.\n");
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
