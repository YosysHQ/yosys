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

	log("Checking %s.%s for iCE40 DSP inference.\n", log_id(pm.module), log_id(st.mul));

	log_debug("ffA:    %s %s %s\n", log_id(st.ffA, "--"), log_id(st.ffAholdmux, "--"), log_id(st.ffArstmux, "--"));
	log_debug("ffB:    %s %s %s\n", log_id(st.ffB, "--"), log_id(st.ffBholdmux, "--"), log_id(st.ffBrstmux, "--"));
	log_debug("ffCD:   %s %s\n", log_id(st.ffCD, "--"), log_id(st.ffCDholdmux, "--"));
	log_debug("mul:    %s\n", log_id(st.mul, "--"));
	log_debug("ffFJKG: %s\n", log_id(st.ffFJKG, "--"));
	log_debug("ffH:    %s\n", log_id(st.ffH, "--"));
	log_debug("add:    %s\n", log_id(st.add, "--"));
	log_debug("mux:    %s\n", log_id(st.mux, "--"));
	log_debug("ffO:    %s %s %s\n", log_id(st.ffO, "--"), log_id(st.ffOholdmux, "--"), log_id(st.ffOrstmux, "--"));
	log_debug("\n");

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
	if (cell->type == ID($mul)) {
		log("  replacing %s with SB_MAC16 cell.\n", log_id(st.mul->type));

		cell = pm.module->addCell(NEW_ID, ID(SB_MAC16));
		pm.module->swap_names(cell, st.mul);
	}
	else log_assert(cell->type == ID(SB_MAC16));

	// SB_MAC16 Input Interface
	SigSpec A = st.sigA;
	A.extend_u0(16, st.mul->parameters.at(ID(A_SIGNED), State::S0).as_bool());
	log_assert(GetSize(A) == 16);

	SigSpec B = st.sigB;
	B.extend_u0(16, st.mul->parameters.at(ID(B_SIGNED), State::S0).as_bool());
	log_assert(GetSize(B) == 16);

	SigSpec CD = st.sigCD;
	if (CD.empty())
		CD = RTLIL::Const(0, 32);
	else
		log_assert(GetSize(CD) == 32);

	cell->setPort(ID::A, A);
	cell->setPort(ID::B, B);
	cell->setPort(ID(C), CD.extract(16, 16));
	cell->setPort(ID(D), CD.extract(0, 16));

	cell->setParam(ID(A_REG), st.ffA ? State::S1 : State::S0);
	cell->setParam(ID(B_REG), st.ffB ? State::S1 : State::S0);
	cell->setParam(ID(C_REG), st.ffCD ? State::S1 : State::S0);
	cell->setParam(ID(D_REG), st.ffCD ? State::S1 : State::S0);

	SigSpec AHOLD, BHOLD, CDHOLD;
	if (st.ffAholdmux)
		AHOLD = st.ffAholdpol ? st.ffAholdmux->getPort(ID(S)) : pm.module->Not(NEW_ID, st.ffAholdmux->getPort(ID(S)));
	else
		AHOLD = State::S0;
	if (st.ffBholdmux)
		BHOLD = st.ffBholdpol ? st.ffBholdmux->getPort(ID(S)) : pm.module->Not(NEW_ID, st.ffBholdmux->getPort(ID(S)));
	else
		BHOLD = State::S0;
	if (st.ffCDholdmux)
		CDHOLD = st.ffCDholdpol ? st.ffCDholdmux->getPort(ID(S)) : pm.module->Not(NEW_ID, st.ffCDholdmux->getPort(ID(S)));
	else
		CDHOLD = State::S0;
	cell->setPort(ID(AHOLD), AHOLD);
	cell->setPort(ID(BHOLD), BHOLD);
	cell->setPort(ID(CHOLD), CDHOLD);
	cell->setPort(ID(DHOLD), CDHOLD);

	SigSpec IRSTTOP, IRSTBOT;
	if (st.ffArstmux)
		IRSTTOP = st.ffArstpol ? st.ffArstmux->getPort(ID(S)) : pm.module->Not(NEW_ID, st.ffArstmux->getPort(ID(S)));
	else
		IRSTTOP = State::S0;
	if (st.ffBrstmux)
		IRSTBOT = st.ffBrstpol ? st.ffBrstmux->getPort(ID(S)) : pm.module->Not(NEW_ID, st.ffBrstmux->getPort(ID(S)));
	else
		IRSTBOT = State::S0;
	cell->setPort(ID(IRSTTOP), IRSTTOP);
	cell->setPort(ID(IRSTBOT), IRSTBOT);

	if (st.clock != SigBit())
	{
		cell->setPort(ID(CLK), st.clock);
		cell->setPort(ID(CE), State::S1);
		cell->setParam(ID(NEG_TRIGGER), st.clock_pol ? State::S0 : State::S1);

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
		cell->setPort(ID(CLK), State::S0);
		cell->setPort(ID(CE), State::S0);
		cell->setParam(ID(NEG_TRIGGER), State::S0);
	}

	// SB_MAC16 Cascade Interface

	cell->setPort(ID(SIGNEXTIN), State::Sx);
	cell->setPort(ID(SIGNEXTOUT), pm.module->addWire(NEW_ID));

	cell->setPort(ID(CI), State::Sx);

	cell->setPort(ID(ACCUMCI), State::Sx);
	cell->setPort(ID(ACCUMCO), pm.module->addWire(NEW_ID));

	// SB_MAC16 Output Interface

	SigSpec O = st.sigO;
	int O_width = GetSize(O);
	if (O_width == 33) {
		log_assert(st.add);
		// If we have a signed multiply-add, then perform sign extension
		if (st.add->getParam(ID(A_SIGNED)).as_bool() && st.add->getParam(ID(B_SIGNED)).as_bool())
			pm.module->connect(O[32], O[31]);
		else
			cell->setPort(ID(CO), O[32]);
		O.remove(O_width-1);
	}
	else
		cell->setPort(ID(CO), pm.module->addWire(NEW_ID));
	log_assert(GetSize(O) <= 32);
	if (GetSize(O) < 32)
		O.append(pm.module->addWire(NEW_ID, 32-GetSize(O)));

	cell->setPort(ID(O), O);

	bool accum = false;
	if (st.add) {
		accum = (st.ffO && st.add->getPort(st.addAB == ID::A ? ID::B : ID::A) == st.sigO);
		if (accum)
			log("  accumulator %s (%s)\n", log_id(st.add), log_id(st.add->type));
		else
			log("  adder %s (%s)\n", log_id(st.add), log_id(st.add->type));
		cell->setPort(ID(ADDSUBTOP), st.add->type == ID($add) ? State::S0 : State::S1);
		cell->setPort(ID(ADDSUBBOT), st.add->type == ID($add) ? State::S0 : State::S1);
	} else {
		cell->setPort(ID(ADDSUBTOP), State::S0);
		cell->setPort(ID(ADDSUBBOT), State::S0);
	}

	SigSpec OHOLD;
	if (st.ffOholdmux)
		OHOLD = st.ffOholdpol ? st.ffOholdmux->getPort(ID(S)) : pm.module->Not(NEW_ID, st.ffOholdmux->getPort(ID(S)));
	else
		OHOLD = State::S0;
	cell->setPort(ID(OHOLDTOP), OHOLD);
	cell->setPort(ID(OHOLDBOT), OHOLD);

	SigSpec ORST;
	if (st.ffOrstmux)
		ORST = st.ffOrstpol ? st.ffOrstmux->getPort(ID(S)) : pm.module->Not(NEW_ID, st.ffOrstmux->getPort(ID(S)));
	else
		ORST = State::S0;
	cell->setPort(ID(ORSTTOP), ORST);
	cell->setPort(ID(ORSTBOT), ORST);

	SigSpec acc_reset = State::S0;
	if (st.mux) {
		if (st.muxAB == ID::A)
			acc_reset = st.mux->getPort(ID(S));
		else
			acc_reset = pm.module->Not(NEW_ID, st.mux->getPort(ID(S)));
	}
	cell->setPort(ID(OLOADTOP), acc_reset);
	cell->setPort(ID(OLOADBOT), acc_reset);

	// SB_MAC16 Remaining Parameters

	cell->setParam(ID(TOP_8x8_MULT_REG), st.ffFJKG ? State::S1 : State::S0);
	cell->setParam(ID(BOT_8x8_MULT_REG), st.ffFJKG ? State::S1 : State::S0);
	cell->setParam(ID(PIPELINE_16x16_MULT_REG1), st.ffFJKG ? State::S1 : State::S0);
	cell->setParam(ID(PIPELINE_16x16_MULT_REG2), st.ffH ? State::S1 : State::S0);

	cell->setParam(ID(TOPADDSUB_LOWERINPUT), Const(2, 2));
	cell->setParam(ID(TOPADDSUB_UPPERINPUT), accum ? State::S0 : State::S1);
	cell->setParam(ID(TOPADDSUB_CARRYSELECT), Const(3, 2));

	cell->setParam(ID(BOTADDSUB_LOWERINPUT), Const(2, 2));
	cell->setParam(ID(BOTADDSUB_UPPERINPUT), accum ? State::S0 : State::S1);
	cell->setParam(ID(BOTADDSUB_CARRYSELECT), Const(0, 2));

	cell->setParam(ID(MODE_8x8), State::S0);
	cell->setParam(ID(A_SIGNED), st.mul->parameters.at(ID(A_SIGNED), State::S0).as_bool());
	cell->setParam(ID(B_SIGNED), st.mul->parameters.at(ID(B_SIGNED), State::S0).as_bool());

	if (st.ffO) {
		if (st.o_lo)
			cell->setParam(ID(TOPOUTPUT_SELECT), Const(st.add ? 0 : 3, 2));
		else
			cell->setParam(ID(TOPOUTPUT_SELECT), Const(1, 2));

		st.ffO->connections_.at(ID(Q)).replace(O, pm.module->addWire(NEW_ID, GetSize(O)));
		cell->setParam(ID(BOTOUTPUT_SELECT), Const(1, 2));
	}
	else {
		cell->setParam(ID(TOPOUTPUT_SELECT), Const(st.add ? 0 : 3, 2));
		cell->setParam(ID(BOTOUTPUT_SELECT), Const(st.add ? 0 : 3, 2));
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
		log("Map multipliers ($mul/SB_MAC16) and multiply-accumulate ($mul/SB_MAC16 + $add)\n");
		log("cells into iCE40 DSP resources.\n");
		log("Currently, only the 16x16 multiply mode is supported and not the 2 x 8x8 mode.\n");
		log("\n");
		log("Pack input registers (A, B, {C,D}; with optional hold), pipeline registers\n");
		log("({F,J,K,G}, H), output registers (O -- full 32-bits or lower 16-bits only; with\n");
		log("optional hold), and post-adder into into the SB_MAC16 resource.\n");
		log("\n");
		log("Multiply-accumulate operations using the post-adder with feedback on the {C,D}\n");
		log("input will be folded into the DSP. In this scenario only, resetting the\n");
		log("the accumulator to an arbitrary value can be inferred to use the {C,D} input.\n");
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
