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

template<class T> bool includes(const T &lhs, const T &rhs) {
	return std::includes(lhs.begin(), lhs.end(), rhs.begin(), rhs.end());
}
#include "passes/pmgen/ice40_dsp_pm.h"

void create_ice40_dsp(ice40_dsp_pm &pm)
{
	auto &st = pm.st_ice40_dsp;

#if 1
	log("\n");
	log("ffA:    %s\n", log_id(st.ffA, "--"));
	log("ffB:    %s\n", log_id(st.ffB, "--"));
	log("mul:    %s\n", log_id(st.mul, "--"));
	log("ffH:    %s\n", log_id(st.ffH, "--"));
	log("addAB:  %s\n", log_id(st.addAB, "--"));
	log("muxAB:  %s\n", log_id(st.muxAB, "--"));
	log("ffO_lo: %s\n", log_id(st.ffO_lo, "--"));
	log("ffO_hi: %s\n", log_id(st.ffO_hi, "--"));
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

	if (GetSize(st.sigO) > 32) {
		log("  accumulator (%s) is too large (%d > 32).\n", log_signal(st.sigO), GetSize(st.sigO));
		return;
	}

	if (GetSize(st.sigH) > 32) {
		log("  output (%s) is too large (%d > 32).\n", log_signal(st.sigH), GetSize(st.sigH));
		return;
	}

	log("  replacing %s with SB_MAC16 cell.\n", log_id(st.mul->type));

	Cell *cell = pm.module->addCell(NEW_ID, "\\SB_MAC16");
	pm.module->swap_names(cell, st.mul);

	// SB_MAC16 Input Interface
	bool a_signed = st.mul->getParam("\\A_SIGNED").as_bool();
	bool b_signed = st.mul->getParam("\\B_SIGNED").as_bool();

	SigSpec A = st.sigA;
	A.extend_u0(16, a_signed);

	SigSpec B = st.sigB;
	B.extend_u0(16, b_signed);

	SigSpec CD;
	bool CD_signed = false;
	if (st.muxAB != st.addAB) {
		if (st.muxA)
			CD = st.muxA->getPort("\\B");
		else if (st.muxB)
			CD = st.muxB->getPort("\\A");
		else log_abort();
		CD_signed = a_signed && b_signed; // TODO: Do muxes have [AB]_SIGNED?
	}
	else if (st.addAB) {
		if (st.addA)
			CD = st.addAB->getPort("\\B");
		else if (st.addB)
			CD = st.addAB->getPort("\\A");
		else log_abort();
		CD_signed = st.sigO_signed;
	}
	CD.extend_u0(32, CD_signed);

	cell->setPort("\\A", A);
	cell->setPort("\\B", B);
	cell->setPort("\\C", CD.extract(16, 16));
	cell->setPort("\\D", CD.extract(0, 16));

	cell->setParam("\\A_REG", st.ffA ? State::S1 : State::S0);
	cell->setParam("\\B_REG", st.ffB ? State::S1 : State::S0);

	cell->setPort("\\AHOLD", State::S0);
	cell->setPort("\\BHOLD", State::S0);
	cell->setPort("\\CHOLD", State::S0);
	cell->setPort("\\DHOLD", State::S0);

	cell->setPort("\\IRSTTOP", State::S0);
	cell->setPort("\\IRSTBOT", State::S0);

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

		if (st.ffH)
			log(" ffH:%s", log_id(st.ffH));

		if (st.ffO_lo)
			log(" ffO_lo:%s", log_id(st.ffO_lo));
		if (st.ffO_hi)
			log(" ffO_hi:%s", log_id(st.ffO_hi));

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

	SigSpec O_lo = (st.ffO_lo ? st.sigO : (st.addAB ? st.addAB->getPort("\\Y") : st.sigH)).extract(0,16);
	if (GetSize(O_lo) < 16)
		O_lo.append(pm.module->addWire(NEW_ID, 16-GetSize(O_lo)));
	SigSpec O_hi = (st.ffO_hi ? st.sigO : (st.addAB ? st.addAB->getPort("\\Y") : st.sigH)).extract(16,16);
	if (GetSize(O_hi) < 16)
		O_hi.append(pm.module->addWire(NEW_ID, 16-GetSize(O_hi)));

	SigSpec O{O_hi,O_lo};
	cell->setPort("\\O", O);

	bool accum = false;
	if (st.addAB) {
                if (st.addA)
                      accum = (st.ffO_lo && st.ffO_hi && st.addAB->getPort("\\B") == O);
                else if (st.addB)
                      accum = (st.ffO_lo && st.ffO_hi && st.addAB->getPort("\\A") == O);
                else log_abort();
                if (accum)
                        log("  accumulator %s (%s)\n", log_id(st.addAB), log_id(st.addAB->type));
                else
                        log("  adder %s (%s)\n", log_id(st.addAB), log_id(st.addAB->type));
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

	cell->setParam("\\TOP_8x8_MULT_REG", st.ffH ? State::S1 : State::S0);
	cell->setParam("\\BOT_8x8_MULT_REG", st.ffH ? State::S1 : State::S0);
	cell->setParam("\\PIPELINE_16x16_MULT_REG1", st.ffH ? State::S1 : State::S0);
	cell->setParam("\\PIPELINE_16x16_MULT_REG2", State::S0);

	cell->setParam("\\TOPOUTPUT_SELECT", Const(st.ffO_hi ? 1 : (st.addAB ? 0 : 3), 2));
	cell->setParam("\\TOPADDSUB_LOWERINPUT", Const(2, 2));
	cell->setParam("\\TOPADDSUB_UPPERINPUT", accum ? State::S0 : State::S1);
	cell->setParam("\\TOPADDSUB_CARRYSELECT", Const(3, 2));

	cell->setParam("\\BOTOUTPUT_SELECT", Const(st.ffO_lo ? 1 : (st.addAB ? 0 : 3), 2));
	cell->setParam("\\BOTADDSUB_LOWERINPUT", Const(2, 2));
	cell->setParam("\\BOTADDSUB_UPPERINPUT", accum ? State::S0 : State::S1);
	cell->setParam("\\BOTADDSUB_CARRYSELECT", Const(0, 2));

	cell->setParam("\\MODE_8x8", State::S0);
	cell->setParam("\\A_SIGNED", a_signed);
	cell->setParam("\\B_SIGNED", b_signed);

	pm.autoremove(st.mul);
	pm.autoremove(st.ffH);
	pm.autoremove(st.addAB);
        if (st.ffO_lo)
                st.ffO_lo->connections_.at("\\Q").replace(O.extract(0,16), pm.module->addWire(NEW_ID, 16));
        if (st.ffO_hi)
                st.ffO_hi->connections_.at("\\Q").replace(O.extract(16,16), pm.module->addWire(NEW_ID, 16));
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
