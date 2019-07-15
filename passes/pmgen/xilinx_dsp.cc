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

#include "passes/pmgen/xilinx_dsp_pm.h"

void create_xilinx_dsp(xilinx_dsp_pm &pm)
{
	auto &st = pm.st_xilinx_dsp;

#if 0
	log("\n");
	log("ffA:   %s\n", log_id(st.ffA, "--"));
	log("ffB:   %s\n", log_id(st.ffB, "--"));
	log("mul:   %s\n", log_id(st.mul, "--"));
	log("ffY:   %s\n", log_id(st.ffY, "--"));
#endif

	log("Analysing %s.%s for Xilinx DSP register packing.\n", log_id(pm.module), log_id(st.mul));

	Cell *cell = st.mul;
	log_assert(cell);

	// Input Interface

	cell->setPort("\\A", st.sigA);
	cell->setPort("\\B", st.sigB);

	cell->setParam("\\AREG", st.ffA ? State::S1 : State::S0);
	cell->setParam("\\BREG", st.ffB ? State::S1 : State::S0);

	if (st.clock != SigBit())
	{
		cell->setPort("\\CLK", st.clock);

		if (st.ffA) {
			cell->setParam("\\AREG", State::S1);
			cell->setPort("\\CEA2", State::S1);
		}
		if (st.ffB) {
			cell->setParam("\\BREG", State::S1);
			cell->setPort("\\CEA2", State::S1);
		}
		if (st.ffY) {
			cell->setPort("\\PREG", State::S1);
			cell->setPort("\\CEP", State::S1);
		}

		log("  clock: %s (%s)", log_signal(st.clock), "posedge");

		if (st.ffA)
			log(" ffA:%s", log_id(st.ffA));

		if (st.ffB)
			log(" ffB:%s", log_id(st.ffB));

		if (st.ffY)
			log(" ffY:%s", log_id(st.ffY));

		log("\n");
	}

	// Output Interface

	pm.autoremove(st.ffY);
}

struct Ice40DspPass : public Pass {
	Ice40DspPass() : Pass("xilinx_dsp", "Xilinx: pack DSP registers") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_dsp [options] [selection]\n");
		log("\n");
		log("Pack registers into Xilinx DSPs\n");
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
			xilinx_dsp_pm(module, module->selected_cells()).run_xilinx_dsp(create_xilinx_dsp);
	}
} Ice40DspPass;

PRIVATE_NAMESPACE_END
