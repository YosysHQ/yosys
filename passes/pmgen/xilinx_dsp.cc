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

void pack_xilinx_dsp(xilinx_dsp_pm &pm)
{
	auto &st = pm.st_xilinx_dsp;

#if 1
	log("\n");
	log("ffA:   %s\n", log_id(st.ffA, "--"));
	log("ffB:   %s\n", log_id(st.ffB, "--"));
	log("dsp:   %s\n", log_id(st.dsp, "--"));
	log("ffP:   %s\n", log_id(st.ffP, "--"));
	log("muxP:  %s\n", log_id(st.muxP, "--"));
	log("P_WIDTH:  %d\n", st.P_WIDTH);
#endif

	log("Analysing %s.%s for Xilinx DSP register packing.\n", log_id(pm.module), log_id(st.dsp));

	Cell *cell = st.dsp;
	log_assert(cell);

	if (st.clock != SigBit())
	{
		cell->setPort("\\CLK", st.clock);

		if (st.ffA) {
			SigSpec A = cell->getPort("\\A");
			SigSpec D = st.ffA->getPort("\\D");
			SigSpec Q = st.ffA->getPort("\\Q");
			A.replace(Q, D);
			cell->setPort("\\A", A);
			cell->setParam("\\AREG", State::S1);
			if (st.ffA->type == "$dff")
				cell->setPort("\\CEA2", State::S1);
			else if (st.ffA->type == "$dffe")
				cell->setPort("\\CEA2", st.ffA->getPort("\\EN"));
			else log_abort();
		}
		if (st.ffB) {
			SigSpec B = cell->getPort("\\B");
			SigSpec D = st.ffB->getPort("\\D");
			SigSpec Q = st.ffB->getPort("\\Q");
			B.replace(Q, D);
			cell->setPort("\\B", B);
			cell->setParam("\\BREG", State::S1);
			if (st.ffB->type == "$dff")
				cell->setPort("\\CEB2", State::S1);
			else if (st.ffB->type == "$dffe")
				cell->setPort("\\CEB2", st.ffB->getPort("\\EN"));
			else log_abort();
		}
		if (st.ffP) {
			SigSpec P = cell->getPort("\\P");
			SigSpec Q = st.ffP->getPort("\\Q");
			P.replace(Q, P.extract(0, GetSize(Q)));
			cell->setPort("\\P", Q);
			cell->setParam("\\PREG", State::S1);
			if (st.ffP->type == "$dff")
				cell->setPort("\\CEP", State::S1);
			else if (st.ffP->type == "$dffe")
				cell->setPort("\\CEP", st.ffP->getPort("\\EN"));
			else log_abort();
		}

		log("  clock: %s (%s)", log_signal(st.clock), "posedge");

		if (st.ffA)
			log(" ffA:%s", log_id(st.ffA));

		if (st.ffB)
			log(" ffB:%s", log_id(st.ffB));

		if (st.ffP)
			log(" ffY:%s", log_id(st.ffP));

		log("\n");
	}

	pm.autoremove(st.ffP);
	pm.autoremove(st.muxP);
	pm.blacklist(cell);
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
		log_header(design, "Executing XILINX_DSP pass (pack DSPs).\n");

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
			xilinx_dsp_pm(module, module->selected_cells()).run_xilinx_dsp(pack_xilinx_dsp);
	}
} Ice40DspPass;

PRIVATE_NAMESPACE_END
