/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Eddie Hung    <eddie@fpgeh.com>
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
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/pmgen/xilinx_bram_pm.h"

void xilinx_bram_pack(xilinx_bram_pm &pm) 
{
	auto &st = pm.st_xilinx_bram_pack;
	
	log("Analysing %s.%s for BRAM packing.\n", log_id(pm.module), log_id(st.bram));

	log_debug("ffDOAcemux:	%s\n", log_id(st.ffDOAcemux, "--"));
	log_debug("ffDOBcemux:	%s\n", log_id(st.ffDOBcemux, "--"));
	log_debug("ffDOA:	%s\n", log_id(st.ffDOA, "--"));
	log_debug("ffDOB:	%s\n", log_id(st.ffDOB, "--"));


	Cell *cell = st.bram;

	if(st.ffDOAcemux)
	{
		log("	Enable function: %s (%s)\n", log_id(st.ffDOAcemux), log_id(st.ffDOAcemux->type));
		SigSpec ena = st.ffDOAcemux->getPort(ID(S));
		cell->setPort(ID(REGCEAREGCE), ena);
	}

	if(st.ffDOBcemux)
	{
		log("	Enable function: %s (%s)\n", log_id(st.ffDOBcemux), log_id(st.ffDOBcemux->type));
		SigSpec ena = st.ffDOBcemux->getPort(ID(S));
		cell->setPort(ID(REGCEB), ena);
	}

	if(st.ffDOA) 
	{
		log("	Registers in DOADO port that can be packed: %s (%s)\n", log_id(st.ffDOA), log_id(st.ffDOA->type));
		cell->setParam(ID(DOA_REG), 1);
		cell->setPort(ID(DOADO), st.sigDOA);
		if (st.ffDOPA) 
		{	
			log("	Registers in DOPADOP port that can be packed: %s (%s)\n", log_id(st.ffDOPA), log_id(st.ffDOPA->type));
			cell->setPort(ID(DOPADOP), st.sigDOPA);
		}
	}

	if(st.ffDOB)
	{
		log("	Enable function: %s (%s)\n", log_id(st.ffDOBcemux), log_id(st.ffDOBcemux->type));
		cell->setParam(ID(DOB_REG), 1);
		cell->setPort(ID(DOBDO), st.sigDOB);
	}

}

struct XilinxBramPass: public Pass {
	XilinxBramPass() : Pass("xilinx_bram", "Xilinx: pack flip-flops into BRAM") { }
	void help () YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    xilinx_bram\n");
		log("\n");
		log("Pack A/B output port flops into RAMB18/36E1 primitives\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing XILINX_BRAM pass\n");
		
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			xilinx_bram_pm pm(module, module->selected_cells());
			pm.run_xilinx_bram_pack(xilinx_bram_pack);
		}
	}
} XilinxBramPass;
PRIVATE_NAMESPACE_END
