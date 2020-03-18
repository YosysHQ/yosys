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
	log_debug("ffDOArstmux: %s\n", log_id(st.ffADrstmux, "--"));
	log_debug("ffDOBrstmux: %s\n", log_id(st.ffBDrstmux, "--"));
	log_debug("ffDOA:	%s\n", log_id(st.ffDOA, "--"));
	log_debug("ffDOB:	%s\n", log_id(st.ffDOB, "--"));

	Cell *cell = st.bram;

	auto replace = [&pm, cell] (SigSpec &source, Cell* cemux, Cell* rstmux, bool cepol, bool rstpol, IdString cetarget, IdString rsttarget) {
		if (rstmux)
		{
			source.replace(pm.sigmap(rstmux->getPort(rstpol ? ID::A : ID::B)),
		   	         rstmux->getPort(ID::Y));
			log("Merging Reset function: %s (%s) into BRAM %s port %s.\n",
				   log_id(rstmux), log_id(rstmux->type), log_id(cell), log_id(rsttarget));
		   	SigSpec S = rstmux->getPort(ID(S));
		   	cell->setPort(rsttarget, rstpol ? S : pm.module->Not(NEW_ID, S));
		}

		if (cemux)
		{
			source.replace(pm.sigmap(cemux->getPort(cepol ? ID::B : ID::A)),
				 cemux->getPort(ID::Y));
			log("Merging Enable function: %s (%s) into BRAM %s port %s.\n",
				    log_id(cemux), log_id(cemux->type), log_id(cell), log_id(cetarget));
			SigSpec S = cemux->getPort(ID(S));
			cell->setPort(cetarget, cepol ?  S : pm.module->Not(NEW_ID, S));

		}

	};

	if (st.ffDOA) {
		log("Candidate registers in DOADO port to pack into BRAM cell: %s (%s).\n",
				log_id(st.ffDOA), log_id(st.ffDOA->type));

		SigSpec DOADO = cell->getPort(ID(DOADO));
		SigSpec Q = st.ffDOA->getPort(ID(Q));

		replace (DOADO, st.ffDOAcemux, st.ffADrstmux, st.ffDOAcepol, st.ffADrstpol, ID(REGCEAREGCE), ID(RSTRAMB));

		// BRAM DO port flops have been packed. Setting the DOx_REG register to 1, reflecting this change into the cell.
		cell->setParam(ID(DOA_REG), 1);
		// Since output flops will be optimised away due packing, its consumers (loads) needs to be connected (moved) to DO port.
		// At this point, ce and/or rst functionallity is already connected to the corresponding BRAM input port.
		DOADO.replace(pm.sigmap(st.ffDOA->getPort(ID(D))), st.ffDOA->getPort(ID(Q)));
		cell->setPort(ID(DOADO), DOADO);

		// Flop.Q driver has been moved to BRAM.DO port. Adding dummy wires to it.
		Q.replace(st.sigDOA, pm.module->addWire(NEW_ID, GetSize(st.sigDOA)));
		st.ffDOA->setPort(ID(Q), Q);

		// The modification in Flop.Q needs to be carried back to cemux and/or rst mux, to preserve equality.
		if (st.ffDOAcemux) {
			SigSpec AB = st.ffDOAcemux->getPort(st.ffDOAcepol ? ID::B : ID::A);
			AB.replace(AB, Q);
			st.ffDOAcemux->setPort((st.ffDOAcepol ? ID::A : ID::B), Q);
		}

		if (st.ffADrstmux) {
			SigSpec BA = st.ffADrstmux->getPort(st.ffADrstpol ? ID::A : ID::B);
			BA.replace(BA, Q);
			st.ffADrstmux->setPort((st.ffADrstpol ? ID::B : ID::A), Q);
		}
	}

	if (st.ffDOB) {
		log("Candidate registers in DOBDO port to pack into BRAM cell: %s (%s).\n",
			log_id(st.ffDOB), log_id(st.ffDOB->type));

		SigSpec DOBDO = cell->getPort(ID(DOBDO));
		SigSpec Q = st.ffDOB->getPort(ID(Q));

		replace (DOBDO, st.ffDOBcemux, st.ffBDrstmux, st.ffDOBcepol, st.ffBDrstpol, ID(REGCEB), ID(RSTREGB));

		// BRAM DO port flops have been packed. Setting the DOx_REG register to 1, reflecting this change into the cell.
		cell->setParam(ID(DOB_REG), 1);
		// Since output flops will be optimised away due packing, its consumers (loads) needs to be connected (moved) to DO port.
		// At this point, ce and/or rst functionallity is already connected to the corresponding BRAM input port.
		DOBDO.replace(pm.sigmap(st.ffDOB->getPort(ID(D))), st.ffDOB->getPort(ID(Q)));
		cell->setPort(ID(DOBDO), DOBDO);

		// Flop.Q driver has been moved to BRAM.DO port. Adding dummy wires to it.
		Q.replace(st.sigDOB, pm.module->addWire(NEW_ID, GetSize(st.sigDOB)));
		st.ffDOB->setPort(ID(Q), Q);

		// The modification in Flop.Q needs to be carried back to cemux and/or rst mux, to preserve equality.
		if (st.ffDOBcemux) {
			SigSpec AB = st.ffDOBcemux->getPort(st.ffDOBcepol ? ID::B : ID::A);
			AB.replace(AB, Q);
			st.ffDOBcemux->setPort((st.ffDOBcepol ? ID::A : ID::B), Q);
		}

		if (st.ffBDrstmux) {
			SigSpec BA = st.ffBDrstmux->getPort(st.ffBDrstpol ? ID::A : ID::B);
			BA.replace(BA, Q);
			st.ffBDrstmux->setPort((st.ffBDrstpol ? ID::B : ID::A), Q);
		}
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
