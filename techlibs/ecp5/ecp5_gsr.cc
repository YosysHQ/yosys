/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2019  David Shah <david@symbioticeda.com>
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

struct Ecp5GsrPass : public Pass {
	Ecp5GsrPass() : Pass("ecp5_gsr", "ECP5: handle GSR") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ecp5_gsr [options] [selection]\n");
		log("\n");
		log("Trim active low async resets connected to GSR and resolve GSR parameter,\n");
		log("if a GSR or SGSR primitive is used in the design.\n");
		log("\n");
		log("If any cell has the GSR parameter set to \"AUTO\", this will be resolved\n");
		log("to \"ENABLED\" if a GSR primitive is present and the (* nogsr *) attribute\n");
		log("is not set, otherwise it will be resolved to \"DISABLED\".\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ECP5_GSR pass (implement FF init values).\n");

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
		{
			log("Handling GSR in %s.\n", log_id(module));

			SigMap sigmap(module);

			SigBit gsr;
			bool found_gsr = false;

			for (auto cell : module->selected_cells())
			{
				if (cell->type != ID(GSR) && cell->type != ID(SGSR))
					continue;
				if (found_gsr)
					log_error("Found more than one GSR or SGSR cell in module %s.\n", log_id(module));
				found_gsr = true;
				SigSpec sig_gsr = cell->getPort(ID(GSR));
				if (GetSize(sig_gsr) < 1)
					log_error("GSR cell %s has disconnected GSR input.\n", log_id(cell));
				gsr = sigmap(sig_gsr[0]);
			}

			// Resolve GSR parameter

			for (auto cell : module->selected_cells())
			{
				if (!cell->hasParam(ID(GSR)) || cell->getParam(ID(GSR)).decode_string() != "AUTO")
					continue;
				
				bool gsren = found_gsr;
				if (cell->get_bool_attribute("\\nogsr"))
					gsren = false;
				cell->setParam(ID(GSR), gsren ? Const("ENABLED") : Const("DISABLED"));
				
			}

			if (!found_gsr)
				continue;

			// For finding active low FF inputs
			pool<SigBit> inverted_gsr;

			log_debug("GSR net in module %s is %s.\n", log_id(module), log_signal(gsr));
			for (auto cell : module->selected_cells())
			{
				if (cell->type != ID($_NOT_))
					continue;
				SigSpec sig_a = cell->getPort(ID(A)), sig_y = cell->getPort(ID(Y));
				if (GetSize(sig_a) < 1 || GetSize(sig_y) < 1)
					continue;
				SigBit a = sigmap(sig_a[0]);
				if (a == gsr)
					inverted_gsr.insert(sigmap(sig_y[0]));
			}

			for (auto cell : module->selected_cells())
			{
				if (cell->type != ID(TRELLIS_FF))
					continue;
				if (!cell->hasParam(ID(GSR)) || cell->getParam(ID(GSR)).decode_string() != "ENABLED")
					continue;
				if (!cell->hasParam(ID(SRMODE)) || cell->getParam(ID(SRMODE)).decode_string() != "ASYNC")
					continue;
				SigSpec sig_lsr = cell->getPort(ID(LSR));
				if (GetSize(sig_lsr) < 1)
					continue;
				SigBit lsr = sigmap(sig_lsr[0]);
				if (!inverted_gsr.count(lsr))
					continue;
				cell->setParam(ID(SRMODE), Const("LSR_OVER_CE"));
				cell->unsetPort(ID(LSR));
			}

		}
	}
} Ecp5GsrPass;

PRIVATE_NAMESPACE_END
