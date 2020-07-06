/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2019  Marcin Kościelnicki <mwk@0x04.net>
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

void split_portname_pair(std::string &port1, std::string &port2)
{
	size_t pos = port1.find_first_of(':');
	if (pos != std::string::npos) {
		port2 = port1.substr(pos+1);
		port1 = port1.substr(0, pos);
	}
}

struct ExtractinvPass : public Pass {
	ExtractinvPass() : Pass("extractinv", "extract explicit inverter cells for invertible cell pins") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    extractinv [options] [selection]\n");
		log("\n");
		log("Searches the design for all cells with invertible pins controlled by a cell\n");
		log("parameter (eg. IS_CLK_INVERTED on many Xilinx cells) and removes the parameter.\n");
		log("If the parameter was set to 1, inserts an explicit inverter cell in front of\n");
		log("the pin instead.  Normally used for output to ISE, which does not support the\n");
		log("inversion parameters.\n");
		log("\n");
		log("To mark a cell port as invertible, use (* invertible_pin = \"param_name\" *)\n");
		log("on the wire in the blackbox module.  The parameter value should have\n");
		log("the same width as the port, and will be effectively XORed with it.\n");
		log("\n");
		log("    -inv <celltype> <portname_out>:<portname_in>\n");
		log("        Specifies the cell type to use for the inverters and its port names.\n");
		log("        This option is required.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing EXTRACTINV pass (extracting pin inverters).\n");

		std::string inv_celltype, inv_portname, inv_portname2;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-inv" && argidx+2 < args.size()) {
				inv_celltype = args[++argidx];
				inv_portname = args[++argidx];
				split_portname_pair(inv_portname, inv_portname2);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (inv_celltype.empty())
			log_error("The -inv option is required.\n");

		for (auto module : design->selected_modules())
		{
			for (auto cell : module->selected_cells())
			for (auto port : cell->connections()) {
				auto cell_module = design->module(cell->type);
				if (!cell_module)
					continue;
				auto cell_wire = cell_module->wire(port.first);
				if (!cell_wire)
					continue;
				auto it = cell_wire->attributes.find("\\invertible_pin");
				if (it == cell_wire->attributes.end())
					continue;
				IdString param_name = RTLIL::escape_id(it->second.decode_string());
				auto it2 = cell->parameters.find(param_name);
				// Inversion not used -- skip.
				if (it2 == cell->parameters.end())
					continue;
				SigSpec sig = port.second;
				if (it2->second.size() != sig.size())
					log_error("The inversion parameter needs to be the same width as the port (%s.%s port %s parameter %s)", log_id(module->name), log_id(cell->type), log_id(port.first), log_id(param_name));
				RTLIL::Const invmask = it2->second;
				cell->parameters.erase(param_name);
				if (invmask.is_fully_zero())
					continue;
				Wire *iwire = module->addWire(NEW_ID, sig.size());
				for (int i = 0; i < sig.size(); i++)
					if (invmask[i] == State::S1) {
						RTLIL::Cell *icell = module->addCell(NEW_ID, RTLIL::escape_id(inv_celltype));
						icell->setPort(RTLIL::escape_id(inv_portname), SigSpec(iwire, i));
						icell->setPort(RTLIL::escape_id(inv_portname2), sig[i]);
						log("Inserting %s on %s.%s.%s[%d].\n", inv_celltype.c_str(), log_id(module), log_id(cell->type), log_id(port.first), i);
						sig[i] = SigBit(iwire, i);
					}
				cell->setPort(port.first, sig);
			}
		}
	}
} ExtractinvPass;

PRIVATE_NAMESPACE_END
