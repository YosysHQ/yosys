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

#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

struct IopadmapPass : public Pass {
	IopadmapPass() : Pass("iopadmap", "technology mapping of flip-flops") { }
	virtual void help()
	{
		log("\n");
		log("    iopadmap [options] [selection]\n");
		log("\n");
		log("Map module inputs/outputs to PAD cells from a library. This pass\n");
		log("can only map to very simple PAD cells. Use 'techmap' to further map\n");
		log("the resulting cells to more sophisticated PAD cells.\n");
		log("\n");
		log("    -inpad <celltype> <portname>\n");
		log("        Map module input ports to the given cell type with\n");
		log("        the given port name.\n");
		log("\n");
		log("    -outpad <celltype> <portname>\n");
		log("    -inoutpad <celltype> <portname>\n");
		log("        Similar to -inpad, but for output and inout ports.\n");
		log("\n");
		log("    -widthparam <param_name>\n");
		log("        Use the specified parameter name to set the port width.\n");
		log("\n");
		log("    -nameparam <param_name>\n");
		log("        Use the specified parameter to set the port name.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing IOPADMAP pass (mapping inputs/outputs to IO-PAD cells).\n");

		std::string inpad_celltype, inpad_portname;
		std::string outpad_celltype, outpad_portname;
		std::string inoutpad_celltype, inoutpad_portname;
		std::string widthparam, nameparam;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-inpad" && argidx+2 < args.size()) {
				inpad_celltype = args[++argidx];
				inpad_portname = args[++argidx];
				continue;
			}
			if (arg == "-outpad" && argidx+2 < args.size()) {
				outpad_celltype = args[++argidx];
				outpad_portname = args[++argidx];
				continue;
			}
			if (arg == "-inoutpad" && argidx+2 < args.size()) {
				inoutpad_celltype = args[++argidx];
				inoutpad_portname = args[++argidx];
				continue;
			}
			if (arg == "-widthparam" && argidx+1 < args.size()) {
				widthparam = args[++argidx];
				continue;
			}
			if (arg == "-nameparam" && argidx+1 < args.size()) {
				nameparam = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &it : design->modules)
		{
			RTLIL::Module *module = it.second;

			if (!design->selected(module))
				continue;

			for (auto &it2 : module->wires)
			{
				RTLIL::Wire *wire = it2.second;

				if (!wire->port_id || !design->selected(module, wire))
					continue;

				std::string celltype, portname;

				if (wire->port_input && !wire->port_output) {
					if (inpad_celltype.empty()) {
						log("Don't map input port %s.%s: Missing option -inpad.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));
						continue;
					}
					celltype = inpad_celltype;
					portname = inpad_portname;
				} else
				if (!wire->port_input && wire->port_output) {
					if (outpad_celltype.empty()) {
						log("Don't map output port %s.%s: Missing option -outpad.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));
						continue;
					}
					celltype = outpad_celltype;
					portname = outpad_portname;
				} else
				if (wire->port_input && wire->port_output) {
					if (inoutpad_celltype.empty()) {
						log("Don't map inout port %s.%s: Missing option -inoutpad.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));
						continue;
					}
					celltype = inoutpad_celltype;
					portname = inoutpad_portname;
				} else
					log_abort();

				if (wire->width != 1 && widthparam.empty()) {
					log("Don't map multi-bit port %s.%s: Missing option -widthparam.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));
					continue;
				}

				log("Mapping port %s.%s.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));

				RTLIL::Cell *cell = new RTLIL::Cell;
				cell->name = NEW_ID;
				cell->type = RTLIL::escape_id(celltype);
				cell->connections[RTLIL::escape_id(portname)] = RTLIL::SigSpec(wire);
				if (!widthparam.empty())
					cell->parameters[RTLIL::escape_id(widthparam)] = RTLIL::Const(wire->width);
				if (!nameparam.empty())
					cell->parameters[RTLIL::escape_id(nameparam)] = RTLIL::Const(RTLIL::id2cstr(wire->name));
				cell->attributes["\\keep"] = RTLIL::Const(1);
				module->add(cell);

				wire->port_id = 0;
				wire->port_input = false;
				wire->port_output = false;
			}

			module->fixup_ports();
		}
	}
} IopadmapPass;
 
