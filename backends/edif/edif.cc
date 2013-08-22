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

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string>
#include <assert.h>

struct EdifBackend : public Backend {
	EdifBackend() : Backend("edif", "write design to EDIF netlist file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_edif [options] [filename]\n");
		log("\n");
		log("Write the current design to an EDIF netlist file.\n");
		log("\n");
		log("    -top top_module\n");
		log("        set the specified module as design top module\n");
		log("\n");
		log("FIXME: This backend in under construction!\n");
		log("\n");
	}
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing EDIF backend.\n");

		std::string top_module_name;
		std::map<std::string, std::set<std::string>> lib_cell_ports;
		CellTypes ct(design);

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module_name = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		for (auto module_it : design->modules)
		{
			RTLIL::Module *module = module_it.second;
			if ((module->attributes.count("\\placeholder") > 0) > 0)
				continue;

			if (top_module_name.empty())
				top_module_name = module->name;

			if (module->processes.size() != 0)
				log_error("Found unmapped processes in module %s: unmapped processes are not supported in EDIF backend!\n", RTLIL::id2cstr(module->name));
			if (module->memories.size() != 0)
				log_error("Found munmapped emories in module %s: unmapped memories are not supported in EDIF backend!\n", RTLIL::id2cstr(module->name));

			for (auto cell_it : module->cells)
			{
				RTLIL::Cell *cell = cell_it.second;
				if (!design->modules.count(cell->type) || design->modules.at(cell->type)->attributes.count("\\placeholder")) {
					lib_cell_ports[cell->type];
					for (auto p : cell->connections) {
						if (p.second.width > 1)
							log_error("Found multi-bit port %s on library cell %s.%s (%s): not supported in EDIF backend!\n",
									RTLIL::id2cstr(p.first), RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
						lib_cell_ports[cell->type].insert(p.first);
					}
				}
			}
		}

		if (top_module_name.empty())
			log_error("No module found in design!\n");

		fprintf(f, "(edif %s\n", RTLIL::id2cstr(top_module_name));
		fprintf(f, "  (edifVersion 2 0 0)\n");
		fprintf(f, "  (edifLevel 0)\n");
		fprintf(f, "  (keywordMap (keywordLevel 0))\n");

		fprintf(f, "  (external LIB\n");
		fprintf(f, "    (edifLevel 0)\n");
		fprintf(f, "    (technology (numberDefinition))\n");
		for (auto &cell_it : lib_cell_ports) {
			fprintf(f, "    (cell %s\n", RTLIL::id2cstr(cell_it.first));
			fprintf(f, "      (cellType GENERIC)\n");
			fprintf(f, "      (view VIEW_NETLIST\n");
			fprintf(f, "        (viewType NETLIST)\n");
			fprintf(f, "        (interface\n");
			for (auto &port_it : cell_it.second) {
				const char *dir = "INOUT";
				if (ct.cell_known(cell_it.first)) {
					if (!ct.cell_output(cell_it.first, port_it))
						dir = "INPUT";
					else if (!ct.cell_input(cell_it.first, port_it))
						dir = "OUTPUT";
				}
				fprintf(f, "          (port %s (direction %s))\n", RTLIL::id2cstr(port_it), dir);
			}
			fprintf(f, "        )\n");
			fprintf(f, "      )\n");
			fprintf(f, "    )\n");
		}
		fprintf(f, "  )\n");

		fprintf(f, "  (library DESIGN\n");
		fprintf(f, "    (edifLevel 0)\n");
		fprintf(f, "    (technology (numberDefinition))\n");
		for (auto module_it : design->modules)
		{
			RTLIL::Module *module = module_it.second;
			if ((module->attributes.count("\\placeholder") > 0) > 0)
				continue;

			SigMap sigmap(module);
			std::map<RTLIL::SigSpec, std::set<std::string>> net_join_db;

			fprintf(f, "    (cell %s\n", RTLIL::id2cstr(module->name));
			fprintf(f, "      (cellType GENERIC)\n");
			fprintf(f, "      (view VIEW_NETLIST\n");
			fprintf(f, "        (viewType NETLIST)\n");
			fprintf(f, "        (interface\n");
			for (auto &wire_it : module->wires) {
				RTLIL::Wire *wire = wire_it.second;
				if (wire->port_id == 0)
					continue;
				const char *dir = "INOUT";
				if (!wire->port_output)
					dir = "INPUT";
				else if (!wire->port_input)
					dir = "OUTPUT";
				for (int i = 0; i < wire->width; i++) {
					std::string portname = wire->width > 1 ? stringf("%s[%d]", RTLIL::id2cstr(wire->name),
							i+wire->start_offset) : RTLIL::id2cstr(wire->name);
					fprintf(f, "          (port %s (direction %s))\n", portname.c_str(), dir);
					RTLIL::SigSpec sig = sigmap(RTLIL::SigSpec(wire, 1, i));
					net_join_db[sig].insert(stringf("(portRef %s)", portname.c_str()));
				}
			}
			fprintf(f, "        )\n");
			fprintf(f, "        (contents\n");
			for (auto &cell_it : module->cells) {
				RTLIL::Cell *cell = cell_it.second;
				fprintf(f, "          (instance %s (viewRef VIEW_NETLIST (cellRef %s%s)))\n",
						RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type),
						lib_cell_ports.count(cell->type) > 0 ? " (libraryRef LIB)" : "");
				for (auto &p : cell->connections) {
					RTLIL::SigSpec sig = sigmap(p.second);
					sig.expand();
					for (int i = 0; i < sig.width; i++) {
						RTLIL::SigSpec sigbit(sig.chunks.at(i));
						std::string portname = sig.width > 1 ? stringf("%s[%d]", RTLIL::id2cstr(p.first), i) : RTLIL::id2cstr(p.first);
						net_join_db[sigbit].insert(stringf("(portRef %s (instanceRef %s))", portname.c_str(), RTLIL::id2cstr(cell->name)));
					}
				}
			}
			for (auto &it : net_join_db) {
				std::string netname = log_signal(it.first);
				for (size_t i = 0; i < netname.size(); i++)
					if (netname[i] == ' ' || netname[i] == '\\')
						netname.erase(netname.begin() + i--);
				fprintf(f, "          (net %s (joined\n", netname.c_str());
				for (auto &ref : it.second)
					fprintf(f, "            %s\n", ref.c_str());
				fprintf(f, "          ))\n");
			}
			fprintf(f, "        )\n");
			fprintf(f, "      )\n");
			fprintf(f, "    )\n");
		}
		fprintf(f, "  )\n");

		fprintf(f, "  (design %s\n", RTLIL::id2cstr(top_module_name));
		fprintf(f, "    (cellRef %s (libraryRef DESIGN))\n", RTLIL::id2cstr(top_module_name));
		fprintf(f, "  )\n");

		fprintf(f, ")\n");
	}
} EdifBackend;

