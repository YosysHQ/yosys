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


static std::string netname(std::set<std::string> &conntypes_code, std::set<std::string> &celltypes_code, std::set<std::string> &constcells_code, RTLIL::SigSpec sig)
{
	sig.optimize();

	if (sig.chunks.size() != 1)
error:
		log_error("Can't export composite or non-word-wide signal %s.\n", log_signal(sig));

	conntypes_code.insert(stringf("conntype b%d %d 2 %d\n", sig.width, sig.width, sig.width));

	if (sig.chunks[0].wire == NULL) {
		celltypes_code.insert(stringf("celltype const%d b%d *CONST cfg:%d VALUE\n", sig.width, sig.width));
		constcells_code.insert(stringf("node const%d_0x%x const%d CONST const%d_%x VALUE 0x%x\n", sig.width, sig.chunks[0].data.as_int(),
				sig.width, sig.width, sig.chunks[0].data.as_int(), sig.chunks[0].data.as_int()));
		return stringf("const%d_0x%x", sig.width, sig.chunks[0].data.as_int());
	}

	if (sig.chunks[0].offset != 0 || sig.width != sig.chunks[0].wire->width)
		goto error;

	return unescape_id(sig.chunks[0].wire->name);
}

struct IntersynthBackend : public Backend {
	IntersynthBackend() : Backend("intersynth", "write design to InterSynth netlist file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_intersynth [filename]\n");
		log("\n");
		log("Write the current design to an 'intersynth' netlist file. InterSynth is\n");
		log("a tool for Coarse-Grain Example-Driven Interconnect Synthesis.\n");
		log("\n");
		log("http://www.clifford.at/intersynth/\n");
		log("\n");
	}
	virtual void execute(FILE *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing INTERSYNTH backend.\n");
		extra_args(f, filename, args, 1);
		log("Output filename: %s\n", filename.c_str());

		std::set<std::string> conntypes_code, celltypes_code;
		std::string netlists_code;
		CellTypes ct(design);

		for (auto module_it : design->modules)
		{
			RTLIL::Module *module = module_it.second;
			SigMap sigmap(module);

			if (module->memories.size() == 0 && module->processes.size() == 0 && module->cells.size() == 0)
				continue;

			log("Generating netlist %s.\n", id2cstr(module->name));

			if (module->memories.size() != 0 || module->processes.size() != 0)
				log_error("Can't generate a netlist for a module with unprocessed memories or processes!\n");

			std::set<std::string> constcells_code;
			netlists_code += stringf("netlist %s\n", id2cstr(module->name));

			for (auto wire_it : module->wires) {
				RTLIL::Wire *wire = wire_it.second;
				if (wire->port_input || wire->port_output) {
					celltypes_code.insert(stringf("celltype !%s b%d %sPORT\n" "%s %s %d %s PORT\n",
							id2cstr(wire->name), wire->width, wire->port_input ? "*" : "",
							wire->port_input ? "input" : "output", id2cstr(wire->name), wire->width, id2cstr(wire->name)));
					netlists_code += stringf("node %s %s PORT %s\n", id2cstr(wire->name), id2cstr(wire->name),
							netname(conntypes_code, celltypes_code, constcells_code, sigmap(wire)).c_str());
				}
			}

			for (auto cell_it : module->cells)
			{
				RTLIL::Cell *cell = cell_it.second;
				std::string celltype_code, node_code;

				celltype_code = stringf("celltype %s", id2cstr(cell->type));
				node_code = stringf("node %s %s", id2cstr(cell->name), id2cstr(cell->type));
				for (auto &port : cell->connections) {
					RTLIL::SigSpec sig = sigmap(port.second);
					conntypes_code.insert(stringf("conntype b%d %d 2 %d\n", sig.width, sig.width, sig.width));
					celltype_code += stringf(" b%d %s%s", sig.width, ct.cell_output(cell->type, port.first) ? "*" : "", id2cstr(port.first));
					node_code += stringf(" %s %s", id2cstr(port.first), netname(conntypes_code, celltypes_code, constcells_code, sig).c_str());
				}
				for (auto &param : cell->parameters) {
					celltype_code += stringf(" cfg:%d %s", int(param.second.bits.size()), id2cstr(param.first));
					if (param.second.bits.size() != 32) {
						node_code += stringf(" %s '", id2cstr(param.first));
						for (int i = param.second.bits.size()-1; i >= 0; i--)
							node_code += param.second.bits[i] == RTLIL::S1 ? "1" : "0";
					} else
						node_code += stringf(" %s 0x%x", id2cstr(param.first), param.second.as_int());
				}

				celltypes_code.insert(celltype_code + "\n");
				netlists_code += node_code + "\n";
			}
		}

		for (auto str : conntypes_code)
			fprintf(f, "%s", str.c_str());
		for (auto str : celltypes_code)
			fprintf(f, "%s", str.c_str());
		fprintf(f, "%s", netlists_code.c_str());
	}
} IntersynthBackend;

