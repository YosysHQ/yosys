/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/newcelltypes.h"
#include "kernel/log.h"
#include <string>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static std::string netname(std::set<std::string> &conntypes_code, std::set<std::string> &celltypes_code, std::set<std::string> &constcells_code, RTLIL::SigSpec sig)
{
	if (!sig.is_fully_const() && !sig.is_wire())
		log_error("Can't export composite or non-word-wide signal %s.\n", log_signal(sig));

	conntypes_code.insert(stringf("conntype b%d %d 2 %d\n", sig.size(), sig.size(), sig.size()));

	if (sig.is_fully_const()) {
		celltypes_code.insert(stringf("celltype CONST_%d b%d *CONST cfg:%d VALUE\n", sig.size(), sig.size(), sig.size()));
		constcells_code.insert(stringf("node CONST_%d_0x%x CONST_%d CONST CONST_%d_0x%x VALUE 0x%x\n",
				sig.size(), sig.as_int(), sig.size(), sig.size(), sig.as_int(), sig.as_int()));
		return stringf("CONST_%d_0x%x", sig.size(), sig.as_int());
	}

	return design->twines.unescaped_str(sig.as_wire()->name);
}

struct IntersynthBackend : public Backend {
	IntersynthBackend() : Backend("intersynth", "write design to InterSynth netlist file") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_intersynth [options] [filename]\n");
		log("\n");
		log("Write the current design to an 'intersynth' netlist file. InterSynth is\n");
		log("a tool for Coarse-Grain Example-Driven Interconnect Synthesis.\n");
		log("\n");
		log("    -notypes\n");
		log("        do not generate celltypes and conntypes commands. i.e. just output\n");
		log("        the netlists. this is used for postsilicon synthesis.\n");
		log("\n");
		log("    -lib <verilog_or_rtlil_file>\n");
		log("        Use the specified library file for determining whether cell ports are\n");
		log("        inputs or outputs. This option can be used multiple times to specify\n");
		log("        more than one library.\n");
		log("\n");
		log("    -selected\n");
		log("        only write selected modules. modules must be selected entirely or\n");
		log("        not at all.\n");
		log("\n");
		log("http://bygone.clairexen.net/intersynth/\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing INTERSYNTH backend.\n");
		log_push();

		std::vector<std::string> libfiles;
		std::vector<RTLIL::Design*> libs;
		bool flag_notypes = false;
		bool selected = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-notypes") {
				flag_notypes = true;
				continue;
			}
			if (args[argidx] == "-lib" && argidx+1 < args.size()) {
				libfiles.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-selected") {
				selected = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		log("Output filename: %s\n", filename);

		for (auto filename : libfiles) {
			std::ifstream f;
			f.open(filename.c_str());
			if (f.fail())
				log_error("Can't open lib file `%s'.\n", filename);
			RTLIL::Design *lib = new RTLIL::Design;
			Frontend::frontend_call(lib, &f, filename, (filename.size() > 3 && filename.compare(filename.size()-3, std::string::npos, ".il") == 0 ? "rtlil" : "verilog"));
			libs.push_back(lib);
		}

		if (libs.size() > 0)
			log_header(design, "Continuing INTERSYNTH backend.\n");

		std::set<std::string> conntypes_code, celltypes_code;
		std::string netlists_code;
		NewCellTypes ct(design);

		for (auto lib : libs)
			ct.setup_design(lib);

		for (auto module : design->modules())
		{
			SigMap sigmap(module);

			if (module->get_blackbox_attribute())
				continue;
			if (module->memories.size() == 0 && module->processes.size() == 0 && module->cells().size() == 0)
				continue;

			if (selected && !design->selected_whole_module(module->meta_->name)) {
				if (design->selected_module(module->meta_->name))
					log_cmd_error("Can't handle partially selected module %s!\n", design->twines.str(module->meta_->name).c_str());
				continue;
			}

			log("Generating netlist %s.\n", design->twines.str(module->meta_->name).c_str());

			if (module->memories.size() != 0 || module->processes.size() != 0)
				log_error("Can't generate a netlist for a module with unprocessed memories or processes!\n");

			std::set<std::string> constcells_code;
			netlists_code += stringf("# Netlist of module %s\n", design->twines.str(module->meta_->name).c_str());
			netlists_code += stringf("netlist %s\n", design->twines.str(module->meta_->name).c_str());

			// Module Ports: "std::set<string> celltypes_code" prevents duplicate top level ports
			for (auto wire : module->wires()) {
				if (wire->port_input || wire->port_output) {
					celltypes_code.insert(stringf("celltype !%s b%d %sPORT\n" "%s %s %d %s PORT\n",
							wire->name.unescape(), wire->width, wire->port_input ? "*" : "",
							wire->port_input ? "input" : "output", design->twines.unescaped_str(wire->name), wire->width, design->twines.unescaped_str(wire->name)));
					netlists_code += stringf("node %s %s PORT %s\n", design->twines.unescaped_str(wire->name), design->twines.unescaped_str(wire->name),
							netname(conntypes_code, celltypes_code, constcells_code, sigmap(wire)).c_str());
				}
			}

			// Submodules: "std::set<string> celltypes_code" prevents duplicate cell types
			for (auto cell : module->cells())
			{
				std::string celltype_code, node_code;

				if (!ct.cell_known(cell->type_impl))
					log_error("Found unknown cell type %s in module!\n", cell->type.unescaped());

				celltype_code = stringf("celltype %s", cell->type.unescaped());
				node_code = stringf("node %s %s", cell->module->design->twines.str(cell->meta_->name), cell->type.unescaped());
				for (auto &port : cell->connections()) {
					RTLIL::SigSpec sig = sigmap(port.second);
					if (sig.size() != 0) {
						conntypes_code.insert(stringf("conntype b%d %d 2 %d\n", sig.size(), sig.size(), sig.size()));
						std::string port_name = design->twines.str(port.first);
						celltype_code += stringf(" b%d %s%s", sig.size(), ct.cell_output(cell->type_impl, port.first) ? "*" : "", port_name.c_str());
						node_code += stringf(" %s %s", port_name.c_str(), netname(conntypes_code, celltypes_code, constcells_code, sig));
					}
				}
				for (auto &param : cell->parameters) {
					celltype_code += stringf(" cfg:%d %s", int(param.second.size()), design->twines.unescaped_str(param.first));
					if (param.second.size() != 32) {
						node_code += stringf(" %s '", design->twines.unescaped_str(param.first));
						for (int i = param.second.size()-1; i >= 0; i--)
							node_code += param.second[i] == State::S1 ? "1" : "0";
					} else
						node_code += stringf(" %s 0x%x", design->twines.unescaped_str(param.first), param.second.as_int());
				}

				celltypes_code.insert(celltype_code + "\n");
				netlists_code += node_code + "\n";
			}

			if (constcells_code.size() > 0)
			  netlists_code += "# constant cells\n";
			for (auto code : constcells_code)
				netlists_code += code;
			netlists_code += "\n";
		}

		if (!flag_notypes) {
			*f << stringf("### Connection Types\n");
			for (auto code : conntypes_code)
				*f << stringf("%s", code);
			*f << stringf("\n### Cell Types\n");
			for (auto code : celltypes_code)
				*f << stringf("%s", code);
		}
		*f << stringf("\n### Netlists\n");
		*f << stringf("%s", netlists_code);

		for (auto lib : libs)
			delete lib;

		log_pop();
	}
} IntersynthBackend;

PRIVATE_NAMESPACE_END
