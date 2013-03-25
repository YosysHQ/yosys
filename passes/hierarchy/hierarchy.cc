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
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <fnmatch.h>
#include <set>

namespace {
	struct generate_port_decl_t {
		bool input, output;
		std::string portname;
		int index;
	};
}

static void generate(RTLIL::Design *design, const std::vector<std::string> &celltypes, const std::vector<generate_port_decl_t> &portdecls)
{
	std::set<std::string> found_celltypes;

	for (auto i1 : design->modules)
	for (auto i2 : i1.second->cells)
	{
		RTLIL::Cell *cell = i2.second;
		if (cell->type[0] == '$' || design->modules.count(cell->type) > 0)
			continue;
		for (auto &pattern : celltypes)
			if (!fnmatch(pattern.c_str(), RTLIL::unescape_id(cell->type).c_str(), FNM_NOESCAPE))
				found_celltypes.insert(cell->type);
	}

	for (auto &celltype : found_celltypes)
	{
		std::set<std::string> portnames;
		std::map<std::string, int> portwidths;
		log("Generate module for cell type %s:\n", celltype.c_str());

		for (auto i1 : design->modules)
		for (auto i2 : i1.second->cells)
			if (i2.second->type == celltype)
				for (auto &conn : i2.second->connections) {
					if (conn.first[0] != '$')
						portnames.insert(conn.first);
					portwidths[conn.first] = std::max(portwidths[conn.first], conn.second.width);
				}

		for (auto &decl : portdecls)
			if (decl.index > 0)
				portnames.insert(decl.portname);

		std::set<int> indices;
		for (int i = 0; i < int(portnames.size()); i++)
			indices.insert(i+1);

		std::vector<generate_port_decl_t> ports(portnames.size());

		for (auto &decl : portdecls)
			if (decl.index > 0) {
				portwidths[decl.portname] = std::max(portwidths[decl.portname], 1);
				portwidths[decl.portname] = std::max(portwidths[decl.portname], portwidths[stringf("$%d", decl.index)]);
				log("  port %d: %s [%d:0] %s\n", decl.index, decl.input ? decl.output ? "inout" : "input" : "output", portwidths[decl.portname]-1, RTLIL::id2cstr(decl.portname));
				if (indices.count(decl.index) > ports.size())
					log_error("Port index (%d) exceeds number of found ports (%d).\n", decl.index, int(ports.size()));
				if (indices.count(decl.index) == 0)
					log_error("Conflict on port index %d.\n", decl.index);
				indices.erase(decl.index);
				portnames.erase(decl.portname);
				ports[decl.index-1] = decl;
			}

		while (portnames.size() > 0) {
			std::string portname = *portnames.begin();
			for (auto &decl : portdecls)
				if (decl.index == 0 && !fnmatch(decl.portname.c_str(), RTLIL::unescape_id(portname).c_str(), FNM_NOESCAPE)) {
					generate_port_decl_t d = decl;
					d.portname = portname;
					d.index = *indices.begin();
					assert(!indices.empty());
					indices.erase(d.index);
					ports[d.index-1] = d;
					portwidths[d.portname] = std::max(portwidths[d.portname], 1);
					log("  port %d: %s [%d:0] %s\n", d.index, d.input ? d.output ? "inout" : "input" : "output", portwidths[d.portname]-1, RTLIL::id2cstr(d.portname));
					goto found_matching_decl;
				}
			log_error("Can't match port %s.\n", RTLIL::id2cstr(portname));
		found_matching_decl:;
			portnames.erase(portname);
		}

		assert(indices.empty());

		RTLIL::Module *mod = new RTLIL::Module;
		mod->name = celltype;
		design->modules[mod->name] = mod;

		for (auto &decl : ports) {
			RTLIL::Wire *wire = new RTLIL::Wire;
			wire->name = decl.portname;
			wire->width = portwidths.at(decl.portname);
			wire->port_id = decl.index;
			wire->port_input = decl.input;
			wire->port_output = decl.output;
			mod->add(wire);
		}

		log("  module %s created.\n", RTLIL::id2cstr(mod->name));
	}
}

static bool expand_module(RTLIL::Design *design, RTLIL::Module *module, bool flag_check)
{
	bool did_something = false;

	for (auto &cell_it : module->cells) {
		RTLIL::Cell *cell = cell_it.second;
		if (design->modules.count(cell->type) == 0) {
			if (flag_check && cell->type[0] != '$')
				log_error("Module `%s' referenced in module `%s' in cell `%s' is not part of the design.\n",
						cell->type.c_str(), module->name.c_str(), cell->name.c_str());
			continue;
		}
		if (cell->parameters.size() == 0)
			continue;
		RTLIL::Module *mod = design->modules[cell->type];
		cell->type = mod->derive(design, cell->parameters);
		cell->parameters.clear();
	}

	if (did_something)
		return did_something;

	std::map<RTLIL::SigSpec, int> auto_wires;

	for (auto &wire_it : module->wires) {
		if (wire_it.second->auto_width)
			auto_wires[RTLIL::SigSpec(wire_it.second)] = -1;
	}

	for (auto &cell_it : module->cells)
	for (auto &conn : cell_it.second->connections)
	for (auto &awit : auto_wires) {
		if (awit.second >= 0 || conn.second != awit.first)
			continue;
		if (design->modules.count(cell_it.second->type) == 0) {
			log("WARNING: Module `%s' used in auto-delaration of the wire `%s.%s' cannot be found.\n",
					cell_it.second->type.c_str(), module->name.c_str(), log_signal(awit.first));
			continue;
		}
		RTLIL::Module *mod = design->modules[cell_it.second->type];
		RTLIL::Wire *wire = NULL;
		if (mod->wires.count(conn.first) == 0) {
			for (auto &wire_it : mod->wires) {
				if (wire_it.second->port_id == 0)
					continue;
				char buffer[100];
				snprintf(buffer, 100, "$%d", wire_it.second->port_id);
				if (buffer == conn.first) {
					wire = wire_it.second;
					break;
				}
			}
		} else
			wire = mod->wires[conn.first];
		if (!wire || wire->port_id == 0)
			log_error("No port `%s' found in `%s' but used by instanciation in `%s'!\n",
					conn.first.c_str(), mod->name.c_str(), module->name.c_str());
		if (wire->auto_width)
			log_error("Signal `%s' found in `%s' and used by instanciation in `%s' for an auto wire is an auto-wire itself!\n",
					log_signal(awit.first), mod->name.c_str(), module->name.c_str());
		awit.second = wire->width;
	}

	std::map<RTLIL::IdString, int> auto_sizes;
	for (auto &awit : auto_wires) {
		if (awit.second < 0)
			log("Can't further resolve auto-wire `%s.%s' (width %d) using cell ports.\n",
					module->name.c_str(), awit.first.chunks[0].wire->name.c_str(),
					awit.first.chunks[0].wire->width);
		else
			auto_sizes[awit.first.chunks[0].wire->name] = awit.second;
	}

	if (auto_sizes.size() > 0) {
		module->update_auto_wires(auto_sizes);
		log_header("Continuing EXPAND pass.\n");
		did_something = true;
	}

	return did_something;
}

static void hierarchy_worker(RTLIL::Design *design, std::set<RTLIL::Module*> &used, RTLIL::Module *mod, bool is_top = false)
{
	if (used.count(mod) > 0)
		return;

	log("%s module: %s\n", is_top ? "Top" : "Used", mod->name.c_str());
	used.insert(mod);

	for (auto &it : mod->cells) {
		if (design->modules.count(it.second->type) > 0)
			hierarchy_worker(design, used, design->modules[it.second->type]);
	}
}

static void hierarchy(RTLIL::Design *design, RTLIL::Module *top)
{
	std::set<RTLIL::Module*> used;
	hierarchy_worker(design, used, top, true);

	std::vector<RTLIL::Module*> del_modules;
	for (auto &it : design->modules)
		if (used.count(it.second) == 0)
			del_modules.push_back(it.second);

	for (auto mod : del_modules) {
		log("Removing unused module `%s'.\n", mod->name.c_str());
		design->modules.erase(mod->name);
		delete mod;
	}

	log("Removed %zd unused modules.\n", del_modules.size());
}

struct HierarchyPass : public Pass {
	HierarchyPass() : Pass("hierarchy", "check, expand and clean up design hierarchy") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    hierarchy [-check] [-top <module>]\n");
		log("    hierarchy -generate <cell-types> <port-decls>\n");
		log("\n");
		log("In parametric designs, a module might exists in serveral variations with\n");
		log("different parameter values. This pass looks at all modules in the current\n");
		log("design an re-runs the language frontends for the parametric modules as\n");
		log("needed.\n");
		log("\n");
		log("    -check\n");
		log("        also check the design hierarchy. this generates an error when\n");
		log("        an unknown module is used as cell type.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified top module to built a design hierarchy. modules\n");
		log("        outside this tree (unused modules) are removed.\n");
		log("\n");
		log("In -generate mode this pass generates skeletton modules for the given cell\n");
		log("types (wildcards supported). For this the design is searched for cells that\n");
		log("match the given types and then the given port declarations are used to\n");
		log("determine the direction of the ports. The syntax for a port declaration is:\n");
		log("\n");
		log("    {i|o|io}[@<num>]:<portname>\n");
		log("\n");
		log("Input ports are specified with the 'i' prefix, output ports with the 'o'\n");
		log("prefix and inout ports with the 'io' prefix. The optional <num> specifies\n");
		log("the position of the port in the parameter list (needed when instanciated\n");
		log("using positional arguments). When <num> is not specified, the <portname> can\n");
		log("also contain wildcard characters.\n");
		log("\n");
		log("This pass ignores the current selection and always operates on all modules\n");
		log("in the current design.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing HIERARCHY pass (managing design hierarchy).\n");

		bool flag_check = false;
		RTLIL::Module *top_mod = NULL;

		bool generate_mode = false;
		std::vector<std::string> generate_cells;
		std::vector<generate_port_decl_t> generate_ports;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-generate" && !flag_check && !top_mod) {
				generate_mode = true;
				log("Entering generate mode.\n");
				while (++argidx < args.size()) {
					const char *p = args[argidx].c_str();
					generate_port_decl_t decl;
					if (p[0] == 'i' && p[1] == 'o')
						decl.input = true, decl.output = true, p += 2;
					else if (*p == 'i')
						decl.input = true, decl.output = false, p++;
					else if (*p == 'o')
						decl.input = false, decl.output = true, p++;
					else
						goto is_celltype;
					if (*p == '@') {
						char *endptr;
						decl.index = strtol(++p, &endptr, 10);
						if (decl.index < 1)
							goto is_celltype;
						p = endptr;
					} else
						decl.index = 0;
					if (*(p++) != ':')
						goto is_celltype;
					if (*p == 0)
						goto is_celltype;
					decl.portname = p;
					log("Port declaration: %s", decl.input ? decl.output ? "inout" : "input" : "output");
					if (decl.index >= 1)
						log(" [at position %d]", decl.index);
					log(" %s\n", decl.portname.c_str());
					generate_ports.push_back(decl);
					continue;
				is_celltype:
					log("Celltype: %s\n", args[argidx].c_str());
					generate_cells.push_back(RTLIL::unescape_id(args[argidx]));
				}
				continue;
			}
			if (args[argidx] == "-check") {
				flag_check = true;
				continue;
			}
			if (args[argidx] == "-top") {
				if (++argidx >= args.size())
					log_cmd_error("Option -top requires an additional argument!\n");
				if (args[argidx][0] != '$' && args[argidx][0] != '\\')
					top_mod = design->modules.count("\\" + args[argidx]) > 0 ? design->modules["\\" + args[argidx]] : NULL;
				else
					top_mod = design->modules.count(args[argidx]) > 0 ? design->modules[args[argidx]] : NULL;
				if (top_mod == NULL)
					log_cmd_error("Module `%s' not found!\n", args[argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);

		if (generate_mode) {
			generate(design, generate_cells, generate_ports);
			return;
		}

		if (top_mod != NULL)
			hierarchy(design, top_mod);

		bool did_something = true;
		while (did_something) {
			did_something = false;
			std::vector<std::string> modnames;
			modnames.reserve(design->modules.size());
			for (auto &mod_it : design->modules)
				modnames.push_back(mod_it.first);
			for (auto &modname : modnames) {
				if (design->modules.count(modname) == 0)
					continue;
				if (expand_module(design, design->modules[modname], flag_check))
					did_something = true;
			}
		}

		if (top_mod != NULL)
			hierarchy(design, top_mod);
	}
} HierarchyPass;
 
