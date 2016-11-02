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
#include <stdlib.h>
#include <stdio.h>
#include <set>

#ifndef _WIN32
#  include <unistd.h>
#endif


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct generate_port_decl_t {
	bool input, output;
	string portname;
	int index;
};

void generate(RTLIL::Design *design, const std::vector<std::string> &celltypes, const std::vector<generate_port_decl_t> &portdecls)
{
	std::set<RTLIL::IdString> found_celltypes;

	for (auto i1 : design->modules_)
	for (auto i2 : i1.second->cells_)
	{
		RTLIL::Cell *cell = i2.second;
		if (design->has(cell->type))
			continue;
		if (cell->type.substr(0, 1) == "$" && cell->type.substr(0, 3) != "$__")
			continue;
		for (auto &pattern : celltypes)
			if (patmatch(pattern.c_str(), RTLIL::unescape_id(cell->type).c_str()))
				found_celltypes.insert(cell->type);
	}

	for (auto &celltype : found_celltypes)
	{
		std::set<RTLIL::IdString> portnames;
		std::set<RTLIL::IdString> parameters;
		std::map<RTLIL::IdString, int> portwidths;
		log("Generate module for cell type %s:\n", celltype.c_str());

		for (auto i1 : design->modules_)
		for (auto i2 : i1.second->cells_)
			if (i2.second->type == celltype) {
				for (auto &conn : i2.second->connections()) {
					if (conn.first[0] != '$')
						portnames.insert(conn.first);
					portwidths[conn.first] = max(portwidths[conn.first], conn.second.size());
				}
				for (auto &para : i2.second->parameters)
					parameters.insert(para.first);
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
				portwidths[decl.portname] = max(portwidths[decl.portname], 1);
				portwidths[decl.portname] = max(portwidths[decl.portname], portwidths[stringf("$%d", decl.index)]);
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
			RTLIL::IdString portname = *portnames.begin();
			for (auto &decl : portdecls)
				if (decl.index == 0 && patmatch(decl.portname.c_str(), RTLIL::unescape_id(portname).c_str())) {
					generate_port_decl_t d = decl;
					d.portname = portname.str();
					d.index = *indices.begin();
					log_assert(!indices.empty());
					indices.erase(d.index);
					ports[d.index-1] = d;
					portwidths[d.portname] = max(portwidths[d.portname], 1);
					log("  port %d: %s [%d:0] %s\n", d.index, d.input ? d.output ? "inout" : "input" : "output", portwidths[d.portname]-1, RTLIL::id2cstr(d.portname));
					goto found_matching_decl;
				}
			log_error("Can't match port %s.\n", RTLIL::id2cstr(portname));
		found_matching_decl:;
			portnames.erase(portname);
		}

		log_assert(indices.empty());

		RTLIL::Module *mod = new RTLIL::Module;
		mod->name = celltype;
		mod->attributes["\\blackbox"] = RTLIL::Const(1);
		design->add(mod);

		for (auto &decl : ports) {
			RTLIL::Wire *wire = mod->addWire(decl.portname, portwidths.at(decl.portname));
			wire->port_id = decl.index;
			wire->port_input = decl.input;
			wire->port_output = decl.output;
		}

		mod->fixup_ports();

		for (auto &para : parameters)
			log("  ignoring parameter %s.\n", RTLIL::id2cstr(para));

		log("  module %s created.\n", RTLIL::id2cstr(mod->name));
	}
}

bool expand_module(RTLIL::Design *design, RTLIL::Module *module, bool flag_check, std::vector<std::string> &libdirs)
{
	bool did_something = false;
	std::map<RTLIL::Cell*, std::pair<int, int>> array_cells;
	std::string filename;

	for (auto &cell_it : module->cells_)
	{
		RTLIL::Cell *cell = cell_it.second;

		if (cell->type.substr(0, 7) == "$array:") {
			int pos_idx = cell->type.str().find_first_of(':');
			int pos_num = cell->type.str().find_first_of(':', pos_idx + 1);
			int pos_type = cell->type.str().find_first_of(':', pos_num + 1);
			int idx = atoi(cell->type.str().substr(pos_idx + 1, pos_num).c_str());
			int num = atoi(cell->type.str().substr(pos_num + 1, pos_type).c_str());
			array_cells[cell] = std::pair<int, int>(idx, num);
			cell->type = cell->type.str().substr(pos_type + 1);
		}

		if (design->modules_.count(cell->type) == 0)
		{
			if (design->modules_.count("$abstract" + cell->type.str()))
			{
				cell->type = design->modules_.at("$abstract" + cell->type.str())->derive(design, cell->parameters);
				cell->parameters.clear();
				did_something = true;
				continue;
			}

			if (cell->type[0] == '$')
				continue;

			for (auto &dir : libdirs)
			{
				filename = dir + "/" + RTLIL::unescape_id(cell->type) + ".v";
				if (check_file_exists(filename)) {
					std::vector<std::string> args;
					args.push_back(filename);
					Frontend::frontend_call(design, NULL, filename, "verilog");
					goto loaded_module;
				}

				filename = dir + "/" + RTLIL::unescape_id(cell->type) + ".il";
				if (check_file_exists(filename)) {
					std::vector<std::string> args;
					args.push_back(filename);
					Frontend::frontend_call(design, NULL, filename, "ilang");
					goto loaded_module;
				}
			}

			if (flag_check && cell->type[0] != '$')
				log_error("Module `%s' referenced in module `%s' in cell `%s' is not part of the design.\n",
						cell->type.c_str(), module->name.c_str(), cell->name.c_str());
			continue;

		loaded_module:
			if (design->modules_.count(cell->type) == 0)
				log_error("File `%s' from libdir does not declare module `%s'.\n", filename.c_str(), cell->type.c_str());
			did_something = true;
		} else
		if (flag_check)
		{
			RTLIL::Module *mod = design->module(cell->type);
			for (auto &conn : cell->connections())
				if (conn.first[0] == '$' && '0' <= conn.first[1] && conn.first[1] <= '9') {
					int id = atoi(conn.first.c_str()+1);
					if (id <= 0 || id > GetSize(mod->ports))
						log_error("Module `%s' referenced in module `%s' in cell `%s' has only %d ports, requested port %d.\n",
								log_id(cell->type), log_id(module), log_id(cell), GetSize(mod->ports), id);
				} else if (mod->wire(conn.first) == nullptr || mod->wire(conn.first)->port_id == 0)
					log_error("Module `%s' referenced in module `%s' in cell `%s' does not have a port named '%s'.\n",
							log_id(cell->type), log_id(module), log_id(cell), log_id(conn.first));
			for (auto &param : cell->parameters)
				if (mod->avail_parameters.count(param.first) == 0 && param.first[0] != '$')
					log_error("Module `%s' referenced in module `%s' in cell `%s' does not have a parameter named '%s'.\n",
							log_id(cell->type), log_id(module), log_id(cell), log_id(param.first));
		}

		if (cell->parameters.size() == 0)
			continue;

		if (design->modules_.at(cell->type)->get_bool_attribute("\\blackbox"))
			continue;

		RTLIL::Module *mod = design->modules_[cell->type];
		cell->type = mod->derive(design, cell->parameters);
		cell->parameters.clear();
		did_something = true;
	}

	for (auto &it : array_cells)
	{
		RTLIL::Cell *cell = it.first;
		int idx = it.second.first, num = it.second.second;

		if (design->modules_.count(cell->type) == 0)
			log_error("Array cell `%s.%s' of unknown type `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));

		RTLIL::Module *mod = design->modules_[cell->type];

		for (auto &conn : cell->connections_) {
			int conn_size = conn.second.size();
			RTLIL::IdString portname = conn.first;
			if (portname.substr(0, 1) == "$") {
				int port_id = atoi(portname.substr(1).c_str());
				for (auto &wire_it : mod->wires_)
					if (wire_it.second->port_id == port_id) {
						portname = wire_it.first;
						break;
					}
			}
			if (mod->wires_.count(portname) == 0)
				log_error("Array cell `%s.%s' connects to unknown port `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(conn.first));
			int port_size = mod->wires_.at(portname)->width;
			if (conn_size == port_size)
				continue;
			if (conn_size != port_size*num)
				log_error("Array cell `%s.%s' has invalid port vs. signal size for port `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(conn.first));
			conn.second = conn.second.extract(port_size*idx, port_size);
		}
	}

	return did_something;
}

void hierarchy_worker(RTLIL::Design *design, std::set<RTLIL::Module*, IdString::compare_ptr_by_name<Module>> &used, RTLIL::Module *mod, int indent)
{
	if (used.count(mod) > 0)
		return;

	if (indent == 0)
		log("Top module:  %s\n", mod->name.c_str());
	else if (!mod->get_bool_attribute("\\blackbox"))
		log("Used module: %*s%s\n", indent, "", mod->name.c_str());
	used.insert(mod);

	for (auto cell : mod->cells()) {
		std::string celltype = cell->type.str();
		if (celltype.substr(0, 7) == "$array:") {
			int pos_idx = celltype.find_first_of(':');
			int pos_num = celltype.find_first_of(':', pos_idx + 1);
			int pos_type = celltype.find_first_of(':', pos_num + 1);
			celltype = celltype.substr(pos_type + 1);
		}
		if (design->module(celltype))
			hierarchy_worker(design, used, design->module(celltype), indent+4);
	}
}

void hierarchy_clean(RTLIL::Design *design, RTLIL::Module *top, bool purge_lib)
{
	std::set<RTLIL::Module*, IdString::compare_ptr_by_name<Module>> used;
	hierarchy_worker(design, used, top, 0);

	std::vector<RTLIL::Module*> del_modules;
	for (auto &it : design->modules_)
		if (used.count(it.second) == 0)
			del_modules.push_back(it.second);

	int del_counter = 0;
	for (auto mod : del_modules) {
		if (!purge_lib && mod->get_bool_attribute("\\blackbox"))
			continue;
		log("Removing unused module `%s'.\n", mod->name.c_str());
		design->modules_.erase(mod->name);
		del_counter++;
		delete mod;
	}

	log("Removed %d unused modules.\n", del_counter);
}

bool set_keep_assert(std::map<RTLIL::Module*, bool> &cache, RTLIL::Module *mod)
{
	if (cache.count(mod) == 0)
		for (auto c : mod->cells()) {
			RTLIL::Module *m = mod->design->module(c->type);
			if ((m != nullptr && set_keep_assert(cache, m)) || c->type.in("$assert", "$assume"))
				return cache[mod] = true;
		}
	return cache[mod];
}

int find_top_mod_score(Design *design, Module *module, dict<Module*, int> &db)
{
	if (db.count(module) == 0) {
		int score = 0;
		db[module] = 0;
		for (auto cell : module->cells())
			if (design->module(cell->type))
				score = max(score, find_top_mod_score(design, design->module(cell->type), db) + 1);
		db[module] = score;
	}
	return db.at(module);
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
		log("In parametric designs, a module might exists in several variations with\n");
		log("different parameter values. This pass looks at all modules in the current\n");
		log("design an re-runs the language frontends for the parametric modules as\n");
		log("needed.\n");
		log("\n");
		log("    -check\n");
		log("        also check the design hierarchy. this generates an error when\n");
		log("        an unknown module is used as cell type.\n");
		log("\n");
		log("    -purge_lib\n");
		log("        by default the hierarchy command will not remove library (blackbox)\n");
		log("        modules. use this option to also remove unused blackbox modules.\n");
		log("\n");
		log("    -libdir <directory>\n");
		log("        search for files named <module_name>.v in the specified directory\n");
		log("        for unknown modules and automatically run read_verilog for each\n");
		log("        unknown module.\n");
		log("\n");
		log("    -keep_positionals\n");
		log("        per default this pass also converts positional arguments in cells\n");
		log("        to arguments using port names. this option disables this behavior.\n");
		log("\n");
		log("    -nokeep_asserts\n");
		log("        per default this pass sets the \"keep\" attribute on all modules\n");
		log("        that directly or indirectly contain one or more $assert cells. this\n");
		log("        option disables this behavior.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified top module to built a design hierarchy. modules\n");
		log("        outside this tree (unused modules) are removed.\n");
		log("\n");
		log("        when the -top option is used, the 'top' attribute will be set on the\n");
		log("        specified top module. otherwise a module with the 'top' attribute set\n");
		log("        will implicitly be used as top module, if such a module exists.\n");
		log("\n");
		log("    -auto-top\n");
		log("        automatically determine the top of the design hierarchy and mark it.\n");
		log("\n");
		log("In -generate mode this pass generates blackbox modules for the given cell\n");
		log("types (wildcards supported). For this the design is searched for cells that\n");
		log("match the given types and then the given port declarations are used to\n");
		log("determine the direction of the ports. The syntax for a port declaration is:\n");
		log("\n");
		log("    {i|o|io}[@<num>]:<portname>\n");
		log("\n");
		log("Input ports are specified with the 'i' prefix, output ports with the 'o'\n");
		log("prefix and inout ports with the 'io' prefix. The optional <num> specifies\n");
		log("the position of the port in the parameter list (needed when instantiated\n");
		log("using positional arguments). When <num> is not specified, the <portname> can\n");
		log("also contain wildcard characters.\n");
		log("\n");
		log("This pass ignores the current selection and always operates on all modules\n");
		log("in the current design.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing HIERARCHY pass (managing design hierarchy).\n");

		bool flag_check = false;
		bool purge_lib = false;
		RTLIL::Module *top_mod = NULL;
		std::vector<std::string> libdirs;

		bool auto_top_mode = false;
		bool generate_mode = false;
		bool keep_positionals = false;
		bool nokeep_asserts = false;
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
			if (args[argidx] == "-purge_lib") {
				purge_lib = true;
				continue;
			}
			if (args[argidx] == "-keep_positionals") {
				keep_positionals = true;
				continue;
			}
			if (args[argidx] == "-nokeep_asserts") {
				nokeep_asserts = true;
				continue;
			}
			if (args[argidx] == "-libdir" && argidx+1 < args.size()) {
				libdirs.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-top") {
				if (++argidx >= args.size())
					log_cmd_error("Option -top requires an additional argument!\n");
				top_mod = design->modules_.count(RTLIL::escape_id(args[argidx])) ? design->modules_.at(RTLIL::escape_id(args[argidx])) : NULL;
				if (top_mod == NULL && design->modules_.count("$abstract" + RTLIL::escape_id(args[argidx]))) {
					dict<RTLIL::IdString, RTLIL::Const> empty_parameters;
					design->modules_.at("$abstract" + RTLIL::escape_id(args[argidx]))->derive(design, empty_parameters);
					top_mod = design->modules_.count(RTLIL::escape_id(args[argidx])) ? design->modules_.at(RTLIL::escape_id(args[argidx])) : NULL;
				}
				if (top_mod == NULL)
					log_cmd_error("Module `%s' not found!\n", args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-auto-top") {
				auto_top_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);

		if (generate_mode) {
			generate(design, generate_cells, generate_ports);
			return;
		}

		log_push();

		if (top_mod == nullptr)
			for (auto &mod_it : design->modules_)
				if (mod_it.second->get_bool_attribute("\\top"))
					top_mod = mod_it.second;

		if (top_mod == nullptr && auto_top_mode) {
			log_header(design, "Finding top of design hierarchy..\n");
			dict<Module*, int> db;
			for (Module *mod : design->selected_modules()) {
				int score = find_top_mod_score(design, mod, db);
				log("root of %3d design levels: %-20s\n", score, log_id(mod));
				if (!top_mod || score > db[top_mod])
					top_mod = mod;
			}
			if (top_mod != nullptr)
				log("Automatically selected %s as design top module.\n", log_id(top_mod));
		}

		bool did_something = true;
		while (did_something)
		{
			did_something = false;

			std::set<RTLIL::Module*, IdString::compare_ptr_by_name<Module>> used_modules;
			if (top_mod != NULL) {
				log_header(design, "Analyzing design hierarchy..\n");
				hierarchy_worker(design, used_modules, top_mod, 0);
			} else {
				for (auto mod : design->modules())
					used_modules.insert(mod);
			}

			for (auto module : used_modules) {
				if (expand_module(design, module, flag_check, libdirs))
					did_something = true;
			}
		}

		if (top_mod != NULL) {
			log_header(design, "Analyzing design hierarchy..\n");
			hierarchy_clean(design, top_mod, purge_lib);
		}

		if (top_mod != NULL) {
			for (auto &mod_it : design->modules_)
				if (mod_it.second == top_mod)
					mod_it.second->attributes["\\top"] = RTLIL::Const(1);
				else
					mod_it.second->attributes.erase("\\top");
		}

		if (!nokeep_asserts) {
			std::map<RTLIL::Module*, bool> cache;
			for (auto mod : design->modules())
				if (set_keep_assert(cache, mod)) {
					log("Module %s directly or indirectly contains $assert cells -> setting \"keep\" attribute.\n", log_id(mod));
					mod->set_bool_attribute("\\keep");
				}
		}

		if (!keep_positionals)
		{
			std::set<RTLIL::Module*> pos_mods;
			std::map<std::pair<RTLIL::Module*,int>, RTLIL::IdString> pos_map;
			std::vector<std::pair<RTLIL::Module*,RTLIL::Cell*>> pos_work;

			for (auto &mod_it : design->modules_)
			for (auto &cell_it : mod_it.second->cells_) {
				RTLIL::Cell *cell = cell_it.second;
				if (design->modules_.count(cell->type) == 0)
					continue;
				for (auto &conn : cell->connections())
					if (conn.first[0] == '$' && '0' <= conn.first[1] && conn.first[1] <= '9') {
						pos_mods.insert(design->modules_.at(cell->type));
						pos_work.push_back(std::pair<RTLIL::Module*,RTLIL::Cell*>(mod_it.second, cell));
						break;
					}
			}

			for (auto module : pos_mods)
			for (auto &wire_it : module->wires_) {
				RTLIL::Wire *wire = wire_it.second;
				if (wire->port_id > 0)
					pos_map[std::pair<RTLIL::Module*,int>(module, wire->port_id)] = wire->name;
			}

			for (auto &work : pos_work) {
				RTLIL::Module *module = work.first;
				RTLIL::Cell *cell = work.second;
				log("Mapping positional arguments of cell %s.%s (%s).\n",
						RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
				dict<RTLIL::IdString, RTLIL::SigSpec> new_connections;
				for (auto &conn : cell->connections())
					if (conn.first[0] == '$' && '0' <= conn.first[1] && conn.first[1] <= '9') {
						int id = atoi(conn.first.c_str()+1);
						std::pair<RTLIL::Module*,int> key(design->modules_.at(cell->type), id);
						if (pos_map.count(key) == 0) {
							log("  Failed to map positional argument %d of cell %s.%s (%s).\n",
									id, RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
							new_connections[conn.first] = conn.second;
						} else
							new_connections[pos_map.at(key)] = conn.second;
					} else
						new_connections[conn.first] = conn.second;
				cell->connections_ = new_connections;
			}
		}

		log_pop();
	}
} HierarchyPass;

PRIVATE_NAMESPACE_END
