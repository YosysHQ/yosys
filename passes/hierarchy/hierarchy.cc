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
#include <set>

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
		log("This pass ignores the current selection and always operates on all modules\n");
		log("in the current design.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing HIERARCHY pass (removing modules outside design hierarchy).\n");

		bool flag_check = false;
		RTLIL::Module *top_mod = NULL;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
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
 
