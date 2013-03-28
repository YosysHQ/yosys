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
#include <assert.h>
#include <stdio.h>
#include <string.h>

#include "passes/techmap/stdcells.inc"

static void apply_prefix(std::string prefix, std::string &id)
{
	if (id[0] == '\\')
		id = prefix + "." + id.substr(1);
	else
		id = prefix + "." + id;
}

static void apply_prefix(std::string prefix, RTLIL::SigSpec &sig, RTLIL::Module *module)
{
	for (size_t i = 0; i < sig.chunks.size(); i++) {
		if (sig.chunks[i].wire == NULL)
			continue;
		std::string wire_name = sig.chunks[i].wire->name;
		apply_prefix(prefix, wire_name);
		assert(module->wires.count(wire_name) > 0);
		sig.chunks[i].wire = module->wires[wire_name];
	}
}

std::map<std::pair<RTLIL::IdString, std::map<RTLIL::IdString, RTLIL::Const>>, RTLIL::Module*> techmap_cache;
std::map<RTLIL::Module*, bool> techmap_fail_cache;

static bool techmap_fail_check(RTLIL::Module *module)
{
	if (module == NULL)
		return false;

	if (techmap_fail_cache.count(module) > 0)
		return techmap_fail_cache.at(module);

	for (auto &it : module->wires) {
		std::string name = it.first;
		if (name == "\\TECHMAP_FAIL")
			return techmap_fail_cache[module] = true;
		if (name.size() > 13 && name[0] == '\\' && name.substr(name.size()-13) == ".TECHMAP_FAIL")
			return techmap_fail_cache[module] = true;
	}

	return techmap_fail_cache[module] = false;
}

static void techmap_module_worker(RTLIL::Design *design, RTLIL::Module *module, RTLIL::Cell *cell, RTLIL::Module *tpl)
{
	log("Mapping `%s.%s' using `%s'.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(cell->name), RTLIL::id2cstr(tpl->name));

	if (tpl->memories.size() != 0)
		log_error("Technology map yielded memories -> this is not supported.");

	if (tpl->processes.size() != 0)
		log_error("Technology map yielded processes -> this is not supported.");

	for (auto &it : tpl->wires) {
		RTLIL::Wire *w = new RTLIL::Wire(*it.second);
		apply_prefix(cell->name, w->name);
		w->port_input = false;
		w->port_output = false;
		w->port_id = 0;
		module->wires[w->name] = w;
		design->select(module, w);
	}

	for (auto &it : tpl->cells) {
		RTLIL::Cell *c = new RTLIL::Cell(*it.second);
		if (c->type.substr(0, 2) == "\\$")
			c->type = c->type.substr(1);
		apply_prefix(cell->name, c->name);
		for (auto &it2 : c->connections)
			apply_prefix(cell->name, it2.second, module);
		module->cells[c->name] = c;
		design->select(module, c);
	}

	for (auto &it : tpl->connections) {
		RTLIL::SigSig c = it;
		apply_prefix(cell->name, c.first, module);
		apply_prefix(cell->name, c.second, module);
		module->connections.push_back(c);
	}

	for (auto &it : cell->connections) {
		assert(tpl->wires.count(it.first));
		assert(tpl->wires[it.first]->port_id > 0);
		RTLIL::Wire *w = tpl->wires[it.first];
		RTLIL::SigSig c;
		if (w->port_output) {
			c.first = it.second;
			c.second = RTLIL::SigSpec(w);
			apply_prefix(cell->name, c.second, module);
		} else {
			c.first = RTLIL::SigSpec(w);
			c.second = it.second;
			apply_prefix(cell->name, c.first, module);
		}
		if (c.second.width > c.first.width)
			c.second.remove(c.first.width, c.second.width - c.first.width);
		if (c.second.width < c.first.width)
			c.second.append(RTLIL::SigSpec(RTLIL::State::S0, c.first.width - c.second.width));
		assert(c.first.width == c.second.width);
		module->connections.push_back(c);
	}

	module->cells.erase(cell->name);
	delete cell;
}

static bool techmap_module(RTLIL::Design *design, RTLIL::Module *module, RTLIL::Design *map, std::set<RTLIL::Cell*> &handled_cells,
		const std::map<RTLIL::IdString, std::set<RTLIL::IdString>> &celltypeMap)
{
	if (!design->selected(module))
		return false;

	bool did_something = false;

	std::vector<std::string> cell_names;

	for (auto &cell_it : module->cells)
		cell_names.push_back(cell_it.first);

	for (auto &cell_name : cell_names)
	{
		if (module->cells.count(cell_name) == 0)
			continue;

		RTLIL::Cell *cell = module->cells[cell_name];

		if (!design->selected(module, cell) || handled_cells.count(cell) > 0)
			continue;

		if (celltypeMap.count(cell->type) == 0)
			continue;

		for (auto &tpl_name : celltypeMap.at(cell->type))
		{
			RTLIL::Module *tpl = map->modules[tpl_name];
			std::pair<RTLIL::IdString, std::map<RTLIL::IdString, RTLIL::Const>> key(cell->type, cell->parameters);
			std::string derived_name = cell->type;

			if (techmap_cache.count(key) > 0) {
				tpl = techmap_cache[key];
			} else {
				if (cell->parameters.size() != 0) {
					derived_name = tpl->derive(map, cell->parameters);
					tpl = map->modules[derived_name];
					log_header("Continuing TECHMAP pass.\n");
				}
				techmap_cache[key] = tpl;
			}

			if (techmap_fail_check(tpl)) {
				log("Not using module `%s' from techmap as it contains a TECHMAP_FAIL marker wire.\n", derived_name.c_str());
				continue;
			}

			techmap_module_worker(design, module, cell, tpl);
			did_something = true;
			cell = NULL;
			break;
		}

		handled_cells.insert(cell);
	}

	return did_something;
}

struct TechmapPass : public Pass {
	TechmapPass() : Pass("techmap", "simple technology mapper") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    techmap [-map filename] [selection]\n");
		log("\n");
		log("This pass implements a very simple technology mapper that replaces cells in\n");
		log("the design with implementations given in form of a verilog or ilang source\n");
		log("file.\n");
		log("\n");
		log("    -map filename\n");
		log("        the library of cell implementations to be used.\n");
		log("        without this parameter a builtin library is used that\n");
		log("        transforms the internal RTL cells to the internal gate\n");
		log("        library.\n");
		log("\n");
		log("When a module in the map file has the 'celltype' attribute set, it will match\n");
		log("cells with a type that match the text value of this attribute.\n");
		log("\n");
		log("When a module in the map file contains a wire with the name 'TECHMAP_FAIL' (or\n");
		log("one matching '*.TECHMAP_FAIL') then no substitution will be performed. The\n");
		log("module in the map file are tried in alphabetical order.\n");
		log("\n");
		log("See 'help extract' for a pass that does the opposite thing.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing TECHMAP pass (map to technology primitives).\n");
		log_push();

		std::string filename;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		FILE *f = filename.empty() ? fmemopen(stdcells_code, strlen(stdcells_code), "rt") : fopen(filename.c_str(), "rt");
		if (f == NULL)
			log_cmd_error("Can't open map file `%s'\n", filename.c_str());

		RTLIL::Design *map = new RTLIL::Design;
		Frontend::frontend_call(map, f, filename.empty() ? "<stdcells.v>" : filename,
				(filename.size() > 3 && filename.substr(filename.size()-3) == ".il") ? "ilang" : "verilog");

		fclose(f);

		std::map<RTLIL::IdString, RTLIL::Module*> modules_new;
		for (auto &it : map->modules) {
			if (it.first.substr(0, 2) == "\\$")
				it.second->name = it.first.substr(1);
			modules_new[it.second->name] = it.second;
		}
		map->modules.swap(modules_new);

		std::map<RTLIL::IdString, std::set<RTLIL::IdString>> celltypeMap;
		for (auto &it : map->modules) {
			if (it.second->attributes.count("\\celltype") && !it.second->attributes.at("\\celltype").str.empty()) {
				celltypeMap[RTLIL::escape_id(it.second->attributes.at("\\celltype").str)].insert(it.first);
			} else
				celltypeMap[it.first].insert(it.first);
		}

		bool did_something = true;
		std::set<RTLIL::Cell*> handled_cells;
		while (did_something) {
			did_something = false;
			for (auto &mod_it : design->modules)
				if (techmap_module(design, mod_it.second, map, handled_cells, celltypeMap))
					did_something = true;
		}

		log("No more expansions possible.\n");
		techmap_cache.clear();
		techmap_fail_cache.clear();
		delete map;
		log_pop();
	}
} TechmapPass;
 
