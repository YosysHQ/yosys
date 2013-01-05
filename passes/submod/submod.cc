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
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

struct SubmodWorker
{
	CellTypes ct;
	RTLIL::Design *design;
	RTLIL::Module *module;

	struct SubModule
	{
		std::string name, full_name;
		std::set<RTLIL::Cell*> cells;
	};

	std::map<std::string, SubModule> submodules;

	struct wire_flags_t {
		RTLIL::Wire *new_wire;
		bool is_int_driven, is_int_used, is_ext_driven, is_ext_used;
		wire_flags_t() : new_wire(NULL), is_int_driven(false), is_int_used(false), is_ext_driven(false), is_ext_used(false) { }
	};
	std::map<RTLIL::Wire*, wire_flags_t> wire_flags;
	bool flag_found_something;

	void flag_wire(RTLIL::Wire *wire, bool create, bool set_int_driven, bool set_int_used, bool set_ext_driven, bool set_ext_used)
	{
		if (wire_flags.count(wire) == 0) {
			if (!create)
				return;
			wire_flags[wire] = wire_flags_t();
		}
		if (set_int_driven)
			wire_flags[wire].is_int_driven = true;
		if (set_int_used)
			wire_flags[wire].is_int_used = true;
		if (set_ext_driven)
			wire_flags[wire].is_ext_driven = true;
		if (set_ext_used)
			wire_flags[wire].is_ext_used = true;
		flag_found_something = true;
	}

	void flag_signal(RTLIL::SigSpec &sig, bool create, bool set_int_driven, bool set_int_used, bool set_ext_driven, bool set_ext_used)
	{
		for (auto &c : sig.chunks)
			if (c.wire != NULL)
				flag_wire(c.wire, create, set_int_driven, set_int_used, set_ext_driven, set_ext_used);
	}

	void handle_submodule(SubModule &submod)
	{
		log("Creating submodule %s (%s) of module %s.\n", submod.name.c_str(), submod.full_name.c_str(), module->name.c_str());

		wire_flags.clear();
		for (RTLIL::Cell *cell : submod.cells) {
			if (ct.cell_known(cell->type)) {
				for (auto &conn : cell->connections)
					flag_signal(conn.second, true, ct.cell_output(cell->type, conn.first), ct.cell_input(cell->type, conn.first), false, false);
			} else {
				log("WARNING: Port directions for cell %s (%s) are unknown. Assuming inout for all ports.\n", cell->name.c_str(), cell->type.c_str());
				for (auto &conn : cell->connections)
					flag_signal(conn.second, true, true, true, false, false);
			}
		}
		for (auto &it : module->cells) {
			RTLIL::Cell *cell = it.second;
			if (submod.cells.count(cell) > 0)
				continue;
			if (ct.cell_known(cell->type)) {
				for (auto &conn : cell->connections)
					flag_signal(conn.second, false, false, false, ct.cell_output(cell->type, conn.first), ct.cell_input(cell->type, conn.first));
			} else {
				flag_found_something = false;
				for (auto &conn : cell->connections)
					flag_signal(conn.second, false, false, false, true, true);
				if (flag_found_something)
					log("WARNING: Port directions for cell %s (%s) are unknown. Assuming inout for all ports.\n", cell->name.c_str(), cell->type.c_str());
			}
		}

		RTLIL::Module *new_mod = new RTLIL::Module;
		new_mod->name = submod.full_name;
		design->modules[new_mod->name] = new_mod;
		int port_counter = 1, auto_name_counter = 1;

		std::set<std::string> all_wire_names;
		for (auto &it : wire_flags) {
			all_wire_names.insert(it.first->name);
		}

		for (auto &it : wire_flags)
		{
			RTLIL::Wire *wire = it.first;
			wire_flags_t &flags = it.second;

			if (wire->port_input)
				flags.is_ext_driven = true;
			if (wire->port_output)
				flags.is_ext_used = true;

			RTLIL::Wire *new_wire = new RTLIL::Wire;
			new_wire->name = wire->name;
			new_wire->width = wire->width;
			new_wire->start_offset = wire->start_offset;
			new_wire->attributes = wire->attributes;

			if (flags.is_int_driven && flags.is_ext_used)
				new_wire->port_output = true;
			if (flags.is_ext_driven && flags.is_int_used)
				new_wire->port_input = true;

			if (flags.is_int_driven && flags.is_ext_driven)
				new_wire->port_input = true, new_wire->port_output = true;

			if (new_wire->port_input || new_wire->port_output) {
				new_wire->port_id = port_counter++;
				while (new_wire->name[0] == '$') {
					std::string new_wire_name = stringf("\\n%d", auto_name_counter++);
					if (all_wire_names.count(new_wire_name) == 0) {
						all_wire_names.insert(new_wire_name);
						new_wire->name = new_wire_name;
					}
				}
			}

			if (new_wire->port_input && new_wire->port_output)
				log("  signal %s: inout %s\n", wire->name.c_str(), new_wire->name.c_str());
			else if (new_wire->port_input)
				log("  signal %s: input %s\n", wire->name.c_str(), new_wire->name.c_str());
			else if (new_wire->port_output)
				log("  signal %s: output %s\n", wire->name.c_str(), new_wire->name.c_str());
			else
				log("  signal %s: internal\n", wire->name.c_str());

			new_mod->wires[new_wire->name] = new_wire;
			flags.new_wire = new_wire;
		}

		for (RTLIL::Cell *cell : submod.cells) {
			RTLIL::Cell *new_cell = new RTLIL::Cell(*cell);
			for (auto &conn : new_cell->connections)
				for (auto &c : conn.second.chunks)
					if (c.wire != NULL) {
						assert(wire_flags.count(c.wire) > 0);
						c.wire = wire_flags[c.wire].new_wire;
					}
			log("  cell %s (%s)\n", new_cell->name.c_str(), new_cell->type.c_str());
			new_mod->cells[new_cell->name] = new_cell;
			module->cells.erase(cell->name);
			delete cell;
		}
		submod.cells.clear();

		RTLIL::Cell *new_cell = new RTLIL::Cell;
		new_cell->name = submod.full_name;
		new_cell->type = submod.full_name;
		for (auto &it : wire_flags)
		{
			RTLIL::Wire *old_wire = it.first;
			RTLIL::Wire *new_wire = it.second.new_wire;
			if (new_wire->port_id > 0)
				new_cell->connections[new_wire->name] = RTLIL::SigSpec(old_wire);
		}
		module->cells[new_cell->name] = new_cell;
	}

	SubmodWorker(RTLIL::Design *design, RTLIL::Module *module) : design(design), module(module)
	{
		if (!design->selected_whole_module(module->name))
			return;

		if (module->processes.size() > 0) {
			log("Skipping module %s as it contains processes (run 'proc' pass first).\n", module->name.c_str());
			return;
		}

		if (module->memories.size() > 0) {
			log("Skipping module %s as it contains memories (run 'memory' pass first).\n", module->name.c_str());
			return;
		}

		ct.setup_internals();
		ct.setup_internals_mem();
		ct.setup_stdcells();
		ct.setup_stdcells_mem();

		for (auto &it : module->wires)
			it.second->attributes.erase("\\submod");

		for (auto &it : module->cells)
		{
			RTLIL::Cell *cell = it.second;
			if (cell->attributes.count("\\submod") == 0 || cell->attributes["\\submod"].str.size() == 0) {
				cell->attributes.erase("\\submod");
				continue;
			}

			std::string submod_str = cell->attributes["\\submod"].str;
			cell->attributes.erase("\\submod");

			if (submodules.count(submod_str) == 0) {
				submodules[submod_str].name = submod_str;
				submodules[submod_str].full_name = module->name + "_" + submod_str;
				while (design->modules.count(submodules[submod_str].full_name) != 0 ||
						module->count_id(submodules[submod_str].full_name) != 0)
					submodules[submod_str].full_name += "_";
			}

			submodules[submod_str].cells.insert(cell);
		}

		for (auto &it : submodules)
			handle_submodule(it.second);
	}
};

struct SubmodPass : public Pass {
	SubmodPass() : Pass("submod") { }
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing SUBMOD pass (moving cells to submodes as requested).\n");
		log_push();

		Pass::call(design, "opt_rmunused");
		log_header("Continuing SUBMOD pass.\n");

		extra_args(args, 1, design);

		std::set<std::string> handled_modules;

		bool did_something = true;
		while (did_something) {
			did_something = false;
			std::vector<std::string> queued_modules;
			for (auto &mod_it : design->modules)
				if (handled_modules.count(mod_it.first) == 0)
					queued_modules.push_back(mod_it.first);
			for (auto &modname : queued_modules)
				if (design->modules.count(modname) != 0) {
					SubmodWorker worker(design, design->modules[modname]);
					handled_modules.insert(modname);
					did_something = true;
				}
		}

		Pass::call(design, "opt_rmunused");
	}
} SubmodPass;
 
