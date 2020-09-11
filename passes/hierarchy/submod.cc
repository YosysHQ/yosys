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
#include "kernel/sigtools.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SubmodWorker
{
	CellTypes ct;
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap;

	bool copy_mode;
	bool hidden_mode;
	std::string opt_name;

	struct SubModule
	{
		std::string name, full_name;
		pool<RTLIL::Cell*> cells;
	};

	std::map<std::string, SubModule> submodules;

	struct wire_flags_t {
		RTLIL::Wire *new_wire;
		RTLIL::Const is_int_driven;
		bool is_int_used, is_ext_driven, is_ext_used;
		wire_flags_t(RTLIL::Wire* wire) : new_wire(nullptr), is_int_driven(State::S0, GetSize(wire)), is_int_used(false), is_ext_driven(false), is_ext_used(false) { }
	};
	std::map<RTLIL::Wire*, wire_flags_t> wire_flags;
	bool flag_found_something;

	void flag_wire(RTLIL::Wire *wire, bool create, bool set_int_used, bool set_ext_driven, bool set_ext_used)
	{
		if (wire_flags.count(wire) == 0) {
			if (!create)
				return;
			wire_flags.emplace(wire, wire);
		}
		if (set_int_used)
			wire_flags.at(wire).is_int_used = true;
		if (set_ext_driven)
			wire_flags.at(wire).is_ext_driven = true;
		if (set_ext_used)
			wire_flags.at(wire).is_ext_used = true;
		flag_found_something = true;
	}

	void flag_signal(const RTLIL::SigSpec &sig, bool create, bool set_int_driven, bool set_int_used, bool set_ext_driven, bool set_ext_used)
	{
		for (auto &c : sig.chunks())
			if (c.wire != nullptr) {
				flag_wire(c.wire, create, set_int_used, set_ext_driven, set_ext_used);
				if (set_int_driven)
					for (int i = c.offset; i < c.offset+c.width; i++) {
						wire_flags.at(c.wire).is_int_driven[i] = State::S1;
						flag_found_something = true;
					}
			}
	}

	void handle_submodule(SubModule &submod)
	{
		log("Creating submodule %s (%s) of module %s.\n", submod.name.c_str(), submod.full_name.c_str(), module->name.c_str());

		wire_flags.clear();
		for (RTLIL::Cell *cell : submod.cells) {
			if (ct.cell_known(cell->type)) {
				for (auto &conn : cell->connections())
					flag_signal(conn.second, true, ct.cell_output(cell->type, conn.first), ct.cell_input(cell->type, conn.first), false, false);
			} else {
				log_warning("Port directions for cell %s (%s) are unknown. Assuming inout for all ports.\n", cell->name.c_str(), cell->type.c_str());
				for (auto &conn : cell->connections())
					flag_signal(conn.second, true, true, true, false, false);
			}
		}
		for (auto cell : module->cells()) {
			if (submod.cells.count(cell) > 0)
				continue;
			if (ct.cell_known(cell->type)) {
				for (auto &conn : cell->connections())
					flag_signal(conn.second, false, false, false, ct.cell_output(cell->type, conn.first), ct.cell_input(cell->type, conn.first));
			} else {
				flag_found_something = false;
				for (auto &conn : cell->connections())
					flag_signal(conn.second, false, false, false, true, true);
				if (flag_found_something)
					log_warning("Port directions for cell %s (%s) are unknown. Assuming inout for all ports.\n", cell->name.c_str(), cell->type.c_str());
			}
		}

		RTLIL::Module *new_mod = new RTLIL::Module;
		new_mod->name = submod.full_name;
		design->add(new_mod);
		int auto_name_counter = 1;

		std::set<RTLIL::IdString> all_wire_names;
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
			else {
				auto sig = sigmap(wire);
				for (auto c : sig.chunks())
					if (c.wire && c.wire->port_output) {
						flags.is_ext_used = true;
						break;
					}
			}

			bool new_wire_port_input = false;
			bool new_wire_port_output = false;

			if (!flags.is_int_driven.is_fully_zero() && flags.is_ext_used)
				new_wire_port_output = true;
			if (flags.is_ext_driven && flags.is_int_used)
				new_wire_port_input = true;

			if (!flags.is_int_driven.is_fully_zero() && flags.is_ext_driven)
				new_wire_port_input = true, new_wire_port_output = true;

			std::string new_wire_name = wire->name.str();
			if (new_wire_port_input || new_wire_port_output) {
				if (new_wire_name[0] == '$')
					while (1) {
						std::string next_wire_name = stringf("%s\\n%d", hidden_mode ? "$submod" : "", auto_name_counter++);
						if (all_wire_names.count(next_wire_name) == 0) {
							all_wire_names.insert(next_wire_name);
							new_wire_name = next_wire_name;
							break;
						}
					}
				else if (hidden_mode)
					new_wire_name = stringf("$submod%s", new_wire_name.c_str());
			}

			RTLIL::Wire *new_wire = new_mod->addWire(new_wire_name, wire->width);
			new_wire->port_input = new_wire_port_input;
			new_wire->port_output = new_wire_port_output;
			new_wire->start_offset = wire->start_offset;
			new_wire->attributes = wire->attributes;
			if (!flags.is_int_driven.is_fully_zero()) {
				new_wire->attributes.erase(ID::init);
				auto sig = sigmap(wire);
				for (int i = 0; i < GetSize(sig); i++) {
					if (flags.is_int_driven[i] == State::S0)
						continue;
					if (!sig[i].wire)
						continue;
					auto it = sig[i].wire->attributes.find(ID::init);
					if (it != sig[i].wire->attributes.end()) {
						auto jt = new_wire->attributes.insert(std::make_pair(ID::init, Const(State::Sx, GetSize(sig)))).first;
						jt->second[i] = it->second[sig[i].offset];
						it->second[sig[i].offset] = State::Sx;
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

			flags.new_wire = new_wire;
		}

		new_mod->fixup_ports();
		ct.setup_module(new_mod);

		for (RTLIL::Cell *cell : submod.cells) {
			RTLIL::Cell *new_cell = new_mod->addCell(cell->name, cell);
			for (auto &conn : new_cell->connections_)
				for (auto &bit : conn.second)
					if (bit.wire != nullptr) {
						log_assert(wire_flags.count(bit.wire) > 0);
						bit.wire = wire_flags.at(bit.wire).new_wire;
					}
			log("  cell %s (%s)\n", new_cell->name.c_str(), new_cell->type.c_str());
			if (!copy_mode)
				module->remove(cell);
		}
		submod.cells.clear();

		if (!copy_mode) {
			RTLIL::Cell *new_cell = module->addCell(submod.full_name, submod.full_name);
			for (auto &it : wire_flags)
			{
				RTLIL::SigSpec old_sig = sigmap(it.first);
				RTLIL::Wire *new_wire = it.second.new_wire;
				if (new_wire->port_id > 0) {
					if (new_wire->port_output)
						for (int i = 0; i < GetSize(old_sig); i++) {
							auto &b = old_sig[i];
							// Prevents "ERROR: Mismatch in directionality ..." when flattening
							if (!b.wire)
								b = module->addWire(NEW_ID);
							// Prevents "Warning: multiple conflicting drivers ..."
							else if (!it.second.is_int_driven[i])
								b = module->addWire(NEW_ID);
						}
					new_cell->setPort(new_wire->name, old_sig);
				}
			}
		}
	}

	SubmodWorker(RTLIL::Design *design, RTLIL::Module *module, bool copy_mode = false, bool hidden_mode = false, std::string opt_name = std::string()) :
			design(design), module(module), sigmap(module), copy_mode(copy_mode), hidden_mode(hidden_mode), opt_name(opt_name)
	{
		if (!design->selected_whole_module(module->name) && opt_name.empty())
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
		ct.setup_design(design);

		for (auto port : module->ports) {
			auto wire = module->wire(port);
			if (wire->port_output)
				sigmap.add(wire);
		}

		if (opt_name.empty())
		{
			for (auto wire : module->wires())
				wire->attributes.erase(ID::submod);

			for (auto cell : module->cells())
			{
				if (cell->attributes.count(ID::submod) == 0 || cell->attributes[ID::submod].bits.size() == 0) {
					cell->attributes.erase(ID::submod);
					continue;
				}

				std::string submod_str = cell->attributes[ID::submod].decode_string();
				cell->attributes.erase(ID::submod);

				if (submodules.count(submod_str) == 0) {
					submodules[submod_str].name = submod_str;
					submodules[submod_str].full_name = module->name.str() + "_" + submod_str;
					while (design->module(submodules[submod_str].full_name) != nullptr ||
							module->count_id(submodules[submod_str].full_name) != 0)
						submodules[submod_str].full_name += "_";
				}

				submodules[submod_str].cells.insert(cell);
			}
		}
		else
		{
			for (auto cell : module->cells())
			{
				if (!design->selected(module, cell))
					continue;
				submodules[opt_name].name = opt_name;
				submodules[opt_name].full_name = RTLIL::escape_id(opt_name);
				submodules[opt_name].cells.insert(cell);
			}

			if (submodules.size() == 0)
				log("Nothing selected -> do nothing.\n");
		}

		for (auto &it : submodules)
			handle_submodule(it.second);
	}
};

struct SubmodPass : public Pass {
	SubmodPass() : Pass("submod", "moving part of a module to a new submodule") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    submod [options] [selection]\n");
		log("\n");
		log("This pass identifies all cells with the 'submod' attribute and moves them to\n");
		log("a newly created module. The value of the attribute is used as name for the\n");
		log("cell that replaces the group of cells with the same attribute value.\n");
		log("\n");
		log("This pass can be used to create a design hierarchy in flat design. This can\n");
		log("be useful for analyzing or reverse-engineering a design.\n");
		log("\n");
		log("This pass only operates on completely selected modules with no processes\n");
		log("or memories.\n");
		log("\n");
		log("    -copy\n");
		log("        by default the cells are 'moved' from the source module and the source\n");
		log("        module will use an instance of the new module after this command is\n");
		log("        finished. call with -copy to not modify the source module.\n");
		log("\n");
		log("    -name <name>\n");
		log("        don't use the 'submod' attribute but instead use the selection. only\n");
		log("        objects from one module might be selected. the value of the -name option\n");
		log("        is used as the value of the 'submod' attribute instead.\n");
		log("\n");
		log("    -hidden\n");
		log("        instead of creating submodule ports with public names, create ports with\n");
		log("        private names so that a subsequent 'flatten; clean' call will restore the\n");
		log("        original module with original public names.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing SUBMOD pass (moving cells to submodules as requested).\n");
		log_push();

		std::string opt_name;
		bool copy_mode = false;
		bool hidden_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-name" && argidx+1 < args.size()) {
				opt_name = args[++argidx];
				continue;
			}
			if (args[argidx] == "-copy") {
				copy_mode = true;
				continue;
			}
			if (args[argidx] == "-hidden") {
				hidden_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (opt_name.empty())
		{
			Pass::call(design, "opt_clean");
			log_header(design, "Continuing SUBMOD pass.\n");

			std::set<RTLIL::IdString> handled_modules;

			bool did_something = true;
			while (did_something) {
				did_something = false;
				std::vector<RTLIL::IdString> queued_modules;
				for (auto mod : design->modules())
					if (handled_modules.count(mod->name) == 0 && design->selected_whole_module(mod->name))
						queued_modules.push_back(mod->name);
				for (auto &modname : queued_modules)
					if (design->module(modname) != nullptr) {
						SubmodWorker worker(design, design->module(modname), copy_mode, hidden_mode);
						handled_modules.insert(modname);
						did_something = true;
					}
			}

			Pass::call(design, "opt_clean");
		}
		else
		{
			RTLIL::Module *module = nullptr;
			for (auto mod : design->selected_modules()) {
				if (module != nullptr)
					log_cmd_error("More than one module selected: %s %s\n", module->name.c_str(), mod->name.c_str());
				module = mod;
			}
			if (module == nullptr)
				log("Nothing selected -> do nothing.\n");
			else {
				Pass::call_on_module(design, module, "opt_clean");
				log_header(design, "Continuing SUBMOD pass.\n");
				SubmodWorker worker(design, module, copy_mode, hidden_mode, opt_name);
			}
		}

		log_pop();
	}
} SubmodPass;

PRIVATE_NAMESPACE_END
