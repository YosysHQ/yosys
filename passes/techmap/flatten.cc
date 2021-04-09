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
#include "kernel/utils.h"
#include "kernel/sigtools.h"

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

IdString concat_name(RTLIL::Cell *cell, IdString object_name)
{
	if (object_name[0] == '\\')
		return stringf("%s.%s", cell->name.c_str(), object_name.c_str() + 1);
	else {
		std::string object_name_str = object_name.str();
		if (object_name_str.substr(0, 8) == "$flatten")
			object_name_str.erase(0, 8);
		return stringf("$flatten%s.%s", cell->name.c_str(), object_name_str.c_str());
	}
}

template<class T>
IdString map_name(RTLIL::Cell *cell, T *object)
{
	return cell->module->uniquify(concat_name(cell, object->name));
}

template<class T>
void map_attributes(RTLIL::Cell *cell, T *object, IdString orig_object_name)
{
	if (object->has_attribute(ID::src))
		object->add_strpool_attribute(ID::src, cell->get_strpool_attribute(ID::src));

	// Preserve original names via the hdlname attribute, but only for objects with a fully public name.
	if (cell->name[0] == '\\' && (object->has_attribute(ID::hdlname) || orig_object_name[0] == '\\')) {
		std::vector<std::string> hierarchy;
		if (object->has_attribute(ID::hdlname))
			hierarchy = object->get_hdlname_attribute();
		else
			hierarchy.push_back(orig_object_name.str().substr(1));
		hierarchy.insert(hierarchy.begin(), cell->name.str().substr(1));
		object->set_hdlname_attribute(hierarchy);
	}
}

void map_sigspec(const dict<RTLIL::Wire*, RTLIL::Wire*> &map, RTLIL::SigSpec &sig, RTLIL::Module *into = nullptr)
{
	vector<SigChunk> chunks = sig;
	for (auto &chunk : chunks)
		if (chunk.wire != nullptr && chunk.wire->module != into)
			chunk.wire = map.at(chunk.wire);
	sig = chunks;
}

struct FlattenWorker
{
	bool ignore_wb = false;

	void flatten_cell(RTLIL::Design *design, RTLIL::Module *module, RTLIL::Cell *cell, RTLIL::Module *tpl, std::vector<RTLIL::Cell*> &new_cells)
	{
		// Copy the contents of the flattened cell

		dict<IdString, IdString> memory_map;
		for (auto &tpl_memory_it : tpl->memories) {
			RTLIL::Memory *new_memory = module->addMemory(map_name(cell, tpl_memory_it.second), tpl_memory_it.second);
			map_attributes(cell, new_memory, tpl_memory_it.second->name);
			memory_map[tpl_memory_it.first] = new_memory->name;
			design->select(module, new_memory);
		}

		dict<RTLIL::Wire*, RTLIL::Wire*> wire_map;
		dict<IdString, IdString> positional_ports;
		for (auto tpl_wire : tpl->wires()) {
			if (tpl_wire->port_id > 0)
				positional_ports.emplace(stringf("$%d", tpl_wire->port_id), tpl_wire->name);

			RTLIL::Wire *new_wire = nullptr;
			if (tpl_wire->name[0] == '\\') {
				RTLIL::Wire *hier_wire = module->wire(concat_name(cell, tpl_wire->name));
				if (hier_wire != nullptr && hier_wire->get_bool_attribute(ID::hierconn)) {
					hier_wire->attributes.erase(ID::hierconn);
					if (GetSize(hier_wire) < GetSize(tpl_wire)) {
						log_warning("Widening signal %s.%s to match size of %s.%s (via %s.%s).\n",
							log_id(module), log_id(hier_wire), log_id(tpl), log_id(tpl_wire), log_id(module), log_id(cell));
						hier_wire->width = GetSize(tpl_wire);
					}
					new_wire = hier_wire;
				}
			}
			if (new_wire == nullptr) {
				new_wire = module->addWire(map_name(cell, tpl_wire), tpl_wire);
				new_wire->port_input = new_wire->port_output = false;
				new_wire->port_id = false;
			}

			map_attributes(cell, new_wire, tpl_wire->name);
			wire_map[tpl_wire] = new_wire;
			design->select(module, new_wire);
		}

		for (auto &tpl_proc_it : tpl->processes) {
			RTLIL::Process *new_proc = module->addProcess(map_name(cell, tpl_proc_it.second), tpl_proc_it.second);
			map_attributes(cell, new_proc, tpl_proc_it.second->name);
			for (auto new_proc_sync : new_proc->syncs)
				for (auto &memwr_action : new_proc_sync->mem_write_actions)
					memwr_action.memid = memory_map.at(memwr_action.memid).str();
			auto rewriter = [&](RTLIL::SigSpec &sig) { map_sigspec(wire_map, sig); };
			new_proc->rewrite_sigspecs(rewriter);
			design->select(module, new_proc);
		}

		for (auto tpl_cell : tpl->cells()) {
			RTLIL::Cell *new_cell = module->addCell(map_name(cell, tpl_cell), tpl_cell);
			map_attributes(cell, new_cell, tpl_cell->name);
			if (new_cell->type.in(ID($memrd), ID($memwr), ID($meminit))) {
				IdString memid = new_cell->getParam(ID::MEMID).decode_string();
				new_cell->setParam(ID::MEMID, Const(memory_map.at(memid).str()));
			} else if (new_cell->type == ID($mem)) {
				IdString memid = new_cell->getParam(ID::MEMID).decode_string();
				new_cell->setParam(ID::MEMID, Const(concat_name(cell, memid).str()));
			}
			auto rewriter = [&](RTLIL::SigSpec &sig) { map_sigspec(wire_map, sig); };
			new_cell->rewrite_sigspecs(rewriter);
			design->select(module, new_cell);
			new_cells.push_back(new_cell);
		}

		for (auto &tpl_conn_it : tpl->connections()) {
			RTLIL::SigSig new_conn = tpl_conn_it;
			map_sigspec(wire_map, new_conn.first);
			map_sigspec(wire_map, new_conn.second);
			module->connect(new_conn);
		}

		// Attach port connections of the flattened cell

		pool<SigBit> tpl_driven;
		for (auto tpl_cell : tpl->cells())
			for (auto &tpl_conn : tpl_cell->connections())
				if (tpl_cell->output(tpl_conn.first))
					for (auto bit : tpl_conn.second)
						tpl_driven.insert(bit);
		for (auto &tpl_conn : tpl->connections())
			for (auto bit : tpl_conn.first)
				tpl_driven.insert(bit);

		SigMap sigmap(module);
		for (auto &port_it : cell->connections())
		{
			IdString port_name = port_it.first;
			if (positional_ports.count(port_name) > 0)
				port_name = positional_ports.at(port_name);
			if (tpl->wire(port_name) == nullptr || tpl->wire(port_name)->port_id == 0) {
				if (port_name.begins_with("$"))
					log_error("Can't map port `%s' of cell `%s' to template `%s'!\n",
						port_name.c_str(), cell->name.c_str(), tpl->name.c_str());
				continue;
			}

			if (GetSize(port_it.second) == 0)
				continue;

			RTLIL::Wire *tpl_wire = tpl->wire(port_name);
			RTLIL::SigSig new_conn;
			bool is_signed = false;
			if (tpl_wire->port_output && !tpl_wire->port_input) {
				new_conn.first = port_it.second;
				new_conn.second = tpl_wire;
				is_signed = tpl_wire->is_signed;
			} else if (!tpl_wire->port_output && tpl_wire->port_input) {
				new_conn.first = tpl_wire;
				new_conn.second = port_it.second;
				is_signed = new_conn.second.is_wire() && new_conn.second.as_wire()->is_signed;
			} else {
				SigSpec sig_tpl = tpl_wire, sig_mod = port_it.second;
				for (int i = 0; i < GetSize(sig_tpl) && i < GetSize(sig_mod); i++) {
					if (tpl_driven.count(sig_tpl[i])) {
						new_conn.first.append(sig_mod[i]);
						new_conn.second.append(sig_tpl[i]);
					} else {
						new_conn.first.append(sig_tpl[i]);
						new_conn.second.append(sig_mod[i]);
					}
				}
			}
			map_sigspec(wire_map, new_conn.first, module);
			map_sigspec(wire_map, new_conn.second, module);

			if (new_conn.second.size() > new_conn.first.size())
				new_conn.second.remove(new_conn.first.size(), new_conn.second.size() - new_conn.first.size());
			if (new_conn.second.size() < new_conn.first.size())
				new_conn.second.extend_u0(new_conn.first.size(), is_signed);
			log_assert(new_conn.first.size() == new_conn.second.size());

			if (sigmap(new_conn.first).has_const())
				log_error("Cell port %s.%s.%s is driving constant bits: %s <= %s\n",
					log_id(module), log_id(cell), log_id(port_it.first), log_signal(new_conn.first), log_signal(new_conn.second));

			module->connect(new_conn);
		}

		module->remove(cell);
	}

	void flatten_module(RTLIL::Design *design, RTLIL::Module *module, pool<RTLIL::Module*> &used_modules)
	{
		if (!design->selected(module) || module->get_blackbox_attribute(ignore_wb))
			return;

		std::vector<RTLIL::Cell*> worklist = module->selected_cells();
		while (!worklist.empty())
		{
			RTLIL::Cell *cell = worklist.back();
			worklist.pop_back();

			if (!design->has(cell->type))
				continue;

			RTLIL::Module *tpl = design->module(cell->type);
			if (tpl->get_blackbox_attribute(ignore_wb))
				continue;

			if (cell->get_bool_attribute(ID::keep_hierarchy) || tpl->get_bool_attribute(ID::keep_hierarchy)) {
				log("Keeping %s.%s (found keep_hierarchy attribute).\n", log_id(module), log_id(cell));
				used_modules.insert(tpl);
				continue;
			}

			log_debug("Flattening %s.%s (%s).\n", log_id(module), log_id(cell), log_id(cell->type));
			// If a design is fully selected and has a top module defined, topological sorting ensures that all cells
			// added during flattening are black boxes, and flattening is finished in one pass. However, when flattening
			// individual modules, this isn't the case, and the newly added cells might have to be flattened further.
			flatten_cell(design, module, cell, tpl, worklist);
		}
	}
};

struct FlattenPass : public Pass {
	FlattenPass() : Pass("flatten", "flatten design") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    flatten [options] [selection]\n");
		log("\n");
		log("This pass flattens the design by replacing cells by their implementation. This\n");
		log("pass is very similar to the 'techmap' pass. The only difference is that this\n");
		log("pass is using the current design as mapping library.\n");
		log("\n");
		log("Cells and/or modules with the 'keep_hierarchy' attribute set will not be\n");
		log("flattened by this command.\n");
		log("\n");
		log("    -wb\n");
		log("        Ignore the 'whitebox' attribute on cell implementations.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing FLATTEN pass (flatten design).\n");
		log_push();

		FlattenWorker worker;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-wb") {
				worker.ignore_wb = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Module *top = nullptr;
		if (design->full_selection())
			for (auto module : design->modules())
				if (module->get_bool_attribute(ID::top))
					top = module;

		pool<RTLIL::Module*> used_modules;
		if (top == nullptr)
			used_modules = design->modules();
		else
			used_modules.insert(top);

		TopoSort<RTLIL::Module*, IdString::compare_ptr_by_name<RTLIL::Module>> topo_modules;
		pool<RTLIL::Module*> worklist = used_modules;
		while (!worklist.empty()) {
			RTLIL::Module *module = worklist.pop();
			for (auto cell : module->selected_cells()) {
				RTLIL::Module *tpl = design->module(cell->type);
				if (tpl != nullptr) {
					if (topo_modules.database.count(tpl) == 0)
						worklist.insert(tpl);
					topo_modules.edge(tpl, module);
				}
			}
		}

		if (!topo_modules.sort())
			log_error("Cannot flatten a design containing recursive instantiations.\n");

		for (auto module : topo_modules.sorted)
			worker.flatten_module(design, module, used_modules);

		if (top != nullptr)
			for (auto module : design->modules().to_vector())
				if (!used_modules[module] && !module->get_blackbox_attribute(worker.ignore_wb)) {
					log("Deleting now unused module %s.\n", log_id(module));
					design->remove(module);
				}

		log_pop();
	}
} FlattenPass;

PRIVATE_NAMESPACE_END
