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

#include "opt_status.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <set>

using RTLIL::id2cstr;

static CellTypes ct;

static void rmunused_module_cells(RTLIL::Module *module)
{
	SigMap assign_map(module);
	std::set<RTLIL::Cell*> queue, unused;

	SigSet<RTLIL::Cell*> wire2driver;
	for (auto &it : module->cells) {
		RTLIL::Cell *cell = it.second;
		for (auto &it2 : cell->connections) {
			if (!ct.cell_input(cell->type, it2.first)) {
				RTLIL::SigSpec sig = it2.second;
				assign_map.apply(sig);
				wire2driver.insert(sig, cell);
			}
		}
		if (cell->type == "$memwr")
			queue.insert(cell);
		unused.insert(cell);
	}

	for (auto &it : module->wires) {
		RTLIL::Wire *wire = it.second;
		if (wire->port_output) {
			std::set<RTLIL::Cell*> cell_list;
			RTLIL::SigSpec sig = RTLIL::SigSpec(wire);
			assign_map.apply(sig);
			wire2driver.find(sig, cell_list);
			for (auto cell : cell_list)
				queue.insert(cell);
		}
	}

	while (queue.size() > 0)
	{
		std::set<RTLIL::Cell*> new_queue;
		for (auto cell : queue)
			unused.erase(cell);
		for (auto cell : queue) {
			for (auto &it : cell->connections) {
				if (!ct.cell_output(cell->type, it.first)) {
					std::set<RTLIL::Cell*> cell_list;
					RTLIL::SigSpec sig = it.second;
					assign_map.apply(sig);
					wire2driver.find(sig, cell_list);
					for (auto cell : cell_list) {
						if (unused.count(cell) > 0)
							new_queue.insert(cell);
					}
				}
			}
		}
		queue.swap(new_queue);
	}

	for (auto cell : unused) {
		log("  removing unused `%s' cell `%s'.\n", cell->type.c_str(), cell->name.c_str());
		OPT_DID_SOMETHING = true;
		module->cells.erase(cell->name);
		delete cell;
	}
}

static bool compare_signals(RTLIL::SigSpec &s1, RTLIL::SigSpec &s2)
{
	assert(s1.width == 1);
	assert(s2.width == 1);
	assert(s1.chunks.size() == 1);
	assert(s2.chunks.size() == 1);

	RTLIL::Wire *w1 = s1.chunks[0].wire;
	RTLIL::Wire *w2 = s2.chunks[0].wire;

	if (w1 == NULL || w2 == NULL)
		return w2 == NULL;

	if (w1->port_input != w2->port_input)
		return w2->port_input;

	if (w1->name[0] != w2->name[0])
		return w2->name[0] == '\\';

	if (w1->attributes.size() != w2->attributes.size())
		return w2->attributes.size() > w1->attributes.size();

	return w2->name < w1->name;
}

static bool check_public_name(RTLIL::IdString id)
{
	if (id[0] == '$')
		return false;
#if 0
	if (id.find(".$") != std::string::npos)
		return false;
#endif
	return true;
}

static void rmunused_module_signals(RTLIL::Module *module)
{
	SigMap assign_map(module);
	for (auto &it : module->wires) {
		RTLIL::Wire *wire = it.second;
		for (int i = 0; i < wire->width; i++) {
			RTLIL::SigSpec s1 = RTLIL::SigSpec(wire, 1, i), s2 = assign_map(s1);
			if (!compare_signals(s1, s2))
				assign_map.add(s1);
		}
	}

	module->connections.clear();

	SigPool used_signals;
	SigPool used_signals_nodrivers;
	for (auto &it : module->cells) {
		RTLIL::Cell *cell = it.second;
		for (auto &it2 : cell->connections) {
			assign_map.apply(it2.second);
			used_signals.add(it2.second);
			if (!ct.cell_output(cell->type, it2.first))
				used_signals_nodrivers.add(it2.second);
		}
	}
	for (auto &it : module->wires) {
		RTLIL::Wire *wire = it.second;
		if (wire->port_id > 0) {
			RTLIL::SigSpec sig = RTLIL::SigSpec(wire);
			assign_map.apply(sig);
			used_signals.add(sig);
			if (!wire->port_input)
				used_signals_nodrivers.add(sig);
		}
	}

	std::vector<RTLIL::Wire*> del_wires;
	for (auto &it : module->wires) {
		RTLIL::Wire *wire = it.second;
		if (check_public_name(wire->name)) {
			RTLIL::SigSpec s1 = RTLIL::SigSpec(wire), s2 = s1;
			assign_map.apply(s2);
			if (!used_signals.check_any(s2) && wire->port_id == 0) {
				log("  removing unused non-port wire %s.\n", wire->name.c_str());
				del_wires.push_back(wire);
			} else {
				s1.expand();
				s2.expand();
				assert(s1.chunks.size() == s2.chunks.size());
				RTLIL::SigSig new_conn;
				for (size_t i = 0; i < s1.chunks.size(); i++)
					if (s1.chunks[i] != s2.chunks[i]) {
						new_conn.first.append(s1.chunks[i]);
						new_conn.second.append(s2.chunks[i]);
					}
				if (new_conn.first.width > 0) {
					new_conn.first.optimize();
					new_conn.second.optimize();
					module->connections.push_back(new_conn);
				}
			}
		} else {
			if (!used_signals.check_any(RTLIL::SigSpec(wire)))
				del_wires.push_back(wire);
		}
		RTLIL::SigSpec sig = assign_map(RTLIL::SigSpec(wire));
		if (!used_signals_nodrivers.check_any(sig)) {
			std::string unused_bits;
			sig.expand();
			for (size_t i = 0; i < sig.chunks.size(); i++) {
				if (sig.chunks[i].wire == NULL)
					continue;
				if (!used_signals_nodrivers.check_any(sig)) {
					if (!unused_bits.empty())
						unused_bits += " ";
					unused_bits += stringf("%zd", i);
				}
			}
			if (unused_bits.empty() || wire->port_id != 0)
				wire->attributes.erase("\\unused_bits");
			else
				wire->attributes["\\unused_bits"] = RTLIL::Const(unused_bits);
		} else {
			wire->attributes.erase("\\unused_bits");
		}
	}

	for (auto wire : del_wires) {
		module->wires.erase(wire->name);
		delete wire;
	}

	if (del_wires.size() > 0)
		log("  removed %zd unused temporary wires.\n", del_wires.size());
}

static void rmunused_module(RTLIL::Module *module)
{
	log("Finding unused cells or wires in module %s..\n", module->name.c_str());

	rmunused_module_cells(module);
	rmunused_module_signals(module);
}

struct OptRmUnusedPass : public Pass {
	OptRmUnusedPass() : Pass("opt_rmunused", "remove unused cells and wires") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_rmunused [selection]\n");
		log("\n");
		log("This pass identifies wires and cells that are unused and removes them. Other\n");
		log("often remove cells but leave the wires in the design or reconnect the wires\n");
		log("but leave the old cells in the design. This pass can be used to clean up after\n");
		log("the passes that do the actual work.\n");
		log("\n");
		log("This pass only operates on completely selected modules without processes.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing OPT_RMUNUSED pass (remove unused cells and wires).\n");
		log_push();

		extra_args(args, 1, design);

		ct.setup_internals();
		ct.setup_internals_mem();
		ct.setup_stdcells();
		ct.setup_stdcells_mem();

		for (auto &mod_it : design->modules) {
			if (!design->selected_whole_module(mod_it.first)) {
				if (design->selected(mod_it.second))
					log("Skipping module %s as it is only partially selected.\n", id2cstr(mod_it.second->name));
				continue;
			}
			if (mod_it.second->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", mod_it.second->name.c_str());
			} else {
				rmunused_module(mod_it.second);
			}
		}

		ct.clear();
		log_pop();
	}
} OptRmUnusedPass;
 
