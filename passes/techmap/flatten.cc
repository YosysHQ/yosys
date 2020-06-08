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

void apply_prefix(IdString prefix, IdString &id)
{
	if (id[0] == '\\')
		id = stringf("%s.%s", prefix.c_str(), id.c_str()+1);
	else
		id = stringf("$flatten%s.%s", prefix.c_str(), id.c_str());
}

void apply_prefix(IdString prefix, RTLIL::SigSpec &sig, RTLIL::Module *module)
{
	vector<SigChunk> chunks = sig;
	for (auto &chunk : chunks)
		if (chunk.wire != nullptr) {
			IdString wire_name = chunk.wire->name;
			apply_prefix(prefix, wire_name);
			log_assert(module->wire(wire_name) != nullptr);
			chunk.wire = module->wire(wire_name);
		}
	sig = chunks;
}

struct FlattenWorker
{
	bool ignore_wb = false;

	void flatten_cell(RTLIL::Design *design, RTLIL::Module *module, RTLIL::Cell *cell, RTLIL::Module *tpl, std::vector<RTLIL::Cell*> &new_cells)
	{
		if (tpl->processes.size() != 0) {
			log("Flattening yielded processes:");
			for (auto &it : tpl->processes)
				log(" %s",log_id(it.first));
			log("\n");
			log_error("Flattening yielded processes -> this is not supported.\n");
		}

		pool<string> extra_src_attrs = cell->get_strpool_attribute(ID::src);

		dict<IdString, IdString> memory_renames;

		for (auto &it : tpl->memories) {
			IdString m_name = it.first;
			apply_prefix(cell->name, m_name);
			RTLIL::Memory *m = module->addMemory(m_name, it.second);
			if (m->attributes.count(ID::src))
				m->add_strpool_attribute(ID::src, extra_src_attrs);
			memory_renames[it.first] = m->name;
			design->select(module, m);
		}

		dict<IdString, IdString> positional_ports;
		dict<Wire*, IdString> temp_renamed_wires;

		for (auto tpl_w : tpl->wires())
		{
			if (tpl_w->port_id > 0)
			{
				IdString posportname = stringf("$%d", tpl_w->port_id);
				positional_ports.emplace(posportname, tpl_w->name);
			}
			IdString w_name = tpl_w->name;
			apply_prefix(cell->name, w_name);
			RTLIL::Wire *w = module->wire(w_name);
			if (w != nullptr) {
				if (!w->get_bool_attribute(ID::hierconn)) {
					temp_renamed_wires[w] = w->name;
					module->rename(w, NEW_ID);
					w = nullptr;
				} else {
					w->attributes.erase(ID::hierconn);
					if (GetSize(w) < GetSize(tpl_w)) {
						log_warning("Widening signal %s.%s to match size of %s.%s (via %s.%s).\n", log_id(module), log_id(w),
								log_id(tpl), log_id(tpl_w), log_id(module), log_id(cell));
						w->width = GetSize(tpl_w);
					}
				}
			}
			if (w == nullptr) {
				w = module->addWire(w_name, tpl_w);
				w->port_input = false;
				w->port_output = false;
				w->port_id = 0;
				if (w->attributes.count(ID::src))
					w->add_strpool_attribute(ID::src, extra_src_attrs);
			}
			design->select(module, w);
		}

		SigMap sigmap(module);

		SigMap tpl_sigmap(tpl);
		pool<SigBit> tpl_written_bits;

		for (auto tpl_cell : tpl->cells())
		for (auto &conn : tpl_cell->connections())
			if (tpl_cell->output(conn.first))
				for (auto bit : tpl_sigmap(conn.second))
					tpl_written_bits.insert(bit);
		for (auto &conn : tpl->connections())
			for (auto bit : tpl_sigmap(conn.first))
				tpl_written_bits.insert(bit);

		SigMap port_signal_map;

		for (auto &it : cell->connections())
		{
			IdString portname = it.first;
			if (positional_ports.count(portname) > 0)
				portname = positional_ports.at(portname);
			if (tpl->wire(portname) == nullptr || tpl->wire(portname)->port_id == 0) {
				if (portname.begins_with("$"))
					log_error("Can't map port `%s' of cell `%s' to template `%s'!\n", portname.c_str(), cell->name.c_str(), tpl->name.c_str());
				continue;
			}

			if (GetSize(it.second) == 0)
				continue;

			RTLIL::Wire *w = tpl->wire(portname);
			RTLIL::SigSig c;

			if (w->port_output && !w->port_input) {
				c.first = it.second;
				c.second = RTLIL::SigSpec(w);
				apply_prefix(cell->name, c.second, module);
			} else if (!w->port_output && w->port_input) {
				c.first = RTLIL::SigSpec(w);
				c.second = it.second;
				apply_prefix(cell->name, c.first, module);
			} else {
				SigSpec sig_tpl = w, sig_tpl_pf = w, sig_mod = it.second;
				apply_prefix(cell->name, sig_tpl_pf, module);
				for (int i = 0; i < GetSize(sig_tpl) && i < GetSize(sig_mod); i++) {
					if (tpl_written_bits.count(tpl_sigmap(sig_tpl[i]))) {
						c.first.append(sig_mod[i]);
						c.second.append(sig_tpl_pf[i]);
					} else {
						c.first.append(sig_tpl_pf[i]);
						c.second.append(sig_mod[i]);
					}
				}
			}

			if (c.second.size() > c.first.size())
				c.second.remove(c.first.size(), c.second.size() - c.first.size());

			if (c.second.size() < c.first.size())
				c.second.append(RTLIL::SigSpec(RTLIL::State::S0, c.first.size() - c.second.size()));

			log_assert(c.first.size() == c.second.size());

			// connect internal and external wires

			if (sigmap(c.first).has_const())
				log_error("Mismatch in directionality for cell port %s.%s.%s: %s <= %s\n",
					log_id(module), log_id(cell), log_id(it.first), log_signal(c.first), log_signal(c.second));

			module->connect(c);
		}

		for (auto tpl_cell : tpl->cells())
		{
			IdString c_name = tpl_cell->name;
			apply_prefix(cell->name, c_name);

			RTLIL::Cell *c = module->addCell(c_name, tpl_cell);
			new_cells.push_back(c);
			design->select(module, c);

			for (auto &conn : c->connections())
			{
				RTLIL::SigSpec new_conn = conn.second;
				apply_prefix(cell->name, new_conn, module);
				port_signal_map.apply(new_conn);
				c->setPort(conn.first, std::move(new_conn));
			}

			if (c->type.in(ID($memrd), ID($memwr), ID($meminit))) {
				IdString memid = c->getParam(ID::MEMID).decode_string();
				log_assert(memory_renames.count(memid) != 0);
				c->setParam(ID::MEMID, Const(memory_renames[memid].str()));
			}

			if (c->type == ID($mem)) {
				IdString memid = c->getParam(ID::MEMID).decode_string();
				apply_prefix(cell->name, memid);
				c->setParam(ID::MEMID, Const(memid.c_str()));
			}

			if (c->attributes.count(ID::src))
				c->add_strpool_attribute(ID::src, extra_src_attrs);
		}

		for (auto &it : tpl->connections()) {
			RTLIL::SigSig c = it;
			apply_prefix(cell->name.str(), c.first, module);
			apply_prefix(cell->name.str(), c.second, module);
			port_signal_map.apply(c.first);
			port_signal_map.apply(c.second);
			module->connect(c);
		}

		module->remove(cell);

		for (auto &it : temp_renamed_wires)
		{
			Wire *w = it.first;
			IdString name = it.second;
			IdString altname = module->uniquify(name);
			Wire *other_w = module->wire(name);
			module->rename(other_w, altname);
			module->rename(w, name);
		}
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
	void help() YS_OVERRIDE
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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
