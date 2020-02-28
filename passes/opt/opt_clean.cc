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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using RTLIL::id2cstr;

struct keep_cache_t
{
	Design *design;
	dict<Module*, bool> cache;

	void reset(Design *design = nullptr)
	{
		this->design = design;
		cache.clear();
	}

	bool query(Module *module)
	{
		log_assert(design != nullptr);

		if (module == nullptr)
			return false;

		if (cache.count(module))
			return cache.at(module);

		cache[module] = true;
		if (!module->get_bool_attribute(ID::keep)) {
		    bool found_keep = false;
		    for (auto cell : module->cells())
			if (query(cell, true /* ignore_specify */)) {
			    found_keep = true;
			    break;
			}
		    cache[module] = found_keep;
		}

		return cache[module];
	}

	bool query(Cell *cell, bool ignore_specify = false)
	{
		if (cell->type.in(ID($memwr), ID($meminit), ID($assert), ID($assume), ID($live), ID($fair), ID($cover)))
			return true;

		if (!ignore_specify && cell->type.in(ID($specify2), ID($specify3), ID($specrule)))
			return true;

		if (cell->has_keep_attr())
			return true;

		if (cell->module && cell->module->design)
			return query(cell->module->design->module(cell->type));

		return false;
	}
};

keep_cache_t keep_cache;
CellTypes ct_reg, ct_all;
int count_rm_cells, count_rm_wires;

void rmunused_module_cells(Module *module, bool verbose)
{
	SigMap sigmap(module);
	pool<Cell*> queue, unused;
	pool<SigBit> used_raw_bits;
	dict<SigBit, pool<Cell*>> wire2driver;
	dict<SigBit, vector<string>> driver_driver_logs;

	SigMap raw_sigmap;
	for (auto &it : module->connections_) {
		for (int i = 0; i < GetSize(it.second); i++) {
			if (it.second[i].wire != nullptr)
				raw_sigmap.add(it.first[i], it.second[i]);
		}
	}

	for (auto &it : module->cells_) {
		Cell *cell = it.second;
		for (auto &it2 : cell->connections()) {
			if (ct_all.cell_known(cell->type) && !ct_all.cell_output(cell->type, it2.first))
				continue;
			for (auto raw_bit : it2.second) {
				if (raw_bit.wire == nullptr)
					continue;
				auto bit = sigmap(raw_bit);
				if (bit.wire == nullptr && ct_all.cell_known(cell->type))
					driver_driver_logs[raw_sigmap(raw_bit)].push_back(stringf("Driver-driver conflict "
							"for %s between cell %s.%s and constant %s in %s: Resolved using constant.",
							log_signal(raw_bit), log_id(cell), log_id(it2.first), log_signal(bit), log_id(module)));
				if (bit.wire != nullptr)
					wire2driver[bit].insert(cell);
			}
		}
		if (keep_cache.query(cell))
			queue.insert(cell);
		else
			unused.insert(cell);
	}

	for (auto &it : module->wires_) {
		Wire *wire = it.second;
		if (wire->port_output || wire->get_bool_attribute(ID::keep)) {
			for (auto bit : sigmap(wire))
			for (auto c : wire2driver[bit])
				queue.insert(c), unused.erase(c);
			for (auto raw_bit : SigSpec(wire))
				used_raw_bits.insert(raw_sigmap(raw_bit));
		}
	}

	while (!queue.empty())
	{
		pool<SigBit> bits;
		for (auto cell : queue)
		for (auto &it : cell->connections())
			if (!ct_all.cell_known(cell->type) || ct_all.cell_input(cell->type, it.first))
				for (auto bit : sigmap(it.second))
					bits.insert(bit);

		queue.clear();
		for (auto bit : bits)
		for (auto c : wire2driver[bit])
			if (unused.count(c))
				queue.insert(c), unused.erase(c);
	}

	unused.sort(RTLIL::sort_by_name_id<RTLIL::Cell>());

	for (auto cell : unused) {
		if (verbose)
			log_debug("  removing unused `%s' cell `%s'.\n", cell->type.c_str(), cell->name.c_str());
		module->design->scratchpad_set_bool("opt.did_something", true);
		module->remove(cell);
		count_rm_cells++;
	}

	for (auto &it : module->cells_) {
		Cell *cell = it.second;
		for (auto &it2 : cell->connections()) {
			if (ct_all.cell_known(cell->type) && !ct_all.cell_input(cell->type, it2.first))
				continue;
			for (auto raw_bit : raw_sigmap(it2.second))
				used_raw_bits.insert(raw_bit);
		}
	}

	for (auto it : driver_driver_logs) {
		if (used_raw_bits.count(it.first))
			for (auto msg : it.second)
				log_warning("%s\n", msg.c_str());
	}
}

int count_nontrivial_wire_attrs(RTLIL::Wire *w)
{
	int count = w->attributes.size();
	count -= w->attributes.count(ID(src));
	count -= w->attributes.count(ID(unused_bits));
	return count;
}

bool compare_signals(RTLIL::SigBit &s1, RTLIL::SigBit &s2, SigPool &regs, SigPool &conns, pool<RTLIL::Wire*> &direct_wires)
{
	RTLIL::Wire *w1 = s1.wire;
	RTLIL::Wire *w2 = s2.wire;

	if (w1 == NULL || w2 == NULL)
		return w2 == NULL;

	if (w1->port_input != w2->port_input)
		return w2->port_input;

	if ((w1->port_input && w1->port_output) != (w2->port_input && w2->port_output))
		return !(w2->port_input && w2->port_output);

	if (w1->name[0] == '\\' && w2->name[0] == '\\') {
		if (regs.check_any(s1) != regs.check_any(s2))
			return regs.check_any(s2);
		if (direct_wires.count(w1) != direct_wires.count(w2))
			return direct_wires.count(w2) != 0;
		if (conns.check_any(s1) != conns.check_any(s2))
			return conns.check_any(s2);
	}

	if (w1->port_output != w2->port_output)
		return w2->port_output;

	if (w1->name[0] != w2->name[0])
		return w2->name[0] == '\\';

	int attrs1 = count_nontrivial_wire_attrs(w1);
	int attrs2 = count_nontrivial_wire_attrs(w2);

	if (attrs1 != attrs2)
		return attrs2 > attrs1;

	return strcmp(w2->name.c_str(), w1->name.c_str()) < 0;
}

bool check_public_name(RTLIL::IdString id)
{
	if (id.begins_with("$"))
		return false;
	const std::string &id_str = id.str();
	if (id.begins_with("\\_") && (id.ends_with("_") || id_str.find("_[") != std::string::npos))
		return false;
	if (id_str.find(".$") != std::string::npos)
		return false;
	return true;
}

bool rmunused_module_signals(RTLIL::Module *module, bool purge_mode, bool verbose)
{
	SigPool register_signals;
	SigPool connected_signals;

	if (!purge_mode)
		for (auto &it : module->cells_) {
			RTLIL::Cell *cell = it.second;
			if (ct_reg.cell_known(cell->type))
				for (auto &it2 : cell->connections())
					if (ct_reg.cell_output(cell->type, it2.first))
						register_signals.add(it2.second);
			for (auto &it2 : cell->connections())
				connected_signals.add(it2.second);
		}

	SigMap assign_map(module);
	pool<RTLIL::SigSpec> direct_sigs;
	pool<RTLIL::Wire*> direct_wires;
	for (auto &it : module->cells_) {
		RTLIL::Cell *cell = it.second;
		if (ct_all.cell_known(cell->type))
			for (auto &it2 : cell->connections())
				if (ct_all.cell_output(cell->type, it2.first))
					direct_sigs.insert(assign_map(it2.second));
	}
	for (auto &it : module->wires_) {
		if (direct_sigs.count(assign_map(it.second)) || it.second->port_input)
			direct_wires.insert(it.second);
	}

	for (auto &it : module->wires_) {
		RTLIL::Wire *wire = it.second;
		for (int i = 0; i < wire->width; i++) {
			RTLIL::SigBit s1 = RTLIL::SigBit(wire, i), s2 = assign_map(s1);
			if (!compare_signals(s1, s2, register_signals, connected_signals, direct_wires))
				assign_map.add(s1);
		}
	}

	module->connections_.clear();

	SigPool used_signals;
	SigPool raw_used_signals;
	SigPool used_signals_nodrivers;
	for (auto &it : module->cells_) {
		RTLIL::Cell *cell = it.second;
		for (auto &it2 : cell->connections_) {
			assign_map.apply(it2.second);
			raw_used_signals.add(it2.second);
			used_signals.add(it2.second);
			if (!ct_all.cell_output(cell->type, it2.first))
				used_signals_nodrivers.add(it2.second);
		}
	}
	for (auto &it : module->wires_) {
		RTLIL::Wire *wire = it.second;
		if (wire->port_id > 0) {
			RTLIL::SigSpec sig = RTLIL::SigSpec(wire);
			raw_used_signals.add(sig);
			assign_map.apply(sig);
			used_signals.add(sig);
			if (!wire->port_input)
				used_signals_nodrivers.add(sig);
		}
		if (wire->get_bool_attribute(ID::keep)) {
			RTLIL::SigSpec sig = RTLIL::SigSpec(wire);
			assign_map.apply(sig);
			used_signals.add(sig);
		}
	}

	pool<RTLIL::Wire*> del_wires_queue;
	for (auto wire : module->wires())
	{
		SigSpec s1 = SigSpec(wire), s2 = assign_map(s1);
		log_assert(GetSize(s1) == GetSize(s2));

		Const initval;
		if (wire->attributes.count(ID(init)))
			initval = wire->attributes.at(ID(init));
		if (GetSize(initval) != GetSize(wire))
			initval.bits.resize(GetSize(wire), State::Sx);
		if (initval.is_fully_undef())
			wire->attributes.erase(ID(init));

		if (GetSize(wire) == 0) {
			// delete zero-width wires, unless they are module ports
			if (wire->port_id == 0)
				goto delete_this_wire;
		} else
		if (wire->port_id != 0 || wire->get_bool_attribute(ID::keep) || !initval.is_fully_undef()) {
			// do not delete anything with "keep" or module ports or initialized wires
		} else
		if (!purge_mode && check_public_name(wire->name) && (raw_used_signals.check_any(s1) || used_signals.check_any(s2) || s1 != s2)) {
			// do not get rid of public names unless in purge mode or if the wire is entirely unused, not even aliased
		} else
		if (!raw_used_signals.check_any(s1)) {
			// delete wires that aren't used by anything directly
			goto delete_this_wire;
		} else
		if (!used_signals.check_any(s2)) {
			// delete wires that aren't used by anything indirectly, even though other wires may alias it
			goto delete_this_wire;
		}

		if (0)
		{
	delete_this_wire:
			del_wires_queue.insert(wire);
		}
		else
		{
			RTLIL::SigSig new_conn;
			for (int i = 0; i < GetSize(s1); i++)
				if (s1[i] != s2[i]) {
					if (s2[i] == State::Sx && (initval[i] == State::S0 || initval[i] == State::S1)) {
						s2[i] = initval[i];
						initval[i] = State::Sx;
					}
					new_conn.first.append_bit(s1[i]);
					new_conn.second.append_bit(s2[i]);
				}
			if (new_conn.first.size() > 0) {
				if (initval.is_fully_undef())
					wire->attributes.erase(ID(init));
				else
					wire->attributes.at(ID(init)) = initval;
				used_signals.add(new_conn.first);
				used_signals.add(new_conn.second);
				module->connect(new_conn);
			}

			if (!used_signals_nodrivers.check_all(s2)) {
				std::string unused_bits;
				for (int i = 0; i < GetSize(s2); i++) {
					if (s2[i].wire == NULL)
						continue;
					if (!used_signals_nodrivers.check(s2[i])) {
						if (!unused_bits.empty())
							unused_bits += " ";
						unused_bits += stringf("%d", i);
					}
				}
				if (unused_bits.empty() || wire->port_id != 0)
					wire->attributes.erase(ID(unused_bits));
				else
					wire->attributes[ID(unused_bits)] = RTLIL::Const(unused_bits);
			} else {
				wire->attributes.erase(ID(unused_bits));
			}
		}
	}

	int del_temp_wires_count = 0;
	for (auto wire : del_wires_queue) {
		if (ys_debug() || (check_public_name(wire->name) && verbose))
			log_debug("  removing unused non-port wire %s.\n", wire->name.c_str());
		else
			del_temp_wires_count++;
	}

	module->remove(del_wires_queue);
	count_rm_wires += GetSize(del_wires_queue);

	if (verbose && del_temp_wires_count)
		log_debug("  removed %d unused temporary wires.\n", del_temp_wires_count);

	return !del_wires_queue.empty();
}

bool rmunused_module_init(RTLIL::Module *module, bool purge_mode, bool verbose)
{
	bool did_something = false;
	CellTypes fftypes;
	fftypes.setup_internals_mem();

	SigMap sigmap(module);
	dict<SigBit, State> qbits;

	for (auto cell : module->cells())
		if (fftypes.cell_known(cell->type) && cell->hasPort(ID(Q)))
		{
			SigSpec sig = cell->getPort(ID(Q));

			for (int i = 0; i < GetSize(sig); i++)
			{
				SigBit bit = sig[i];

				if (bit.wire == nullptr || bit.wire->attributes.count(ID(init)) == 0)
					continue;

				Const init = bit.wire->attributes.at(ID(init));

				if (i >= GetSize(init) || init[i] == State::Sx || init[i] == State::Sz)
					continue;

				sigmap.add(bit);
				qbits[bit] = init[i];
			}
		}

	for (auto wire : module->wires())
	{
		if (!purge_mode && wire->name[0] == '\\')
			continue;

		if (wire->attributes.count(ID(init)) == 0)
			continue;

		Const init = wire->attributes.at(ID(init));

		for (int i = 0; i < GetSize(wire) && i < GetSize(init); i++)
		{
			if (init[i] == State::Sx || init[i] == State::Sz)
				continue;

			SigBit wire_bit = SigBit(wire, i);
			SigBit mapped_wire_bit = sigmap(wire_bit);

			if (wire_bit == mapped_wire_bit)
				goto next_wire;

			if (qbits.count(sigmap(SigBit(wire, i))) == 0)
				goto next_wire;

			if (qbits.at(sigmap(SigBit(wire, i))) != init[i])
				goto next_wire;
		}

		if (verbose)
			log_debug("  removing redundant init attribute on %s.\n", log_id(wire));

		wire->attributes.erase(ID(init));
		did_something = true;
	next_wire:;
	}

	return did_something;
}

void rmunused_module(RTLIL::Module *module, bool purge_mode, bool verbose, bool rminit)
{
	if (verbose)
		log("Finding unused cells or wires in module %s..\n", module->name.c_str());

	std::vector<RTLIL::Cell*> delcells;
	for (auto cell : module->cells())
		if (cell->type.in(ID($pos), ID($_BUF_)) && !cell->has_keep_attr()) {
			bool is_signed = cell->type == ID($pos) && cell->getParam(ID(A_SIGNED)).as_bool();
			RTLIL::SigSpec a = cell->getPort(ID::A);
			RTLIL::SigSpec y = cell->getPort(ID::Y);
			a.extend_u0(GetSize(y), is_signed);
			module->connect(y, a);
			delcells.push_back(cell);
		}
	for (auto cell : delcells) {
		if (verbose)
			log_debug("  removing buffer cell `%s': %s = %s\n", cell->name.c_str(),
					log_signal(cell->getPort(ID::Y)), log_signal(cell->getPort(ID::A)));
		module->remove(cell);
	}
	if (!delcells.empty())
		module->design->scratchpad_set_bool("opt.did_something", true);

	rmunused_module_cells(module, verbose);
	while (rmunused_module_signals(module, purge_mode, verbose)) { }

	if (rminit && rmunused_module_init(module, purge_mode, verbose))
		while (rmunused_module_signals(module, purge_mode, verbose)) { }
}

struct OptCleanPass : public Pass {
	OptCleanPass() : Pass("opt_clean", "remove unused cells and wires") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_clean [options] [selection]\n");
		log("\n");
		log("This pass identifies wires and cells that are unused and removes them. Other\n");
		log("passes often remove cells but leave the wires in the design or reconnect the\n");
		log("wires but leave the old cells in the design. This pass can be used to clean up\n");
		log("after the passes that do the actual work.\n");
		log("\n");
		log("This pass only operates on completely selected modules without processes.\n");
		log("\n");
		log("    -purge\n");
		log("        also remove internal nets if they have a public name\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool purge_mode = false;

		log_header(design, "Executing OPT_CLEAN pass (remove unused cells and wires).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge") {
				purge_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		keep_cache.reset(design);

		ct_reg.setup_internals_mem();
		ct_reg.setup_stdcells_mem();

		ct_all.setup(design);

		count_rm_cells = 0;
		count_rm_wires = 0;

		for (auto module : design->selected_whole_modules_warn()) {
			if (module->has_processes_warn())
				continue;
			rmunused_module(module, purge_mode, true, true);
		}

		if (count_rm_cells > 0 || count_rm_wires > 0)
			log("Removed %d unused cells and %d unused wires.\n", count_rm_cells, count_rm_wires);

		design->optimize();
		design->sort();
		design->check();

		keep_cache.reset();
		ct_reg.clear();
		ct_all.clear();
		log_pop();
	}
} OptCleanPass;

struct CleanPass : public Pass {
	CleanPass() : Pass("clean", "remove unused cells and wires") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    clean [options] [selection]\n");
		log("\n");
		log("This is identical to 'opt_clean', but less verbose.\n");
		log("\n");
		log("When commands are separated using the ';;' token, this command will be executed\n");
		log("between the commands.\n");
		log("\n");
		log("When commands are separated using the ';;;' token, this command will be executed\n");
		log("in -purge mode between the commands.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool purge_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge") {
				purge_mode = true;
				continue;
			}
			break;
		}
		if (argidx < args.size())
			extra_args(args, argidx, design);

		keep_cache.reset(design);

		ct_reg.setup_internals_mem();
		ct_reg.setup_stdcells_mem();

		ct_all.setup(design);

		count_rm_cells = 0;
		count_rm_wires = 0;

		for (auto module : design->selected_whole_modules()) {
			if (module->has_processes())
				continue;
			rmunused_module(module, purge_mode, ys_debug(), false);
		}

		log_suppressed();
		if (count_rm_cells > 0 || count_rm_wires > 0)
			log("Removed %d unused cells and %d unused wires.\n", count_rm_cells, count_rm_wires);

		design->optimize();
		design->sort();
		design->check();

		keep_cache.reset();
		ct_reg.clear();
		ct_all.clear();
	}
} CleanPass;

PRIVATE_NAMESPACE_END
