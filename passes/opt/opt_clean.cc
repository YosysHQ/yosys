/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/ffinit.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using RTLIL::id2cstr;

bool should_be_kept(Design *d, Cell *cell)
{
	if (cell->type.in(ID($meminit), ID($meminit_v2), ID($memwr), ID($memwr_v2)))
		return true;

	if (cell->type.in(ID($assert), ID($assume), ID($live), ID($fair), ID($cover), ID($check)))
		return true;

	if (cell->type.in(ID($overwrite_tag), ID($print)))
		return true;

	if (cell->type.in(ID($specify2), ID($specify3), ID($specrule)))
		return true;

	if (cell->has_keep_attr())
		return true;

	// TODO: is this sufficient?
	if (d->module(cell->type) && d->module(cell->type)->get_bool_attribute(ID::keep))
		return true;

	return false;
}

void rmunused_coarse(Design *d, Module *m)
{
	CellTypes ct(d);

	// the private wires we are keeping
	pool<Wire *> keep;
	std::vector<Wire *> keep_queue;

	// only among private wires
	dict<Wire *, std::vector<Wire *>> wire_dependencies;

	for (auto w : m->wires())
	if (!w->name.isPublic() && (w->port_input || w->port_output || w->get_bool_attribute(ID::keep)))
	if (!keep.count(w)) {
		keep.insert(w);
		keep_queue.push_back(w);
	}

	for (auto conn : m->connections())
	for (int i = 0; i < conn.first.size(); i++)
	if (conn.first[i].wire && conn.second[i].wire && !conn.second[i].wire->name.isPublic()) {
		if (conn.first[i].wire->name.isPublic()) {
			Wire *rhs = conn.second[i].wire;
			if (!keep.count(rhs)) {
				keep.insert(rhs);
				keep_queue.push_back(rhs);
			}
		} else {
			wire_dependencies[conn.first[i].wire].push_back(conn.second[i].wire);
		}
	}

	for (auto cell : m->cells()) {
		std::vector<Wire *> driven_wires;
		std::vector<Wire *> consumed_wires;

		for (auto conn : cell->connections()) {
			if (ct.cell_output(cell->type, conn.first)) {
				for (auto chunk : conn.second.chunks())
				if (chunk.wire)
					driven_wires.push_back(chunk.wire);
			} else if (ct.cell_input(cell->type, conn.first)) {
				for (auto chunk : conn.second.chunks())
				if (chunk.wire)
					consumed_wires.push_back(chunk.wire);
			} else {
				for (auto chunk : conn.second.chunks())
				if (chunk.wire) {
					driven_wires.push_back(chunk.wire);
					consumed_wires.push_back(chunk.wire);
				}
			}
		}

		if (should_be_kept(d, cell))
			goto cell_kept;

		for (auto wire : driven_wires)
		if (wire->name.isPublic() || keep.count(wire))
			goto cell_kept;

		for (auto driven : driven_wires)
		for (auto consumed : consumed_wires)
		if (!consumed->name.isPublic())
			wire_dependencies[driven].push_back(consumed);
		continue;

	cell_kept:
		for (auto consumed : consumed_wires)
		if (!consumed->name.isPublic() && !keep.count(consumed)) {
			keep.insert(consumed);
			keep_queue.push_back(consumed);
		}
	}

	for (int i = 0; i < (int) keep_queue.size(); i++) {
		Wire *w = keep_queue[i];
		for (auto w2 : wire_dependencies[w])
		if (!keep.count(w2)) {
			keep.insert(w2);
			keep_queue.push_back(w2);
		}
	}

	std::vector<Cell *> to_remove_cells;
	pool<Wire *> to_remove_wires;
	for (auto cell : m->cells()) {
		if (should_be_kept(d, cell))
			goto cell_kept2;

		for (auto conn : cell->connections())
		if (!ct.cell_input(cell->type, conn.first))
		for (auto chunk : conn.second.chunks())
		if (chunk.wire && (chunk.wire->name.isPublic() || keep.count(chunk.wire)))
			goto cell_kept2;

		to_remove_cells.push_back(cell);
		continue;		

	cell_kept2:
		;
	}

	int removed_wires = 0, removed_cells = 0;

	for (auto w : m->wires())
	if (!w->name.isPublic() && !keep.count(w)) {
		removed_wires++;
		to_remove_wires.insert(w);
	}
	for (auto cell : to_remove_cells) {
		removed_cells++;
		m->remove(cell);
	}
	m->remove(to_remove_wires);
	m->check();

	std::vector<SigSig> new_conns;
	for (auto conn : m->connections())
	if (!conn.first.empty())
		new_conns.push_back(conn);
	std::swap(new_conns, m->connections_);

	log("Removed %d wires and %d cells in module %s.\n", removed_wires, removed_cells, log_id(m));
}

struct keep_cache_t
{
	Design *design;
	dict<Module*, bool> cache;
	bool purge_mode = false;

	void reset(Design *design = nullptr, bool purge_mode = false)
	{
		this->design = design;
		this->purge_mode = purge_mode;
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
		    for (auto wire : module->wires())
			if (wire->get_bool_attribute(ID::keep)) {
			    found_keep = true;
			    break;
			}
		    cache[module] = found_keep;
		}

		return cache[module];
	}

	bool query(Cell *cell, bool ignore_specify = false)
	{
		if (cell->type.in(ID($assert), ID($assume), ID($live), ID($fair), ID($cover)))
			return true;

		if (cell->type.in(ID($overwrite_tag)))
			return true;

		if (!ignore_specify && cell->type.in(ID($specify2), ID($specify3), ID($specrule)))
			return true;

		if (cell->type == ID($print) || cell->type == ID($check))
			return true;

		if (cell->has_keep_attr())
			return true;

		if (!purge_mode && cell->type == ID($scopeinfo))
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
	dict<IdString, pool<Cell*>> mem2cells;
	pool<IdString> mem_unused;
	pool<Cell*> queue, unused;
	pool<SigBit> used_raw_bits;
	dict<SigBit, pool<Cell*>> wire2driver;
	dict<SigBit, vector<string>> driver_driver_logs;
	FfInitVals ffinit(&sigmap, module);

	SigMap raw_sigmap;
	for (auto &it : module->connections_) {
		for (int i = 0; i < GetSize(it.second); i++) {
			if (it.second[i].wire != nullptr)
				raw_sigmap.add(it.first[i], it.second[i]);
		}
	}

	for (auto &it : module->memories) {
		mem_unused.insert(it.first);
	}

	for (Cell *cell : module->cells()) {
		if (cell->type.in(ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2))) {
			IdString mem_id = cell->getParam(ID::MEMID).decode_string();
			mem2cells[mem_id].insert(cell);
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
		pool<IdString> mems;
		for (auto cell : queue) {
			for (auto &it : cell->connections())
				if (!ct_all.cell_known(cell->type) || ct_all.cell_input(cell->type, it.first))
					for (auto bit : sigmap(it.second))
						bits.insert(bit);

			if (cell->type.in(ID($memrd), ID($memrd_v2))) {
				IdString mem_id = cell->getParam(ID::MEMID).decode_string();
				if (mem_unused.count(mem_id)) {
					mem_unused.erase(mem_id);
					mems.insert(mem_id);
				}
			}
		}

		queue.clear();

		for (auto bit : bits)
		for (auto c : wire2driver[bit])
			if (unused.count(c))
				queue.insert(c), unused.erase(c);

		for (auto mem : mems)
		for (auto c : mem2cells[mem])
			if (unused.count(c))
				queue.insert(c), unused.erase(c);
	}

	unused.sort(RTLIL::sort_by_name_id<RTLIL::Cell>());

	for (auto cell : unused) {
		if (verbose)
			log_debug("  removing unused `%s' cell `%s'.\n", cell->type.c_str(), cell->name.c_str());
		module->design->scratchpad_set_bool("opt.did_something", true);
		if (RTLIL::builtin_ff_cell_types().count(cell->type))
			ffinit.remove_init(cell->getPort(ID::Q));
		module->remove(cell);
		count_rm_cells++;
	}

	for (auto it : mem_unused)
	{
		if (verbose)
			log_debug("  removing unused memory `%s'.\n", it.c_str());
		delete module->memories.at(it);
		module->memories.erase(it);
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
	count -= w->attributes.count(ID::src);
	count -= w->attributes.count(ID::hdlname);
	count -= w->attributes.count(ID(scopename));
	count -= w->attributes.count(ID::unused_bits);
	return count;
}

// Should we pick `s2` over `s1` to represent a signal?
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

	if (w1->name.isPublic() && w2->name.isPublic()) {
		if (regs.check(s1) != regs.check(s2))
			return regs.check(s2);
		if (direct_wires.count(w1) != direct_wires.count(w2))
			return direct_wires.count(w2) != 0;
		if (conns.check_any(s1) != conns.check_any(s2))
			return conns.check_any(s2);
	}

	if (w1->port_output != w2->port_output)
		return w2->port_output;

	if (w1->name[0] != w2->name[0])
		return w2->name.isPublic();

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
	// `register_signals` and `connected_signals` will help us decide later on
	// on picking representatives out of groups of connected signals
	SigPool register_signals;
	SigPool connected_signals;
	if (!purge_mode)
		for (auto &it : module->cells_) {
			RTLIL::Cell *cell = it.second;
			if (ct_reg.cell_known(cell->type)) {
				bool clk2fflogic = cell->get_bool_attribute(ID(clk2fflogic));
				for (auto &it2 : cell->connections())
					if (clk2fflogic ? it2.first == ID::D : ct_reg.cell_output(cell->type, it2.first))
						register_signals.add(it2.second);
			}
			for (auto &it2 : cell->connections())
				connected_signals.add(it2.second);
		}

	SigMap assign_map(module);

	// construct a pool of wires which are directly driven by a known celltype,
	// this will influence our choice of representatives
	pool<RTLIL::Wire*> direct_wires;
	{
		pool<RTLIL::SigSpec> direct_sigs;
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
	}

	// weight all options for representatives with `compare_signals`,
	// the one that wins will be what `assign_map` maps to
	for (auto &it : module->wires_) {
		RTLIL::Wire *wire = it.second;
		for (int i = 0; i < wire->width; i++) {
			RTLIL::SigBit s1 = RTLIL::SigBit(wire, i), s2 = assign_map(s1);
			if (!compare_signals(s1, s2, register_signals, connected_signals, direct_wires))
				assign_map.add(s1);
		}
	}

	// we are removing all connections
	module->connections_.clear();

	// used signals sigmapped
	SigPool used_signals;
	// used signals pre-sigmapped
	SigPool raw_used_signals;
	// used signals sigmapped, ignoring drivers (we keep track of this to set `unused_bits`)
	SigPool used_signals_nodrivers;

	// gather the usage information for cells
	for (auto &it : module->cells_) {
		RTLIL::Cell *cell = it.second;
		for (auto &it2 : cell->connections_) {
			assign_map.apply(it2.second); // modify the cell connection in place
			raw_used_signals.add(it2.second);
			used_signals.add(it2.second);
			if (!ct_all.cell_output(cell->type, it2.first))
				used_signals_nodrivers.add(it2.second);
		}
	}

	// gather the usage information for ports, wires with `keep`,
	// also gather init bits
	dict<RTLIL::SigBit, RTLIL::State> init_bits;
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
		auto it2 = wire->attributes.find(ID::init);
		if (it2 != wire->attributes.end()) {
			RTLIL::Const &val = it2->second;
			SigSpec sig = assign_map(wire);
			for (int i = 0; i < GetSize(val) && i < GetSize(sig); i++)
				if (val.bits[i] != State::Sx)
					init_bits[sig[i]] = val.bits[i];
			wire->attributes.erase(it2);
		}
	}

	// set init attributes on all wires of a connected group
	for (auto wire : module->wires()) {
		bool found = false;
		Const val(State::Sx, wire->width);
		for (int i = 0; i < wire->width; i++) {
			auto it = init_bits.find(RTLIL::SigBit(wire, i));
			if (it != init_bits.end()) {
				val.bits[i] = it->second;
				found = true;
			}
		}
		if (found)
			wire->attributes[ID::init] = val;
	}

	// now decide for each wire if we should be deleting it
	pool<RTLIL::Wire*> del_wires_queue;
	for (auto wire : module->wires())
	{
		SigSpec s1 = SigSpec(wire), s2 = assign_map(s1);
		log_assert(GetSize(s1) == GetSize(s2));

		Const initval;
		if (wire->attributes.count(ID::init))
			initval = wire->attributes.at(ID::init);
		if (GetSize(initval) != GetSize(wire))
			initval.bits.resize(GetSize(wire), State::Sx);
		if (initval.is_fully_undef())
			wire->attributes.erase(ID::init);

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
			// this path shouldn't be possible: this wire is used directly (otherwise it would get cleaned up above), and indirectly
			// used wires are a superset of those used directly
			log_assert(false);
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
					new_conn.first.append(s1[i]);
					new_conn.second.append(s2[i]);
				}
			if (new_conn.first.size() > 0) {
				if (initval.is_fully_undef())
					wire->attributes.erase(ID::init);
				else
					wire->attributes.at(ID::init) = initval;
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
					wire->attributes.erase(ID::unused_bits);
				else
					wire->attributes[ID::unused_bits] = RTLIL::Const(unused_bits);
			} else {
				wire->attributes.erase(ID::unused_bits);
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

	if (!del_wires_queue.empty())
		module->design->scratchpad_set_bool("opt.did_something", true);

	return !del_wires_queue.empty();
}

bool rmunused_module_init(RTLIL::Module *module, bool verbose)
{
	bool did_something = false;
	CellTypes fftypes;
	fftypes.setup_internals_mem();

	SigMap sigmap(module);
	dict<SigBit, State> qbits;

	for (auto cell : module->cells())
		if (fftypes.cell_known(cell->type) && cell->hasPort(ID::Q))
		{
			SigSpec sig = cell->getPort(ID::Q);

			for (int i = 0; i < GetSize(sig); i++)
			{
				SigBit bit = sig[i];

				if (bit.wire == nullptr || bit.wire->attributes.count(ID::init) == 0)
					continue;

				Const init = bit.wire->attributes.at(ID::init);

				if (i >= GetSize(init) || init[i] == State::Sx || init[i] == State::Sz)
					continue;

				sigmap.add(bit);
				qbits[bit] = init[i];
			}
		}

	for (auto wire : module->wires())
	{
		if (wire->attributes.count(ID::init) == 0)
			continue;

		Const init = wire->attributes.at(ID::init);

		for (int i = 0; i < GetSize(wire) && i < GetSize(init); i++)
		{
			if (init[i] == State::Sx || init[i] == State::Sz)
				continue;

			SigBit wire_bit = SigBit(wire, i);
			SigBit mapped_wire_bit = sigmap(wire_bit);

			if (wire_bit == mapped_wire_bit)
				goto next_wire;

			if (mapped_wire_bit.wire) {
				if (qbits.count(mapped_wire_bit) == 0)
					goto next_wire;

				if (qbits.at(mapped_wire_bit) != init[i])
					goto next_wire;
			}
			else {
				if (mapped_wire_bit == State::Sx || mapped_wire_bit == State::Sz)
					goto next_wire;

				if (mapped_wire_bit != init[i]) {
					log_warning("Initial value conflict for %s resolving to %s but with init %s.\n", log_signal(wire_bit), log_signal(mapped_wire_bit), log_signal(init[i]));
					goto next_wire;
				}
			}
		}

		if (verbose)
			log_debug("  removing redundant init attribute on %s.\n", log_id(wire));

		wire->attributes.erase(ID::init);
		did_something = true;
	next_wire:;
	}

	if (did_something)
		module->design->scratchpad_set_bool("opt.did_something", true);

	return did_something;
}

void rmunused_module(RTLIL::Module *module, bool purge_mode, bool verbose, bool rminit)
{
	if (verbose)
		log("Finding unused cells or wires in module %s..\n", module->name.c_str());

	std::vector<RTLIL::Cell*> delcells;
	for (auto cell : module->cells())
		if (cell->type.in(ID($pos), ID($_BUF_)) && !cell->has_keep_attr()) {
			bool is_signed = cell->type == ID($pos) && cell->getParam(ID::A_SIGNED).as_bool();
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

	if (rminit && rmunused_module_init(module, verbose))
		while (rmunused_module_signals(module, purge_mode, verbose)) { }
}

struct OptCleanPass : public Pass {
	OptCleanPass() : Pass("opt_clean", "remove unused cells and wires") { }
	void help() override
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
		log("    -coarse\n");
		log("        perform a fast, conservative clean-up in which no public wires are\n");
		log("        removed and wire usage is analyzed at a coarse level without\n");
		log("        distinguishing individual bits\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool purge_mode = false;
		bool coarse_mode = false;

		log_header(design, "Executing OPT_CLEAN pass (remove unused cells and wires).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge")
				purge_mode = true;
			if (args[argidx] == "-coarse")
				coarse_mode = true;
			else
				break;
		}
		extra_args(args, argidx, design);

		if (coarse_mode && purge_mode)
			log_cmd_error("Coarse and purge modes cannot be combined.\n");

		keep_cache.reset(design, purge_mode);

		ct_reg.setup_internals_mem();
		ct_reg.setup_internals_anyinit();
		ct_reg.setup_stdcells_mem();

		ct_all.setup(design);

		count_rm_cells = 0;
		count_rm_wires = 0;

		for (auto module : design->selected_whole_modules_warn()) {
			if (module->has_processes_warn())
				continue;
			if (coarse_mode)
				rmunused_coarse(design, module);
			else
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
	void help() override
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
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
		extra_args(args, argidx, design);

		keep_cache.reset(design);

		ct_reg.setup_internals_mem();
		ct_reg.setup_internals_anyinit();
		ct_reg.setup_stdcells_mem();

		ct_all.setup(design);

		count_rm_cells = 0;
		count_rm_wires = 0;

		for (auto module : design->selected_whole_modules()) {
			if (module->has_processes())
				continue;
			rmunused_module(module, purge_mode, ys_debug(), true);
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
