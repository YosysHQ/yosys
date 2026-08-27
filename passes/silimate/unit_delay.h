/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.     <akash@silimate.com>
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
 */

// Unit-level delay model shared by the timing-guarded rewrite passes, so that
// they agree on which arrivals dominate rather than each drifting on its own
// copy. Include after PRIVATE_NAMESPACE_BEGIN, and derive the pass worker from
// UnitDelayTiming; the worker owns filling driver_map and consumer_map, since
// it usually builds other connectivity in the same sweep.
//
// (opt_timing_balance and opt_carry_select carry their own variants: those cost
// a cell in fractional levels against its output width, which is a different
// currency and not interchangeable with this one.)

#ifndef UNIT_DELAY_H
#define UNIT_DELAY_H

#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <vector>

// Bit count of w, i.e. floor(log2(w)) + 1, the depth charged to a carry chain
// of that width.
inline int log2p1_int(int w)
{
	int n = 0;
	while (w > 0) { w >>= 1; n++; }
	return n < 1 ? 1 : n;
}

// Levels through one cell: carry-chain operators cost their log-depth,
// multipliers their full width, bitwise operators and muxes one level.
inline int estimate_cell_delay(RTLIL::Cell *cell)
{
	IdString t = cell->type;
	if (t.in(ID($not), ID($pos), ID($_NOT_), ID($_BUF_)))
		return 0;
	int width = 1;
	if (cell->hasParam(ID::Y_WIDTH))
		width = cell->getParam(ID::Y_WIDTH).as_int();
	else if (cell->hasParam(ID::WIDTH))
		width = cell->getParam(ID::WIDTH).as_int();
	if (t.in(ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor)))
		return width < 1 ? 1 : width;
	if (t.in(ID($add), ID($sub), ID($neg), ID($alu),
	         ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx)))
		return log2p1_int(width);
	// Comparators and reductions collapse their operand width to one bit.
	if (t.in(ID($lt), ID($le), ID($gt), ID($ge), ID($eq), ID($ne), ID($eqx), ID($nex),
	         ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor),
	         ID($reduce_bool), ID($logic_not), ID($logic_and), ID($logic_or)))
		return log2p1_int(cell->hasParam(ID::A_WIDTH) ? cell->getParam(ID::A_WIDTH).as_int() : width);
	if (t == ID($pmux))
		return log2p1_int(cell->hasParam(ID::S_WIDTH) ? cell->getParam(ID::S_WIDTH).as_int() : 1);
	return 1;
}

struct UnitDelayTiming
{
	RTLIL::Module *module;
	SigMap sigmap;

	// Filled by the derived worker. A bit maps to nullptr when it is driven by
	// more than one cell, which ends a path rather than picking a driver.
	dict<RTLIL::SigBit, RTLIL::Cell *> driver_map;
	dict<RTLIL::SigBit, std::vector<RTLIL::Cell *>> consumer_map;

	dict<RTLIL::SigBit, int> arrival_cache, depart_cache;
	pool<RTLIL::SigBit> arrival_active, depart_active;
	int module_depth = 0;
	bool module_depth_valid = false;

	UnitDelayTiming(RTLIL::Module *module) : module(module), sigmap(module) { }

	// Every rewrite invalidates the cached levels, so the next guard rebuilds.
	// The connectivity maps the derived worker owns are its own to refresh.
	void reset_timing()
	{
		arrival_cache.clear();
		arrival_active.clear();
		depart_cache.clear();
		depart_active.clear();
		module_depth_valid = false;
	}

	// Cached level, or 0 when absent (start point, constant, or broken loop edge).
	static int level_of(const dict<RTLIL::SigBit, int> &cache, RTLIL::SigBit bit)
	{
		auto it = cache.find(bit);
		return it == cache.end() ? 0 : it->second;
	}

	// Combinational driver of `bit`, and the bits feeding it. Null at a start
	// point (constant, undriven / multi-driven, or register output).
	RTLIL::Cell *driver_inputs(RTLIL::SigBit bit, std::vector<RTLIL::SigBit> &ins)
	{
		ins.clear();
		auto it = driver_map.find(bit);
		RTLIL::Cell *drv = it == driver_map.end() ? nullptr : it->second;
		if (drv == nullptr || drv->is_builtin_ff())
			return nullptr;
		for (auto &conn : drv->connections())
			if (drv->input(conn.first))
				for (auto &in_bit : sigmap(conn.second))
					ins.push_back(in_bit);
		return drv;
	}

	// Output bits of a cell, flattened across its output ports.
	void cell_outputs(RTLIL::Cell *cell, std::vector<RTLIL::SigBit> &outs)
	{
		outs.clear();
		for (auto &conn : cell->connections())
			if (cell->output(conn.first))
				for (auto &out_bit : sigmap(conn.second))
					outs.push_back(out_bit);
	}

	// Levels from a start point up to this bit. Iterative so a deep datapath
	// cannot blow the C stack; `*_active` breaks combinational loops.
	int arrival_bit(RTLIL::SigBit bit)
	{
		if (bit.wire == nullptr)
			return 0;
		if (arrival_cache.count(bit))
			return arrival_cache.at(bit);

		std::vector<RTLIL::SigBit> stack{bit}, ins;
		while (!stack.empty()) {
			RTLIL::SigBit b = stack.back();
			if (b.wire == nullptr || arrival_cache.count(b)) {
				stack.pop_back();
				continue;
			}

			// Push unresolved inputs; skip actives (loop) and constants (never cached).
			RTLIL::Cell *drv = driver_inputs(b, ins);
			bool ready = true;
			for (auto &in_bit : ins)
				if (in_bit.wire != nullptr && !arrival_cache.count(in_bit) &&
				    !arrival_active.count(in_bit)) {
					stack.push_back(in_bit);
					ready = false;
				}
			if (!ready) {
				arrival_active.insert(b);
				continue; // leave b on the stack; neighbours are above it now
			}

			int latest = 0;
			for (auto &in_bit : ins)
				latest = std::max(latest, level_of(arrival_cache, in_bit));
			arrival_cache[b] = drv == nullptr ? 0 : latest + estimate_cell_delay(drv);
			arrival_active.erase(b);
			stack.pop_back();
		}
		return arrival_cache.at(bit);
	}

	int arrival(const RTLIL::SigSpec &sig)
	{
		int t = 0;
		for (auto &bit : sigmap(sig))
			t = std::max(t, arrival_bit(bit));
		return t;
	}

	// Levels from this bit down to the latest endpoint that reads it.
	int depart_bit(RTLIL::SigBit bit)
	{
		if (bit.wire == nullptr)
			return 0;
		if (depart_cache.count(bit))
			return depart_cache.at(bit);

		std::vector<RTLIL::SigBit> stack{bit}, outs;
		while (!stack.empty()) {
			RTLIL::SigBit b = stack.back();
			if (b.wire == nullptr || depart_cache.count(b)) {
				stack.pop_back();
				continue;
			}

			// Push unresolved fanout bits; registers end a path (no neighbours).
			bool ready = true;
			auto it_cons = consumer_map.find(b);
			if (it_cons != consumer_map.end())
				for (auto cons : it_cons->second) {
					if (cons->is_builtin_ff())
						continue;
					cell_outputs(cons, outs);
					for (auto &out_bit : outs)
						if (out_bit.wire != nullptr && !depart_cache.count(out_bit) &&
						    !depart_active.count(out_bit)) {
							stack.push_back(out_bit);
							ready = false;
						}
				}
			if (!ready) {
				depart_active.insert(b);
				continue;
			}

			int worst = 0;
			if (it_cons != consumer_map.end())
				for (auto cons : it_cons->second) {
					if (cons->is_builtin_ff())
						continue;
					int latest = 0;
					cell_outputs(cons, outs);
					for (auto &out_bit : outs)
						latest = std::max(latest, level_of(depart_cache, out_bit));
					worst = std::max(worst, estimate_cell_delay(cons) + latest);
				}
			depart_cache[b] = worst;
			depart_active.erase(b);
			stack.pop_back();
		}
		return depart_cache.at(bit);
	}

	// Longest path through this signal, in the same unit-delay currency as the
	// module's own depth.
	int path_depth(const RTLIL::SigSpec &sig)
	{
		int t = 0;
		for (auto &bit : sigmap(sig))
			t = std::max(t, arrival_bit(bit) + depart_bit(bit));
		return t;
	}

	// The slack guard needs the module's longest path, which costs a full
	// arrival+depart walk of every cell. Most modules never reach the guard, so
	// pay for the walk on first use rather than up front.
	int longest_path()
	{
		if (module_depth_valid)
			return module_depth;
		module_depth_valid = true;
		module_depth = 0;
		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				if (!cell->output(conn.first))
					continue;
				for (auto &bit : sigmap(conn.second))
					module_depth = std::max(module_depth, arrival_bit(bit) + depart_bit(bit));
			}
		return module_depth;
	}
};

#endif
