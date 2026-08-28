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

	// Memoized per cell, not per bit: every output bit of a cell shares one
	// arrival (the max over all its inputs) and every input bit shares one
	// departure, so a per-bit cache recomputed the same number once per bit and
	// rescanned the cell's whole port list each time -- O(width**2) per cell.
	dict<RTLIL::Cell *, int> cell_arrival, cell_depart;
	pool<RTLIL::Cell *> arrival_active, depart_active;
	int module_depth = 0;
	bool module_depth_valid = false;

	UnitDelayTiming(RTLIL::Module *module) : module(module), sigmap(module) { }

	// Every rewrite invalidates the cached levels, so the next guard rebuilds.
	// The connectivity maps the derived worker owns are its own to refresh.
	void reset_timing()
	{
		cell_arrival.clear();
		arrival_active.clear();
		cell_depart.clear();
		depart_active.clear();
		module_depth_valid = false;
	}

	// Combinational driver of `bit`, or null at a start point (constant,
	// undriven / multi-driven, or register output).
	RTLIL::Cell *driver_of(RTLIL::SigBit bit)
	{
		if (bit.wire == nullptr)
			return nullptr;
		auto it = driver_map.find(bit);
		RTLIL::Cell *drv = it == driver_map.end() ? nullptr : it->second;
		return drv == nullptr || drv->is_builtin_ff() ? nullptr : drv;
	}

	// Levels from a start point up to this cell's outputs. Iterative so a deep
	// datapath cannot blow the C stack; `*_active` breaks combinational loops by
	// charging the back edge zero.
	int arrival_of(RTLIL::Cell *cell)
	{
		if (cell == nullptr)
			return 0;
		auto hit = cell_arrival.find(cell);
		if (hit != cell_arrival.end())
			return hit->second;

		std::vector<RTLIL::Cell *> stack{cell};
		while (!stack.empty()) {
			RTLIL::Cell *c = stack.back();
			if (cell_arrival.count(c)) {
				stack.pop_back();
				continue;
			}

			// Resolve the driving cells, pushing the ones not yet known
			bool ready = true;
			int latest = 0;
			for (auto &conn : c->connections()) {
				if (!c->input(conn.first))
					continue;
				for (auto &in_bit : sigmap(conn.second)) {
					RTLIL::Cell *drv = driver_of(in_bit);
					if (drv == nullptr)
						continue; // start point, contributes 0
					auto it = cell_arrival.find(drv);
					if (it != cell_arrival.end())
						latest = std::max(latest, it->second);
					else if (!arrival_active.count(drv)) {
						stack.push_back(drv);
						ready = false;
					}
				}
			}
			if (!ready) {
				arrival_active.insert(c);
				continue; // leave c on the stack; its drivers are above it now
			}

			cell_arrival[c] = latest + estimate_cell_delay(c);
			arrival_active.erase(c);
			stack.pop_back();
		}
		return cell_arrival.at(cell);
	}

	int arrival_bit(RTLIL::SigBit bit) { return arrival_of(driver_of(bit)); }

	int arrival(const RTLIL::SigSpec &sig)
	{
		int t = 0;
		for (auto &bit : sigmap(sig))
			t = std::max(t, arrival_bit(bit));
		return t;
	}

	// Levels from this cell's inputs down to the latest endpoint below it.
	int depart_of(RTLIL::Cell *cell)
	{
		if (cell == nullptr || cell->is_builtin_ff())
			return 0;
		auto hit = cell_depart.find(cell);
		if (hit != cell_depart.end())
			return hit->second;

		std::vector<RTLIL::Cell *> stack{cell};
		while (!stack.empty()) {
			RTLIL::Cell *c = stack.back();
			if (cell_depart.count(c)) {
				stack.pop_back();
				continue;
			}

			// Resolve the reading cells; registers end a path
			bool ready = true;
			int worst = 0;
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				for (auto &out_bit : sigmap(conn.second)) {
					if (out_bit.wire == nullptr)
						continue;
					auto it_cons = consumer_map.find(out_bit);
					if (it_cons == consumer_map.end())
						continue;
					for (auto cons : it_cons->second) {
						if (cons->is_builtin_ff())
							continue;
						auto it = cell_depart.find(cons);
						if (it != cell_depart.end())
							worst = std::max(worst, it->second);
						else if (!depart_active.count(cons)) {
							stack.push_back(cons);
							ready = false;
						}
					}
				}
			}
			if (!ready) {
				depart_active.insert(c);
				continue;
			}

			cell_depart[c] = worst + estimate_cell_delay(c);
			depart_active.erase(c);
			stack.pop_back();
		}
		return cell_depart.at(cell);
	}

	int depart_bit(RTLIL::SigBit bit)
	{
		if (bit.wire == nullptr)
			return 0;
		auto it = consumer_map.find(bit);
		if (it == consumer_map.end())
			return 0;
		int worst = 0;
		for (auto cons : it->second)
			worst = std::max(worst, depart_of(cons));
		return worst;
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
