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

// Per-bit connectivity plus the delay models and arrival/departure walk shared
// by the timing-guarded rewrite passes, so that they agree on which arrivals
// dominate rather than each drifting on its own copy. Include after
// PRIVATE_NAMESPACE_BEGIN and derive the pass worker from NetlistIndex (plain
// connectivity) or from UnitDelayTiming / FracDelayTiming (connectivity plus a
// timing walk).
//
// Two currencies share one walk. Integer levels charge a cell whole levels and
// suit passes that compare a rewrite against a `+1`; fractional levels charge
// against the output width and suit passes that only rank operands by arrival.
// They are not interchangeable, so a pass picks one and stays in it.
// (opt_timing_balance still carries its own variant, entangled with its cell
// registry.)

#ifndef UNIT_DELAY_H
#define UNIT_DELAY_H

// This header is included inside PRIVATE_NAMESPACE_BEGIN, so it cannot pull in
// kernel headers itself; each consumer includes kernel/celltypes.h,
// kernel/sigtools.h, kernel/yosys.h, <cmath> and <vector> at file scope.

// Bit count of w, i.e. floor(log2(w)) + 1, the depth charged to a carry chain
// of that width.
inline int log2p1_int(int w)
{
	int n = 0;
	while (w > 0) { w >>= 1; n++; }
	return n < 1 ? 1 : n;
}

// Fractional counterpart of log2p1_int, so a chain one bit wider is not free.
inline double log2p1_frac(int w) { return std::log2(double(std::max(1, w)) + 1.0); }

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

// Fractional-level counterpart, charged against the cell's widest output. An
// AND/OR costs half a level; a compare or reduction costs the tree that
// collapses its operand, so a control bit behind a wide compare is not ranked
// as early as one straight off a register.
inline double estimate_frac_cell_delay(const RTLIL::Cell *cell, int out_width)
{
	if (cell == nullptr)
		return 1.0;
	auto param = [&](RTLIL::IdString id, int dflt) {
		return cell->hasParam(id) ? cell->getParam(id).as_int() : dflt;
	};
	IdString t = cell->type;
	if (t.in(ID($add), ID($sub), ID($neg), ID($alu), ID($shl), ID($shr), ID($sshl), ID($sshr)))
		return log2p1_frac(out_width);
	if (t.in(ID($mul), ID($div), ID($mod)))
		return out_width;
	if (t == ID($pmux))
		return log2p1_frac(param(ID::S_WIDTH, 1));
	if (t.in(ID($eq), ID($ne), ID($eqx), ID($nex), ID($lt), ID($le), ID($gt), ID($ge)))
		return log2p1_frac(std::max(param(ID::A_WIDTH, 1), param(ID::B_WIDTH, 1)));
	if (t.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool)))
		return log2p1_frac(param(ID::A_WIDTH, 1));
	if (t.in(ID($and), ID($or)))
		return 0.5;
	// $mux, $xor, $xnor, $not, gate-level $_*_ and everything else: one level.
	return 1.0;
}

// Per-bit connectivity of one module: who drives a bit, who reads it, how many
// loads it carries, and whether a rewrite is allowed to disturb it. Rebuild
// with build_connectivity() after the netlist changes.
struct NetlistIndex
{
	RTLIL::Module *module;
	SigMap sigmap;

	// A bit maps to nullptr when more than one cell drives it, which ends a
	// path rather than picking a driver.
	dict<RTLIL::SigBit, RTLIL::Cell *> driver_map;
	dict<RTLIL::SigBit, std::vector<RTLIL::Cell *>> consumer_map;
	// Loads per bit: reading cell pins plus module output ports.
	dict<RTLIL::SigBit, int> fanout_map;
	// Bits carrying `keep` on any alias, and bits read by a module output.
	pool<RTLIL::SigBit> keep_bits, port_out_bits;

	NetlistIndex(RTLIL::Module *module) : module(module), sigmap(module) { }
	virtual ~NetlistIndex() { }

	void build_connectivity()
	{
		driver_map.clear();
		consumer_map.clear();
		fanout_map.clear();
		keep_bits.clear();
		port_out_bits.clear();

		// Collect `keep` across every alias, not just the wire sigmap elected:
		// the attribute may sit on any wire of a `connect` group, and testing
		// the representative alone silently drops what a kept probe reads.
		for (auto wire : module->wires())
			if (wire->get_bool_attribute(ID::keep))
				for (auto &bit : sigmap(RTLIL::SigSpec(wire)))
					keep_bits.insert(bit);

		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				RTLIL::SigSpec sig = sigmap(conn.second);
				if (cell->output(conn.first))
					for (auto &bit : sig) {
						if (bit.wire == nullptr)
							continue;
						auto it = driver_map.find(bit);
						if (it == driver_map.end())
							driver_map[bit] = cell;
						else if (it->second != cell)
							it->second = nullptr;
					}
				if (cell->input(conn.first))
					for (auto &bit : sig) {
						if (bit.wire == nullptr)
							continue;
						fanout_map[bit]++;
						// A cell reading one bit on two pins is two loads but
						// still a single consumer.
						auto &cons = consumer_map[bit];
						if (cons.empty() || cons.back() != cell)
							cons.push_back(cell);
					}
			}

		// A module output port loads its driver without being a cell
		for (auto wire : module->wires()) {
			if (!wire->port_output)
				continue;
			for (auto &bit : sigmap(RTLIL::SigSpec(wire))) {
				if (bit.wire == nullptr)
					continue;
				fanout_map[bit]++;
				port_out_bits.insert(bit);
			}
		}
	}

	int fanout_of(RTLIL::SigBit bit) const { return fanout_map.at(bit, 0); }

	// True when a rewrite must leave this bit observable: a `keep` probe reads
	// it, or it escapes through a module output.
	bool bit_escapes(RTLIL::SigBit bit) const { return keep_bits.count(bit) || port_out_bits.count(bit); }

	bool sig_escapes(const RTLIL::SigSpec &sig)
	{
		for (auto &bit : sigmap(sig))
			if (bit_escapes(bit))
				return true;
		return false;
	}
};

template <typename Delay>
struct DelayTiming : NetlistIndex
{
	// Memoized per cell, not per bit: every output bit of a cell shares one
	// arrival (the max over all its inputs) and every input bit shares one
	// departure, so a per-bit cache recomputed the same number once per bit and
	// rescanned the cell's whole port list each time -- O(width**2) per cell.
	dict<RTLIL::Cell *, Delay> cell_arrival, cell_depart;
	pool<RTLIL::Cell *> arrival_active, depart_active;
	Delay module_depth = 0;
	bool module_depth_valid = false;

	using NetlistIndex::NetlistIndex;

	// Levels through one cell, in this walk's currency.
	virtual Delay cell_delay(RTLIL::Cell *cell) = 0;

	// Cells a path cannot cross. Registers always end one; a subclass widens
	// this to whatever else it refuses to reason through.
	virtual bool is_start_point(RTLIL::Cell *cell) { return cell->is_builtin_ff(); }

	// Every rewrite invalidates the cached levels, so the next guard rebuilds.
	// Connectivity is separate: call build_connectivity() alongside this.
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
		return drv == nullptr || is_start_point(drv) ? nullptr : drv;
	}

	// Levels from a start point up to this cell's outputs. Iterative so a deep
	// datapath cannot blow the C stack; `*_active` breaks combinational loops by
	// charging the back edge zero.
	Delay arrival_of(RTLIL::Cell *cell)
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
			Delay latest = 0;
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

			cell_arrival[c] = latest + cell_delay(c);
			arrival_active.erase(c);
			stack.pop_back();
		}
		return cell_arrival.at(cell);
	}

	Delay arrival_bit(RTLIL::SigBit bit) { return arrival_of(driver_of(bit)); }

	Delay arrival(const RTLIL::SigSpec &sig)
	{
		Delay t = 0;
		for (auto &bit : sigmap(sig))
			t = std::max(t, arrival_bit(bit));
		return t;
	}

	// Levels from this cell's inputs down to the latest endpoint below it.
	Delay depart_of(RTLIL::Cell *cell)
	{
		if (cell == nullptr || is_start_point(cell))
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
			Delay worst = 0;
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
						if (is_start_point(cons))
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

			cell_depart[c] = worst + cell_delay(c);
			depart_active.erase(c);
			stack.pop_back();
		}
		return cell_depart.at(cell);
	}

	Delay depart_bit(RTLIL::SigBit bit)
	{
		if (bit.wire == nullptr)
			return 0;
		auto it = consumer_map.find(bit);
		if (it == consumer_map.end())
			return 0;
		Delay worst = 0;
		for (auto cons : it->second)
			worst = std::max(worst, depart_of(cons));
		return worst;
	}

	// Longest path through this signal, in the same unit-delay currency as the
	// module's own depth.
	Delay path_depth(const RTLIL::SigSpec &sig)
	{
		Delay t = 0;
		for (auto &bit : sigmap(sig))
			t = std::max(t, arrival_bit(bit) + depart_bit(bit));
		return t;
	}

	// The slack guard needs the module's longest path, which costs a full
	// arrival+depart walk of every cell. Most modules never reach the guard, so
	// pay for the walk on first use rather than up front.
	Delay longest_path()
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

// Whole levels, for passes that weigh a rewrite against a `+1`.
struct UnitDelayTiming : DelayTiming<int>
{
	using DelayTiming<int>::DelayTiming;
	int cell_delay(RTLIL::Cell *cell) override { return estimate_cell_delay(cell); }
};

// Fractional levels, for passes that only rank operands against each other.
// Anything the walk cannot see through -- a macro, a memory, a cell the user
// pinned -- ends the path rather than being charged a default.
struct FracDelayTiming : DelayTiming<double>
{
	CellTypes cell_types;

	FracDelayTiming(RTLIL::Module *module) : DelayTiming<double>(module) { cell_types.setup(); }

	double cell_delay(RTLIL::Cell *cell) override
	{
		int out_width = 1;
		for (auto &conn : cell->connections())
			if (cell->output(conn.first))
				out_width = std::max(out_width, GetSize(conn.second));
		return estimate_frac_cell_delay(cell, out_width);
	}

	bool is_start_point(RTLIL::Cell *cell) override
	{
		return cell->is_builtin_ff() ||
		       cell->get_bool_attribute(ID::keep) || cell->get_bool_attribute(ID::blackbox) ||
		       cell->type.in(ID($dlatch), ID($adlatch), ID($dlatchsr), ID($sr),
		                     ID($mem), ID($mem_v2), ID($memrd), ID($memrd_v2),
		                     ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2),
		                     ID($assert), ID($assume), ID($live), ID($fair), ID($cover)) ||
		       !cell_types.cell_known(cell->type);
	}
};

#endif
