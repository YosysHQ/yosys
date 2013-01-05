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

#ifndef CONSTEVAL_H
#define CONSTEVAL_H

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"

struct ConstEval
{
	RTLIL::Module *module;
	SigMap assign_map;
	SigMap values_map;
	SigPool stop_signals;
	SigSet<RTLIL::Cell*> sig2driver;
	std::set<RTLIL::Cell*> busy;
	std::vector<SigMap> stack;

	ConstEval(RTLIL::Module *module) : module(module), assign_map(module)
	{
		CellTypes ct;
		ct.setup_internals();
		ct.setup_stdcells();

		for (auto &it : module->cells) {
			if (!ct.cell_known(it.second->type))
				continue;
			for (auto &it2 : it.second->connections)
				if (ct.cell_output(it.second->type, it2.first))
					sig2driver.insert(assign_map(it2.second), it.second);
		}
	}

	void clear()
	{
		values_map.clear();
		stop_signals.clear();
	}

	void push()
	{
		stack.push_back(values_map);
	}

	void pop()
	{
		values_map.swap(stack.back());
		stack.pop_back();
	}

	void set(RTLIL::SigSpec sig, RTLIL::Const value)
	{
		assign_map.apply(sig);
#ifndef NDEBUG
		RTLIL::SigSpec current_val = values_map(sig);
		current_val.expand();
		for (size_t i = 0; i < current_val.chunks.size(); i++) {
			RTLIL::SigChunk &chunk = current_val.chunks[i];
			assert(chunk.wire != NULL || chunk.data.bits[0] == value.bits[i]);
		}
#endif
		values_map.add(sig, RTLIL::SigSpec(value));
	}

	void stop(RTLIL::SigSpec sig)
	{
		assign_map.apply(sig);
		stop_signals.add(sig);
	}

	bool eval(RTLIL::Cell *cell, RTLIL::SigSpec &undef)
	{
		RTLIL::SigSpec sig_a, sig_b, sig_s, sig_y;
		bool ignore_sig_a = false, ignore_sig_b = false;
		int sig_b_shift = -1;

		assert(cell->connections.count("\\Y") > 0);
		sig_y = values_map(assign_map(cell->connections["\\Y"]));
		if (sig_y.is_fully_const())
			return true;

		if (cell->connections.count("\\S") > 0) {
			sig_s = cell->connections["\\S"];
			if (!eval(sig_s, undef, cell))
				return false;
		}

		if (cell->type == "$mux" || cell->type == "$pmux" || cell->type == "$safe_pmux" || cell->type == "$_MUX_") {
			bool found_collision = false;
			for (int i = 0; i < sig_s.width; i++)
				if (sig_s.extract(i, 1).as_bool()) {
					if (sig_b_shift >= 0)
						found_collision = true;
					sig_b_shift = i;
					ignore_sig_a = true;
					if (cell->type != "$safe_pmux")
						break;
				}
			if (found_collision) {
				sig_b_shift = -1;
				ignore_sig_a = false;
			}
			if (sig_b_shift < 0)
				ignore_sig_b = true;
		}

		if (!ignore_sig_a && cell->connections.count("\\A") > 0) {
			sig_a = cell->connections["\\A"];
			if (!eval(sig_a, undef, cell))
				return false;
		}

		if (!ignore_sig_b && cell->connections.count("\\B") > 0) {
			sig_b = cell->connections["\\B"];
			if (sig_b_shift >= 0)
				sig_b = sig_b.extract(sig_y.width*sig_b_shift, sig_y.width);
			if (!eval(sig_b, undef, cell))
				return false;
		}

		if (cell->type == "$mux" || cell->type == "$pmux" || cell->type == "$safe_pmux" || cell->type == "$_MUX_")
			set(sig_y, sig_s.as_bool() ? sig_b.as_const() : sig_a.as_const());
		else
			set(sig_y, CellTypes::eval(cell, sig_a.as_const(), sig_b.as_const()));

		return true;
	}

	bool eval(RTLIL::SigSpec &sig, RTLIL::SigSpec &undef, RTLIL::Cell *busy_cell = NULL)
	{
		assign_map.apply(sig);
		values_map.apply(sig);

		if (sig.is_fully_const())
			return true;

		if (stop_signals.check_any(sig)) {
			undef = stop_signals.extract(sig);
			return false;
		}

		if (busy_cell) {
			if (busy.count(busy_cell) > 0) {
				undef = sig;
				return false;
			}
			busy.insert(busy_cell);
		}

		std::set<RTLIL::Cell*> driver_cells;
		sig2driver.find(sig, driver_cells);
		for (auto cell : driver_cells) {
			if (!eval(cell, undef)) {
				if (busy_cell)
					busy.erase(busy_cell);
				return false;
			}
		}

		if (busy_cell)
			busy.erase(busy_cell);

		values_map.apply(sig);
		if (sig.is_fully_const())
			return true;

		for (size_t i = 0; i < sig.chunks.size(); i++)
			if (sig.chunks[i].wire != NULL)
				undef.append(sig.chunks[i]);
		return false;
	}

	bool eval(RTLIL::SigSpec &sig)
	{
		RTLIL::SigSpec undef;
		return eval(sig, undef);
	}
};

#endif
