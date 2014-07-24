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
		for (int i = 0; i < SIZE(current_val); i++)
			assert(current_val[i].wire != NULL || current_val[i] == value.bits[i]);
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

		assert(cell->connections.count("\\Y") > 0);
		sig_y = values_map(assign_map(cell->connections["\\Y"]));
		if (sig_y.is_fully_const())
			return true;

		if (cell->connections.count("\\S") > 0) {
			sig_s = cell->connections["\\S"];
			if (!eval(sig_s, undef, cell))
				return false;
		}

		if (cell->connections.count("\\A") > 0)
			sig_a = cell->connections["\\A"];

		if (cell->connections.count("\\B") > 0)
			sig_b = cell->connections["\\B"];

		if (cell->type == "$mux" || cell->type == "$pmux" || cell->type == "$safe_pmux" || cell->type == "$_MUX_")
		{
			std::vector<RTLIL::SigSpec> y_candidates;
			int count_maybe_set_s_bits = 0;
			int count_set_s_bits = 0;

			for (int i = 0; i < sig_s.size(); i++)
			{
				RTLIL::State s_bit = sig_s.extract(i, 1).as_const().bits.at(0);
				RTLIL::SigSpec b_slice = sig_b.extract(sig_y.size()*i, sig_y.size());

				if (s_bit == RTLIL::State::Sx || s_bit == RTLIL::State::S1)
					y_candidates.push_back(b_slice);

				if (s_bit == RTLIL::State::S1 || s_bit == RTLIL::State::Sx)
					count_maybe_set_s_bits++;

				if (s_bit == RTLIL::State::S1)
					count_set_s_bits++;
			}

			if (cell->type == "$safe_pmux" && count_set_s_bits > 1)
				y_candidates.clear();

			if ((cell->type == "$safe_pmux" && count_maybe_set_s_bits > 1) || count_set_s_bits == 0)
				y_candidates.push_back(sig_a);

			std::vector<RTLIL::Const> y_values;

			assert(y_candidates.size() > 0);
			for (auto &yc : y_candidates) {
				if (!eval(yc, undef, cell))
					return false;
				y_values.push_back(yc.as_const());
			}

			if (y_values.size() > 1)
			{
				std::vector<RTLIL::State> master_bits = y_values.at(0).bits;

				for (size_t i = 1; i < y_values.size(); i++) {
					std::vector<RTLIL::State> &slave_bits = y_values.at(i).bits;
					assert(master_bits.size() == slave_bits.size());
					for (size_t j = 0; j < master_bits.size(); j++)
						if (master_bits[j] != slave_bits[j])
							master_bits[j] = RTLIL::State::Sx;
				}

				set(sig_y, RTLIL::Const(master_bits));
			}
			else
				set(sig_y, y_values.front());
		}
		else
		{
			if (sig_a.size() > 0 && !eval(sig_a, undef, cell))
				return false;
			if (sig_b.size() > 0 && !eval(sig_b, undef, cell))
				return false;
			set(sig_y, CellTypes::eval(cell, sig_a.as_const(), sig_b.as_const()));
		}

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

		for (auto &c : sig.chunks())
			if (c.wire != NULL)
				undef.append(c);
		return false;
	}

	bool eval(RTLIL::SigSpec &sig)
	{
		RTLIL::SigSpec undef;
		return eval(sig, undef);
	}
};

#endif
