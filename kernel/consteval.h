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
#include "kernel/macc.h"

YOSYS_NAMESPACE_BEGIN

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

		for (auto &it : module->cells_) {
			if (!ct.cell_known(it.second->type))
				continue;
			for (auto &it2 : it.second->connections())
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
		for (int i = 0; i < GetSize(current_val); i++)
			log_assert(current_val[i].wire != NULL || current_val[i] == value.bits[i]);
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
		if (cell->type == "$lcu")
		{
			RTLIL::SigSpec sig_p = cell->getPort("\\P");
			RTLIL::SigSpec sig_g = cell->getPort("\\G");
			RTLIL::SigSpec sig_ci = cell->getPort("\\CI");
			RTLIL::SigSpec sig_co = values_map(assign_map(cell->getPort("\\CO")));

			if (sig_co.is_fully_const())
				return true;

			if (!eval(sig_p, undef, cell))
				return false;

			if (!eval(sig_g, undef, cell))
				return false;

			if (!eval(sig_ci, undef, cell))
				return false;

			if (sig_p.is_fully_def() && sig_g.is_fully_def() && sig_ci.is_fully_def())
			{
				RTLIL::Const coval(RTLIL::Sx, GetSize(sig_co));
				bool carry = sig_ci.as_bool();

				for (int i = 0; i < GetSize(coval); i++) {
					carry = (sig_g[i] == RTLIL::S1) || (sig_p[i] == RTLIL::S1 && carry);
					coval.bits[i] = carry ? RTLIL::S1 : RTLIL::S0;
				}

				set(sig_co, coval);
			}
			else
				set(sig_co, RTLIL::Const(RTLIL::Sx, GetSize(sig_co)));

			return true;
		}

		RTLIL::SigSpec sig_a, sig_b, sig_s, sig_y;

		log_assert(cell->hasPort("\\Y"));
		sig_y = values_map(assign_map(cell->getPort("\\Y")));
		if (sig_y.is_fully_const())
			return true;

		if (cell->hasPort("\\S")) {
			sig_s = cell->getPort("\\S");
			if (!eval(sig_s, undef, cell))
				return false;
		}

		if (cell->hasPort("\\A"))
			sig_a = cell->getPort("\\A");

		if (cell->hasPort("\\B"))
			sig_b = cell->getPort("\\B");

		if (cell->type == "$mux" || cell->type == "$pmux" || cell->type == "$_MUX_")
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

			if (count_set_s_bits == 0)
				y_candidates.push_back(sig_a);

			std::vector<RTLIL::Const> y_values;

			log_assert(y_candidates.size() > 0);
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
					log_assert(master_bits.size() == slave_bits.size());
					for (size_t j = 0; j < master_bits.size(); j++)
						if (master_bits[j] != slave_bits[j])
							master_bits[j] = RTLIL::State::Sx;
				}

				set(sig_y, RTLIL::Const(master_bits));
			}
			else
				set(sig_y, y_values.front());
		}
		else if (cell->type == "$fa")
		{
			RTLIL::SigSpec sig_c = cell->getPort("\\C");
			RTLIL::SigSpec sig_x = cell->getPort("\\X");
			int width = GetSize(sig_c);

			if (!eval(sig_a, undef, cell))
				return false;

			if (!eval(sig_b, undef, cell))
				return false;

			if (!eval(sig_c, undef, cell))
				return false;

			RTLIL::Const t1 = const_xor(sig_a.as_const(), sig_b.as_const(), false, false, width);
			RTLIL::Const val_y = const_xor(t1, sig_c.as_const(), false, false, width);

			RTLIL::Const t2 = const_and(sig_a.as_const(), sig_b.as_const(), false, false, width);
			RTLIL::Const t3 = const_and(sig_c.as_const(), t1, false, false, width);
			RTLIL::Const val_x = const_or(t2, t3, false, false, width);

			for (int i = 0; i < GetSize(val_y); i++)
				if (val_y.bits[i] == RTLIL::Sx)
					val_x.bits[i] = RTLIL::Sx;

			set(sig_y, val_y);
			set(sig_x, val_x);
		}
		else if (cell->type == "$alu")
		{
			bool signed_a = cell->parameters.count("\\A_SIGNED") > 0 && cell->parameters["\\A_SIGNED"].as_bool();
			bool signed_b = cell->parameters.count("\\B_SIGNED") > 0 && cell->parameters["\\B_SIGNED"].as_bool();

			RTLIL::SigSpec sig_ci = cell->getPort("\\CI");
			RTLIL::SigSpec sig_bi = cell->getPort("\\BI");

			if (!eval(sig_a, undef, cell))
				return false;

			if (!eval(sig_b, undef, cell))
				return false;

			if (!eval(sig_ci, undef, cell))
				return false;

			if (!eval(sig_bi, undef, cell))
				return false;

			RTLIL::SigSpec sig_x = cell->getPort("\\X");
			RTLIL::SigSpec sig_co = cell->getPort("\\CO");

			bool any_input_undef = !(sig_a.is_fully_def() && sig_b.is_fully_def() && sig_ci.is_fully_def() && sig_bi.is_fully_def());
			sig_a.extend_u0(GetSize(sig_y), signed_a);
			sig_b.extend_u0(GetSize(sig_y), signed_b);

			bool carry = sig_ci[0] == RTLIL::S1;
			bool b_inv = sig_bi[0] == RTLIL::S1;

			for (int i = 0; i < GetSize(sig_y); i++)
			{
				RTLIL::SigSpec x_inputs = { sig_a[i], sig_b[i], sig_bi[0] };

				if (!x_inputs.is_fully_def()) {
					set(sig_x[i], RTLIL::Sx);
				} else {
					bool bit_a = sig_a[i] == RTLIL::S1;
					bool bit_b = (sig_b[i] == RTLIL::S1) != b_inv;
					bool bit_x = bit_a != bit_b;
					set(sig_x[i], bit_x ? RTLIL::S1 : RTLIL::S0);
				}

				if (any_input_undef) {
					set(sig_y[i], RTLIL::Sx);
					set(sig_co[i], RTLIL::Sx);
				} else {
					bool bit_a = sig_a[i] == RTLIL::S1;
					bool bit_b = (sig_b[i] == RTLIL::S1) != b_inv;
					bool bit_y = (bit_a != bit_b) != carry;
					carry = (bit_a && bit_b) || (bit_a && carry) || (bit_b && carry);
					set(sig_y[i], bit_y ? RTLIL::S1 : RTLIL::S0);
					set(sig_co[i], carry ? RTLIL::S1 : RTLIL::S0);
				}
			}
		}
		else if (cell->type == "$macc")
		{
			Macc macc;
			macc.from_cell(cell);

			if (!eval(macc.bit_ports, undef, cell))
				return false;

			for (auto &port : macc.ports) {
				if (!eval(port.in_a, undef, cell))
					return false;
				if (!eval(port.in_b, undef, cell))
					return false;
			}

			RTLIL::Const result(0, GetSize(cell->getPort("\\Y")));
			if (!macc.eval(result))
				log_abort();

			set(cell->getPort("\\Y"), result);
		}
		else
		{
			RTLIL::SigSpec sig_c, sig_d;

			if (cell->type.in("$_AOI3_", "$_OAI3_", "$_AOI4_", "$_OAI4_")) {
				if (cell->hasPort("\\C"))
					sig_c = cell->getPort("\\C");
				if (cell->hasPort("\\D"))
					sig_d = cell->getPort("\\D");
			}

			if (sig_a.size() > 0 && !eval(sig_a, undef, cell))
				return false;
			if (sig_b.size() > 0 && !eval(sig_b, undef, cell))
				return false;
			if (sig_c.size() > 0 && !eval(sig_c, undef, cell))
				return false;
			if (sig_d.size() > 0 && !eval(sig_d, undef, cell))
				return false;

			set(sig_y, CellTypes::eval(cell, sig_a.as_const(), sig_b.as_const(),
					sig_c.as_const(), sig_d.as_const()));
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

YOSYS_NAMESPACE_END

#endif
