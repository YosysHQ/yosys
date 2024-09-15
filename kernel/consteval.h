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

#ifndef CONSTEVAL_H
#define CONSTEVAL_H

#include "kernel/celltypes.h"
#include "kernel/macc.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

YOSYS_NAMESPACE_BEGIN

struct ConstMap {
	dict<RTLIL::SigBit, RTLIL::State> database;

	void swap(ConstMap &other) { database.swap(other.database); }

	void clear() { database.clear(); }

	void add(const RTLIL::SigSpec &from, const RTLIL::Const &to)
	{
		log_assert(GetSize(from) == GetSize(to));

		for (int i = 0; i < GetSize(from); i++) {
			RTLIL::State bit = to.bits[i];
			RTLIL::State current_bit = database.count(from[i]) ? database.at(from[i]) : State::Sz;

			// resolve signals: Sa+X=Sx, X+Sa=X X+X=X, Sx+X=Sx, X+Sx=Sx, Sz+X=X, X+Sz=X, X+X=X, X+Y=Sx
			// |   | X | 0 | 1 | Z | - |
			// |---|---|---|---|---|---|
			// | X | X | X | X | X | X |
			// | 0 | X | 0 | X | 0 | X |
			// | 1 | X | X | 1 | 1 | X |
			// | Z | X | 0 | 1 | Z | X |
			// | - | X | X | X | X | X |
			if (bit == RTLIL::Sa || current_bit == RTLIL::Sa) {
				bit = RTLIL::Sx;
			} else if (bit == current_bit) {
				// bit = bit
			} else if (bit == RTLIL::Sx || current_bit == RTLIL::Sx) {
				bit = RTLIL::Sx;
			} else if (bit == RTLIL::Sz) {
				bit = current_bit;
			} else if (current_bit == RTLIL::Sz) {
				// bit = bit;
			} else {
				bit = RTLIL::Sx;
			}

			database[from[i]] = bit;
		}
	}

	void overwrite(const RTLIL::SigSpec &from, const RTLIL::Const &to)
	{
		log_assert(GetSize(from) == GetSize(to));

		for (int i = 0; i < GetSize(from); i++)
			database[from[i]] = to.bits[i];
	}

	void apply(RTLIL::SigBit &bit) const
	{
		if (database.count(bit) != 0)
			bit = database.at(bit);
	}

	void apply(RTLIL::SigSpec &sig) const
	{
		for (auto &bit : sig)
			apply(bit);
	}

	RTLIL::SigBit operator()(RTLIL::SigBit bit) const
	{
		apply(bit);
		return bit;
	}

	RTLIL::SigSpec operator()(RTLIL::SigSpec sig) const
	{
		apply(sig);
		return sig;
	}

	RTLIL::SigSpec operator()(RTLIL::Wire *wire) const
	{
		SigSpec sig(wire);
		apply(sig);
		return sig;
	}
};

struct ConstEval {
	RTLIL::Module *module;
	SigMap assign_map;
	ConstMap values_map;
	SigPool stop_signals;
	SigSet<RTLIL::Cell *> sig2driver;
	std::set<RTLIL::Cell *> busy;
	std::vector<std::pair<ConstMap, SigPool>> stack;
	RTLIL::State defaultval;
	SigPool evaluated;

	int ident = 0;

	ConstEval(RTLIL::Module *module, RTLIL::State defaultval = RTLIL::State::Sm) : module(module), assign_map(module), defaultval(defaultval)
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
		evaluated.clear();
	}

	void push() { stack.push_back(std::pair(values_map, evaluated)); }

	void pop()
	{
		values_map.swap(stack.back().first);
		evaluated = std::move(stack.back().second);
		stack.pop_back();
	}

	// set a signal to have the specified value..
	void set(RTLIL::SigSpec sig, RTLIL::Const value)
	{
		assign_map.apply(sig);

		// replace any previous value with the given one.
		values_map.overwrite(sig, value);

		// make sure this signal is no longer evaluated.
		evaluated.add(sig);
	}

	// assign a value to a signal, resolving with any previously assigned value.
	void assign(RTLIL::SigSpec sig, RTLIL::Const value)
	{
		assign_map.apply(sig);
		values_map.add(sig, value);
	}

	void stop(RTLIL::SigSpec sig)
	{
		assign_map.apply(sig);
		stop_signals.add(sig);
	}

	bool eval(RTLIL::Cell *cell, RTLIL::SigSpec &undef)
	{
		if (cell->type == ID($lcu)) {
			RTLIL::SigSpec sig_p = cell->getPort(ID::P);
			RTLIL::SigSpec sig_g = cell->getPort(ID::G);
			RTLIL::SigSpec sig_ci = cell->getPort(ID::CI);
			RTLIL::SigSpec sig_co = assign_map(cell->getPort(ID::CO));

			if (sig_co.is_fully_const())
				return true;

			if (!eval(sig_p, undef, cell))
				return false;

			if (!eval(sig_g, undef, cell))
				return false;

			if (!eval(sig_ci, undef, cell))
				return false;

			if (sig_p.is_fully_def() && sig_g.is_fully_def() && sig_ci.is_fully_def()) {
				RTLIL::Const coval(RTLIL::Sx, GetSize(sig_co));
				bool carry = sig_ci.as_bool();

				for (int i = 0; i < GetSize(coval); i++) {
					carry = (sig_g[i] == State::S1) || (sig_p[i] == RTLIL::S1 && carry);
					coval.bits[i] = carry ? State::S1 : State::S0;
				}

				assign(sig_co, coval);
			} else
				assign(sig_co, RTLIL::Const(RTLIL::Sx, GetSize(sig_co)));

			return true;
		}

		if (cell->type == ID($tribuf) || cell->type == ID($_TBUF_)) {
			IdString en_port = cell->type == ID($tribuf) ? ID::EN : ID::E;
			RTLIL::SigSpec sig_a = cell->getPort(ID::A);
			RTLIL::SigSpec sig_e = cell->getPort(en_port);
			RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

			if (!eval(sig_a, undef, cell))
				return false;

			if (!eval(sig_e, undef, cell))
				return false;

			if (sig_e.as_bool()) {
				assign(sig_y, sig_a.as_const());
			} else {
				assign(sig_y, RTLIL::Const(RTLIL::Sz, GetSize(sig_y)));
			}

			return true;
		}

		RTLIL::SigSpec sig_a, sig_b, sig_s, sig_y;

		log_assert(cell->hasPort(ID::Y));
		sig_y = assign_map(cell->getPort(ID::Y));

		if (cell->hasPort(ID::S)) {
			sig_s = cell->getPort(ID::S);
		}

		if (cell->hasPort(ID::A))
			sig_a = cell->getPort(ID::A);

		if (cell->hasPort(ID::B))
			sig_b = cell->getPort(ID::B);

		if (cell->type.in(ID($mux), ID($pmux), ID($_MUX_), ID($_NMUX_))) {
			std::vector<RTLIL::SigSpec> y_candidates;
			int count_set_s_bits = 0;

			if (!eval(sig_s, undef, cell))
				return false;

			for (int i = 0; i < sig_s.size(); i++) {
				RTLIL::State s_bit = sig_s.extract(i, 1).as_const().bits.at(0);
				RTLIL::SigSpec b_slice = sig_b.extract(sig_y.size() * i, sig_y.size());

				if (s_bit == RTLIL::State::Sx || s_bit == RTLIL::State::S1)
					y_candidates.push_back(b_slice);

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
				if (cell->type == ID($_NMUX_))
					y_values.push_back(RTLIL::const_not(yc.as_const(), Const(), false, false, GetSize(yc)));
				else
					y_values.push_back(yc.as_const());
			}

			if (y_values.size() > 1) {
				std::vector<RTLIL::State> master_bits = y_values.at(0).bits;

				for (size_t i = 1; i < y_values.size(); i++) {
					std::vector<RTLIL::State> &slave_bits = y_values.at(i).bits;
					log_assert(master_bits.size() == slave_bits.size());
					for (size_t j = 0; j < master_bits.size(); j++)
						if (master_bits[j] != slave_bits[j])
							master_bits[j] = RTLIL::State::Sx;
				}

				assign(sig_y, RTLIL::Const(master_bits));
			} else
				assign(sig_y, y_values.front());
		} else if (cell->type == ID($bmux)) {
			if (!eval(sig_s, undef, cell))
				return false;

			if (sig_s.is_fully_def()) {
				int sel = sig_s.as_int();
				int width = GetSize(sig_y);
				SigSpec res = sig_a.extract(sel * width, width);
				if (!eval(res, undef, cell))
					return false;
				assign(sig_y, res.as_const());
			} else {
				if (!eval(sig_a, undef, cell))
					return false;
				assign(sig_y, const_bmux(sig_a.as_const(), sig_s.as_const()));
			}
		} else if (cell->type == ID($demux)) {
			if (!eval(sig_a, undef, cell))
				return false;
			if (sig_a.is_fully_zero()) {
				assign(sig_y, Const(0, GetSize(sig_y)));
			} else {
				if (!eval(sig_s, undef, cell))
					return false;
				assign(sig_y, const_demux(sig_a.as_const(), sig_s.as_const()));
			}
		} else if (cell->type == ID($fa)) {
			RTLIL::SigSpec sig_c = cell->getPort(ID::C);
			RTLIL::SigSpec sig_x = cell->getPort(ID::X);
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

			assign(sig_y, val_y);
			assign(sig_x, val_x);
		} else if (cell->type == ID($alu)) {
			bool signed_a = cell->parameters.count(ID::A_SIGNED) > 0 && cell->parameters[ID::A_SIGNED].as_bool();
			bool signed_b = cell->parameters.count(ID::B_SIGNED) > 0 && cell->parameters[ID::B_SIGNED].as_bool();

			RTLIL::SigSpec sig_ci = cell->getPort(ID::CI);
			RTLIL::SigSpec sig_bi = cell->getPort(ID::BI);

			if (!eval(sig_a, undef, cell))
				return false;

			if (!eval(sig_b, undef, cell))
				return false;

			if (!eval(sig_ci, undef, cell))
				return false;

			if (!eval(sig_bi, undef, cell))
				return false;

			RTLIL::SigSpec sig_x = cell->getPort(ID::X);
			RTLIL::SigSpec sig_co = cell->getPort(ID::CO);

			bool any_input_undef = !(sig_a.is_fully_def() && sig_b.is_fully_def() && sig_ci.is_fully_def() && sig_bi.is_fully_def());
			sig_a.extend_u0(GetSize(sig_y), signed_a);
			sig_b.extend_u0(GetSize(sig_y), signed_b);

			bool carry = sig_ci[0] == State::S1;
			bool b_inv = sig_bi[0] == State::S1;

			for (int i = 0; i < GetSize(sig_y); i++) {
				RTLIL::SigSpec x_inputs = {sig_a[i], sig_b[i], sig_bi[0]};

				if (!x_inputs.is_fully_def()) {
					assign(sig_x[i], RTLIL::Sx);
				} else {
					bool bit_a = sig_a[i] == State::S1;
					bool bit_b = (sig_b[i] == State::S1) != b_inv;
					bool bit_x = bit_a != bit_b;
					assign(sig_x[i], bit_x ? State::S1 : State::S0);
				}

				if (any_input_undef) {
					assign(sig_y[i], RTLIL::Sx);
					assign(sig_co[i], RTLIL::Sx);
				} else {
					bool bit_a = sig_a[i] == State::S1;
					bool bit_b = (sig_b[i] == State::S1) != b_inv;
					bool bit_y = (bit_a != bit_b) != carry;
					carry = (bit_a && bit_b) || (bit_a && carry) || (bit_b && carry);
					assign(sig_y[i], bit_y ? State::S1 : State::S0);
					assign(sig_co[i], carry ? State::S1 : State::S0);
				}
			}
		} else if (cell->type == ID($macc)) {
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

			RTLIL::Const result(0, GetSize(cell->getPort(ID::Y)));
			if (!macc.eval(result))
				log_abort();

			assign(cell->getPort(ID::Y), result);
		} else {
			RTLIL::SigSpec sig_c, sig_d;

			if (cell->type.in(ID($_AOI3_), ID($_OAI3_), ID($_AOI4_), ID($_OAI4_))) {
				if (cell->hasPort(ID::C))
					sig_c = cell->getPort(ID::C);
				if (cell->hasPort(ID::D))
					sig_d = cell->getPort(ID::D);
			}

			if (sig_a.size() > 0 && !eval(sig_a, undef, cell))
				return false;
			if (sig_b.size() > 0 && !eval(sig_b, undef, cell))
				return false;
			if (sig_c.size() > 0 && !eval(sig_c, undef, cell))
				return false;
			if (sig_d.size() > 0 && !eval(sig_d, undef, cell))
				return false;

			bool eval_err = false;
			RTLIL::Const eval_ret =
			  CellTypes::eval(cell, sig_a.as_const(), sig_b.as_const(), sig_c.as_const(), sig_d.as_const(), &eval_err);

			if (eval_err)
				return false;

			assign(sig_y, eval_ret);
		}

		return true;
	}

	bool eval(RTLIL::SigSpec &sig, RTLIL::SigSpec &undef, RTLIL::Cell *busy_cell = NULL)
	{
		if (sig.is_fully_const()) {
			return true;
		}

		assign_map.apply(sig);

		if (evaluated.check_all(sig)) {
			values_map.apply(sig);
			if (sig.is_fully_const())
				return true;

			for (auto &c : sig.chunks())
				if (c.wire != NULL)
					undef.append(c);

			return false;
		}

		RTLIL::SigSpec non_evaluated = evaluated.remove(sig);

		if (stop_signals.check_any(non_evaluated)) {
			undef = stop_signals.extract(non_evaluated);
			return false;
		}

		if (busy_cell) {
			if (busy.count(busy_cell) > 0) {
				undef = non_evaluated;
				return false;
			}
			busy.insert(busy_cell);
		}

		std::set<RTLIL::Cell *> driver_cells;
		sig2driver.find(non_evaluated, driver_cells);
		for (auto cell : driver_cells) {
			if (!eval(cell, undef)) {
				if (busy_cell)
					busy.erase(busy_cell);
				return false;
			}
		}

		if (busy_cell)
			busy.erase(busy_cell);

		// Mark all sigs that received a value as evaluated. The remaining
		// signals didn't have a driver cell and are undef.
		for (auto bit : sig)
			if (values_map(bit).wire == NULL)
				evaluated.add(sig);

		values_map.apply(sig);

		if (sig.is_fully_const()) {
			return true;
		}

		if (defaultval != RTLIL::State::Sm) {
			for (auto &bit : sig) {
				if (bit.wire)
					bit = defaultval;
			}
			return true;
		}

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
