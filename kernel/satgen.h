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

#ifndef SATGEN_H
#define SATGEN_H

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"

#ifdef YOSYS_ENABLE_MINISAT
#  include "libs/ezsat/ezminisat.h"
typedef ezMiniSAT ezDefaultSAT;
#else
#  include "libs/ezsat/ezsat.h"
typedef ezSAT ezDefaultSAT;
#endif

struct SatGen
{
	ezSAT *ez;
	RTLIL::Design *design;
	SigMap *sigmap;
	std::string prefix;
	SigPool initial_state;
	bool ignore_div_by_zero;

	SatGen(ezSAT *ez, RTLIL::Design *design, SigMap *sigmap, std::string prefix = std::string()) :
			ez(ez), design(design), sigmap(sigmap), prefix(prefix), ignore_div_by_zero(false)
	{
	}

	void setContext(RTLIL::Design *design, SigMap *sigmap, std::string prefix = std::string())
	{
		this->design = design;
		this->sigmap = sigmap;
		this->prefix = prefix;
	}

	std::vector<int> importSigSpec(RTLIL::SigSpec sig, int timestep = -1)
	{
		assert(timestep < 0 || timestep > 0);
		sigmap->apply(sig);
		sig.expand();

		std::vector<int> vec;
		vec.reserve(sig.chunks.size());

		for (auto &c : sig.chunks)
			if (c.wire == NULL) {
				vec.push_back(c.data.as_bool() ? ez->TRUE : ez->FALSE);
			} else {
				std::string name = prefix;
				name += timestep == -1 ? "" : stringf("@%d:", timestep);
				name += stringf(c.wire->width == 1 ?  "%s" : "%s [%d]", RTLIL::id2cstr(c.wire->name), c.offset);
				vec.push_back(ez->literal(name));
			}
		return vec;
	}

	void extendSignalWidth(std::vector<int> &vec_a, std::vector<int> &vec_b, RTLIL::Cell *cell, size_t y_width = 0)
	{
		bool is_signed = false;
		if (cell->parameters.count("\\A_SIGNED") > 0 && cell->parameters.count("\\B_SIGNED") > 0)
			is_signed = cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool();
		while (vec_a.size() < vec_b.size() || vec_a.size() < y_width)
			vec_a.push_back(is_signed && vec_a.size() > 0 ? vec_a.back() : ez->FALSE);
		while (vec_b.size() < vec_a.size() || vec_b.size() < y_width)
			vec_b.push_back(is_signed && vec_b.size() > 0 ? vec_b.back() : ez->FALSE);
	}

	void extendSignalWidth(std::vector<int> &vec_a, std::vector<int> &vec_b, std::vector<int> &vec_y, RTLIL::Cell *cell)
	{
		extendSignalWidth(vec_a, vec_b, cell, vec_y.size());
		while (vec_y.size() < vec_a.size())
			vec_y.push_back(ez->literal());
	}

	void extendSignalWidthUnary(std::vector<int> &vec_a, std::vector<int> &vec_y, RTLIL::Cell *cell)
	{
		bool is_signed = cell->parameters.count("\\A_SIGNED") > 0 && cell->parameters["\\A_SIGNED"].as_bool();
		while (vec_a.size() < vec_y.size())
			vec_a.push_back(is_signed && vec_a.size() > 0 ? vec_a.back() : ez->FALSE);
		while (vec_y.size() < vec_a.size())
			vec_y.push_back(ez->literal());
	}

	bool importCell(RTLIL::Cell *cell, int timestep = -1)
	{
		if (cell->type == "$_AND_" || cell->type == "$_OR_" || cell->type == "$_XOR_" ||
				cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor" ||
				cell->type == "$add" || cell->type == "$sub") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			extendSignalWidth(a, b, y, cell);
			if (cell->type == "$and" || cell->type == "$_AND_")
				ez->assume(ez->vec_eq(ez->vec_and(a, b), y));
			if (cell->type == "$or" || cell->type == "$_OR_")
				ez->assume(ez->vec_eq(ez->vec_or(a, b), y));
			if (cell->type == "$xor" || cell->type == "$_XOR_")
				ez->assume(ez->vec_eq(ez->vec_xor(a, b), y));
			if (cell->type == "$xnor")
				ez->assume(ez->vec_eq(ez->vec_not(ez->vec_xor(a, b)), y));
			if (cell->type == "$add")
				ez->assume(ez->vec_eq(ez->vec_add(a, b), y));
			if (cell->type == "$sub")
				ez->assume(ez->vec_eq(ez->vec_sub(a, b), y));
			return true;
		}

		if (cell->type == "$_INV_" || cell->type == "$not") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			extendSignalWidthUnary(a, y, cell);
			ez->assume(ez->vec_eq(ez->vec_not(a), y));
			return true;
		}

		if (cell->type == "$_MUX_" || cell->type == "$mux") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"), timestep);
			std::vector<int> s = importSigSpec(cell->connections.at("\\S"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			ez->assume(ez->vec_eq(ez->vec_ite(s.at(0), b, a), y));
			return true;
		}

		if (cell->type == "$pmux" || cell->type == "$safe_pmux") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"), timestep);
			std::vector<int> s = importSigSpec(cell->connections.at("\\S"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			std::vector<int> tmp = a;
			for (size_t i = 0; i < s.size(); i++) {
				std::vector<int> part_of_b(b.begin()+i*a.size(), b.begin()+(i+1)*a.size());
				tmp = ez->vec_ite(s.at(i), part_of_b, tmp);
			}
			if (cell->type == "$safe_pmux")
				tmp = ez->vec_ite(ez->onehot(s, true), tmp, a);
			ez->assume(ez->vec_eq(tmp, y));
			return true;
		}

		if (cell->type == "$pos" || cell->type == "$neg") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			extendSignalWidthUnary(a, y, cell);
			if (cell->type == "$pos") {
				ez->assume(ez->vec_eq(a, y));
			} else {
				std::vector<int> zero(a.size(), ez->FALSE);
				ez->assume(ez->vec_eq(ez->vec_sub(zero, a), y));
			}
			return true;
		}

		if (cell->type == "$reduce_and" || cell->type == "$reduce_or" || cell->type == "$reduce_xor" ||
				cell->type == "$reduce_xnor" || cell->type == "$reduce_bool" || cell->type == "$logic_not") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			if (cell->type == "$reduce_and")
				ez->SET(ez->expression(ez->OpAnd, a), y.at(0));
			if (cell->type == "$reduce_or" || cell->type == "$reduce_bool")
				ez->SET(ez->expression(ez->OpOr, a), y.at(0));
			if (cell->type == "$reduce_xor")
				ez->SET(ez->expression(ez->OpXor, a), y.at(0));
			if (cell->type == "$reduce_xnor")
				ez->SET(ez->NOT(ez->expression(ez->OpXor, a)), y.at(0));
			if (cell->type == "$logic_not")
				ez->SET(ez->NOT(ez->expression(ez->OpOr, a)), y.at(0));
			for (size_t i = 1; i < y.size(); i++)
				ez->SET(ez->FALSE, y.at(i));
			return true;
		}

		if (cell->type == "$logic_and" || cell->type == "$logic_or") {
			int a = ez->expression(ez->OpOr, importSigSpec(cell->connections.at("\\A"), timestep));
			int b = ez->expression(ez->OpOr, importSigSpec(cell->connections.at("\\B"), timestep));
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			if (cell->type == "$logic_and")
				ez->SET(ez->expression(ez->OpAnd, a, b), y.at(0));
			else
				ez->SET(ez->expression(ez->OpOr, a, b), y.at(0));
			for (size_t i = 1; i < y.size(); i++)
				ez->SET(ez->FALSE, y.at(i));
			return true;
		}

		if (cell->type == "$lt" || cell->type == "$le" || cell->type == "$eq" || cell->type == "$ne" || cell->type == "$ge" || cell->type == "$gt") {
			bool is_signed = cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool();
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			extendSignalWidth(a, b, cell);
			if (cell->type == "$lt")
				ez->SET(is_signed ? ez->vec_lt_signed(a, b) : ez->vec_lt_unsigned(a, b), y.at(0));
			if (cell->type == "$le")
				ez->SET(is_signed ? ez->vec_le_signed(a, b) : ez->vec_le_unsigned(a, b), y.at(0));
			if (cell->type == "$eq")
				ez->SET(ez->vec_eq(a, b), y.at(0));
			if (cell->type == "$ne")
				ez->SET(ez->vec_ne(a, b), y.at(0));
			if (cell->type == "$ge")
				ez->SET(is_signed ? ez->vec_ge_signed(a, b) : ez->vec_ge_unsigned(a, b), y.at(0));
			if (cell->type == "$gt")
				ez->SET(is_signed ? ez->vec_gt_signed(a, b) : ez->vec_gt_unsigned(a, b), y.at(0));
			for (size_t i = 1; i < y.size(); i++)
				ez->SET(ez->FALSE, y.at(i));
			return true;
		}

		if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			char shift_left = cell->type == "$shl" || cell->type == "$sshl";
			bool sign_extend = cell->type == "$sshr" && cell->parameters["\\A_SIGNED"].as_bool();
			while (y.size() < a.size())
				y.push_back(ez->literal());
			while (y.size() > a.size())
				a.push_back(cell->parameters["\\A_SIGNED"].as_bool() ? a.back() : ez->FALSE);
			std::vector<int> tmp = a;
			for (size_t i = 0; i < b.size(); i++)
			{
				std::vector<int> tmp_shifted(tmp.size());
				for (size_t j = 0; j < tmp.size(); j++) {
					int idx = j + (1 << (i > 30 ? 30 : i)) * (shift_left ? -1 : +1);
					tmp_shifted.at(j) = (0 <= idx && idx < int(tmp.size())) ? tmp.at(idx) : sign_extend ? tmp.back() : ez->FALSE;
				}
				tmp = ez->vec_ite(b.at(i), tmp_shifted, tmp);
			}
			ez->assume(ez->vec_eq(tmp, y));
			return true;
		}

		if (cell->type == "$mul") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			extendSignalWidth(a, b, y, cell);
			std::vector<int> tmp(a.size(), ez->FALSE);
			for (int i = 0; i < int(a.size()); i++)
			{
				std::vector<int> shifted_a(a.size(), ez->FALSE);
				for (int j = i; j < int(a.size()); j++)
					shifted_a.at(j) = a.at(j-i);
				tmp = ez->vec_ite(b.at(i), ez->vec_add(tmp, shifted_a), tmp);
			}
			ez->assume(ez->vec_eq(tmp, y));
			return true;
		}

		if (cell->type == "$div" || cell->type == "$mod")
		{
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"), timestep);
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"), timestep);
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"), timestep);
			extendSignalWidth(a, b, y, cell);

			std::vector<int> a_u, b_u;
			if (cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool()) {
				a_u = ez->vec_ite(a.back(), ez->vec_neg(a), a);
				b_u = ez->vec_ite(b.back(), ez->vec_neg(b), b);
			} else {
				a_u = a;
				b_u = b;
			}

			std::vector<int> chain_buf = a_u;
			std::vector<int> y_u(a_u.size(), ez->FALSE);
			for (int i = int(a.size())-1; i >= 0; i--)
			{
				chain_buf.insert(chain_buf.end(), chain_buf.size(), ez->FALSE);

				std::vector<int> b_shl(i, ez->FALSE);
				b_shl.insert(b_shl.end(), b_u.begin(), b_u.end());
				b_shl.insert(b_shl.end(), chain_buf.size()-b_shl.size(), ez->FALSE);

				y_u.at(i) = ez->vec_ge_unsigned(chain_buf, b_shl);
				chain_buf = ez->vec_ite(y_u.at(i), ez->vec_sub(chain_buf, b_shl), chain_buf);

				chain_buf.erase(chain_buf.begin() + a_u.size(), chain_buf.end());
			}

			std::vector<int> y_tmp = ignore_div_by_zero ? y : ez->vec_var(y.size());
			if (cell->type == "$div") {
				if (cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool())
					ez->assume(ez->vec_eq(y_tmp, ez->vec_ite(ez->XOR(a.back(), b.back()), ez->vec_neg(y_u), y_u)));
				else
					ez->assume(ez->vec_eq(y_tmp, y_u));
			} else {
				if (cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool())
					ez->assume(ez->vec_eq(y_tmp, ez->vec_ite(a.back(), ez->vec_neg(chain_buf), chain_buf)));
				else
					ez->assume(ez->vec_eq(y_tmp, chain_buf));
			}

			if (ignore_div_by_zero) {
				ez->assume(ez->expression(ezSAT::OpOr, b));
			} else {
				std::vector<int> div_zero_result;
				if (cell->type == "$div") {
					if (cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool()) {
						std::vector<int> all_ones(y.size(), ez->TRUE);
						std::vector<int> only_first_one(y.size(), ez->FALSE);
						only_first_one.at(0) = ez->TRUE;
						div_zero_result = ez->vec_ite(a.back(), only_first_one, all_ones);
					} else {
						div_zero_result.insert(div_zero_result.end(), cell->connections.at("\\A").width, ez->TRUE);
						div_zero_result.insert(div_zero_result.end(), y.size() - div_zero_result.size(), ez->FALSE);
					}
				} else {
					int copy_a_bits = std::min(cell->connections.at("\\A").width, cell->connections.at("\\B").width);
					div_zero_result.insert(div_zero_result.end(), a.begin(), a.begin() + copy_a_bits);
					if (cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool())
						div_zero_result.insert(div_zero_result.end(), y.size() - div_zero_result.size(), div_zero_result.back());
					else
						div_zero_result.insert(div_zero_result.end(), y.size() - div_zero_result.size(), ez->FALSE);
				}
				ez->assume(ez->vec_eq(y, ez->vec_ite(ez->expression(ezSAT::OpOr, b), y_tmp, div_zero_result)));
			}

			return true;
		}

		if (timestep > 0 && (cell->type == "$dff" || cell->type == "$_DFF_N_" || cell->type == "$_DFF_P_")) {
			if (timestep == 1) {
				initial_state.add((*sigmap)(cell->connections.at("\\Q")));
			} else {
				std::vector<int> d = importSigSpec(cell->connections.at("\\D"), timestep-1);
				std::vector<int> q = importSigSpec(cell->connections.at("\\Q"), timestep);
				ez->assume(ez->vec_eq(d, q));
			}
			return true;
		}

		// Unsupported internal cell types: $div $mod $pow
		// .. and all sequential cells except $dff and $_DFF_[NP]_
		return false;
	}
};

#endif

