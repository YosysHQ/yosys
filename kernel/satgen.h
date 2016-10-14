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
#include "kernel/macc.h"

#include "libs/ezsat/ezminisat.h"

YOSYS_NAMESPACE_BEGIN

// defined in kernel/register.cc
extern struct SatSolver *yosys_satsolver_list;
extern struct SatSolver *yosys_satsolver;

struct SatSolver
{
	string name;
	SatSolver *next;
	virtual ezSAT *create() = 0;

	SatSolver(string name) : name(name) {
		next = yosys_satsolver_list;
		yosys_satsolver_list = this;
	}

	virtual ~SatSolver() {
		auto p = &yosys_satsolver_list;
		while (*p) {
			if (*p == this)
				*p = next;
			else
				p = &(*p)->next;
		}
		if (yosys_satsolver == this)
			yosys_satsolver = yosys_satsolver_list;
	}
};

struct ezSatPtr : public std::unique_ptr<ezSAT> {
	ezSatPtr() : unique_ptr<ezSAT>(yosys_satsolver->create()) { }
};

struct SatGen
{
	ezSAT *ez;
	SigMap *sigmap;
	std::string prefix;
	SigPool initial_state;
	std::map<std::string, RTLIL::SigSpec> asserts_a, asserts_en;
	std::map<std::string, RTLIL::SigSpec> assumes_a, assumes_en;
	std::map<std::string, std::map<RTLIL::SigBit, int>> imported_signals;
	std::map<std::pair<std::string, int>, bool> initstates;
	bool ignore_div_by_zero;
	bool model_undef;

	SatGen(ezSAT *ez, SigMap *sigmap, std::string prefix = std::string()) :
			ez(ez), sigmap(sigmap), prefix(prefix), ignore_div_by_zero(false), model_undef(false)
	{
	}

	void setContext(SigMap *sigmap, std::string prefix = std::string())
	{
		this->sigmap = sigmap;
		this->prefix = prefix;
	}

	std::vector<int> importSigSpecWorker(RTLIL::SigSpec sig, std::string &pf, bool undef_mode, bool dup_undef)
	{
		log_assert(!undef_mode || model_undef);
		sigmap->apply(sig);

		std::vector<int> vec;
		vec.reserve(GetSize(sig));

		for (auto &bit : sig)
			if (bit.wire == NULL) {
				if (model_undef && dup_undef && bit == RTLIL::State::Sx)
					vec.push_back(ez->frozen_literal());
				else
					vec.push_back(bit == (undef_mode ? RTLIL::State::Sx : RTLIL::State::S1) ? ez->CONST_TRUE : ez->CONST_FALSE);
			} else {
				std::string name = pf + (bit.wire->width == 1 ? stringf("%s", log_id(bit.wire)) : stringf("%s [%d]", log_id(bit.wire->name), bit.offset));
				vec.push_back(ez->frozen_literal(name));
				imported_signals[pf][bit] = vec.back();
			}
		return vec;
	}

	std::vector<int> importSigSpec(RTLIL::SigSpec sig, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(sig, pf, false, false);
	}

	std::vector<int> importDefSigSpec(RTLIL::SigSpec sig, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(sig, pf, false, true);
	}

	std::vector<int> importUndefSigSpec(RTLIL::SigSpec sig, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = "undef:" + prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(sig, pf, true, false);
	}

	int importSigBit(RTLIL::SigBit bit, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(bit, pf, false, false).front();
	}

	int importDefSigBit(RTLIL::SigBit bit, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(bit, pf, false, true).front();
	}

	int importUndefSigBit(RTLIL::SigBit bit, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = "undef:" + prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(bit, pf, true, false).front();
	}

	bool importedSigBit(RTLIL::SigBit bit, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return imported_signals[pf].count(bit) != 0;
	}

	void getAsserts(RTLIL::SigSpec &sig_a, RTLIL::SigSpec &sig_en, int timestep = -1)
	{
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		sig_a = asserts_a[pf];
		sig_en = asserts_en[pf];
	}

	void getAssumes(RTLIL::SigSpec &sig_a, RTLIL::SigSpec &sig_en, int timestep = -1)
	{
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		sig_a = assumes_a[pf];
		sig_en = assumes_en[pf];
	}

	int importAsserts(int timestep = -1)
	{
		std::vector<int> check_bits, enable_bits;
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		if (model_undef) {
			check_bits = ez->vec_and(ez->vec_not(importUndefSigSpec(asserts_a[pf], timestep)), importDefSigSpec(asserts_a[pf], timestep));
			enable_bits = ez->vec_and(ez->vec_not(importUndefSigSpec(asserts_en[pf], timestep)), importDefSigSpec(asserts_en[pf], timestep));
		} else {
			check_bits = importDefSigSpec(asserts_a[pf], timestep);
			enable_bits = importDefSigSpec(asserts_en[pf], timestep);
		}
		return ez->vec_reduce_and(ez->vec_or(check_bits, ez->vec_not(enable_bits)));
	}

	int importAssumes(int timestep = -1)
	{
		std::vector<int> check_bits, enable_bits;
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		if (model_undef) {
			check_bits = ez->vec_and(ez->vec_not(importUndefSigSpec(assumes_a[pf], timestep)), importDefSigSpec(assumes_a[pf], timestep));
			enable_bits = ez->vec_and(ez->vec_not(importUndefSigSpec(assumes_en[pf], timestep)), importDefSigSpec(assumes_en[pf], timestep));
		} else {
			check_bits = importDefSigSpec(assumes_a[pf], timestep);
			enable_bits = importDefSigSpec(assumes_en[pf], timestep);
		}
		return ez->vec_reduce_and(ez->vec_or(check_bits, ez->vec_not(enable_bits)));
	}

	int signals_eq(RTLIL::SigSpec lhs, RTLIL::SigSpec rhs, int timestep_lhs = -1, int timestep_rhs = -1)
	{
		if (timestep_rhs < 0)
			timestep_rhs = timestep_lhs;

		log_assert(lhs.size() == rhs.size());

		std::vector<int> vec_lhs = importSigSpec(lhs, timestep_lhs);
		std::vector<int> vec_rhs = importSigSpec(rhs, timestep_rhs);

		if (!model_undef)
			return ez->vec_eq(vec_lhs, vec_rhs);

		std::vector<int> undef_lhs = importUndefSigSpec(lhs, timestep_lhs);
		std::vector<int> undef_rhs = importUndefSigSpec(rhs, timestep_rhs);

		std::vector<int> eq_bits;
		for (int i = 0; i < lhs.size(); i++)
			eq_bits.push_back(ez->AND(ez->IFF(undef_lhs.at(i), undef_rhs.at(i)),
					ez->IFF(ez->OR(vec_lhs.at(i), undef_lhs.at(i)), ez->OR(vec_rhs.at(i), undef_rhs.at(i)))));
		return ez->expression(ezSAT::OpAnd, eq_bits);
	}

	void extendSignalWidth(std::vector<int> &vec_a, std::vector<int> &vec_b, RTLIL::Cell *cell, size_t y_width = 0, bool forced_signed = false)
	{
		bool is_signed = forced_signed;
		if (!forced_signed && cell->parameters.count("\\A_SIGNED") > 0 && cell->parameters.count("\\B_SIGNED") > 0)
			is_signed = cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool();
		while (vec_a.size() < vec_b.size() || vec_a.size() < y_width)
			vec_a.push_back(is_signed && vec_a.size() > 0 ? vec_a.back() : ez->CONST_FALSE);
		while (vec_b.size() < vec_a.size() || vec_b.size() < y_width)
			vec_b.push_back(is_signed && vec_b.size() > 0 ? vec_b.back() : ez->CONST_FALSE);
	}

	void extendSignalWidth(std::vector<int> &vec_a, std::vector<int> &vec_b, std::vector<int> &vec_y, RTLIL::Cell *cell, bool forced_signed = false)
	{
		extendSignalWidth(vec_a, vec_b, cell, vec_y.size(), forced_signed);
		while (vec_y.size() < vec_a.size())
			vec_y.push_back(ez->literal());
	}

	void extendSignalWidthUnary(std::vector<int> &vec_a, std::vector<int> &vec_y, RTLIL::Cell *cell, bool forced_signed = false)
	{
		bool is_signed = forced_signed || (cell->parameters.count("\\A_SIGNED") > 0 && cell->parameters["\\A_SIGNED"].as_bool());
		while (vec_a.size() < vec_y.size())
			vec_a.push_back(is_signed && vec_a.size() > 0 ? vec_a.back() : ez->CONST_FALSE);
		while (vec_y.size() < vec_a.size())
			vec_y.push_back(ez->literal());
	}

	void undefGating(std::vector<int> &vec_y, std::vector<int> &vec_yy, std::vector<int> &vec_undef)
	{
		log_assert(model_undef);
		log_assert(vec_y.size() == vec_yy.size());
		if (vec_y.size() > vec_undef.size()) {
			std::vector<int> trunc_y(vec_y.begin(), vec_y.begin() + vec_undef.size());
			std::vector<int> trunc_yy(vec_yy.begin(), vec_yy.begin() + vec_undef.size());
			ez->assume(ez->expression(ezSAT::OpAnd, ez->vec_or(vec_undef, ez->vec_iff(trunc_y, trunc_yy))));
		} else {
			log_assert(vec_y.size() == vec_undef.size());
			ez->assume(ez->expression(ezSAT::OpAnd, ez->vec_or(vec_undef, ez->vec_iff(vec_y, vec_yy))));
		}
	}

	void undefGating(int y, int yy, int undef)
	{
		ez->assume(ez->OR(undef, ez->IFF(y, yy)));
	}

	void setInitState(int timestep)
	{
		auto key = make_pair(prefix, timestep);
		log_assert(initstates.count(key) == 0 || initstates.at(key) == true);
		initstates[key] = true;
	}

	bool importCell(RTLIL::Cell *cell, int timestep = -1)
	{
		bool arith_undef_handled = false;
		bool is_arith_compare = cell->type.in("$lt", "$le", "$ge", "$gt");

		if (model_undef && (cell->type.in("$add", "$sub", "$mul", "$div", "$mod") || is_arith_compare))
		{
			std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
			if (is_arith_compare)
				extendSignalWidth(undef_a, undef_b, cell, true);
			else
				extendSignalWidth(undef_a, undef_b, undef_y, cell, true);

			int undef_any_a = ez->expression(ezSAT::OpOr, undef_a);
			int undef_any_b = ez->expression(ezSAT::OpOr, undef_b);
			int undef_y_bit = ez->OR(undef_any_a, undef_any_b);

			if (cell->type == "$div" || cell->type == "$mod") {
				std::vector<int> b = importSigSpec(cell->getPort("\\B"), timestep);
				undef_y_bit = ez->OR(undef_y_bit, ez->NOT(ez->expression(ezSAT::OpOr, b)));
			}

			if (is_arith_compare) {
				for (size_t i = 1; i < undef_y.size(); i++)
					ez->SET(ez->CONST_FALSE, undef_y.at(i));
				ez->SET(undef_y_bit, undef_y.at(0));
			} else {
				std::vector<int> undef_y_bits(undef_y.size(), undef_y_bit);
				ez->assume(ez->vec_eq(undef_y_bits, undef_y));
			}

			arith_undef_handled = true;
		}

		if (cell->type.in("$_AND_", "$_NAND_", "$_OR_", "$_NOR_", "$_XOR_", "$_XNOR_",
				"$and", "$or", "$xor", "$xnor", "$add", "$sub"))
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			extendSignalWidth(a, b, y, cell);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;

			if (cell->type == "$and" || cell->type == "$_AND_")
				ez->assume(ez->vec_eq(ez->vec_and(a, b), yy));
			if (cell->type == "$_NAND_")
				ez->assume(ez->vec_eq(ez->vec_not(ez->vec_and(a, b)), yy));
			if (cell->type == "$or" || cell->type == "$_OR_")
				ez->assume(ez->vec_eq(ez->vec_or(a, b), yy));
			if (cell->type == "$_NOR_")
				ez->assume(ez->vec_eq(ez->vec_not(ez->vec_or(a, b)), yy));
			if (cell->type == "$xor" || cell->type == "$_XOR_")
				ez->assume(ez->vec_eq(ez->vec_xor(a, b), yy));
			if (cell->type == "$xnor" || cell->type == "$_XNOR_")
				ez->assume(ez->vec_eq(ez->vec_not(ez->vec_xor(a, b)), yy));
			if (cell->type == "$add")
				ez->assume(ez->vec_eq(ez->vec_add(a, b), yy));
			if (cell->type == "$sub")
				ez->assume(ez->vec_eq(ez->vec_sub(a, b), yy));

			if (model_undef && !arith_undef_handled)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				extendSignalWidth(undef_a, undef_b, undef_y, cell, false);

				if (cell->type.in("$and", "$_AND_", "$_NAND_")) {
					std::vector<int> a0 = ez->vec_and(ez->vec_not(a), ez->vec_not(undef_a));
					std::vector<int> b0 = ez->vec_and(ez->vec_not(b), ez->vec_not(undef_b));
					std::vector<int> yX = ez->vec_and(ez->vec_or(undef_a, undef_b), ez->vec_not(ez->vec_or(a0, b0)));
					ez->assume(ez->vec_eq(yX, undef_y));
				}
				else if (cell->type.in("$or", "$_OR_", "$_NOR_")) {
					std::vector<int> a1 = ez->vec_and(a, ez->vec_not(undef_a));
					std::vector<int> b1 = ez->vec_and(b, ez->vec_not(undef_b));
					std::vector<int> yX = ez->vec_and(ez->vec_or(undef_a, undef_b), ez->vec_not(ez->vec_or(a1, b1)));
					ez->assume(ez->vec_eq(yX, undef_y));
				}
				else if (cell->type.in("$xor", "$xnor", "$_XOR_", "$_XNOR_")) {
					std::vector<int> yX = ez->vec_or(undef_a, undef_b);
					ez->assume(ez->vec_eq(yX, undef_y));
				}
				else
					log_abort();

				undefGating(y, yy, undef_y);
			}
			else if (model_undef)
			{
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type.in("$_AOI3_", "$_OAI3_", "$_AOI4_", "$_OAI4_"))
		{
			bool aoi_mode = cell->type.in("$_AOI3_", "$_AOI4_");
			bool three_mode = cell->type.in("$_AOI3_", "$_OAI3_");

			int a = importDefSigSpec(cell->getPort("\\A"), timestep).at(0);
			int b = importDefSigSpec(cell->getPort("\\B"), timestep).at(0);
			int c = importDefSigSpec(cell->getPort("\\C"), timestep).at(0);
			int d = three_mode ? (aoi_mode ? ez->CONST_TRUE : ez->CONST_FALSE) : importDefSigSpec(cell->getPort("\\D"), timestep).at(0);
			int y = importDefSigSpec(cell->getPort("\\Y"), timestep).at(0);
			int yy = model_undef ? ez->literal() : y;

			if (cell->type.in("$_AOI3_", "$_AOI4_"))
				ez->assume(ez->IFF(ez->NOT(ez->OR(ez->AND(a, b), ez->AND(c, d))), yy));
			else
				ez->assume(ez->IFF(ez->NOT(ez->AND(ez->OR(a, b), ez->OR(c, d))), yy));

			if (model_undef)
			{
				int undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep).at(0);
				int undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep).at(0);
				int undef_c = importUndefSigSpec(cell->getPort("\\C"), timestep).at(0);
				int undef_d = three_mode ? ez->CONST_FALSE : importUndefSigSpec(cell->getPort("\\D"), timestep).at(0);
				int undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep).at(0);

				if (aoi_mode)
				{
					int a0 = ez->AND(ez->NOT(a), ez->NOT(undef_a));
					int b0 = ez->AND(ez->NOT(b), ez->NOT(undef_b));
					int c0 = ez->AND(ez->NOT(c), ez->NOT(undef_c));
					int d0 = ez->AND(ez->NOT(d), ez->NOT(undef_d));

					int ab = ez->AND(a, b), cd = ez->AND(c, d);
					int undef_ab = ez->AND(ez->OR(undef_a, undef_b), ez->NOT(ez->OR(a0, b0)));
					int undef_cd = ez->AND(ez->OR(undef_c, undef_d), ez->NOT(ez->OR(c0, d0)));

					int ab1 = ez->AND(ab, ez->NOT(undef_ab));
					int cd1 = ez->AND(cd, ez->NOT(undef_cd));
					int yX = ez->AND(ez->OR(undef_ab, undef_cd), ez->NOT(ez->OR(ab1, cd1)));

					ez->assume(ez->IFF(yX, undef_y));
				}
				else
				{
					int a1 = ez->AND(a, ez->NOT(undef_a));
					int b1 = ez->AND(b, ez->NOT(undef_b));
					int c1 = ez->AND(c, ez->NOT(undef_c));
					int d1 = ez->AND(d, ez->NOT(undef_d));

					int ab = ez->OR(a, b), cd = ez->OR(c, d);
					int undef_ab = ez->AND(ez->OR(undef_a, undef_b), ez->NOT(ez->OR(a1, b1)));
					int undef_cd = ez->AND(ez->OR(undef_c, undef_d), ez->NOT(ez->OR(c1, d1)));

					int ab0 = ez->AND(ez->NOT(ab), ez->NOT(undef_ab));
					int cd0 = ez->AND(ez->NOT(cd), ez->NOT(undef_cd));
					int yX = ez->AND(ez->OR(undef_ab, undef_cd), ez->NOT(ez->OR(ab0, cd0)));

					ez->assume(ez->IFF(yX, undef_y));
				}

				undefGating(y, yy, undef_y);
			}

			return true;
		}

		if (cell->type == "$_NOT_" || cell->type == "$not")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			extendSignalWidthUnary(a, y, cell);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;
			ez->assume(ez->vec_eq(ez->vec_not(a), yy));

			if (model_undef) {
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				extendSignalWidthUnary(undef_a, undef_y, cell, false);
				ez->assume(ez->vec_eq(undef_a, undef_y));
				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$_MUX_" || cell->type == "$mux")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> s = importDefSigSpec(cell->getPort("\\S"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;
			ez->assume(ez->vec_eq(ez->vec_ite(s.at(0), b, a), yy));

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				std::vector<int> undef_s = importUndefSigSpec(cell->getPort("\\S"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);

				std::vector<int> unequal_ab = ez->vec_not(ez->vec_iff(a, b));
				std::vector<int> undef_ab = ez->vec_or(unequal_ab, ez->vec_or(undef_a, undef_b));
				std::vector<int> yX = ez->vec_ite(undef_s.at(0), undef_ab, ez->vec_ite(s.at(0), undef_b, undef_a));
				ez->assume(ez->vec_eq(yX, undef_y));
				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$pmux")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> s = importDefSigSpec(cell->getPort("\\S"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;

			std::vector<int> tmp = a;
			for (size_t i = 0; i < s.size(); i++) {
				std::vector<int> part_of_b(b.begin()+i*a.size(), b.begin()+(i+1)*a.size());
				tmp = ez->vec_ite(s.at(i), part_of_b, tmp);
			}
			ez->assume(ez->vec_eq(tmp, yy));

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				std::vector<int> undef_s = importUndefSigSpec(cell->getPort("\\S"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);

				int maybe_one_hot = ez->CONST_FALSE;
				int maybe_many_hot = ez->CONST_FALSE;

				int sure_one_hot = ez->CONST_FALSE;
				int sure_many_hot = ez->CONST_FALSE;

				std::vector<int> bits_set = std::vector<int>(undef_y.size(), ez->CONST_FALSE);
				std::vector<int> bits_clr = std::vector<int>(undef_y.size(), ez->CONST_FALSE);

				for (size_t i = 0; i < s.size(); i++)
				{
					std::vector<int> part_of_b(b.begin()+i*a.size(), b.begin()+(i+1)*a.size());
					std::vector<int> part_of_undef_b(undef_b.begin()+i*a.size(), undef_b.begin()+(i+1)*a.size());

					int maybe_s = ez->OR(s.at(i), undef_s.at(i));
					int sure_s = ez->AND(s.at(i), ez->NOT(undef_s.at(i)));

					maybe_one_hot = ez->OR(maybe_one_hot, maybe_s);
					maybe_many_hot = ez->OR(maybe_many_hot, ez->AND(maybe_one_hot, maybe_s));

					sure_one_hot = ez->OR(sure_one_hot, sure_s);
					sure_many_hot = ez->OR(sure_many_hot, ez->AND(sure_one_hot, sure_s));

					bits_set = ez->vec_ite(maybe_s, ez->vec_or(bits_set, ez->vec_or(bits_set, ez->vec_or(part_of_b, part_of_undef_b))), bits_set);
					bits_clr = ez->vec_ite(maybe_s, ez->vec_or(bits_clr, ez->vec_or(bits_clr, ez->vec_or(ez->vec_not(part_of_b), part_of_undef_b))), bits_clr);
				}

				int maybe_a = ez->NOT(maybe_one_hot);

				bits_set = ez->vec_ite(maybe_a, ez->vec_or(bits_set, ez->vec_or(bits_set, ez->vec_or(a, undef_a))), bits_set);
				bits_clr = ez->vec_ite(maybe_a, ez->vec_or(bits_clr, ez->vec_or(bits_clr, ez->vec_or(ez->vec_not(a), undef_a))), bits_clr);

				ez->assume(ez->vec_eq(ez->vec_not(ez->vec_xor(bits_set, bits_clr)), undef_y));
				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$pos" || cell->type == "$neg")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			extendSignalWidthUnary(a, y, cell);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;

			if (cell->type == "$pos") {
				ez->assume(ez->vec_eq(a, yy));
			} else {
				std::vector<int> zero(a.size(), ez->CONST_FALSE);
				ez->assume(ez->vec_eq(ez->vec_sub(zero, a), yy));
			}

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				extendSignalWidthUnary(undef_a, undef_y, cell);

				if (cell->type == "$pos") {
					ez->assume(ez->vec_eq(undef_a, undef_y));
				} else {
					int undef_any_a = ez->expression(ezSAT::OpOr, undef_a);
					std::vector<int> undef_y_bits(undef_y.size(), undef_any_a);
					ez->assume(ez->vec_eq(undef_y_bits, undef_y));
				}

				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$reduce_and" || cell->type == "$reduce_or" || cell->type == "$reduce_xor" ||
				cell->type == "$reduce_xnor" || cell->type == "$reduce_bool" || cell->type == "$logic_not")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;

			if (cell->type == "$reduce_and")
				ez->SET(ez->expression(ez->OpAnd, a), yy.at(0));
			if (cell->type == "$reduce_or" || cell->type == "$reduce_bool")
				ez->SET(ez->expression(ez->OpOr, a), yy.at(0));
			if (cell->type == "$reduce_xor")
				ez->SET(ez->expression(ez->OpXor, a), yy.at(0));
			if (cell->type == "$reduce_xnor")
				ez->SET(ez->NOT(ez->expression(ez->OpXor, a)), yy.at(0));
			if (cell->type == "$logic_not")
				ez->SET(ez->NOT(ez->expression(ez->OpOr, a)), yy.at(0));
			for (size_t i = 1; i < y.size(); i++)
				ez->SET(ez->CONST_FALSE, yy.at(i));

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				int aX = ez->expression(ezSAT::OpOr, undef_a);

				if (cell->type == "$reduce_and") {
					int a0 = ez->expression(ezSAT::OpOr, ez->vec_and(ez->vec_not(a), ez->vec_not(undef_a)));
					ez->assume(ez->IFF(ez->AND(ez->NOT(a0), aX), undef_y.at(0)));
				}
				else if (cell->type == "$reduce_or" || cell->type == "$reduce_bool" || cell->type == "$logic_not") {
					int a1 = ez->expression(ezSAT::OpOr, ez->vec_and(a, ez->vec_not(undef_a)));
					ez->assume(ez->IFF(ez->AND(ez->NOT(a1), aX), undef_y.at(0)));
				}
				else if (cell->type == "$reduce_xor" || cell->type == "$reduce_xnor") {
					ez->assume(ez->IFF(aX, undef_y.at(0)));
				} else
					log_abort();

				for (size_t i = 1; i < undef_y.size(); i++)
					ez->SET(ez->CONST_FALSE, undef_y.at(i));

				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$logic_and" || cell->type == "$logic_or")
		{
			std::vector<int> vec_a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> vec_b = importDefSigSpec(cell->getPort("\\B"), timestep);

			int a = ez->expression(ez->OpOr, vec_a);
			int b = ez->expression(ez->OpOr, vec_b);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;

			if (cell->type == "$logic_and")
				ez->SET(ez->expression(ez->OpAnd, a, b), yy.at(0));
			else
				ez->SET(ez->expression(ez->OpOr, a, b), yy.at(0));
			for (size_t i = 1; i < y.size(); i++)
				ez->SET(ez->CONST_FALSE, yy.at(i));

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);

				int a0 = ez->NOT(ez->OR(ez->expression(ezSAT::OpOr, vec_a), ez->expression(ezSAT::OpOr, undef_a)));
				int b0 = ez->NOT(ez->OR(ez->expression(ezSAT::OpOr, vec_b), ez->expression(ezSAT::OpOr, undef_b)));
				int a1 = ez->expression(ezSAT::OpOr, ez->vec_and(vec_a, ez->vec_not(undef_a)));
				int b1 = ez->expression(ezSAT::OpOr, ez->vec_and(vec_b, ez->vec_not(undef_b)));
				int aX = ez->expression(ezSAT::OpOr, undef_a);
				int bX = ez->expression(ezSAT::OpOr, undef_b);

				if (cell->type == "$logic_and")
					ez->SET(ez->AND(ez->OR(aX, bX), ez->NOT(ez->AND(a1, b1)), ez->NOT(a0), ez->NOT(b0)), undef_y.at(0));
				else if (cell->type == "$logic_or")
					ez->SET(ez->AND(ez->OR(aX, bX), ez->NOT(ez->AND(a0, b0)), ez->NOT(a1), ez->NOT(b1)), undef_y.at(0));
				else
					log_abort();

				for (size_t i = 1; i < undef_y.size(); i++)
					ez->SET(ez->CONST_FALSE, undef_y.at(i));

				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$lt" || cell->type == "$le" || cell->type == "$eq" || cell->type == "$ne" || cell->type == "$eqx" || cell->type == "$nex" || cell->type == "$ge" || cell->type == "$gt")
		{
			bool is_signed = cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool();
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			extendSignalWidth(a, b, cell);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;

			if (model_undef && (cell->type == "$eqx" || cell->type == "$nex")) {
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				extendSignalWidth(undef_a, undef_b, cell, true);
				a = ez->vec_or(a, undef_a);
				b = ez->vec_or(b, undef_b);
			}

			if (cell->type == "$lt")
				ez->SET(is_signed ? ez->vec_lt_signed(a, b) : ez->vec_lt_unsigned(a, b), yy.at(0));
			if (cell->type == "$le")
				ez->SET(is_signed ? ez->vec_le_signed(a, b) : ez->vec_le_unsigned(a, b), yy.at(0));
			if (cell->type == "$eq" || cell->type == "$eqx")
				ez->SET(ez->vec_eq(a, b), yy.at(0));
			if (cell->type == "$ne" || cell->type == "$nex")
				ez->SET(ez->vec_ne(a, b), yy.at(0));
			if (cell->type == "$ge")
				ez->SET(is_signed ? ez->vec_ge_signed(a, b) : ez->vec_ge_unsigned(a, b), yy.at(0));
			if (cell->type == "$gt")
				ez->SET(is_signed ? ez->vec_gt_signed(a, b) : ez->vec_gt_unsigned(a, b), yy.at(0));
			for (size_t i = 1; i < y.size(); i++)
				ez->SET(ez->CONST_FALSE, yy.at(i));

			if (model_undef && (cell->type == "$eqx" || cell->type == "$nex"))
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				extendSignalWidth(undef_a, undef_b, cell, true);

				if (cell->type == "$eqx")
					yy.at(0) = ez->AND(yy.at(0), ez->vec_eq(undef_a, undef_b));
				else
					yy.at(0) = ez->OR(yy.at(0), ez->vec_ne(undef_a, undef_b));

				for (size_t i = 0; i < y.size(); i++)
					ez->SET(ez->CONST_FALSE, undef_y.at(i));

				ez->assume(ez->vec_eq(y, yy));
			}
			else if (model_undef && (cell->type == "$eq" || cell->type == "$ne"))
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				extendSignalWidth(undef_a, undef_b, cell, true);

				int undef_any_a = ez->expression(ezSAT::OpOr, undef_a);
				int undef_any_b = ez->expression(ezSAT::OpOr, undef_b);
				int undef_any = ez->OR(undef_any_a, undef_any_b);

				std::vector<int> masked_a_bits = ez->vec_or(a, ez->vec_or(undef_a, undef_b));
				std::vector<int> masked_b_bits = ez->vec_or(b, ez->vec_or(undef_a, undef_b));

				int masked_ne = ez->vec_ne(masked_a_bits, masked_b_bits);
				int undef_y_bit = ez->AND(undef_any, ez->NOT(masked_ne));

				for (size_t i = 1; i < undef_y.size(); i++)
					ez->SET(ez->CONST_FALSE, undef_y.at(i));
				ez->SET(undef_y_bit, undef_y.at(0));

				undefGating(y, yy, undef_y);
			}
			else
			{
				if (model_undef) {
					std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
					undefGating(y, yy, undef_y);
				}
				log_assert(!model_undef || arith_undef_handled);
			}
			return true;
		}

		if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr" || cell->type == "$shift" || cell->type == "$shiftx")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);

			int extend_bit = ez->CONST_FALSE;

			if (!cell->type.in("$shift", "$shiftx") && cell->parameters["\\A_SIGNED"].as_bool())
				extend_bit = a.back();

			while (y.size() < a.size())
				y.push_back(ez->literal());
			while (y.size() > a.size())
				a.push_back(extend_bit);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;
			std::vector<int> shifted_a;

			if (cell->type == "$shl" || cell->type == "$sshl")
				shifted_a = ez->vec_shift_left(a, b, false, ez->CONST_FALSE, ez->CONST_FALSE);

			if (cell->type == "$shr")
				shifted_a = ez->vec_shift_right(a, b, false, ez->CONST_FALSE, ez->CONST_FALSE);

			if (cell->type == "$sshr")
				shifted_a = ez->vec_shift_right(a, b, false, cell->parameters["\\A_SIGNED"].as_bool() ? a.back() : ez->CONST_FALSE, ez->CONST_FALSE);

			if (cell->type == "$shift" || cell->type == "$shiftx")
				shifted_a = ez->vec_shift_right(a, b, cell->parameters["\\B_SIGNED"].as_bool(), ez->CONST_FALSE, ez->CONST_FALSE);

			ez->assume(ez->vec_eq(shifted_a, yy));

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				std::vector<int> undef_a_shifted;

				extend_bit = cell->type == "$shiftx" ? ez->CONST_TRUE : ez->CONST_FALSE;
				if (!cell->type.in("$shift", "$shiftx") && cell->parameters["\\A_SIGNED"].as_bool())
					extend_bit = undef_a.back();

				while (undef_y.size() < undef_a.size())
					undef_y.push_back(ez->literal());
				while (undef_y.size() > undef_a.size())
					undef_a.push_back(extend_bit);

				if (cell->type == "$shl" || cell->type == "$sshl")
					undef_a_shifted = ez->vec_shift_left(undef_a, b, false, ez->CONST_FALSE, ez->CONST_FALSE);

				if (cell->type == "$shr")
					undef_a_shifted = ez->vec_shift_right(undef_a, b, false, ez->CONST_FALSE, ez->CONST_FALSE);

				if (cell->type == "$sshr")
					undef_a_shifted = ez->vec_shift_right(undef_a, b, false, cell->parameters["\\A_SIGNED"].as_bool() ? undef_a.back() : ez->CONST_FALSE, ez->CONST_FALSE);

				if (cell->type == "$shift")
					undef_a_shifted = ez->vec_shift_right(undef_a, b, cell->parameters["\\B_SIGNED"].as_bool(), ez->CONST_FALSE, ez->CONST_FALSE);

				if (cell->type == "$shiftx")
					undef_a_shifted = ez->vec_shift_right(undef_a, b, cell->parameters["\\B_SIGNED"].as_bool(), ez->CONST_TRUE, ez->CONST_TRUE);

				int undef_any_b = ez->expression(ezSAT::OpOr, undef_b);
				std::vector<int> undef_all_y_bits(undef_y.size(), undef_any_b);
				ez->assume(ez->vec_eq(ez->vec_or(undef_a_shifted, undef_all_y_bits), undef_y));
				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$mul")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			extendSignalWidth(a, b, y, cell);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;

			std::vector<int> tmp(a.size(), ez->CONST_FALSE);
			for (int i = 0; i < int(a.size()); i++)
			{
				std::vector<int> shifted_a(a.size(), ez->CONST_FALSE);
				for (int j = i; j < int(a.size()); j++)
					shifted_a.at(j) = a.at(j-i);
				tmp = ez->vec_ite(b.at(i), ez->vec_add(tmp, shifted_a), tmp);
			}
			ez->assume(ez->vec_eq(tmp, yy));

			if (model_undef) {
				log_assert(arith_undef_handled);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$macc")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);

			Macc macc;
			macc.from_cell(cell);

			std::vector<int> tmp(GetSize(y), ez->CONST_FALSE);

			for (auto &port : macc.ports)
			{
				std::vector<int> in_a = importDefSigSpec(port.in_a, timestep);
				std::vector<int> in_b = importDefSigSpec(port.in_b, timestep);

				while (GetSize(in_a) < GetSize(y))
					in_a.push_back(port.is_signed && !in_a.empty() ? in_a.back() : ez->CONST_FALSE);
				in_a.resize(GetSize(y));

				if (GetSize(in_b))
				{
					while (GetSize(in_b) < GetSize(y))
						in_b.push_back(port.is_signed && !in_b.empty() ? in_b.back() : ez->CONST_FALSE);
					in_b.resize(GetSize(y));

					for (int i = 0; i < GetSize(in_b); i++) {
						std::vector<int> shifted_a(in_a.size(), ez->CONST_FALSE);
						for (int j = i; j < int(in_a.size()); j++)
							shifted_a.at(j) = in_a.at(j-i);
						if (port.do_subtract)
							tmp = ez->vec_ite(in_b.at(i), ez->vec_sub(tmp, shifted_a), tmp);
						else
							tmp = ez->vec_ite(in_b.at(i), ez->vec_add(tmp, shifted_a), tmp);
					}
				}
				else
				{
					if (port.do_subtract)
						tmp = ez->vec_sub(tmp, in_a);
					else
						tmp = ez->vec_add(tmp, in_a);
				}
			}

			for (int i = 0; i < GetSize(b); i++) {
				std::vector<int> val(GetSize(y), ez->CONST_FALSE);
				val.at(0) = b.at(i);
				tmp = ez->vec_add(tmp, val);
			}

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);

				int undef_any_a = ez->expression(ezSAT::OpOr, undef_a);
				int undef_any_b = ez->expression(ezSAT::OpOr, undef_b);

				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				ez->assume(ez->vec_eq(undef_y, std::vector<int>(GetSize(y), ez->OR(undef_any_a, undef_any_b))));

				undefGating(y, tmp, undef_y);
			}
			else
				ez->assume(ez->vec_eq(y, tmp));

			return true;
		}

		if (cell->type == "$div" || cell->type == "$mod")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			extendSignalWidth(a, b, y, cell);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;

			std::vector<int> a_u, b_u;
			if (cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool()) {
				a_u = ez->vec_ite(a.back(), ez->vec_neg(a), a);
				b_u = ez->vec_ite(b.back(), ez->vec_neg(b), b);
			} else {
				a_u = a;
				b_u = b;
			}

			std::vector<int> chain_buf = a_u;
			std::vector<int> y_u(a_u.size(), ez->CONST_FALSE);
			for (int i = int(a.size())-1; i >= 0; i--)
			{
				chain_buf.insert(chain_buf.end(), chain_buf.size(), ez->CONST_FALSE);

				std::vector<int> b_shl(i, ez->CONST_FALSE);
				b_shl.insert(b_shl.end(), b_u.begin(), b_u.end());
				b_shl.insert(b_shl.end(), chain_buf.size()-b_shl.size(), ez->CONST_FALSE);

				y_u.at(i) = ez->vec_ge_unsigned(chain_buf, b_shl);
				chain_buf = ez->vec_ite(y_u.at(i), ez->vec_sub(chain_buf, b_shl), chain_buf);

				chain_buf.erase(chain_buf.begin() + a_u.size(), chain_buf.end());
			}

			std::vector<int> y_tmp = ignore_div_by_zero ? yy : ez->vec_var(y.size());
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
						std::vector<int> all_ones(y.size(), ez->CONST_TRUE);
						std::vector<int> only_first_one(y.size(), ez->CONST_FALSE);
						only_first_one.at(0) = ez->CONST_TRUE;
						div_zero_result = ez->vec_ite(a.back(), only_first_one, all_ones);
					} else {
						div_zero_result.insert(div_zero_result.end(), cell->getPort("\\A").size(), ez->CONST_TRUE);
						div_zero_result.insert(div_zero_result.end(), y.size() - div_zero_result.size(), ez->CONST_FALSE);
					}
				} else {
					int copy_a_bits = min(cell->getPort("\\A").size(), cell->getPort("\\B").size());
					div_zero_result.insert(div_zero_result.end(), a.begin(), a.begin() + copy_a_bits);
					if (cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool())
						div_zero_result.insert(div_zero_result.end(), y.size() - div_zero_result.size(), div_zero_result.back());
					else
						div_zero_result.insert(div_zero_result.end(), y.size() - div_zero_result.size(), ez->CONST_FALSE);
				}
				ez->assume(ez->vec_eq(yy, ez->vec_ite(ez->expression(ezSAT::OpOr, b), y_tmp, div_zero_result)));
			}

			if (model_undef) {
				log_assert(arith_undef_handled);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$lut")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);

			std::vector<int> lut;
			for (auto bit : cell->getParam("\\LUT").bits)
				lut.push_back(bit == RTLIL::S1 ? ez->CONST_TRUE : ez->CONST_FALSE);
			while (GetSize(lut) < (1 << GetSize(a)))
				lut.push_back(ez->CONST_FALSE);
			lut.resize(1 << GetSize(a));

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> t(lut), u(GetSize(t), ez->CONST_FALSE);

				for (int i = GetSize(a)-1; i >= 0; i--)
				{
					std::vector<int> t0(t.begin(), t.begin() + GetSize(t)/2);
					std::vector<int> t1(t.begin() + GetSize(t)/2, t.end());

					std::vector<int> u0(u.begin(), u.begin() + GetSize(u)/2);
					std::vector<int> u1(u.begin() + GetSize(u)/2, u.end());

					t = ez->vec_ite(a[i], t1, t0);
					u = ez->vec_ite(undef_a[i], ez->vec_or(ez->vec_xor(t0, t1), ez->vec_or(u0, u1)), ez->vec_ite(a[i], u1, u0));
				}

				log_assert(GetSize(t) == 1);
				log_assert(GetSize(u) == 1);
				undefGating(y, t, u);
				ez->assume(ez->vec_eq(importUndefSigSpec(cell->getPort("\\Y"), timestep), u));
			}
			else
			{
				std::vector<int> t = lut;
				for (int i = GetSize(a)-1; i >= 0; i--)
				{
					std::vector<int> t0(t.begin(), t.begin() + GetSize(t)/2);
					std::vector<int> t1(t.begin() + GetSize(t)/2, t.end());
					t = ez->vec_ite(a[i], t1, t0);
				}

				log_assert(GetSize(t) == 1);
				ez->assume(ez->vec_eq(y, t));
			}
			return true;
		}

		if (cell->type == "$sop")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			int y = importDefSigSpec(cell->getPort("\\Y"), timestep).at(0);

			int width = cell->getParam("\\WIDTH").as_int();
			int depth = cell->getParam("\\DEPTH").as_int();

			vector<State> table_raw = cell->getParam("\\TABLE").bits;
			while (GetSize(table_raw) < 2*width*depth)
				table_raw.push_back(State::S0);

			vector<vector<int>> table(depth);

			for (int i = 0; i < depth; i++)
			for (int j = 0; j < width; j++)
			{
				bool pat0 = (table_raw[2*width*i + 2*j + 0] == State::S1);
				bool pat1 = (table_raw[2*width*i + 2*j + 1] == State::S1);

				if (pat0 && !pat1)
					table.at(i).push_back(0);
				else if (!pat0 && pat1)
					table.at(i).push_back(1);
				else
					table.at(i).push_back(-1);
			}

			if (model_undef)
			{
				std::vector<int> products, undef_products;
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				int undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep).at(0);

				for (int i = 0; i < depth; i++)
				{
					std::vector<int> cmp_a, cmp_ua, cmp_b;

					for (int j = 0; j < width; j++)
						if (table.at(i).at(j) >= 0) {
							cmp_a.push_back(a.at(j));
							cmp_ua.push_back(undef_a.at(j));
							cmp_b.push_back(table.at(i).at(j) ? ez->CONST_TRUE : ez->CONST_FALSE);
						}

					std::vector<int> masked_a = ez->vec_or(cmp_a, cmp_ua);
					std::vector<int> masked_b = ez->vec_or(cmp_b, cmp_ua);

					int masked_eq = ez->vec_eq(masked_a, masked_b);
					int any_undef = ez->expression(ezSAT::OpOr, cmp_ua);

					undef_products.push_back(ez->AND(any_undef, masked_eq));
					products.push_back(ez->AND(ez->NOT(any_undef), masked_eq));
				}

				int yy = ez->expression(ezSAT::OpOr, products);
				ez->SET(undef_y, ez->AND(ez->NOT(yy), ez->expression(ezSAT::OpOr, undef_products)));
				undefGating(y, yy, undef_y);
			}
			else
			{
				std::vector<int> products;

				for (int i = 0; i < depth; i++)
				{
					std::vector<int> cmp_a, cmp_b;

					for (int j = 0; j < width; j++)
						if (table.at(i).at(j) >= 0) {
							cmp_a.push_back(a.at(j));
							cmp_b.push_back(table.at(i).at(j) ? ez->CONST_TRUE : ez->CONST_FALSE);
						}

					products.push_back(ez->vec_eq(cmp_a, cmp_b));
				}

				ez->SET(y, ez->expression(ezSAT::OpOr, products));
			}

			return true;
		}

		if (cell->type == "$fa")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> c = importDefSigSpec(cell->getPort("\\C"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			std::vector<int> x = importDefSigSpec(cell->getPort("\\X"), timestep);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;
			std::vector<int> xx = model_undef ? ez->vec_var(x.size()) : x;

			std::vector<int> t1 = ez->vec_xor(a, b);
			ez->assume(ez->vec_eq(yy, ez->vec_xor(t1, c)));

			std::vector<int> t2 = ez->vec_and(a, b);
			std::vector<int> t3 = ez->vec_and(c, t1);
			ez->assume(ez->vec_eq(xx, ez->vec_or(t2, t3)));

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				std::vector<int> undef_c = importUndefSigSpec(cell->getPort("\\C"), timestep);

				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				std::vector<int> undef_x = importUndefSigSpec(cell->getPort("\\X"), timestep);

				ez->assume(ez->vec_eq(undef_y, ez->vec_or(ez->vec_or(undef_a, undef_b), undef_c)));
				ez->assume(ez->vec_eq(undef_x, undef_y));

				undefGating(y, yy, undef_y);
				undefGating(x, xx, undef_x);
			}
			return true;
		}

		if (cell->type == "$lcu")
		{
			std::vector<int> p = importDefSigSpec(cell->getPort("\\P"), timestep);
			std::vector<int> g = importDefSigSpec(cell->getPort("\\G"), timestep);
			std::vector<int> ci = importDefSigSpec(cell->getPort("\\CI"), timestep);
			std::vector<int> co = importDefSigSpec(cell->getPort("\\CO"), timestep);

			std::vector<int> yy = model_undef ? ez->vec_var(co.size()) : co;

			for (int i = 0; i < GetSize(co); i++)
				ez->SET(yy[i], ez->OR(g[i], ez->AND(p[i], i ? yy[i-1] : ci[0])));

			if (model_undef)
			{
				std::vector<int> undef_p = importUndefSigSpec(cell->getPort("\\P"), timestep);
				std::vector<int> undef_g = importUndefSigSpec(cell->getPort("\\G"), timestep);
				std::vector<int> undef_ci = importUndefSigSpec(cell->getPort("\\CI"), timestep);
				std::vector<int> undef_co = importUndefSigSpec(cell->getPort("\\CO"), timestep);

				int undef_any_p = ez->expression(ezSAT::OpOr, undef_p);
				int undef_any_g = ez->expression(ezSAT::OpOr, undef_g);
				int undef_any_ci = ez->expression(ezSAT::OpOr, undef_ci);
				int undef_co_bit = ez->OR(undef_any_p, undef_any_g, undef_any_ci);

				std::vector<int> undef_co_bits(undef_co.size(), undef_co_bit);
				ez->assume(ez->vec_eq(undef_co_bits, undef_co));

				undefGating(co, yy, undef_co);
			}
			return true;
		}

		if (cell->type == "$alu")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> b = importDefSigSpec(cell->getPort("\\B"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			std::vector<int> x = importDefSigSpec(cell->getPort("\\X"), timestep);
			std::vector<int> ci = importDefSigSpec(cell->getPort("\\CI"), timestep);
			std::vector<int> bi = importDefSigSpec(cell->getPort("\\BI"), timestep);
			std::vector<int> co = importDefSigSpec(cell->getPort("\\CO"), timestep);

			extendSignalWidth(a, b, y, cell);
			extendSignalWidth(a, b, x, cell);
			extendSignalWidth(a, b, co, cell);

			std::vector<int> def_y = model_undef ? ez->vec_var(y.size()) : y;
			std::vector<int> def_x = model_undef ? ez->vec_var(x.size()) : x;
			std::vector<int> def_co = model_undef ? ez->vec_var(co.size()) : co;

			log_assert(GetSize(y) == GetSize(x));
			log_assert(GetSize(y) == GetSize(co));
			log_assert(GetSize(ci) == 1);
			log_assert(GetSize(bi) == 1);

			for (int i = 0; i < GetSize(y); i++)
			{
				int s1 = a.at(i), s2 = ez->XOR(b.at(i), bi.at(0)), s3 = i ? co.at(i-1) : ci.at(0);
				ez->SET(def_x.at(i), ez->XOR(s1, s2));
				ez->SET(def_y.at(i), ez->XOR(def_x.at(i), s3));
				ez->SET(def_co.at(i), ez->OR(ez->AND(s1, s2), ez->AND(s1, s3), ez->AND(s2, s3)));
			}

			if (model_undef)
			{
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_b = importUndefSigSpec(cell->getPort("\\B"), timestep);
				std::vector<int> undef_ci = importUndefSigSpec(cell->getPort("\\CI"), timestep);
				std::vector<int> undef_bi = importUndefSigSpec(cell->getPort("\\BI"), timestep);

				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				std::vector<int> undef_x = importUndefSigSpec(cell->getPort("\\X"), timestep);
				std::vector<int> undef_co = importUndefSigSpec(cell->getPort("\\CO"), timestep);

				extendSignalWidth(undef_a, undef_b, undef_y, cell);
				extendSignalWidth(undef_a, undef_b, undef_x, cell);
				extendSignalWidth(undef_a, undef_b, undef_co, cell);

				std::vector<int> all_inputs_undef;
				all_inputs_undef.insert(all_inputs_undef.end(), undef_a.begin(), undef_a.end());
				all_inputs_undef.insert(all_inputs_undef.end(), undef_b.begin(), undef_b.end());
				all_inputs_undef.insert(all_inputs_undef.end(), undef_ci.begin(), undef_ci.end());
				all_inputs_undef.insert(all_inputs_undef.end(), undef_bi.begin(), undef_bi.end());
				int undef_any = ez->expression(ezSAT::OpOr, all_inputs_undef);

				for (int i = 0; i < GetSize(undef_y); i++) {
					ez->SET(undef_y.at(i), undef_any);
					ez->SET(undef_x.at(i), ez->OR(undef_a.at(i), undef_b.at(i), undef_bi.at(0)));
					ez->SET(undef_co.at(i), undef_any);
				}

				undefGating(y, def_y, undef_y);
				undefGating(x, def_x, undef_x);
				undefGating(co, def_co, undef_co);
			}
			return true;
		}

		if (cell->type == "$slice")
		{
			RTLIL::SigSpec a = cell->getPort("\\A");
			RTLIL::SigSpec y = cell->getPort("\\Y");
			ez->assume(signals_eq(a.extract(cell->parameters.at("\\OFFSET").as_int(), y.size()), y, timestep));
			return true;
		}

		if (cell->type == "$concat")
		{
			RTLIL::SigSpec a = cell->getPort("\\A");
			RTLIL::SigSpec b = cell->getPort("\\B");
			RTLIL::SigSpec y = cell->getPort("\\Y");

			RTLIL::SigSpec ab = a;
			ab.append(b);

			ez->assume(signals_eq(ab, y, timestep));
			return true;
		}

		if (timestep > 0 && cell->type.in("$ff", "$dff", "$_FF_", "$_DFF_N_", "$_DFF_P_"))
		{
			if (timestep == 1)
			{
				initial_state.add((*sigmap)(cell->getPort("\\Q")));
			}
			else
			{
				std::vector<int> d = importDefSigSpec(cell->getPort("\\D"), timestep-1);
				std::vector<int> q = importDefSigSpec(cell->getPort("\\Q"), timestep);

				std::vector<int> qq = model_undef ? ez->vec_var(q.size()) : q;
				ez->assume(ez->vec_eq(d, qq));

				if (model_undef)
				{
					std::vector<int> undef_d = importUndefSigSpec(cell->getPort("\\D"), timestep-1);
					std::vector<int> undef_q = importUndefSigSpec(cell->getPort("\\Q"), timestep);

					ez->assume(ez->vec_eq(undef_d, undef_q));
					undefGating(q, qq, undef_q);
				}
			}
			return true;
		}

		if (cell->type == "$anyconst")
		{
			if (timestep < 2)
				return true;

			std::vector<int> d = importDefSigSpec(cell->getPort("\\Y"), timestep-1);
			std::vector<int> q = importDefSigSpec(cell->getPort("\\Y"), timestep);

			std::vector<int> qq = model_undef ? ez->vec_var(q.size()) : q;
			ez->assume(ez->vec_eq(d, qq));

			if (model_undef)
			{
				std::vector<int> undef_d = importUndefSigSpec(cell->getPort("\\Y"), timestep-1);
				std::vector<int> undef_q = importUndefSigSpec(cell->getPort("\\Y"), timestep);

				ez->assume(ez->vec_eq(undef_d, undef_q));
				undefGating(q, qq, undef_q);
			}
			return true;
		}

		if (cell->type == "$anyseq")
		{
			return true;
		}

		if (cell->type == "$_BUF_" || cell->type == "$equiv")
		{
			std::vector<int> a = importDefSigSpec(cell->getPort("\\A"), timestep);
			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			extendSignalWidthUnary(a, y, cell);

			std::vector<int> yy = model_undef ? ez->vec_var(y.size()) : y;
			ez->assume(ez->vec_eq(a, yy));

			if (model_undef) {
				std::vector<int> undef_a = importUndefSigSpec(cell->getPort("\\A"), timestep);
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				extendSignalWidthUnary(undef_a, undef_y, cell, false);
				ez->assume(ez->vec_eq(undef_a, undef_y));
				undefGating(y, yy, undef_y);
			}
			return true;
		}

		if (cell->type == "$initstate")
		{
			auto key = make_pair(prefix, timestep);
			if (initstates.count(key) == 0)
				initstates[key] = false;

			std::vector<int> y = importDefSigSpec(cell->getPort("\\Y"), timestep);
			log_assert(GetSize(y) == 1);
			ez->SET(y[0], initstates[key] ? ez->CONST_TRUE : ez->CONST_FALSE);

			if (model_undef) {
				std::vector<int> undef_y = importUndefSigSpec(cell->getPort("\\Y"), timestep);
				log_assert(GetSize(undef_y) == 1);
				ez->SET(undef_y[0], ez->CONST_FALSE);
			}

			return true;
		}

		if (cell->type == "$assert")
		{
			std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
			asserts_a[pf].append((*sigmap)(cell->getPort("\\A")));
			asserts_en[pf].append((*sigmap)(cell->getPort("\\EN")));
			return true;
		}

		if (cell->type == "$assume")
		{
			std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
			assumes_a[pf].append((*sigmap)(cell->getPort("\\A")));
			assumes_en[pf].append((*sigmap)(cell->getPort("\\EN")));
			return true;
		}

		// Unsupported internal cell types: $pow $lut
		// .. and all sequential cells except $dff and $_DFF_[NP]_
		return false;
	}
};

YOSYS_NAMESPACE_END

#endif
