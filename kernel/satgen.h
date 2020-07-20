/* -*- c++ -*-
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
		if (!forced_signed && cell->parameters.count(ID::A_SIGNED) > 0 && cell->parameters.count(ID::B_SIGNED) > 0)
			is_signed = cell->parameters[ID::A_SIGNED].as_bool() && cell->parameters[ID::B_SIGNED].as_bool();
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
		bool is_signed = forced_signed || (cell->parameters.count(ID::A_SIGNED) > 0 && cell->parameters[ID::A_SIGNED].as_bool());
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

	std::pair<std::vector<int>, std::vector<int>> mux(int s, int undef_s, const std::vector<int> &a, const std::vector<int> &undef_a, const std::vector<int> &b, const std::vector<int> &undef_b) {
		std::vector<int> res;
		std::vector<int> undef_res;
		res = ez->vec_ite(s, b, a);
		if (model_undef) {
			std::vector<int> unequal_ab = ez->vec_not(ez->vec_iff(a, b));
			std::vector<int> undef_ab = ez->vec_or(unequal_ab, ez->vec_or(undef_a, undef_b));
			undef_res = ez->vec_ite(undef_s, undef_ab, ez->vec_ite(s, undef_b, undef_a));
		}
		return std::make_pair(res, undef_res);
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

	bool importCell(RTLIL::Cell *cell, int timestep = -1);
};

YOSYS_NAMESPACE_END

#endif
