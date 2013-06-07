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

	SatGen(ezSAT *ez, RTLIL::Design *design, SigMap *sigmap, std::string prefix = std::string()) :
			ez(ez), design(design), sigmap(sigmap), prefix(prefix)
	{
	}

	void setContext(RTLIL::Design *design, SigMap *sigmap, std::string prefix = std::string())
	{
		this->design = design;
		this->sigmap = sigmap;
		this->prefix = prefix;
	}

	virtual ~SatGen()
	{
	}

	virtual std::vector<int> importSigSpec(RTLIL::SigSpec &sig)
	{
		RTLIL::SigSpec s = sig;
		sigmap->apply(s);
		s.expand();

		std::vector<int> vec;
		vec.reserve(s.chunks.size());

		for (auto &c : s.chunks)
			if (c.wire == NULL)
				vec.push_back(c.data.as_bool() ? ez->TRUE : ez->FALSE);
			else
				vec.push_back(ez->literal(prefix + stringf(c.wire->width == 1 ?
						"%s" : "%s [%d]", RTLIL::id2cstr(c.wire->name), c.offset)));
		return vec;
	}

	// ** cell types to be done: **
	// cell_types.insert("$pos");
	// cell_types.insert("$neg");
	// cell_types.insert("$xnor");
	// cell_types.insert("$reduce_and");
	// cell_types.insert("$reduce_or");
	// cell_types.insert("$reduce_xor");
	// cell_types.insert("$reduce_xnor");
	// cell_types.insert("$reduce_bool");
	// cell_types.insert("$shl");
	// cell_types.insert("$shr");
	// cell_types.insert("$sshl");
	// cell_types.insert("$sshr");
	// cell_types.insert("$mul");
	// cell_types.insert("$div");
	// cell_types.insert("$mod");
	// cell_types.insert("$pow");
	// cell_types.insert("$logic_not");
	// cell_types.insert("$logic_and");
	// cell_types.insert("$logic_or");
	// cell_types.insert("$pmux");
	// cell_types.insert("$safe_pmux");

	void extendSignalWidth(std::vector<int> &vec_a, std::vector<int> &vec_b, RTLIL::Cell *cell)
	{
		bool is_signed_a = false, is_signed_b = false;
		if (cell->parameters.count("\\A_SIGNED") > 0)
			is_signed_a = cell->parameters["\\A_SIGNED"].as_bool();
		if (cell->parameters.count("\\B_SIGNED") > 0)
			is_signed_b = cell->parameters["\\B_SIGNED"].as_bool();
		while (vec_a.size() < vec_b.size())
			vec_a.push_back(is_signed_a && vec_a.size() > 0 ? vec_a.back() : ez->FALSE);
		while (vec_b.size() < vec_a.size())
			vec_b.push_back(is_signed_b && vec_b.size() > 0 ? vec_b.back() : ez->FALSE);
	}

	void extendSignalWidth(std::vector<int> &vec_a, std::vector<int> &vec_b, std::vector<int> &vec_y, RTLIL::Cell *cell)
	{
		extendSignalWidth(vec_a, vec_b, cell);
		while (vec_y.size() < vec_a.size())
			vec_y.push_back(ez->literal());
	}

	virtual void importCell(RTLIL::Cell *cell)
	{
		if (cell->type == "$_AND_" || cell->type == "$_OR_" || cell->type == "$_XOR_" ||
				cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" ||
				cell->type == "$add" || cell->type == "$sub") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"));
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"));
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"));
			extendSignalWidth(a, b, y, cell);
			if (cell->type == "$and" || cell->type == "$_AND_")
				ez->assume(ez->vec_eq(ez->vec_and(a, b), y));
			if (cell->type == "$or" || cell->type == "$_OR_")
				ez->assume(ez->vec_eq(ez->vec_or(a, b), y));
			if (cell->type == "$xor" || cell->type == "$_XOR")
				ez->assume(ez->vec_eq(ez->vec_xor(a, b), y));
			if (cell->type == "$add")
				ez->assume(ez->vec_eq(ez->vec_add(a, b), y));
			if (cell->type == "$sub")
				ez->assume(ez->vec_eq(ez->vec_sub(a, b), y));
		} else
		if (cell->type == "$_INV_" || cell->type == "$not") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"));
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"));
			ez->assume(ez->vec_eq(ez->vec_not(a), y));
		} else
		if (cell->type == "$_MUX_" || cell->type == "$mux") {
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"));
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"));
			std::vector<int> s = importSigSpec(cell->connections.at("\\S"));
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"));
			ez->assume(ez->vec_eq(ez->vec_ite(s, b, a), y));
		} else
		if (cell->type == "$lt" || cell->type == "$le" || cell->type == "$eq" || cell->type == "$ne" || cell->type == "$ge" || cell->type == "$gt") {
			bool is_signed = cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool();
			std::vector<int> a = importSigSpec(cell->connections.at("\\A"));
			std::vector<int> b = importSigSpec(cell->connections.at("\\B"));
			std::vector<int> y = importSigSpec(cell->connections.at("\\Y"));
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
		} else
			log_error("Can't handle cell type %s in SAT generator yet.\n", RTLIL::id2cstr(cell->type));
	}
};

#endif
