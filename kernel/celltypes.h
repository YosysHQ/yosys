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

#ifndef CELLTYPES_H
#define CELLTYPES_H

#include <set>
#include <string>
#include <stdlib.h>

#include <kernel/rtlil.h>
#include <kernel/log.h>

struct CellTypes
{
	std::set<RTLIL::IdString> cell_types;
	std::vector<const RTLIL::Design*> designs;

	CellTypes()
	{
	}

	CellTypes(const RTLIL::Design *design)
	{
		setup(design);
	}

	void setup(const RTLIL::Design *design = NULL)
	{
		if (design)
			setup_design(design);
		setup_internals();
		setup_internals_mem();
		setup_stdcells();
		setup_stdcells_mem();
	}

	void setup_design(const RTLIL::Design *design)
	{
		designs.push_back(design);
	}

	void setup_internals()
	{
		cell_types.insert("$not");
		cell_types.insert("$pos");
		cell_types.insert("$bu0");
		cell_types.insert("$neg");
		cell_types.insert("$and");
		cell_types.insert("$or");
		cell_types.insert("$xor");
		cell_types.insert("$xnor");
		cell_types.insert("$reduce_and");
		cell_types.insert("$reduce_or");
		cell_types.insert("$reduce_xor");
		cell_types.insert("$reduce_xnor");
		cell_types.insert("$reduce_bool");
		cell_types.insert("$shl");
		cell_types.insert("$shr");
		cell_types.insert("$sshl");
		cell_types.insert("$sshr");
		cell_types.insert("$shift");
		cell_types.insert("$shiftx");
		cell_types.insert("$lt");
		cell_types.insert("$le");
		cell_types.insert("$eq");
		cell_types.insert("$ne");
		cell_types.insert("$eqx");
		cell_types.insert("$nex");
		cell_types.insert("$ge");
		cell_types.insert("$gt");
		cell_types.insert("$add");
		cell_types.insert("$sub");
		cell_types.insert("$mul");
		cell_types.insert("$div");
		cell_types.insert("$mod");
		cell_types.insert("$pow");
		cell_types.insert("$logic_not");
		cell_types.insert("$logic_and");
		cell_types.insert("$logic_or");
		cell_types.insert("$mux");
		cell_types.insert("$pmux");
		cell_types.insert("$slice");
		cell_types.insert("$concat");
		cell_types.insert("$safe_pmux");
		cell_types.insert("$lut");
		cell_types.insert("$assert");
	}

	void setup_internals_mem()
	{
		cell_types.insert("$sr");
		cell_types.insert("$dff");
		cell_types.insert("$dffsr");
		cell_types.insert("$adff");
		cell_types.insert("$dlatch");
		cell_types.insert("$dlatchsr");
		cell_types.insert("$memrd");
		cell_types.insert("$memwr");
		cell_types.insert("$mem");
		cell_types.insert("$fsm");
	}

	void setup_stdcells()
	{
		cell_types.insert("$_INV_");
		cell_types.insert("$_AND_");
		cell_types.insert("$_OR_");
		cell_types.insert("$_XOR_");
		cell_types.insert("$_MUX_");
	}

	void setup_stdcells_mem()
	{
		cell_types.insert("$_SR_NN_");
		cell_types.insert("$_SR_NP_");
		cell_types.insert("$_SR_PN_");
		cell_types.insert("$_SR_PP_");
		cell_types.insert("$_DFF_N_");
		cell_types.insert("$_DFF_P_");
		cell_types.insert("$_DFF_NN0_");
		cell_types.insert("$_DFF_NN1_");
		cell_types.insert("$_DFF_NP0_");
		cell_types.insert("$_DFF_NP1_");
		cell_types.insert("$_DFF_PN0_");
		cell_types.insert("$_DFF_PN1_");
		cell_types.insert("$_DFF_PP0_");
		cell_types.insert("$_DFF_PP1_");
		cell_types.insert("$_DFFSR_NNN_");
		cell_types.insert("$_DFFSR_NNP_");
		cell_types.insert("$_DFFSR_NPN_");
		cell_types.insert("$_DFFSR_NPP_");
		cell_types.insert("$_DFFSR_PNN_");
		cell_types.insert("$_DFFSR_PNP_");
		cell_types.insert("$_DFFSR_PPN_");
		cell_types.insert("$_DFFSR_PPP_");
		cell_types.insert("$_DLATCH_N_");
		cell_types.insert("$_DLATCH_P_");
		cell_types.insert("$_DLATCHSR_NNN_");
		cell_types.insert("$_DLATCHSR_NNP_");
		cell_types.insert("$_DLATCHSR_NPN_");
		cell_types.insert("$_DLATCHSR_NPP_");
		cell_types.insert("$_DLATCHSR_PNN_");
		cell_types.insert("$_DLATCHSR_PNP_");
		cell_types.insert("$_DLATCHSR_PPN_");
		cell_types.insert("$_DLATCHSR_PPP_");
	}

	void clear()
	{
		cell_types.clear();
		designs.clear();
	}

	bool cell_known(RTLIL::IdString type)
	{
		if (cell_types.count(type) > 0)
			return true;
		for (auto design : designs)
			if (design->modules_.count(type) > 0)
				return true;
		return false;
	}

	bool cell_output(RTLIL::IdString type, RTLIL::IdString port)
	{
		if (cell_types.count(type) == 0) {
			for (auto design : designs)
				if (design->modules_.count(type) > 0) {
					if (design->modules_.at(type)->wires_.count(port))
						return design->modules_.at(type)->wires_.at(port)->port_output;
					return false;
				}
			return false;
		}

		if (port == "\\Y" || port == "\\Q" || port == "\\RD_DATA")
			return true;
		if (type == "$memrd" && port == "\\DATA")
			return true;
		if (type == "$fsm" && port == "\\CTRL_OUT")
			return true;
		if (type == "$lut" && port == "\\O")
			return true;
		return false;
	}

	bool cell_input(RTLIL::IdString type, RTLIL::IdString port)
	{
		if (cell_types.count(type) == 0) {
			for (auto design : designs)
				if (design->modules_.count(type) > 0) {
					if (design->modules_.at(type)->wires_.count(port))
						return design->modules_.at(type)->wires_.at(port)->port_input;
					return false;
				}
			return false;
		}

		if (cell_types.count(type) > 0)
			return !cell_output(type, port);

		return false;
	}

	static RTLIL::Const eval(RTLIL::IdString type, const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
	{
		if (type == "$sshr" && !signed1)
			type = "$shr";
		if (type == "$sshl" && !signed1)
			type = "$shl";

		if (type != "$sshr" && type != "$sshl" && type != "$shr" && type != "$shl" && type != "$shift" && type != "$shiftx" &&
				type != "$pos" && type != "$neg" && type != "$not" && type != "$bu0") {
			if (!signed1 || !signed2)
				signed1 = false, signed2 = false;
		}

#define HANDLE_CELL_TYPE(_t) if (type == "$" #_t) return const_ ## _t(arg1, arg2, signed1, signed2, result_len);
		HANDLE_CELL_TYPE(not)
		HANDLE_CELL_TYPE(and)
		HANDLE_CELL_TYPE(or)
		HANDLE_CELL_TYPE(xor)
		HANDLE_CELL_TYPE(xnor)
		HANDLE_CELL_TYPE(reduce_and)
		HANDLE_CELL_TYPE(reduce_or)
		HANDLE_CELL_TYPE(reduce_xor)
		HANDLE_CELL_TYPE(reduce_xnor)
		HANDLE_CELL_TYPE(reduce_bool)
		HANDLE_CELL_TYPE(logic_not)
		HANDLE_CELL_TYPE(logic_and)
		HANDLE_CELL_TYPE(logic_or)
		HANDLE_CELL_TYPE(shl)
		HANDLE_CELL_TYPE(shr)
		HANDLE_CELL_TYPE(sshl)
		HANDLE_CELL_TYPE(sshr)
		HANDLE_CELL_TYPE(shift)
		HANDLE_CELL_TYPE(shiftx)
		HANDLE_CELL_TYPE(lt)
		HANDLE_CELL_TYPE(le)
		HANDLE_CELL_TYPE(eq)
		HANDLE_CELL_TYPE(ne)
		HANDLE_CELL_TYPE(eqx)
		HANDLE_CELL_TYPE(nex)
		HANDLE_CELL_TYPE(ge)
		HANDLE_CELL_TYPE(gt)
		HANDLE_CELL_TYPE(add)
		HANDLE_CELL_TYPE(sub)
		HANDLE_CELL_TYPE(mul)
		HANDLE_CELL_TYPE(div)
		HANDLE_CELL_TYPE(mod)
		HANDLE_CELL_TYPE(pow)
		HANDLE_CELL_TYPE(pos)
		HANDLE_CELL_TYPE(bu0)
		HANDLE_CELL_TYPE(neg)
#undef HANDLE_CELL_TYPE

		if (type == "$_INV_")
			return const_not(arg1, arg2, false, false, 1);
		if (type == "$_AND_")
			return const_and(arg1, arg2, false, false, 1);
		if (type == "$_OR_")
			return const_or(arg1, arg2, false, false, 1);
		if (type == "$_XOR_")
			return const_xor(arg1, arg2, false, false, 1);

		log_abort();
	}

	static RTLIL::Const eval(RTLIL::Cell *cell, const RTLIL::Const &arg1, const RTLIL::Const &arg2)
	{
		if (cell->type == "$slice") {
			RTLIL::Const ret;
			int width = cell->parameters.at("\\Y_WIDTH").as_int();
			int offset = cell->parameters.at("\\OFFSET").as_int();
			ret.bits.insert(ret.bits.end(), arg1.bits.begin()+offset, arg1.bits.begin()+offset+width);
			return ret;
		}

		if (cell->type == "$concat") {
			RTLIL::Const ret = arg1;
			ret.bits.insert(ret.bits.end(), arg2.bits.begin(), arg2.bits.end());
			return ret;
		}

		bool signed_a = cell->parameters.count("\\A_SIGNED") > 0 && cell->parameters["\\A_SIGNED"].as_bool();
		bool signed_b = cell->parameters.count("\\B_SIGNED") > 0 && cell->parameters["\\B_SIGNED"].as_bool();
		int result_len = cell->parameters.count("\\Y_WIDTH") > 0 ? cell->parameters["\\Y_WIDTH"].as_int() : -1;
		return eval(cell->type, arg1, arg2, signed_a, signed_b, result_len);
	}

	static RTLIL::Const eval(RTLIL::Cell *cell, const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &sel)
	{
		if (cell->type == "$mux" || cell->type == "$pmux" || cell->type == "$safe_pmux" || cell->type == "$_MUX_") {
			RTLIL::Const ret = arg1;
			for (size_t i = 0; i < sel.bits.size(); i++)
				if (sel.bits[i] == RTLIL::State::S1) {
					std::vector<RTLIL::State> bits(arg2.bits.begin() + i*arg1.bits.size(), arg2.bits.begin() + (i+1)*arg1.bits.size());
					ret = RTLIL::Const(bits);
				}
			return ret;
		}

		log_assert(sel.bits.size() == 0);
		return eval(cell, arg1, arg2);
	}
};

#endif

