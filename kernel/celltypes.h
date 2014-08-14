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

struct CellType
{
	RTLIL::IdString type;
	std::set<RTLIL::IdString> inputs, outputs;
	bool maybe_has_internal_state;
};

struct CellTypes
{
	std::map<RTLIL::IdString, CellType> cell_types;

	CellTypes()
	{
	}

	CellTypes(RTLIL::Design *design)
	{
		setup(design);
	}

	void setup(RTLIL::Design *design = NULL)
	{
		if (design)
			setup_design(design);

		setup_internals();
		setup_internals_mem();
		setup_stdcells();
		setup_stdcells_mem();
	}

	void setup_type(RTLIL::IdString type, const std::set<RTLIL::IdString> &inputs, const std::set<RTLIL::IdString> &outputs, bool maybe_has_internal_state)
	{
		CellType ct = {type, inputs, outputs, maybe_has_internal_state};
		cell_types[ct.type] = ct;
	}

	void setup_module(RTLIL::Module *module)
	{
		std::set<RTLIL::IdString> inputs, outputs;
		for (auto wire : module->wires()) {
			if (wire->port_input)
				inputs.insert(wire->name);
			if (wire->port_output)
				outputs.insert(wire->name);
		}
		setup_type(module->name, inputs, outputs, true);
	}

	void setup_design(RTLIL::Design *design)
	{
		for (auto module : design->modules())
			setup_module(module);
	}

	void setup_internals()
	{
		std::vector<RTLIL::IdString> unary_ops = {
			"$not", "$pos", "$bu0", "$neg",
			"$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor", "$reduce_bool",
			"$logic_not", "$slice"
		};

		std::vector<RTLIL::IdString> binary_ops = {
			"$and", "$or", "$xor", "$xnor",
			"$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx",
			"$lt", "$le", "$eq", "$ne", "$eqx", "$nex", "$ge", "$gt",
			"$add", "$sub", "$mul", "$div", "$mod", "$pow",
			"$logic_and", "$logic_or", "$concat"
		};

		for (auto type : unary_ops)
			setup_type(type, {"\\A"}, {"\\Y"}, false);

		for (auto type : binary_ops)
			setup_type(type, {"\\A", "\\B"}, {"\\Y"}, false);

		for (auto type : std::vector<RTLIL::IdString>({"$mux", "$pmux"}))
			setup_type(type, {"\\A", "\\B", "\\S"}, {"\\Y"}, false);

		setup_type("$lut", {"\\I"}, {"\\O"}, false);
		setup_type("$assert", {"\\A", "\\EN"}, {}, false);
	}

	void setup_internals_mem()
	{
		setup_type("$sr", {"\\SET", "\\CLR"}, {"\\Q"}, true);
		setup_type("$dff", {"\\CLK", "\\D"}, {"\\Q"}, true);
		setup_type("$dffsr", {"\\CLK", "\\SET", "\\CLR", "\\D"}, {"\\Q"}, true);
		setup_type("$adff", {"\\CLK", "\\ARST", "\\D"}, {"\\Q"}, true);
		setup_type("$dlatch", {"\\EN", "\\D"}, {"\\Q"}, true);
		setup_type("$dlatchsr", {"\\EN", "\\SET", "\\CLR", "\\D"}, {"\\Q"}, true);

		setup_type("$memrd", {"\\CLK", "\\ADDR"}, {"\\DATA"}, true);
		setup_type("$memwr", {"\\CLK", "\\EN", "\\ADDR", "\\DATA"}, {}, true);
		setup_type("$mem", {"\\RD_CLK", "\\RD_ADDR", "\\WR_CLK", "\\WR_EN", "\\WR_ADDR", "\\WR_DATA"}, {"\\RD_DATA"}, true);

		setup_type("$fsm", {"\\CLK", "\\ARST", "\\CTRL_IN"}, {"\\CTRL_OUT"}, true);
	}

	void setup_stdcells()
	{
		setup_type("$_INV_", {"\\A"}, {"\\Y"}, false);
		setup_type("$_AND_", {"\\A", "\\B"}, {"\\Y"}, false);
		setup_type("$_OR_",  {"\\A", "\\B"}, {"\\Y"}, false);
		setup_type("$_XOR_", {"\\A", "\\B"}, {"\\Y"}, false);
		setup_type("$_MUX_", {"\\A", "\\B", "\\S"}, {"\\Y"}, false);
	}

	void setup_stdcells_mem()
	{
		std::vector<char> list_np = {'N', 'P'}, list_01 = {'0', '1'};

		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_type(stringf("$_SR_%c%c_", c1, c2), {"\\S", "\\R"}, {"\\Q"}, true);

		for (auto c1 : list_np)
			setup_type(stringf("$_DFF_%c_", c1), {"\\C", "\\D"}, {"\\Q"}, true);

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
			setup_type(stringf("$_DFF_%c%c%c_", c1, c2, c3), {"\\C", "\\R", "\\D"}, {"\\Q"}, true);

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_type(stringf("$_DFFSR_%c%c%c_", c1, c2, c3), {"\\C", "\\S", "\\R", "\\D"}, {"\\Q"}, true);

		for (auto c1 : list_np)
			setup_type(stringf("$_DLATCH_%c_", c1), {"\\E", "\\D"}, {"\\Q"}, true);

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_type(stringf("$_DLATCHSR_%c%c%c_", c1, c2, c3), {"\\E", "\\S", "\\R", "\\D"}, {"\\Q"}, true);
	}

	void clear()
	{
		cell_types.clear();
	}

	bool cell_known(RTLIL::IdString type)
	{
		return cell_types.count(type) != 0;
	}

	bool cell_output(RTLIL::IdString type, RTLIL::IdString port)
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.outputs.count(port) != 0;
	}

	bool cell_input(RTLIL::IdString type, RTLIL::IdString port)
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.inputs.count(port) != 0;
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
		if (cell->type == "$mux" || cell->type == "$pmux" || cell->type == "$_MUX_") {
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

