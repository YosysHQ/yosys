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

#ifndef CELLTYPES_H
#define CELLTYPES_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct CellType
{
	RTLIL::IdString type;
	pool<RTLIL::IdString> inputs, outputs;
	// Cell is defined in celltypes.h, as opposed to design-specific
	bool is_internal;
	// Cell can be handled by CellTypes::eval()
	bool is_evaluable = false;
	// Cell has no state; outputs are determined solely by inputs
	bool is_combinatorial = false;
	// Cell is able to be synthesized
	bool is_synthesizable = false;
	// Cell is built-in memory logic, includes flip-flops and latches, but not complex
	// cells like $mem
	bool is_builtin_ff = false;
	// Cell is non-synthesizable, but used for formal verification
	bool is_formal = false;
	// Cell is intended for internal Yosys use, containing informational metadata and
	// shouldn't be automatically cleaned; currently only used for $scopeinfo
	bool is_metainfo = false;
	// Non-synthesizable cell with effects that mean it shouldn't be automatically
	// cleaned, e.g. $print
	bool has_effects = false;
};

struct CellTypes
{
	dict<RTLIL::IdString, CellType> cell_types;

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
		setup_internals_anyinit();
		setup_stdcells();
		setup_stdcells_mem();
	}

	void setup_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs)
	{
		CellType ct = { type, inputs, outputs, false };
		cell_types[ct.type] = ct;
	}

	// Setup internal cell type with no other default properties
	void setup_internal_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs,
			bool is_combinatorial = false, bool is_evaluable = false,
			bool is_synthesizable = false, bool is_builtin_ff = false, bool is_formal = false,
			bool is_metainfo = false, bool has_effects = false)
	{
		CellType ct = {
			type, inputs, outputs, true,
			is_evaluable, is_combinatorial,
			is_synthesizable, is_builtin_ff, is_formal,
			is_metainfo, has_effects,
		};
		cell_types[ct.type] = ct;
	}

	// Setup combinatorial cell type which is synthesizable and evaluable (by default)
	void setup_comb_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs,
			bool is_evaluable = true)
	{
		setup_internal_type(type, inputs, outputs, true, is_evaluable, true);
	}

	// Setup builtin ff cell type which is synthesizable
	void setup_ff_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs)
	{
		setup_internal_type(type, inputs, outputs, false, false, true, true);
	}

	// Setup formal cell type which may be combinatorial, and may have effects
	void setup_formal_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs,
			bool is_combinatorial = false)
	{
		setup_internal_type(type, inputs, outputs, is_combinatorial, false, false, false, true);
	}

	// Setup cell type which has effects, and may be formal
	void setup_effects_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs,
			bool is_formal = false)
	{
		setup_internal_type(type, inputs, outputs, false, false, false, false, is_formal, false, true);
	}

	// Setup meta-info cell type
	void setup_metainfo_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs)
	{
		setup_internal_type(type, inputs, outputs, false, false, false, false, false, true);
	}

	void setup_module(RTLIL::Module *module)
	{
		pool<RTLIL::IdString> inputs, outputs;
		for (RTLIL::IdString wire_name : module->ports) {
			RTLIL::Wire *wire = module->wire(wire_name);
			if (wire->port_input)
				inputs.insert(wire->name);
			if (wire->port_output)
				outputs.insert(wire->name);
		}
		setup_type(module->name, inputs, outputs);
	}

	void setup_design(RTLIL::Design *design)
	{
		for (auto module : design->modules())
			setup_module(module);
	}

	void setup_internals()
	{
		setup_internals_eval();

		// synthesizable
		setup_comb_type(ID($tribuf), {ID::A, ID::EN}, {ID::Y}, false);

		// combinatorial formal
		setup_formal_type(ID($assert), {ID::A, ID::EN}, pool<RTLIL::IdString>(), true);
		setup_formal_type(ID($assume), {ID::A, ID::EN}, pool<RTLIL::IdString>(), true);
		setup_formal_type(ID($live), {ID::A, ID::EN}, pool<RTLIL::IdString>(), true);
		setup_formal_type(ID($fair), {ID::A, ID::EN}, pool<RTLIL::IdString>(), true);
		setup_formal_type(ID($cover), {ID::A, ID::EN}, pool<RTLIL::IdString>(), true);
		setup_formal_type(ID($initstate), pool<RTLIL::IdString>(), {ID::Y}, true);
		setup_formal_type(ID($anyconst), pool<RTLIL::IdString>(), {ID::Y}, true);
		setup_formal_type(ID($anyseq), pool<RTLIL::IdString>(), {ID::Y}, true);
		setup_formal_type(ID($allconst), pool<RTLIL::IdString>(), {ID::Y}, true);
		setup_formal_type(ID($allseq), pool<RTLIL::IdString>(), {ID::Y}, true);
		setup_formal_type(ID($equiv), {ID::A, ID::B}, {ID::Y}, true);

		// combinatorial non-synthesizable
		setup_internal_type(ID($specify2), {ID::EN, ID::SRC, ID::DST}, pool<RTLIL::IdString>(), true);
		setup_internal_type(ID($specify3), {ID::EN, ID::SRC, ID::DST, ID::DAT}, pool<RTLIL::IdString>(), true);
		setup_internal_type(ID($specrule), {ID::EN_SRC, ID::EN_DST, ID::SRC, ID::DST}, pool<RTLIL::IdString>(), true);

		// non-combinatorial formal
		setup_formal_type(ID($set_tag), {ID::A, ID::SET, ID::CLR}, {ID::Y});
		setup_formal_type(ID($get_tag), {ID::A}, {ID::Y});
		setup_formal_type(ID($overwrite_tag), {ID::A, ID::SET, ID::CLR}, pool<RTLIL::IdString>());
		setup_formal_type(ID($original_tag), {ID::A}, {ID::Y});
		setup_formal_type(ID($future_ff), {ID::A}, {ID::Y});

		// has effects
		setup_effects_type(ID($print), {ID::EN, ID::ARGS, ID::TRG}, pool<RTLIL::IdString>());
		setup_effects_type(ID($check), {ID::A, ID::EN, ID::ARGS, ID::TRG}, pool<RTLIL::IdString>(), true);

		// meta-info
		setup_metainfo_type(ID($scopeinfo), {}, {});
	}

	void setup_internals_eval()
	{
		std::vector<RTLIL::IdString> unary_ops = {
			ID($not), ID($pos), ID($buf), ID($neg),
			ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
			ID($logic_not), ID($slice), ID($lut), ID($sop)
		};

		std::vector<RTLIL::IdString> binary_ops = {
			ID($and), ID($or), ID($xor), ID($xnor),
			ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx),
			ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt),
			ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($pow),
			ID($logic_and), ID($logic_or), ID($concat), ID($macc),
			ID($bweqx)
		};

		for (auto type : unary_ops)
			setup_comb_type(type, {ID::A}, {ID::Y});

		for (auto type : binary_ops)
			setup_comb_type(type, {ID::A, ID::B}, {ID::Y});

		for (auto type : std::vector<RTLIL::IdString>({ID($mux), ID($pmux), ID($bwmux)}))
			setup_comb_type(type, {ID::A, ID::B, ID::S}, {ID::Y});

		for (auto type : std::vector<RTLIL::IdString>({ID($bmux), ID($demux)}))
			setup_comb_type(type, {ID::A, ID::S}, {ID::Y});

		setup_comb_type(ID($lcu), {ID::P, ID::G, ID::CI}, {ID::CO});
		setup_comb_type(ID($alu), {ID::A, ID::B, ID::CI, ID::BI}, {ID::X, ID::Y, ID::CO});
		setup_comb_type(ID($fa), {ID::A, ID::B, ID::C}, {ID::X, ID::Y});
	}

	void setup_internals_ff()
	{
		setup_ff_type(ID($sr), {ID::SET, ID::CLR}, {ID::Q});
		setup_ff_type(ID($ff), {ID::D}, {ID::Q});
		setup_ff_type(ID($dff), {ID::CLK, ID::D}, {ID::Q});
		setup_ff_type(ID($dffe), {ID::CLK, ID::EN, ID::D}, {ID::Q});
		setup_ff_type(ID($dffsr), {ID::CLK, ID::SET, ID::CLR, ID::D}, {ID::Q});
		setup_ff_type(ID($dffsre), {ID::CLK, ID::SET, ID::CLR, ID::D, ID::EN}, {ID::Q});
		setup_ff_type(ID($adff), {ID::CLK, ID::ARST, ID::D}, {ID::Q});
		setup_ff_type(ID($adffe), {ID::CLK, ID::ARST, ID::D, ID::EN}, {ID::Q});
		setup_ff_type(ID($aldff), {ID::CLK, ID::ALOAD, ID::AD, ID::D}, {ID::Q});
		setup_ff_type(ID($aldffe), {ID::CLK, ID::ALOAD, ID::AD, ID::D, ID::EN}, {ID::Q});
		setup_ff_type(ID($sdff), {ID::CLK, ID::SRST, ID::D}, {ID::Q});
		setup_ff_type(ID($sdffe), {ID::CLK, ID::SRST, ID::D, ID::EN}, {ID::Q});
		setup_ff_type(ID($sdffce), {ID::CLK, ID::SRST, ID::D, ID::EN}, {ID::Q});
		setup_ff_type(ID($dlatch), {ID::EN, ID::D}, {ID::Q});
		setup_ff_type(ID($adlatch), {ID::EN, ID::D, ID::ARST}, {ID::Q});
		setup_ff_type(ID($dlatchsr), {ID::EN, ID::SET, ID::CLR, ID::D}, {ID::Q});
	}

	void setup_internals_anyinit()
	{
		setup_formal_type(ID($anyinit), {ID::D}, {ID::Q});
	}

	void setup_internals_mem()
	{
		setup_internals_ff();

		setup_internal_type(ID($memrd), {ID::CLK, ID::EN, ID::ADDR}, {ID::DATA});
		setup_internal_type(ID($memrd_v2), {ID::CLK, ID::EN, ID::ARST, ID::SRST, ID::ADDR}, {ID::DATA});
		setup_internal_type(ID($memwr), {ID::CLK, ID::EN, ID::ADDR, ID::DATA}, pool<RTLIL::IdString>());
		setup_internal_type(ID($memwr_v2), {ID::CLK, ID::EN, ID::ADDR, ID::DATA}, pool<RTLIL::IdString>());
		setup_internal_type(ID($meminit), {ID::ADDR, ID::DATA}, pool<RTLIL::IdString>());
		setup_internal_type(ID($meminit_v2), {ID::ADDR, ID::DATA, ID::EN}, pool<RTLIL::IdString>());
		setup_internal_type(ID($mem), {ID::RD_CLK, ID::RD_EN, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA});
		setup_internal_type(ID($mem_v2), {ID::RD_CLK, ID::RD_EN, ID::RD_ARST, ID::RD_SRST, ID::RD_ADDR, ID::WR_CLK, ID::WR_EN, ID::WR_ADDR, ID::WR_DATA}, {ID::RD_DATA});

		setup_internal_type(ID($fsm), {ID::CLK, ID::ARST, ID::CTRL_IN}, {ID::CTRL_OUT});
	}

	void setup_stdcells()
	{
		setup_stdcells_eval();

		setup_comb_type(ID($_TBUF_), {ID::A, ID::E}, {ID::Y}, false);
	}

	void setup_stdcells_eval()
	{
		setup_comb_type(ID($_BUF_), {ID::A}, {ID::Y});
		setup_comb_type(ID($_NOT_), {ID::A}, {ID::Y});
		setup_comb_type(ID($_AND_), {ID::A, ID::B}, {ID::Y});
		setup_comb_type(ID($_NAND_), {ID::A, ID::B}, {ID::Y});
		setup_comb_type(ID($_OR_),  {ID::A, ID::B}, {ID::Y});
		setup_comb_type(ID($_NOR_),  {ID::A, ID::B}, {ID::Y});
		setup_comb_type(ID($_XOR_), {ID::A, ID::B}, {ID::Y});
		setup_comb_type(ID($_XNOR_), {ID::A, ID::B}, {ID::Y});
		setup_comb_type(ID($_ANDNOT_), {ID::A, ID::B}, {ID::Y});
		setup_comb_type(ID($_ORNOT_), {ID::A, ID::B}, {ID::Y});
		setup_comb_type(ID($_MUX_), {ID::A, ID::B, ID::S}, {ID::Y});
		setup_comb_type(ID($_NMUX_), {ID::A, ID::B, ID::S}, {ID::Y});
		setup_comb_type(ID($_MUX4_), {ID::A, ID::B, ID::C, ID::D, ID::S, ID::T}, {ID::Y});
		setup_comb_type(ID($_MUX8_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::S, ID::T, ID::U}, {ID::Y});
		setup_comb_type(ID($_MUX16_), {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::I, ID::J, ID::K, ID::L, ID::M, ID::N, ID::O, ID::P, ID::S, ID::T, ID::U, ID::V}, {ID::Y});
		setup_comb_type(ID($_AOI3_), {ID::A, ID::B, ID::C}, {ID::Y});
		setup_comb_type(ID($_OAI3_), {ID::A, ID::B, ID::C}, {ID::Y});
		setup_comb_type(ID($_AOI4_), {ID::A, ID::B, ID::C, ID::D}, {ID::Y});
		setup_comb_type(ID($_OAI4_), {ID::A, ID::B, ID::C, ID::D}, {ID::Y});
	}

	void setup_stdcells_mem()
	{
		std::vector<char> list_np = {'N', 'P'}, list_01 = {'0', '1'};

		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_ff_type(stringf("$_SR_%c%c_", c1, c2), {ID::S, ID::R}, {ID::Q});

		setup_ff_type(ID($_FF_), {ID::D}, {ID::Q});

		for (auto c1 : list_np)
			setup_ff_type(stringf("$_DFF_%c_", c1), {ID::C, ID::D}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_ff_type(stringf("$_DFFE_%c%c_", c1, c2), {ID::C, ID::D, ID::E}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
			setup_ff_type(stringf("$_DFF_%c%c%c_", c1, c2, c3), {ID::C, ID::R, ID::D}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
		for (auto c4 : list_np)
			setup_ff_type(stringf("$_DFFE_%c%c%c%c_", c1, c2, c3, c4), {ID::C, ID::R, ID::D, ID::E}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_ff_type(stringf("$_ALDFF_%c%c_", c1, c2), {ID::C, ID::L, ID::AD, ID::D}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_ff_type(stringf("$_ALDFFE_%c%c%c_", c1, c2, c3), {ID::C, ID::L, ID::AD, ID::D, ID::E}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_ff_type(stringf("$_DFFSR_%c%c%c_", c1, c2, c3), {ID::C, ID::S, ID::R, ID::D}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
		for (auto c4 : list_np)
			setup_ff_type(stringf("$_DFFSRE_%c%c%c%c_", c1, c2, c3, c4), {ID::C, ID::S, ID::R, ID::D, ID::E}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
			setup_ff_type(stringf("$_SDFF_%c%c%c_", c1, c2, c3), {ID::C, ID::R, ID::D}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
		for (auto c4 : list_np)
			setup_ff_type(stringf("$_SDFFE_%c%c%c%c_", c1, c2, c3, c4), {ID::C, ID::R, ID::D, ID::E}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
		for (auto c4 : list_np)
			setup_ff_type(stringf("$_SDFFCE_%c%c%c%c_", c1, c2, c3, c4), {ID::C, ID::R, ID::D, ID::E}, {ID::Q});

		for (auto c1 : list_np)
			setup_ff_type(stringf("$_DLATCH_%c_", c1), {ID::E, ID::D}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
			setup_ff_type(stringf("$_DLATCH_%c%c%c_", c1, c2, c3), {ID::E, ID::R, ID::D}, {ID::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_ff_type(stringf("$_DLATCHSR_%c%c%c_", c1, c2, c3), {ID::E, ID::S, ID::R, ID::D}, {ID::Q});
	}

	void clear()
	{
		cell_types.clear();
	}

	const CellType* get_cell(RTLIL::IdString type) const
	{
		auto it = cell_types.find(type);
		if (it == cell_types.end())
			return nullptr;
		else
			return &(it->second);
	}

	bool cell_known(RTLIL::IdString type) const
	{
		return cell_types.count(type) != 0;
	}

	bool cell_output(RTLIL::IdString type, RTLIL::IdString port) const
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.outputs.count(port) != 0;
	}

	bool cell_input(RTLIL::IdString type, RTLIL::IdString port) const
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.inputs.count(port) != 0;
	}

	bool cell_evaluable(RTLIL::IdString type) const
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.is_evaluable;
	}

	static RTLIL::Const eval_not(RTLIL::Const v)
	{
		for (auto &bit : v.bits())
			if (bit == State::S0) bit = State::S1;
			else if (bit == State::S1) bit = State::S0;
		return v;
	}

	static RTLIL::Const eval(RTLIL::IdString type, const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len, bool *errp = nullptr)
	{
		if (type == ID($sshr) && !signed1)
			type = ID($shr);
		if (type == ID($sshl) && !signed1)
			type = ID($shl);

		if (type != ID($sshr) && type != ID($sshl) && type != ID($shr) && type != ID($shl) && type != ID($shift) && type != ID($shiftx) &&
				type != ID($pos) && type != ID($buf) && type != ID($neg) && type != ID($not)) {
			if (!signed1 || !signed2)
				signed1 = false, signed2 = false;
		}

#define HANDLE_CELL_TYPE(_t) if (type == ID($##_t)) return const_ ## _t(arg1, arg2, signed1, signed2, result_len);
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
		HANDLE_CELL_TYPE(divfloor)
		HANDLE_CELL_TYPE(modfloor)
		HANDLE_CELL_TYPE(pow)
		HANDLE_CELL_TYPE(pos)
		HANDLE_CELL_TYPE(neg)
#undef HANDLE_CELL_TYPE

		if (type.in(ID($_BUF_), ID($buf)))
			return arg1;
		if (type == ID($_NOT_))
			return eval_not(arg1);
		if (type == ID($_AND_))
			return const_and(arg1, arg2, false, false, 1);
		if (type == ID($_NAND_))
			return eval_not(const_and(arg1, arg2, false, false, 1));
		if (type == ID($_OR_))
			return const_or(arg1, arg2, false, false, 1);
		if (type == ID($_NOR_))
			return eval_not(const_or(arg1, arg2, false, false, 1));
		if (type == ID($_XOR_))
			return const_xor(arg1, arg2, false, false, 1);
		if (type == ID($_XNOR_))
			return const_xnor(arg1, arg2, false, false, 1);
		if (type == ID($_ANDNOT_))
			return const_and(arg1, eval_not(arg2), false, false, 1);
		if (type == ID($_ORNOT_))
			return const_or(arg1, eval_not(arg2), false, false, 1);

		if (errp != nullptr) {
			*errp = true;
			return State::Sm;
		}

		log_abort();
	}

	static RTLIL::Const eval(RTLIL::Cell *cell, const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool *errp = nullptr)
	{
		if (cell->type == ID($slice)) {
			RTLIL::Const ret;
			int width = cell->parameters.at(ID::Y_WIDTH).as_int();
			int offset = cell->parameters.at(ID::OFFSET).as_int();
			ret.bits().insert(ret.bits().end(), arg1.begin()+offset, arg1.begin()+offset+width);
			return ret;
		}

		if (cell->type == ID($concat)) {
			RTLIL::Const ret = arg1;
			ret.bits().insert(ret.bits().end(), arg2.begin(), arg2.end());
			return ret;
		}

		if (cell->type == ID($bmux))
		{
			return const_bmux(arg1, arg2);
		}

		if (cell->type == ID($demux))
		{
			return const_demux(arg1, arg2);
		}

		if (cell->type == ID($bweqx))
		{
			return const_bweqx(arg1, arg2);
		}

		if (cell->type == ID($lut))
		{
			int width = cell->parameters.at(ID::WIDTH).as_int();

			std::vector<RTLIL::State> t = cell->parameters.at(ID::LUT).to_bits();
			while (GetSize(t) < (1 << width))
				t.push_back(State::S0);
			t.resize(1 << width);

			return const_bmux(t, arg1);
		}

		if (cell->type == ID($sop))
		{
			int width = cell->parameters.at(ID::WIDTH).as_int();
			int depth = cell->parameters.at(ID::DEPTH).as_int();
			std::vector<RTLIL::State> t = cell->parameters.at(ID::TABLE).to_bits();

			while (GetSize(t) < width*depth*2)
				t.push_back(State::S0);

			RTLIL::State default_ret = State::S0;

			for (int i = 0; i < depth; i++)
			{
				bool match = true;
				bool match_x = true;

				for (int j = 0; j < width; j++) {
					RTLIL::State a = arg1.at(j);
					if (t.at(2*width*i + 2*j + 0) == State::S1) {
						if (a == State::S1) match_x = false;
						if (a != State::S0) match = false;
					}
					if (t.at(2*width*i + 2*j + 1) == State::S1) {
						if (a == State::S0) match_x = false;
						if (a != State::S1) match = false;
					}
				}

				if (match)
					return State::S1;

				if (match_x)
					default_ret = State::Sx;
			}

			return default_ret;
		}

		bool signed_a = cell->parameters.count(ID::A_SIGNED) > 0 && cell->parameters[ID::A_SIGNED].as_bool();
		bool signed_b = cell->parameters.count(ID::B_SIGNED) > 0 && cell->parameters[ID::B_SIGNED].as_bool();
		int result_len = cell->parameters.count(ID::Y_WIDTH) > 0 ? cell->parameters[ID::Y_WIDTH].as_int() : -1;
		return eval(cell->type, arg1, arg2, signed_a, signed_b, result_len, errp);
	}

	static RTLIL::Const eval(RTLIL::Cell *cell, const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3, bool *errp = nullptr)
	{
		if (cell->type.in(ID($mux), ID($_MUX_)))
			return const_mux(arg1, arg2, arg3);
		if (cell->type == ID($bwmux))
			return const_bwmux(arg1, arg2, arg3);
		if (cell->type == ID($pmux))
			return const_pmux(arg1, arg2, arg3);
		if (cell->type == ID($_AOI3_))
			return eval_not(const_or(const_and(arg1, arg2, false, false, 1), arg3, false, false, 1));
		if (cell->type == ID($_OAI3_))
			return eval_not(const_and(const_or(arg1, arg2, false, false, 1), arg3, false, false, 1));

		log_assert(arg3.size() == 0);
		return eval(cell, arg1, arg2, errp);
	}

	static RTLIL::Const eval(RTLIL::Cell *cell, const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3, const RTLIL::Const &arg4, bool *errp = nullptr)
	{
		if (cell->type == ID($_AOI4_))
			return eval_not(const_or(const_and(arg1, arg2, false, false, 1), const_and(arg3, arg4, false, false, 1), false, false, 1));
		if (cell->type == ID($_OAI4_))
			return eval_not(const_and(const_or(arg1, arg2, false, false, 1), const_or(arg3, arg4, false, false, 1), false, false, 1));

		log_assert(arg4.size() == 0);
		return eval(cell, arg1, arg2, arg3, errp);
	}
};

// initialized by yosys_setup()
extern CellTypes yosys_celltypes;

YOSYS_NAMESPACE_END

#endif
