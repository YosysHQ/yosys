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
#include "kernel/newcelltypes.h"

YOSYS_NAMESPACE_BEGIN

struct CellType
{
	RTLIL::IdString type;
	pool<TwineRef> inputs, outputs;
	bool is_evaluable;
	bool is_combinatorial;
	bool is_synthesizable;
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

	void setup_type(RTLIL::IdString type, const pool<TwineRef> &inputs, const pool<TwineRef> &outputs, bool is_evaluable = false, bool is_combinatorial = false, bool is_synthesizable = false)
	{
		CellType ct = {type, inputs, outputs, is_evaluable, is_combinatorial, is_synthesizable};
		cell_types[ct.type] = ct;
	}

	void setup_module(RTLIL::Module *module)
	{
		pool<TwineRef> inputs, outputs;
		for (auto wire_name : module->ports) {
			RTLIL::Wire *wire = module->wire(wire_name);
			if (wire->port_input)
				inputs.insert(wire->meta_->name);
			if (wire->port_output)
				outputs.insert(wire->meta_->name);
		}
		setup_type(RTLIL::IdString(module->design->twines.str(module->meta_->name)), inputs, outputs);
	}

	void setup_design(RTLIL::Design *design)
	{
		for (auto module : design->modules())
			setup_module(module);
	}

	void setup_internals()
	{
		setup_internals_eval();

		setup_type(ID($tribuf), {TW::A, TW::EN}, {TW::Y});

		setup_type(ID($assert), {TW::A, TW::EN}, pool<TwineRef>());
		setup_type(ID($assume), {TW::A, TW::EN}, pool<TwineRef>());
		setup_type(ID($live), {TW::A, TW::EN}, pool<TwineRef>());
		setup_type(ID($fair), {TW::A, TW::EN}, pool<TwineRef>());
		setup_type(ID($cover), {TW::A, TW::EN}, pool<TwineRef>());
		setup_type(ID($initstate), pool<TwineRef>(), {TW::Y});
		setup_type(ID($anyconst), pool<TwineRef>(), {TW::Y});
		setup_type(ID($anyseq), pool<TwineRef>(), {TW::Y});
		setup_type(ID($allconst), pool<TwineRef>(), {TW::Y});
		setup_type(ID($allseq), pool<TwineRef>(), {TW::Y});
		setup_type(ID($equiv), {TW::A, TW::B}, {TW::Y});
		setup_type(ID($specify2), {TW::EN, TW::SRC, TW::DST}, pool<TwineRef>());
		setup_type(ID($specify3), {TW::EN, TW::SRC, TW::DST, TW::DAT}, pool<TwineRef>());
		setup_type(ID($specrule), {TW::SRC_EN, TW::DST_EN, TW::SRC, TW::DST}, pool<TwineRef>());
		setup_type(ID($print), {TW::EN, TW::ARGS, TW::TRG}, pool<TwineRef>());
		setup_type(ID($check), {TW::A, TW::EN, TW::ARGS, TW::TRG}, pool<TwineRef>());
		setup_type(ID($set_tag), {TW::A, TW::SET, TW::CLR}, {TW::Y});
		setup_type(ID($get_tag), {TW::A}, {TW::Y});
		setup_type(ID($overwrite_tag), {TW::A, TW::SET, TW::CLR}, pool<TwineRef>());
		setup_type(ID($original_tag), {TW::A}, {TW::Y});
		setup_type(ID($future_ff), {TW::A}, {TW::Y});
		setup_type(ID($scopeinfo), {}, {});
		setup_type(ID($input_port), {}, {TW::Y});
		setup_type(ID($output_port), {TW::A}, {});
		setup_type(ID($public), {TW::A}, {});
		setup_type(ID($connect), {TW::A, TW::B}, {});
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
			setup_type(type, {TW::A}, {TW::Y}, true);

		for (auto type : binary_ops)
			setup_type(type, {TW::A, TW::B}, {TW::Y}, true);

		for (auto type : std::vector<RTLIL::IdString>({ID($mux), ID($pmux), ID($bwmux)}))
			setup_type(type, {TW::A, TW::B, TW::S}, {TW::Y}, true);

		for (auto type : std::vector<RTLIL::IdString>({ID($bmux), ID($demux)}))
			setup_type(type, {TW::A, TW::S}, {TW::Y}, true);

		setup_type(ID($lcu), {TW::P, TW::G, TW::CI}, {TW::CO}, true);
		setup_type(ID($alu), {TW::A, TW::B, TW::CI, TW::BI}, {TW::X, TW::Y, TW::CO}, true);
		setup_type(ID($macc_v2), {TW::A, TW::B, TW::C}, {TW::Y}, true);
		setup_type(ID($fa), {TW::A, TW::B, TW::C}, {TW::X, TW::Y}, true);
	}

	void setup_internals_ff()
	{
		setup_type(ID($sr), {TW::SET, TW::CLR}, {TW::Q});
		setup_type(ID($ff), {TW::D}, {TW::Q});
		setup_type(ID($dff), {TW::CLK, TW::D}, {TW::Q});
		setup_type(ID($dffe), {TW::CLK, TW::EN, TW::D}, {TW::Q});
		setup_type(ID($dffsr), {TW::CLK, TW::SET, TW::CLR, TW::D}, {TW::Q});
		setup_type(ID($dffsre), {TW::CLK, TW::SET, TW::CLR, TW::D, TW::EN}, {TW::Q});
		setup_type(ID($adff), {TW::CLK, TW::ARST, TW::D}, {TW::Q});
		setup_type(ID($adffe), {TW::CLK, TW::ARST, TW::D, TW::EN}, {TW::Q});
		setup_type(ID($aldff), {TW::CLK, TW::ALOAD, TW::AD, TW::D}, {TW::Q});
		setup_type(ID($aldffe), {TW::CLK, TW::ALOAD, TW::AD, TW::D, TW::EN}, {TW::Q});
		setup_type(ID($sdff), {TW::CLK, TW::SRST, TW::D}, {TW::Q});
		setup_type(ID($sdffe), {TW::CLK, TW::SRST, TW::D, TW::EN}, {TW::Q});
		setup_type(ID($sdffce), {TW::CLK, TW::SRST, TW::D, TW::EN}, {TW::Q});
		setup_type(ID($dlatch), {TW::EN, TW::D}, {TW::Q});
		setup_type(ID($adlatch), {TW::EN, TW::D, TW::ARST}, {TW::Q});
		setup_type(ID($dlatchsr), {TW::EN, TW::SET, TW::CLR, TW::D}, {TW::Q});
	}

	void setup_internals_anyinit()
	{
		setup_type(ID($anyinit), {TW::D}, {TW::Q});
	}

	void setup_internals_mem()
	{
		setup_internals_ff();

		setup_type(ID($memrd), {TW::CLK, TW::EN, TW::ADDR}, {TW::DATA});
		setup_type(ID($memrd_v2), {TW::CLK, TW::EN, TW::ARST, TW::SRST, TW::ADDR}, {TW::DATA});
		setup_type(ID($memwr), {TW::CLK, TW::EN, TW::ADDR, TW::DATA}, pool<TwineRef>());
		setup_type(ID($memwr_v2), {TW::CLK, TW::EN, TW::ADDR, TW::DATA}, pool<TwineRef>());
		setup_type(ID($meminit), {TW::ADDR, TW::DATA}, pool<TwineRef>());
		setup_type(ID($meminit_v2), {TW::ADDR, TW::DATA, TW::EN}, pool<TwineRef>());
		setup_type(ID($mem), {TW::RD_CLK, TW::RD_EN, TW::RD_ADDR, TW::WR_CLK, TW::WR_EN, TW::WR_ADDR, TW::WR_DATA}, {TW::RD_DATA});
		setup_type(ID($mem_v2), {TW::RD_CLK, TW::RD_EN, TW::RD_ARST, TW::RD_SRST, TW::RD_ADDR, TW::WR_CLK, TW::WR_EN, TW::WR_ADDR, TW::WR_DATA}, {TW::RD_DATA});

		setup_type(ID($fsm), {TW::CLK, TW::ARST, TW::CTRL_IN}, {TW::CTRL_OUT});
	}

	void setup_stdcells()
	{
		setup_stdcells_eval();

		setup_type(ID($_TBUF_), {TW::A, TW::E}, {TW::Y});
	}

	void setup_stdcells_eval()
	{
		setup_type(ID($_BUF_), {TW::A}, {TW::Y}, true);
		setup_type(ID($_NOT_), {TW::A}, {TW::Y}, true);
		setup_type(ID($_AND_), {TW::A, TW::B}, {TW::Y}, true);
		setup_type(ID($_NAND_), {TW::A, TW::B}, {TW::Y}, true);
		setup_type(ID($_OR_),  {TW::A, TW::B}, {TW::Y}, true);
		setup_type(ID($_NOR_),  {TW::A, TW::B}, {TW::Y}, true);
		setup_type(ID($_XOR_), {TW::A, TW::B}, {TW::Y}, true);
		setup_type(ID($_XNOR_), {TW::A, TW::B}, {TW::Y}, true);
		setup_type(ID($_ANDNOT_), {TW::A, TW::B}, {TW::Y}, true);
		setup_type(ID($_ORNOT_), {TW::A, TW::B}, {TW::Y}, true);
		setup_type(ID($_MUX_), {TW::A, TW::B, TW::S}, {TW::Y}, true);
		setup_type(ID($_NMUX_), {TW::A, TW::B, TW::S}, {TW::Y}, true);
		setup_type(ID($_MUX4_), {TW::A, TW::B, TW::C, TW::D, TW::S, TW::T}, {TW::Y}, true);
		setup_type(ID($_MUX8_), {TW::A, TW::B, TW::C, TW::D, TW::E, TW::F, TW::G, TW::H, TW::S, TW::T, TW::U}, {TW::Y}, true);
		setup_type(ID($_MUX16_), {TW::A, TW::B, TW::C, TW::D, TW::E, TW::F, TW::G, TW::H, TW::I, TW::J, TW::K, TW::L, TW::M, TW::N, TW::O, TW::P, TW::S, TW::T, TW::U, TW::V}, {TW::Y}, true);
		setup_type(ID($_AOI3_), {TW::A, TW::B, TW::C}, {TW::Y}, true);
		setup_type(ID($_OAI3_), {TW::A, TW::B, TW::C}, {TW::Y}, true);
		setup_type(ID($_AOI4_), {TW::A, TW::B, TW::C, TW::D}, {TW::Y}, true);
		setup_type(ID($_OAI4_), {TW::A, TW::B, TW::C, TW::D}, {TW::Y}, true);
	}

	void setup_stdcells_mem()
	{
		std::vector<char> list_np = {'N', 'P'}, list_01 = {'0', '1'};

		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_type(stringf("$_SR_%c%c_", c1, c2), {TW::S, TW::R}, {TW::Q});

		setup_type(ID($_FF_), {TW::D}, {TW::Q});

		for (auto c1 : list_np)
			setup_type(stringf("$_DFF_%c_", c1), {TW::C, TW::D}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_type(stringf("$_DFFE_%c%c_", c1, c2), {TW::C, TW::D, TW::E}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
			setup_type(stringf("$_DFF_%c%c%c_", c1, c2, c3), {TW::C, TW::R, TW::D}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
		for (auto c4 : list_np)
			setup_type(stringf("$_DFFE_%c%c%c%c_", c1, c2, c3, c4), {TW::C, TW::R, TW::D, TW::E}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_type(stringf("$_ALDFF_%c%c_", c1, c2), {TW::C, TW::L, TW::AD, TW::D}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_type(stringf("$_ALDFFE_%c%c%c_", c1, c2, c3), {TW::C, TW::L, TW::AD, TW::D, TW::E}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_type(stringf("$_DFFSR_%c%c%c_", c1, c2, c3), {TW::C, TW::S, TW::R, TW::D}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
		for (auto c4 : list_np)
			setup_type(stringf("$_DFFSRE_%c%c%c%c_", c1, c2, c3, c4), {TW::C, TW::S, TW::R, TW::D, TW::E}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
			setup_type(stringf("$_SDFF_%c%c%c_", c1, c2, c3), {TW::C, TW::R, TW::D}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
		for (auto c4 : list_np)
			setup_type(stringf("$_SDFFE_%c%c%c%c_", c1, c2, c3, c4), {TW::C, TW::R, TW::D, TW::E}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
		for (auto c4 : list_np)
			setup_type(stringf("$_SDFFCE_%c%c%c%c_", c1, c2, c3, c4), {TW::C, TW::R, TW::D, TW::E}, {TW::Q});

		for (auto c1 : list_np)
			setup_type(stringf("$_DLATCH_%c_", c1), {TW::E, TW::D}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
			setup_type(stringf("$_DLATCH_%c%c%c_", c1, c2, c3), {TW::E, TW::R, TW::D}, {TW::Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_type(stringf("$_DLATCHSR_%c%c%c_", c1, c2, c3), {TW::E, TW::S, TW::R, TW::D}, {TW::Q});
	}

	void clear()
	{
		cell_types.clear();
	}

	bool cell_known(RTLIL::IdString type) const
	{
		return cell_types.count(type) != 0;
	}

	bool cell_output(RTLIL::IdString type, TwineRef port) const
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.outputs.count(port) != 0;
	}

	bool cell_input(RTLIL::IdString type, TwineRef port) const
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.inputs.count(port) != 0;
	}

	RTLIL::PortDir cell_port_dir(RTLIL::IdString type, TwineRef port) const
	{
		auto it = cell_types.find(type);
		if (it == cell_types.end())
			return RTLIL::PD_UNKNOWN;
		bool is_input = it->second.inputs.count(port);
		bool is_output = it->second.outputs.count(port);
		return RTLIL::PortDir(is_input + is_output * 2);
	}

	bool cell_evaluable(RTLIL::IdString type) const
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.is_evaluable;
	}

	static RTLIL::Const eval_not(RTLIL::Const v)
	{
		for (auto bit : v)
			if (bit == State::S0) bit = State::S1;
			else if (bit == State::S1) bit = State::S0;
		return v;
	}

	// Consider using the ConstEval struct instead if you need named ports and/or multiple outputs
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

	// Consider using the ConstEval struct instead if you need named ports and/or multiple outputs
	static RTLIL::Const eval(RTLIL::Cell *cell, const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool *errp = nullptr)
	{
		if (cell->type == ID($slice)) {
			int width = cell->parameters.at(ID::Y_WIDTH).as_int();
			int offset = cell->parameters.at(ID::OFFSET).as_int();
			return arg1.extract(offset, width);
		}

		if (cell->type == ID($concat)) {
			RTLIL::Const ret = arg1;
			ret.append(arg2);
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

	// Consider using the ConstEval struct instead if you need named ports and/or multiple outputs
	static RTLIL::Const eval(RTLIL::Cell *cell, const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3, bool *errp = nullptr)
	{
		if (cell->type.in(ID($mux), ID($_MUX_)))
			return const_mux(arg1, arg2, arg3);
		if (cell->type == ID($_NMUX_))
			return eval_not(const_mux(arg1, arg2, arg3));
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

	// Consider using the ConstEval struct instead if you need named ports and/or multiple outputs
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

YOSYS_NAMESPACE_END

#endif
