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

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct CellType
{
	RTLIL::IdString type;
	pool<RTLIL::IdString> inputs, outputs;
	bool is_evaluable;
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
		setup_stdcells();
		setup_stdcells_mem();
	}

	void setup_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs, bool is_evaluable = false)
	{
		CellType ct = {type, inputs, outputs, is_evaluable};
		cell_types[ct.type] = ct;
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

		IdString A = ID::A, B = ID::B, EN = ID(EN), Y = ID::Y;
		IdString SRC = ID(SRC), DST = ID(DST), DAT = ID(DAT);
		IdString EN_SRC = ID(EN_SRC), EN_DST = ID(EN_DST);

		setup_type(ID($tribuf), {A, EN}, {Y}, true);

		setup_type(ID($assert), {A, EN}, pool<RTLIL::IdString>(), true);
		setup_type(ID($assume), {A, EN}, pool<RTLIL::IdString>(), true);
		setup_type(ID($live), {A, EN}, pool<RTLIL::IdString>(), true);
		setup_type(ID($fair), {A, EN}, pool<RTLIL::IdString>(), true);
		setup_type(ID($cover), {A, EN}, pool<RTLIL::IdString>(), true);
		setup_type(ID($initstate), pool<RTLIL::IdString>(), {Y}, true);
		setup_type(ID($anyconst), pool<RTLIL::IdString>(), {Y}, true);
		setup_type(ID($anyseq), pool<RTLIL::IdString>(), {Y}, true);
		setup_type(ID($allconst), pool<RTLIL::IdString>(), {Y}, true);
		setup_type(ID($allseq), pool<RTLIL::IdString>(), {Y}, true);
		setup_type(ID($equiv), {A, B}, {Y}, true);
		setup_type(ID($specify2), {EN, SRC, DST}, pool<RTLIL::IdString>(), true);
		setup_type(ID($specify3), {EN, SRC, DST, DAT}, pool<RTLIL::IdString>(), true);
		setup_type(ID($specrule), {EN_SRC, EN_DST, SRC, DST}, pool<RTLIL::IdString>(), true);
	}

	void setup_internals_eval()
	{
		std::vector<RTLIL::IdString> unary_ops = {
			ID($not), ID($pos), ID($neg),
			ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
			ID($logic_not), ID($slice), ID($lut), ID($sop)
		};

		std::vector<RTLIL::IdString> binary_ops = {
			ID($and), ID($or), ID($xor), ID($xnor),
			ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx),
			ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt),
			ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($pow),
			ID($logic_and), ID($logic_or), ID($concat), ID($macc)
		};
		IdString A = ID::A, B = ID::B, S = ID(S), Y = ID::Y;
		IdString P = ID(P), G = ID(G), C = ID(C), X = ID(X);
		IdString BI = ID(BI), CI = ID(CI), CO = ID(CO), EN = ID(EN);

		for (auto type : unary_ops)
			setup_type(type, {A}, {Y}, true);

		for (auto type : binary_ops)
			setup_type(type, {A, B}, {Y}, true);

		for (auto type : std::vector<RTLIL::IdString>({ID($mux), ID($pmux)}))
			setup_type(type, {A, B, S}, {Y}, true);

		setup_type(ID($lcu), {P, G, CI}, {CO}, true);
		setup_type(ID($alu), {A, B, CI, BI}, {X, Y, CO}, true);
		setup_type(ID($fa), {A, B, C}, {X, Y}, true);
	}

	void setup_internals_ff()
	{
		IdString SET = ID(SET), CLR = ID(CLR), CLK = ID(CLK), ARST = ID(ARST), EN = ID(EN);
		IdString Q = ID(Q), D = ID(D);

		setup_type(ID($sr), {SET, CLR}, {Q});
		setup_type(ID($ff), {D}, {Q});
		setup_type(ID($dff), {CLK, D}, {Q});
		setup_type(ID($dffe), {CLK, EN, D}, {Q});
		setup_type(ID($dffsr), {CLK, SET, CLR, D}, {Q});
		setup_type(ID($adff), {CLK, ARST, D}, {Q});
		setup_type(ID($dlatch), {EN, D}, {Q});
		setup_type(ID($dlatchsr), {EN, SET, CLR, D}, {Q});

	}

	void setup_internals_mem()
	{
		setup_internals_ff();

		IdString CLK = ID(CLK), ARST = ID(ARST), EN = ID(EN);
		IdString ADDR = ID(ADDR), DATA = ID(DATA), RD_EN = ID(RD_EN);
		IdString RD_CLK = ID(RD_CLK), RD_ADDR = ID(RD_ADDR), WR_CLK = ID(WR_CLK), WR_EN = ID(WR_EN);
		IdString WR_ADDR = ID(WR_ADDR), WR_DATA = ID(WR_DATA), RD_DATA = ID(RD_DATA);
		IdString CTRL_IN = ID(CTRL_IN), CTRL_OUT = ID(CTRL_OUT);

		setup_type(ID($memrd), {CLK, EN, ADDR}, {DATA});
		setup_type(ID($memwr), {CLK, EN, ADDR, DATA}, pool<RTLIL::IdString>());
		setup_type(ID($meminit), {ADDR, DATA}, pool<RTLIL::IdString>());
		setup_type(ID($mem), {RD_CLK, RD_EN, RD_ADDR, WR_CLK, WR_EN, WR_ADDR, WR_DATA}, {RD_DATA});

		setup_type(ID($fsm), {CLK, ARST, CTRL_IN}, {CTRL_OUT});
	}

	void setup_stdcells()
	{
		setup_stdcells_eval();

		IdString A = ID::A, E = ID(E), Y = ID::Y;

		setup_type(ID($_TBUF_), {A, E}, {Y}, true);
	}

	void setup_stdcells_eval()
	{
		IdString A = ID::A, B = ID::B, C = ID(C), D = ID(D);
		IdString E = ID(E), F = ID(F), G = ID(G), H = ID(H);
		IdString I = ID(I), J = ID(J), K = ID(K), L = ID(L);
		IdString M = ID(M), N = ID(N), O = ID(O), P = ID(P);
		IdString S = ID(S), T = ID(T), U = ID(U), V = ID(V);
		IdString Y = ID::Y;

		setup_type(ID($_BUF_), {A}, {Y}, true);
		setup_type(ID($_NOT_), {A}, {Y}, true);
		setup_type(ID($_AND_), {A, B}, {Y}, true);
		setup_type(ID($_NAND_), {A, B}, {Y}, true);
		setup_type(ID($_OR_),  {A, B}, {Y}, true);
		setup_type(ID($_NOR_),  {A, B}, {Y}, true);
		setup_type(ID($_XOR_), {A, B}, {Y}, true);
		setup_type(ID($_XNOR_), {A, B}, {Y}, true);
		setup_type(ID($_ANDNOT_), {A, B}, {Y}, true);
		setup_type(ID($_ORNOT_), {A, B}, {Y}, true);
		setup_type(ID($_MUX_), {A, B, S}, {Y}, true);
		setup_type(ID($_NMUX_), {A, B, S}, {Y}, true);
		setup_type(ID($_MUX4_), {A, B, C, D, S, T}, {Y}, true);
		setup_type(ID($_MUX8_), {A, B, C, D, E, F, G, H, S, T, U}, {Y}, true);
		setup_type(ID($_MUX16_), {A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, S, T, U, V}, {Y}, true);
		setup_type(ID($_AOI3_), {A, B, C}, {Y}, true);
		setup_type(ID($_OAI3_), {A, B, C}, {Y}, true);
		setup_type(ID($_AOI4_), {A, B, C, D}, {Y}, true);
		setup_type(ID($_OAI4_), {A, B, C, D}, {Y}, true);
	}

	void setup_stdcells_mem()
	{
		IdString S = ID(S), R = ID(R), C = ID(C);
		IdString D = ID(D), Q = ID(Q), E = ID(E);

		std::vector<char> list_np = {'N', 'P'}, list_01 = {'0', '1'};

		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_type(stringf("$_SR_%c%c_", c1, c2), {S, R}, {Q});

		setup_type(ID($_FF_), {D}, {Q});

		for (auto c1 : list_np)
			setup_type(stringf("$_DFF_%c_", c1), {C, D}, {Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_type(stringf("$_DFFE_%c%c_", c1, c2), {C, D, E}, {Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
			setup_type(stringf("$_DFF_%c%c%c_", c1, c2, c3), {C, R, D}, {Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_type(stringf("$_DFFSR_%c%c%c_", c1, c2, c3), {C, S, R, D}, {Q});

		for (auto c1 : list_np)
			setup_type(stringf("$_DLATCH_%c_", c1), {E, D}, {Q});

		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_type(stringf("$_DLATCHSR_%c%c%c_", c1, c2, c3), {E, S, R, D}, {Q});
	}

	void clear()
	{
		cell_types.clear();
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
		for (auto &bit : v.bits)
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
				type != ID($pos) && type != ID($neg) && type != ID($not)) {
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
		HANDLE_CELL_TYPE(neg)
#undef HANDLE_CELL_TYPE

		if (type == ID($_BUF_))
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
			int width = cell->parameters.at(ID(Y_WIDTH)).as_int();
			int offset = cell->parameters.at(ID(OFFSET)).as_int();
			ret.bits.insert(ret.bits.end(), arg1.bits.begin()+offset, arg1.bits.begin()+offset+width);
			return ret;
		}

		if (cell->type == ID($concat)) {
			RTLIL::Const ret = arg1;
			ret.bits.insert(ret.bits.end(), arg2.bits.begin(), arg2.bits.end());
			return ret;
		}

		if (cell->type == ID($lut))
		{
			int width = cell->parameters.at(ID(WIDTH)).as_int();

			std::vector<RTLIL::State> t = cell->parameters.at(ID(LUT)).bits;
			while (GetSize(t) < (1 << width))
				t.push_back(State::S0);
			t.resize(1 << width);

			for (int i = width-1; i >= 0; i--) {
				RTLIL::State sel = arg1.bits.at(i);
				std::vector<RTLIL::State> new_t;
				if (sel == State::S0)
					new_t = std::vector<RTLIL::State>(t.begin(), t.begin() + GetSize(t)/2);
				else if (sel == State::S1)
					new_t = std::vector<RTLIL::State>(t.begin() + GetSize(t)/2, t.end());
				else
					for (int j = 0; j < GetSize(t)/2; j++)
						new_t.push_back(t[j] == t[j + GetSize(t)/2] ? t[j] : RTLIL::Sx);
				t.swap(new_t);
			}

			log_assert(GetSize(t) == 1);
			return t;
		}

		if (cell->type == ID($sop))
		{
			int width = cell->parameters.at(ID(WIDTH)).as_int();
			int depth = cell->parameters.at(ID(DEPTH)).as_int();
			std::vector<RTLIL::State> t = cell->parameters.at(ID(TABLE)).bits;

			while (GetSize(t) < width*depth*2)
				t.push_back(State::S0);

			RTLIL::State default_ret = State::S0;

			for (int i = 0; i < depth; i++)
			{
				bool match = true;
				bool match_x = true;

				for (int j = 0; j < width; j++) {
					RTLIL::State a = arg1.bits.at(j);
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

		bool signed_a = cell->parameters.count(ID(A_SIGNED)) > 0 && cell->parameters[ID(A_SIGNED)].as_bool();
		bool signed_b = cell->parameters.count(ID(B_SIGNED)) > 0 && cell->parameters[ID(B_SIGNED)].as_bool();
		int result_len = cell->parameters.count(ID(Y_WIDTH)) > 0 ? cell->parameters[ID(Y_WIDTH)].as_int() : -1;
		return eval(cell->type, arg1, arg2, signed_a, signed_b, result_len, errp);
	}

	static RTLIL::Const eval(RTLIL::Cell *cell, const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3, bool *errp = nullptr)
	{
		if (cell->type.in(ID($mux), ID($pmux), ID($_MUX_))) {
			RTLIL::Const ret = arg1;
			for (size_t i = 0; i < arg3.bits.size(); i++)
				if (arg3.bits[i] == RTLIL::State::S1) {
					std::vector<RTLIL::State> bits(arg2.bits.begin() + i*arg1.bits.size(), arg2.bits.begin() + (i+1)*arg1.bits.size());
					ret = RTLIL::Const(bits);
				}
			return ret;
		}

		if (cell->type == ID($_AOI3_))
			return eval_not(const_or(const_and(arg1, arg2, false, false, 1), arg3, false, false, 1));
		if (cell->type == ID($_OAI3_))
			return eval_not(const_and(const_or(arg1, arg2, false, false, 1), arg3, false, false, 1));

		log_assert(arg3.bits.size() == 0);
		return eval(cell, arg1, arg2, errp);
	}

	static RTLIL::Const eval(RTLIL::Cell *cell, const RTLIL::Const &arg1, const RTLIL::Const &arg2, const RTLIL::Const &arg3, const RTLIL::Const &arg4, bool *errp = nullptr)
	{
		if (cell->type == ID($_AOI4_))
			return eval_not(const_or(const_and(arg1, arg2, false, false, 1), const_and(arg3, arg4, false, false, 1), false, false, 1));
		if (cell->type == ID($_OAI4_))
			return eval_not(const_and(const_or(arg1, arg2, false, false, 1), const_or(arg3, arg4, false, false, 1), false, false, 1));

		log_assert(arg4.bits.size() == 0);
		return eval(cell, arg1, arg2, arg3, errp);
	}
};

// initialized by yosys_setup()
extern CellTypes yosys_celltypes;

YOSYS_NAMESPACE_END

#endif
