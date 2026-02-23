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
#include "kernel/gen_celltypes_data.h"

YOSYS_NAMESPACE_BEGIN

struct CellType
{
	RTLIL::IdString type;
	pool<RTLIL::IdString> inputs, outputs;
	bool is_evaluable;
	bool is_combinatorial;
	bool is_synthesizable;
};

struct CellTypes
{
	dict<RTLIL::IdString, CellType> cell_types;

	static constexpr uint16_t BIT_INTERNALS_OTHER   = 0x0001;
	static constexpr uint16_t BIT_INTERNALS_EVAL    = 0x0002;
	static constexpr uint16_t BIT_INTERNALS_FF      = 0x0004;
	static constexpr uint16_t BIT_INTERNALS_ANYINIT = 0x0008;
	static constexpr uint16_t BIT_INTERNALS_MEM     = 0x0010;
	static constexpr uint16_t BIT_STDCELLS_EVAL     = 0x0020;
	static constexpr uint16_t BIT_STDCELLS_TRISTATE = 0x0040;
	static constexpr uint16_t BIT_STDCELLS_FF       = 0x0080;

	static constexpr uint16_t BITS_ALL = BIT_INTERNALS_OTHER | BIT_INTERNALS_EVAL |
		BIT_INTERNALS_FF | BIT_INTERNALS_ANYINIT | BIT_INTERNALS_MEM |
		BIT_STDCELLS_EVAL | BIT_STDCELLS_TRISTATE | BIT_STDCELLS_FF;

	uint16_t enabled_cats = 0;

	CellTypes() {}

	CellTypes(RTLIL::Design *design) { setup(design); }

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

	void setup_type(RTLIL::IdString type, const pool<RTLIL::IdString> &inputs, const pool<RTLIL::IdString> &outputs, bool is_evaluable = false, bool is_combinatorial = false, bool is_synthesizable = false)
	{
		CellType ct = {type, inputs, outputs, is_evaluable, is_combinatorial, is_synthesizable};
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

	void setup_internals()         { enabled_cats |= BIT_INTERNALS_OTHER | BIT_INTERNALS_EVAL; }
	void setup_internals_eval()    { enabled_cats |= BIT_INTERNALS_EVAL; }
	void setup_internals_ff()      { enabled_cats |= BIT_INTERNALS_FF; }
	void setup_internals_anyinit() { enabled_cats |= BIT_INTERNALS_ANYINIT; }
	void setup_internals_mem()     { enabled_cats |= BIT_INTERNALS_FF | BIT_INTERNALS_MEM; }
	void setup_stdcells()          { enabled_cats |= BIT_STDCELLS_EVAL | BIT_STDCELLS_TRISTATE; }
	void setup_stdcells_eval()     { enabled_cats |= BIT_STDCELLS_EVAL; }
	void setup_stdcells_mem()      { enabled_cats |= BIT_STDCELLS_FF; }

	void clear()
	{
		cell_types.clear();
		enabled_cats = 0;
	}

	bool builtin_match(size_t idx) const
	{
		if (!enabled_cats || idx >= (size_t)StaticCellTypes::GEN_MAX_CELLS)
			return false;

		using namespace StaticCellTypes::GeneratedData;

		if (!is_known[idx])
			return false;

		if (!is_stdcell[idx]) {
			if ((enabled_cats & BIT_INTERNALS_EVAL) && is_evaluable[idx])
				return true;
			if ((enabled_cats & BIT_INTERNALS_FF) && is_ff[idx])
				return true;
			if ((enabled_cats & BIT_INTERNALS_ANYINIT) && is_anyinit[idx])
				return true;
			if ((enabled_cats & BIT_INTERNALS_MEM) && is_mem_noff[idx])
				return true;
			if (enabled_cats & BIT_INTERNALS_OTHER) {
				if (!is_evaluable[idx] && !is_ff[idx] && !is_mem_noff[idx] && !is_anyinit[idx])
					return true;
			}
		} else {
			if ((enabled_cats & BIT_STDCELLS_EVAL) && is_evaluable[idx])
				return true;
			if ((enabled_cats & BIT_STDCELLS_TRISTATE) && is_tristate[idx])
				return true;
			if ((enabled_cats & BIT_STDCELLS_FF) && is_ff[idx])
				return true;
		}

		return false;
	}

	bool builtin_is_known(size_t idx) const
	{
		return enabled_cats && idx < (size_t)StaticCellTypes::GEN_MAX_CELLS &&
			StaticCellTypes::GeneratedData::is_known[idx];
	}

	bool cell_known(const RTLIL::IdString &type) const
	{
		if (enabled_cats == BITS_ALL) {
			if (builtin_is_known(type.index_))
				return true;
		} else if (builtin_match(type.index_)) {
			return true;
		}
		return cell_types.count(type) != 0;
	}

bool cell_output(const RTLIL::IdString &type, const RTLIL::IdString &port) const
	{
		auto it = cell_types.find(type);
		if (it != cell_types.end())
			return it->second.outputs.count(port) != 0;
		size_t idx = type.index_;
		bool is_builtin = (enabled_cats == BITS_ALL) ? builtin_is_known(idx) : builtin_match(idx);
		if (is_builtin) {
			uint32_t target = (uint32_t)port.index_;
			uint16_t count = StaticCellTypes::GeneratedData::port_outputs_counts[idx];
			for (uint16_t i = 0; i < count; i++)
				if (StaticCellTypes::GeneratedData::port_outputs_ports[idx][i] == target)
					return true;
		}
		return false;
	}

	bool cell_input(const RTLIL::IdString &type, const RTLIL::IdString &port) const
	{
		auto it = cell_types.find(type);
		if (it != cell_types.end())
			return it->second.inputs.count(port) != 0;
		size_t idx = type.index_;
		bool is_builtin = (enabled_cats == BITS_ALL) ? builtin_is_known(idx) : builtin_match(idx);
		if (is_builtin) {
			uint32_t target = (uint32_t)port.index_;
			uint16_t count = StaticCellTypes::GeneratedData::port_inputs_counts[idx];
			for (uint16_t i = 0; i < count; i++)
				if (StaticCellTypes::GeneratedData::port_inputs_ports[idx][i] == target)
					return true;
		}
		return false;
	}

	RTLIL::PortDir cell_port_dir(RTLIL::IdString type, RTLIL::IdString port) const
	{
		auto it = cell_types.find(type);
		if (it != cell_types.end()) {
			bool is_input = it->second.inputs.count(port);
			bool is_output = it->second.outputs.count(port);
			return RTLIL::PortDir(is_input + is_output * 2);
		}
		size_t idx = type.index_;
		bool is_builtin = (enabled_cats == BITS_ALL) ? builtin_is_known(idx) : builtin_match(idx);
		if (is_builtin) {
			bool is_in = false, is_out = false;
			uint32_t target = (uint32_t)port.index_;
			uint16_t ic = StaticCellTypes::GeneratedData::port_inputs_counts[idx];
			for (uint16_t i = 0; i < ic; i++)
				if (StaticCellTypes::GeneratedData::port_inputs_ports[idx][i] == target)
					{ is_in = true; break; }
			uint16_t oc = StaticCellTypes::GeneratedData::port_outputs_counts[idx];
			for (uint16_t i = 0; i < oc; i++)
				if (StaticCellTypes::GeneratedData::port_outputs_ports[idx][i] == target)
					{ is_out = true; break; }
			return RTLIL::PortDir(is_in + is_out * 2);
		}
		return RTLIL::PD_UNKNOWN;
	}

	bool cell_evaluable(const RTLIL::IdString &type) const
	{
		auto it = cell_types.find(type);
		if (it != cell_types.end())
			return it->second.is_evaluable;

		size_t idx = type.index_;
		bool is_builtin = (enabled_cats == BITS_ALL) ? builtin_is_known(idx) : builtin_match(idx);
		if (is_builtin)
			return idx < (size_t)StaticCellTypes::GEN_MAX_CELLS &&
				StaticCellTypes::GeneratedData::is_cell_evaluable[idx];
		return false;
	}

	static RTLIL::Const eval_not(RTLIL::Const v)
	{
		for (auto bit : v)
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
			return const_bmux(arg1, arg2);

		if (cell->type == ID($demux))
			return const_demux(arg1, arg2);

		if (cell->type == ID($bweqx))
			return const_bweqx(arg1, arg2);

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

extern CellTypes yosys_celltypes;

YOSYS_NAMESPACE_END

#endif
