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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/utils.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool did_something;

void replace_undriven(RTLIL::Design *design, RTLIL::Module *module)
{
	CellTypes ct(design);
	SigMap sigmap(module);
	SigPool driven_signals;
	SigPool used_signals;
	SigPool all_signals;

	for (auto cell : module->cells())
	for (auto &conn : cell->connections()) {
		if (!ct.cell_known(cell->type) || ct.cell_output(cell->type, conn.first))
			driven_signals.add(sigmap(conn.second));
		if (!ct.cell_known(cell->type) || ct.cell_input(cell->type, conn.first))
			used_signals.add(sigmap(conn.second));
	}

	for (auto wire : module->wires()) {
		if (wire->port_input)
			driven_signals.add(sigmap(wire));
		if (wire->port_output)
			used_signals.add(sigmap(wire));
		all_signals.add(sigmap(wire));
	}

	all_signals.del(driven_signals);
	RTLIL::SigSpec undriven_signals = all_signals.export_all();

	for (auto &c : undriven_signals.chunks())
	{
		RTLIL::SigSpec sig = c;

		if (c.wire->name[0] == '$')
			sig = used_signals.extract(sig);
		if (sig.size() == 0)
			continue;

		log("Setting undriven signal in %s to undef: %s\n", RTLIL::id2cstr(module->name), log_signal(c));
		module->connect(RTLIL::SigSig(c, RTLIL::SigSpec(RTLIL::State::Sx, c.width)));
		did_something = true;
	}
}

void replace_cell(SigMap &assign_map, RTLIL::Module *module, RTLIL::Cell *cell, std::string info, std::string out_port, RTLIL::SigSpec out_val)
{
	RTLIL::SigSpec Y = cell->getPort(out_port);
	out_val.extend_u0(Y.size(), false);

	log("Replacing %s cell `%s' (%s) in module `%s' with constant driver `%s = %s'.\n",
			cell->type.c_str(), cell->name.c_str(), info.c_str(),
			module->name.c_str(), log_signal(Y), log_signal(out_val));
	// log_cell(cell);
	assign_map.add(Y, out_val);
	module->connect(Y, out_val);
	module->remove(cell);
	did_something = true;
}

bool group_cell_inputs(RTLIL::Module *module, RTLIL::Cell *cell, bool commutative, SigMap &sigmap)
{
	std::string b_name = cell->hasPort("\\B") ? "\\B" : "\\A";

	bool a_signed = cell->parameters.at("\\A_SIGNED").as_bool();
	bool b_signed = cell->parameters.at(b_name + "_SIGNED").as_bool();

	RTLIL::SigSpec sig_a = sigmap(cell->getPort("\\A"));
	RTLIL::SigSpec sig_b = sigmap(cell->getPort(b_name));
	RTLIL::SigSpec sig_y = sigmap(cell->getPort("\\Y"));

	sig_a.extend_u0(sig_y.size(), a_signed);
	sig_b.extend_u0(sig_y.size(), b_signed);

	std::vector<RTLIL::SigBit> bits_a = sig_a, bits_b = sig_b, bits_y = sig_y;

	enum { GRP_DYN, GRP_CONST_A, GRP_CONST_B, GRP_CONST_AB, GRP_N };
	std::map<std::pair<RTLIL::SigBit, RTLIL::SigBit>, std::set<RTLIL::SigBit>> grouped_bits[GRP_N];

	for (int i = 0; i < GetSize(bits_y); i++)
	{
		int group_idx = GRP_DYN;
		RTLIL::SigBit bit_a = bits_a[i], bit_b = bits_b[i];

		if (cell->type == "$or" && (bit_a == RTLIL::State::S1 || bit_b == RTLIL::State::S1))
			bit_a = bit_b = RTLIL::State::S1;

		if (cell->type == "$and" && (bit_a == RTLIL::State::S0 || bit_b == RTLIL::State::S0))
			bit_a = bit_b = RTLIL::State::S0;

		if (bit_a.wire == NULL && bit_b.wire == NULL)
			group_idx = GRP_CONST_AB;
		else if (bit_a.wire == NULL)
			group_idx = GRP_CONST_A;
		else if (bit_b.wire == NULL && commutative)
			group_idx = GRP_CONST_A, std::swap(bit_a, bit_b);
		else if (bit_b.wire == NULL)
			group_idx = GRP_CONST_B;

		grouped_bits[group_idx][std::pair<RTLIL::SigBit, RTLIL::SigBit>(bit_a, bit_b)].insert(bits_y[i]);
	}

	for (int i = 0; i < GRP_N; i++)
		if (GetSize(grouped_bits[i]) == GetSize(bits_y))
			return false;

	log("Replacing %s cell `%s' in module `%s' with cells using grouped bits:\n",
			log_id(cell->type), log_id(cell), log_id(module));

	for (int i = 0; i < GRP_N; i++)
	{
		if (grouped_bits[i].empty())
			continue;

		RTLIL::Wire *new_y = module->addWire(NEW_ID, GetSize(grouped_bits[i]));
		RTLIL::SigSpec new_a, new_b;
		RTLIL::SigSig new_conn;

		for (auto &it : grouped_bits[i]) {
			for (auto &bit : it.second) {
				new_conn.first.append_bit(bit);
				new_conn.second.append_bit(RTLIL::SigBit(new_y, new_a.size()));
			}
			new_a.append_bit(it.first.first);
			new_b.append_bit(it.first.second);
		}

		RTLIL::Cell *c = module->addCell(NEW_ID, cell->type);

		c->setPort("\\A", new_a);
		c->parameters["\\A_WIDTH"] = new_a.size();
		c->parameters["\\A_SIGNED"] = false;

		if (b_name == "\\B") {
			c->setPort("\\B", new_b);
			c->parameters["\\B_WIDTH"] = new_b.size();
			c->parameters["\\B_SIGNED"] = false;
		}

		c->setPort("\\Y", new_y);
		c->parameters["\\Y_WIDTH"] = new_y->width;
		c->check();

		module->connect(new_conn);

		log("  New cell `%s': A=%s", log_id(c), log_signal(new_a));
		if (b_name == "\\B")
			log(", B=%s", log_signal(new_b));
		log("\n");
	}

	cover_list("opt.opt_expr.fine.group", "$not", "$pos", "$and", "$or", "$xor", "$xnor", cell->type.str());

	module->remove(cell);
	did_something = true;
	return true;
}

void handle_polarity_inv(Cell *cell, IdString port, IdString param, const SigMap &assign_map, const dict<RTLIL::SigSpec, RTLIL::SigSpec> &invert_map)
{
	SigSpec sig = assign_map(cell->getPort(port));
	if (invert_map.count(sig)) {
		log("Inverting %s of %s cell `%s' in module `%s': %s -> %s\n",
				log_id(port), log_id(cell->type), log_id(cell), log_id(cell->module),
				log_signal(sig), log_signal(invert_map.at(sig)));
		cell->setPort(port, (invert_map.at(sig)));
		cell->setParam(param, !cell->getParam(param).as_bool());
	}
}

void handle_clkpol_celltype_swap(Cell *cell, string type1, string type2, IdString port, const SigMap &assign_map, const dict<RTLIL::SigSpec, RTLIL::SigSpec> &invert_map)
{
	log_assert(GetSize(type1) == GetSize(type2));
	string cell_type = cell->type.str();

	if (GetSize(type1) != GetSize(cell_type))
		return;

	for (int i = 0; i < GetSize(type1); i++) {
		log_assert((type1[i] == '?') == (type2[i] == '?'));
		if (type1[i] == '?') {
			if (cell_type[i] != '0' && cell_type[i] != '1' && cell_type[i] != 'N' && cell_type[i] != 'P')
				return;
			type1[i] = cell_type[i];
			type2[i] = cell_type[i];
		}
	}

	if (cell->type.in(type1, type2)) {
		SigSpec sig = assign_map(cell->getPort(port));
		if (invert_map.count(sig)) {
			log("Inverting %s of %s cell `%s' in module `%s': %s -> %s\n",
					log_id(port), log_id(cell->type), log_id(cell), log_id(cell->module),
					log_signal(sig), log_signal(invert_map.at(sig)));
			cell->setPort(port, (invert_map.at(sig)));
			cell->type = cell->type == type1 ? type2 : type1;
		}
	}
}

bool is_one_or_minus_one(const Const &value, bool is_signed, bool &is_negative)
{
	bool all_bits_one = true;
	bool last_bit_one = true;

	if (GetSize(value.bits) < 1)
		return false;

	if (GetSize(value.bits) == 1) {
		if (value.bits[0] != State::S1)
			return false;
		if (is_signed)
			is_negative = true;
		return true;
	}

	for (int i = 0; i < GetSize(value.bits); i++) {
		if (value.bits[i] != State::S1)
			all_bits_one = false;
		if (value.bits[i] != (i ? State::S0 : State::S1))
			last_bit_one = false;
	}

	if (all_bits_one && is_signed) {
		is_negative = true;
		return true;
	}

	return last_bit_one;
}

void replace_const_cells(RTLIL::Design *design, RTLIL::Module *module, bool consume_x, bool mux_undef, bool mux_bool, bool do_fine, bool keepdc, bool clkinv)
{
	if (!design->selected(module))
		return;

	CellTypes ct_combinational;
	ct_combinational.setup_internals();
	ct_combinational.setup_stdcells();

	SigMap assign_map(module);
	dict<RTLIL::SigSpec, RTLIL::SigSpec> invert_map;

	TopoSort<RTLIL::Cell*, RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell>> cells;
	dict<RTLIL::Cell*, std::set<RTLIL::SigBit>> cell_to_inbit;
	dict<RTLIL::SigBit, std::set<RTLIL::Cell*>> outbit_to_cell;

	for (auto cell : module->cells())
		if (design->selected(module, cell) && cell->type[0] == '$') {
			if ((cell->type == "$_NOT_" || cell->type == "$not" || cell->type == "$logic_not") &&
					cell->getPort("\\A").size() == 1 && cell->getPort("\\Y").size() == 1)
				invert_map[assign_map(cell->getPort("\\Y"))] = assign_map(cell->getPort("\\A"));
			if ((cell->type == "$mux" || cell->type == "$_MUX_") && cell->getPort("\\A") == SigSpec(State::S1) && cell->getPort("\\B") == SigSpec(State::S0))
				invert_map[assign_map(cell->getPort("\\Y"))] = assign_map(cell->getPort("\\S"));
			if (ct_combinational.cell_known(cell->type))
				for (auto &conn : cell->connections()) {
					RTLIL::SigSpec sig = assign_map(conn.second);
					sig.remove_const();
					if (ct_combinational.cell_input(cell->type, conn.first))
						cell_to_inbit[cell].insert(sig.begin(), sig.end());
					if (ct_combinational.cell_output(cell->type, conn.first))
						for (auto &bit : sig)
							outbit_to_cell[bit].insert(cell);
				}
			cells.node(cell);
		}

	for (auto &it_right : cell_to_inbit)
	for (auto &it_sigbit : it_right.second)
	for (auto &it_left : outbit_to_cell[it_sigbit])
		cells.edge(it_left, it_right.first);

	cells.sort();

	for (auto cell : cells.sorted)
	{
#define ACTION_DO(_p_, _s_) do { cover("opt.opt_expr.action_" S__LINE__); replace_cell(assign_map, module, cell, input.as_string(), _p_, _s_); goto next_cell; } while (0)
#define ACTION_DO_Y(_v_) ACTION_DO("\\Y", RTLIL::SigSpec(RTLIL::State::S ## _v_))

		if (clkinv)
		{
			if (cell->type.in("$dff", "$dffe", "$dffsr", "$adff", "$fsm", "$memrd", "$memwr"))
				handle_polarity_inv(cell, "\\CLK", "\\CLK_POLARITY", assign_map, invert_map);

			if (cell->type.in("$sr", "$dffsr", "$dlatchsr")) {
				handle_polarity_inv(cell, "\\SET", "\\SET_POLARITY", assign_map, invert_map);
				handle_polarity_inv(cell, "\\CLR", "\\CLR_POLARITY", assign_map, invert_map);
			}

			if (cell->type.in("$dffe", "$dlatch", "$dlatchsr"))
				handle_polarity_inv(cell, "\\EN", "\\EN_POLARITY", assign_map, invert_map);

			handle_clkpol_celltype_swap(cell, "$_SR_N?_", "$_SR_P?_", "\\S", assign_map, invert_map);
			handle_clkpol_celltype_swap(cell, "$_SR_?N_", "$_SR_?P_", "\\R", assign_map, invert_map);

			handle_clkpol_celltype_swap(cell, "$_DFF_N_", "$_DFF_P_", "\\C", assign_map, invert_map);

			handle_clkpol_celltype_swap(cell, "$_DFFE_N?_", "$_DFFE_P?_", "\\C", assign_map, invert_map);
			handle_clkpol_celltype_swap(cell, "$_DFFE_?N_", "$_DFFE_?P_", "\\E", assign_map, invert_map);

			handle_clkpol_celltype_swap(cell, "$_DFF_N??_", "$_DFF_P??_", "\\C", assign_map, invert_map);
			handle_clkpol_celltype_swap(cell, "$_DFF_?N?_", "$_DFF_?P?_", "\\R", assign_map, invert_map);

			handle_clkpol_celltype_swap(cell, "$_DFFSR_N??_", "$_DFFSR_P??_", "\\C", assign_map, invert_map);
			handle_clkpol_celltype_swap(cell, "$_DFFSR_?N?_", "$_DFFSR_?P?_", "\\S", assign_map, invert_map);
			handle_clkpol_celltype_swap(cell, "$_DFFSR_??N_", "$_DFFSR_??P_", "\\R", assign_map, invert_map);

			handle_clkpol_celltype_swap(cell, "$_DLATCH_N_", "$_DLATCH_P_", "\\E", assign_map, invert_map);

			handle_clkpol_celltype_swap(cell, "$_DLATCHSR_N??_", "$_DLATCHSR_P??_", "\\E", assign_map, invert_map);
			handle_clkpol_celltype_swap(cell, "$_DLATCHSR_?N?_", "$_DLATCHSR_?P?_", "\\S", assign_map, invert_map);
			handle_clkpol_celltype_swap(cell, "$_DLATCHSR_??N_", "$_DLATCHSR_??P_", "\\R", assign_map, invert_map);
		}

		bool detect_const_and = false;
		bool detect_const_or = false;

		if (cell->type.in("$reduce_and", "$_AND_"))
			detect_const_and = true;

		if (cell->type.in("$and", "$logic_and") && GetSize(cell->getPort("\\A")) == 1 && GetSize(cell->getPort("\\B")) == 1)
			detect_const_and = true;

		if (cell->type.in("$reduce_or", "$reduce_bool", "$_OR_"))
			detect_const_or = true;

		if (cell->type.in("$or", "$logic_or") && GetSize(cell->getPort("\\A")) == 1 && GetSize(cell->getPort("\\B")) == 1)
			detect_const_or = true;

		if (detect_const_and || detect_const_or)
		{
			pool<SigBit> input_bits = assign_map(cell->getPort("\\A")).to_sigbit_pool();
			bool found_zero = false, found_one = false, found_inv = false;

			if (cell->hasPort("\\B")) {
				vector<SigBit> more_bits = assign_map(cell->getPort("\\B")).to_sigbit_vector();
				input_bits.insert(more_bits.begin(), more_bits.end());
			}

			for (auto bit : input_bits) {
				if (bit == State::S0)
					found_zero = true;
				if (bit == State::S1)
					found_one = true;
				if (invert_map.count(bit) && input_bits.count(invert_map.at(bit)))
					found_inv = true;
			}

			if (detect_const_and && (found_zero || found_inv)) {
				cover("opt.opt_expr.const_and");
				replace_cell(assign_map, module, cell, "const_and", "\\Y", RTLIL::State::S0);
				goto next_cell;
			}

			if (detect_const_or && (found_one || found_inv)) {
				cover("opt.opt_expr.const_or");
				replace_cell(assign_map, module, cell, "const_or", "\\Y", RTLIL::State::S1);
				goto next_cell;
			}
		}

		if (cell->type.in("$reduce_and", "$reduce_or", "$reduce_bool", "$reduce_xor", "$reduce_xnor", "$neg") &&
				GetSize(cell->getPort("\\A")) == 1 && GetSize(cell->getPort("\\Y")) == 1)
		{
			if (cell->type == "$reduce_xnor") {
				cover("opt.opt_expr.reduce_xnor_not");
				log("Replacing %s cell `%s' in module `%s' with $not cell.\n",
						log_id(cell->type), log_id(cell->name), log_id(module));
				cell->type = "$not";
			} else {
				cover("opt.opt_expr.unary_buffer");
				replace_cell(assign_map, module, cell, "unary_buffer", "\\Y", cell->getPort("\\A"));
			}
			goto next_cell;
		}

		if (do_fine)
		{
			if (cell->type == "$not" || cell->type == "$pos" ||
					cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor")
				if (group_cell_inputs(module, cell, true, assign_map))
					goto next_cell;

			if (cell->type == "$reduce_and")
			{
				RTLIL::SigSpec sig_a = assign_map(cell->getPort("\\A"));

				RTLIL::State new_a = RTLIL::State::S1;
				for (auto &bit : sig_a.to_sigbit_vector())
					if (bit == RTLIL::State::Sx) {
						if (new_a == RTLIL::State::S1)
							new_a = RTLIL::State::Sx;
					} else if (bit == RTLIL::State::S0) {
						new_a = RTLIL::State::S0;
						break;
					} else if (bit.wire != NULL) {
						new_a = RTLIL::State::Sm;
					}

				if (new_a != RTLIL::State::Sm && RTLIL::SigSpec(new_a) != sig_a) {
					cover("opt.opt_expr.fine.$reduce_and");
					log("Replacing port A of %s cell `%s' in module `%s' with constant driver: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->name.c_str(), log_signal(sig_a), log_signal(new_a));
					cell->setPort("\\A", sig_a = new_a);
					cell->parameters.at("\\A_WIDTH") = 1;
					did_something = true;
				}
			}

			if (cell->type == "$logic_not" || cell->type == "$logic_and" || cell->type == "$logic_or" || cell->type == "$reduce_or" || cell->type == "$reduce_bool")
			{
				RTLIL::SigSpec sig_a = assign_map(cell->getPort("\\A"));

				RTLIL::State new_a = RTLIL::State::S0;
				for (auto &bit : sig_a.to_sigbit_vector())
					if (bit == RTLIL::State::Sx) {
						if (new_a == RTLIL::State::S0)
							new_a = RTLIL::State::Sx;
					} else if (bit == RTLIL::State::S1) {
						new_a = RTLIL::State::S1;
						break;
					} else if (bit.wire != NULL) {
						new_a = RTLIL::State::Sm;
					}

				if (new_a != RTLIL::State::Sm && RTLIL::SigSpec(new_a) != sig_a) {
					cover_list("opt.opt_expr.fine.A", "$logic_not", "$logic_and", "$logic_or", "$reduce_or", "$reduce_bool", cell->type.str());
					log("Replacing port A of %s cell `%s' in module `%s' with constant driver: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->name.c_str(), log_signal(sig_a), log_signal(new_a));
					cell->setPort("\\A", sig_a = new_a);
					cell->parameters.at("\\A_WIDTH") = 1;
					did_something = true;
				}
			}

			if (cell->type == "$logic_and" || cell->type == "$logic_or")
			{
				RTLIL::SigSpec sig_b = assign_map(cell->getPort("\\B"));

				RTLIL::State new_b = RTLIL::State::S0;
				for (auto &bit : sig_b.to_sigbit_vector())
					if (bit == RTLIL::State::Sx) {
						if (new_b == RTLIL::State::S0)
							new_b = RTLIL::State::Sx;
					} else if (bit == RTLIL::State::S1) {
						new_b = RTLIL::State::S1;
						break;
					} else if (bit.wire != NULL) {
						new_b = RTLIL::State::Sm;
					}

				if (new_b != RTLIL::State::Sm && RTLIL::SigSpec(new_b) != sig_b) {
					cover_list("opt.opt_expr.fine.B", "$logic_and", "$logic_or", cell->type.str());
					log("Replacing port B of %s cell `%s' in module `%s' with constant driver: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->name.c_str(), log_signal(sig_b), log_signal(new_b));
					cell->setPort("\\B", sig_b = new_b);
					cell->parameters.at("\\B_WIDTH") = 1;
					did_something = true;
				}
			}
		}

		if (cell->type == "$reduce_xor" || cell->type == "$reduce_xnor" || cell->type == "$shift" || cell->type == "$shiftx" ||
				cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr" ||
				cell->type == "$lt" || cell->type == "$le" || cell->type == "$ge" || cell->type == "$gt" ||
				cell->type == "$neg" || cell->type == "$add" || cell->type == "$sub" ||
				cell->type == "$mul" || cell->type == "$div" || cell->type == "$mod" || cell->type == "$pow")
		{
			RTLIL::SigSpec sig_a = assign_map(cell->getPort("\\A"));
			RTLIL::SigSpec sig_b = cell->hasPort("\\B") ? assign_map(cell->getPort("\\B")) : RTLIL::SigSpec();

			if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr" || cell->type == "$shift" || cell->type == "$shiftx")
				sig_a = RTLIL::SigSpec();

			for (auto &bit : sig_a.to_sigbit_vector())
				if (bit == RTLIL::State::Sx)
					goto found_the_x_bit;

			for (auto &bit : sig_b.to_sigbit_vector())
				if (bit == RTLIL::State::Sx)
					goto found_the_x_bit;

			if (0) {
		found_the_x_bit:
				cover_list("opt.opt_expr.xbit", "$reduce_xor", "$reduce_xnor", "$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx",
						"$lt", "$le", "$ge", "$gt", "$neg", "$add", "$sub", "$mul", "$div", "$mod", "$pow", cell->type.str());
				if (cell->type == "$reduce_xor" || cell->type == "$reduce_xnor" ||
						cell->type == "$lt" || cell->type == "$le" || cell->type == "$ge" || cell->type == "$gt")
					replace_cell(assign_map, module, cell, "x-bit in input", "\\Y", RTLIL::State::Sx);
				else
					replace_cell(assign_map, module, cell, "x-bit in input", "\\Y", RTLIL::SigSpec(RTLIL::State::Sx, cell->getPort("\\Y").size()));
				goto next_cell;
			}
		}

		if ((cell->type == "$_NOT_" || cell->type == "$not" || cell->type == "$logic_not") && cell->getPort("\\Y").size() == 1 &&
				invert_map.count(assign_map(cell->getPort("\\A"))) != 0) {
			cover_list("opt.opt_expr.invert.double", "$_NOT_", "$not", "$logic_not", cell->type.str());
			replace_cell(assign_map, module, cell, "double_invert", "\\Y", invert_map.at(assign_map(cell->getPort("\\A"))));
			goto next_cell;
		}

		if ((cell->type == "$_MUX_" || cell->type == "$mux") && invert_map.count(assign_map(cell->getPort("\\S"))) != 0) {
			cover_list("opt.opt_expr.invert.muxsel", "$_MUX_", "$mux", cell->type.str());
			log("Optimizing away select inverter for %s cell `%s' in module `%s'.\n", log_id(cell->type), log_id(cell), log_id(module));
			RTLIL::SigSpec tmp = cell->getPort("\\A");
			cell->setPort("\\A", cell->getPort("\\B"));
			cell->setPort("\\B", tmp);
			cell->setPort("\\S", invert_map.at(assign_map(cell->getPort("\\S"))));
			did_something = true;
			goto next_cell;
		}

		if (cell->type == "$_NOT_") {
			RTLIL::SigSpec input = cell->getPort("\\A");
			assign_map.apply(input);
			if (input.match("1")) ACTION_DO_Y(0);
			if (input.match("0")) ACTION_DO_Y(1);
			if (input.match("*")) ACTION_DO_Y(x);
		}

		if (cell->type == "$_AND_") {
			RTLIL::SigSpec input;
			input.append(cell->getPort("\\B"));
			input.append(cell->getPort("\\A"));
			assign_map.apply(input);
			if (input.match(" 0")) ACTION_DO_Y(0);
			if (input.match("0 ")) ACTION_DO_Y(0);
			if (input.match("11")) ACTION_DO_Y(1);
			if (input.match("**")) ACTION_DO_Y(x);
			if (input.match("1*")) ACTION_DO_Y(x);
			if (input.match("*1")) ACTION_DO_Y(x);
			if (consume_x) {
				if (input.match(" *")) ACTION_DO_Y(0);
				if (input.match("* ")) ACTION_DO_Y(0);
			}
			if (input.match(" 1")) ACTION_DO("\\Y", input.extract(1, 1));
			if (input.match("1 ")) ACTION_DO("\\Y", input.extract(0, 1));
		}

		if (cell->type == "$_OR_") {
			RTLIL::SigSpec input;
			input.append(cell->getPort("\\B"));
			input.append(cell->getPort("\\A"));
			assign_map.apply(input);
			if (input.match(" 1")) ACTION_DO_Y(1);
			if (input.match("1 ")) ACTION_DO_Y(1);
			if (input.match("00")) ACTION_DO_Y(0);
			if (input.match("**")) ACTION_DO_Y(x);
			if (input.match("0*")) ACTION_DO_Y(x);
			if (input.match("*0")) ACTION_DO_Y(x);
			if (consume_x) {
				if (input.match(" *")) ACTION_DO_Y(1);
				if (input.match("* ")) ACTION_DO_Y(1);
			}
			if (input.match(" 0")) ACTION_DO("\\Y", input.extract(1, 1));
			if (input.match("0 ")) ACTION_DO("\\Y", input.extract(0, 1));
		}

		if (cell->type == "$_XOR_") {
			RTLIL::SigSpec input;
			input.append(cell->getPort("\\B"));
			input.append(cell->getPort("\\A"));
			assign_map.apply(input);
			if (input.match("00")) ACTION_DO_Y(0);
			if (input.match("01")) ACTION_DO_Y(1);
			if (input.match("10")) ACTION_DO_Y(1);
			if (input.match("11")) ACTION_DO_Y(0);
			if (input.match(" *")) ACTION_DO_Y(x);
			if (input.match("* ")) ACTION_DO_Y(x);
			if (input.match(" 0")) ACTION_DO("\\Y", input.extract(1, 1));
			if (input.match("0 ")) ACTION_DO("\\Y", input.extract(0, 1));
		}

		if (cell->type == "$_MUX_") {
			RTLIL::SigSpec input;
			input.append(cell->getPort("\\S"));
			input.append(cell->getPort("\\B"));
			input.append(cell->getPort("\\A"));
			assign_map.apply(input);
			if (input.extract(2, 1) == input.extract(1, 1))
				ACTION_DO("\\Y", input.extract(2, 1));
			if (input.match("  0")) ACTION_DO("\\Y", input.extract(2, 1));
			if (input.match("  1")) ACTION_DO("\\Y", input.extract(1, 1));
			if (input.match("01 ")) ACTION_DO("\\Y", input.extract(0, 1));
			if (input.match("10 ")) {
				cover("opt.opt_expr.mux_to_inv");
				cell->type = "$_NOT_";
				cell->setPort("\\A", input.extract(0, 1));
				cell->unsetPort("\\B");
				cell->unsetPort("\\S");
				goto next_cell;
			}
			if (input.match("11 ")) ACTION_DO_Y(1);
			if (input.match("00 ")) ACTION_DO_Y(0);
			if (input.match("** ")) ACTION_DO_Y(x);
			if (input.match("01*")) ACTION_DO_Y(x);
			if (input.match("10*")) ACTION_DO_Y(x);
			if (mux_undef) {
				if (input.match("*  ")) ACTION_DO("\\Y", input.extract(1, 1));
				if (input.match(" * ")) ACTION_DO("\\Y", input.extract(2, 1));
				if (input.match("  *")) ACTION_DO("\\Y", input.extract(2, 1));
			}
		}

		if (cell->type == "$eq" || cell->type == "$ne" || cell->type == "$eqx" || cell->type == "$nex")
		{
			RTLIL::SigSpec a = cell->getPort("\\A");
			RTLIL::SigSpec b = cell->getPort("\\B");

			if (cell->parameters["\\A_WIDTH"].as_int() != cell->parameters["\\B_WIDTH"].as_int()) {
				int width = max(cell->parameters["\\A_WIDTH"].as_int(), cell->parameters["\\B_WIDTH"].as_int());
				a.extend_u0(width, cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool());
				b.extend_u0(width, cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool());
			}

			RTLIL::SigSpec new_a, new_b;

			log_assert(GetSize(a) == GetSize(b));
			for (int i = 0; i < GetSize(a); i++) {
				if (a[i].wire == NULL && b[i].wire == NULL && a[i] != b[i] && a[i].data <= RTLIL::State::S1 && b[i].data <= RTLIL::State::S1) {
					cover_list("opt.opt_expr.eqneq.isneq", "$eq", "$ne", "$eqx", "$nex", cell->type.str());
					RTLIL::SigSpec new_y = RTLIL::SigSpec((cell->type == "$eq" || cell->type == "$eqx") ?  RTLIL::State::S0 : RTLIL::State::S1);
					new_y.extend_u0(cell->parameters["\\Y_WIDTH"].as_int(), false);
					replace_cell(assign_map, module, cell, "isneq", "\\Y", new_y);
					goto next_cell;
				}
				if (a[i] == b[i])
					continue;
				new_a.append(a[i]);
				new_b.append(b[i]);
			}

			if (new_a.size() == 0) {
				cover_list("opt.opt_expr.eqneq.empty", "$eq", "$ne", "$eqx", "$nex", cell->type.str());
				RTLIL::SigSpec new_y = RTLIL::SigSpec((cell->type == "$eq" || cell->type == "$eqx") ?  RTLIL::State::S1 : RTLIL::State::S0);
				new_y.extend_u0(cell->parameters["\\Y_WIDTH"].as_int(), false);
				replace_cell(assign_map, module, cell, "empty", "\\Y", new_y);
				goto next_cell;
			}

			if (new_a.size() < a.size() || new_b.size() < b.size()) {
				cover_list("opt.opt_expr.eqneq.resize", "$eq", "$ne", "$eqx", "$nex", cell->type.str());
				cell->setPort("\\A", new_a);
				cell->setPort("\\B", new_b);
				cell->parameters["\\A_WIDTH"] = new_a.size();
				cell->parameters["\\B_WIDTH"] = new_b.size();
			}
		}

		if ((cell->type == "$eq" || cell->type == "$ne") && cell->parameters["\\Y_WIDTH"].as_int() == 1 &&
				cell->parameters["\\A_WIDTH"].as_int() == 1 && cell->parameters["\\B_WIDTH"].as_int() == 1)
		{
			RTLIL::SigSpec a = assign_map(cell->getPort("\\A"));
			RTLIL::SigSpec b = assign_map(cell->getPort("\\B"));

			if (a.is_fully_const() && !b.is_fully_const()) {
				cover_list("opt.opt_expr.eqneq.swapconst", "$eq", "$ne", cell->type.str());
				cell->setPort("\\A", b);
				cell->setPort("\\B", a);
				std::swap(a, b);
			}

			if (b.is_fully_const()) {
				if (b.as_bool() == (cell->type == "$eq")) {
					RTLIL::SigSpec input = b;
					ACTION_DO("\\Y", cell->getPort("\\A"));
				} else {
					cover_list("opt.opt_expr.eqneq.isnot", "$eq", "$ne", cell->type.str());
					log("Replacing %s cell `%s' in module `%s' with inverter.\n", log_id(cell->type), log_id(cell), log_id(module));
					cell->type = "$not";
					cell->parameters.erase("\\B_WIDTH");
					cell->parameters.erase("\\B_SIGNED");
					cell->unsetPort("\\B");
					did_something = true;
				}
				goto next_cell;
			}
		}

		if ((cell->type == "$eq" || cell->type == "$ne") &&
				(assign_map(cell->getPort("\\A")).is_fully_zero() || assign_map(cell->getPort("\\B")).is_fully_zero()))
		{
			cover_list("opt.opt_expr.eqneq.cmpzero", "$eq", "$ne", cell->type.str());
			log("Replacing %s cell `%s' in module `%s' with %s.\n", log_id(cell->type), log_id(cell),
					log_id(module), "$eq" ? "$logic_not" : "$reduce_bool");
			cell->type = cell->type == "$eq" ? "$logic_not" : "$reduce_bool";
			if (assign_map(cell->getPort("\\A")).is_fully_zero()) {
				cell->setPort("\\A", cell->getPort("\\B"));
				cell->setParam("\\A_SIGNED", cell->getParam("\\B_SIGNED"));
				cell->setParam("\\A_WIDTH", cell->getParam("\\B_WIDTH"));
			}
			cell->unsetPort("\\B");
			cell->unsetParam("\\B_SIGNED");
			cell->unsetParam("\\B_WIDTH");
			did_something = true;
			goto next_cell;
		}

		if (cell->type.in("$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx") && assign_map(cell->getPort("\\B")).is_fully_const())
		{
			bool sign_ext = cell->type == "$sshr" && cell->getParam("\\A_SIGNED").as_bool();
			int shift_bits = assign_map(cell->getPort("\\B")).as_int(cell->type.in("$shift", "$shiftx") && cell->getParam("\\B_SIGNED").as_bool());

			if (cell->type.in("$shl", "$sshl"))
				shift_bits *= -1;

			RTLIL::SigSpec sig_a = assign_map(cell->getPort("\\A"));
			RTLIL::SigSpec sig_y(cell->type == "$shiftx" ? RTLIL::State::Sx : RTLIL::State::S0, cell->getParam("\\Y_WIDTH").as_int());

			if (GetSize(sig_a) < GetSize(sig_y))
				sig_a.extend_u0(GetSize(sig_y), cell->getParam("\\A_SIGNED").as_bool());

			for (int i = 0; i < GetSize(sig_y); i++) {
				int idx = i + shift_bits;
				if (0 <= idx && idx < GetSize(sig_a))
					sig_y[i] = sig_a[idx];
				else if (GetSize(sig_a) <= idx && sign_ext)
					sig_y[i] = sig_a[GetSize(sig_a)-1];
			}

			cover_list("opt.opt_expr.constshift", "$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx", cell->type.str());

			log("Replacing %s cell `%s' (B=%s, SHR=%d) in module `%s' with fixed wiring: %s\n",
					log_id(cell->type), log_id(cell), log_signal(assign_map(cell->getPort("\\B"))), shift_bits, log_id(module), log_signal(sig_y));

			module->connect(cell->getPort("\\Y"), sig_y);
			module->remove(cell);

			did_something = true;
			goto next_cell;
		}

		if (!keepdc)
		{
			bool identity_wrt_a = false;
			bool identity_wrt_b = false;
			bool arith_inverse = false;

			if (cell->type == "$add" || cell->type == "$sub" || cell->type == "$or" || cell->type == "$xor")
			{
				RTLIL::SigSpec a = assign_map(cell->getPort("\\A"));
				RTLIL::SigSpec b = assign_map(cell->getPort("\\B"));

				if (cell->type != "$sub" && a.is_fully_const() && a.as_bool() == false)
					identity_wrt_b = true;

				if (b.is_fully_const() && b.as_bool() == false)
					identity_wrt_a = true;
			}

			if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr" || cell->type == "$shift" || cell->type == "$shiftx")
			{
				RTLIL::SigSpec b = assign_map(cell->getPort("\\B"));

				if (b.is_fully_const() && b.as_bool() == false)
					identity_wrt_a = true;
			}

			if (cell->type == "$mul")
			{
				RTLIL::SigSpec a = assign_map(cell->getPort("\\A"));
				RTLIL::SigSpec b = assign_map(cell->getPort("\\B"));

				if (a.is_fully_const() && is_one_or_minus_one(a.as_const(), cell->getParam("\\A_SIGNED").as_bool(), arith_inverse))
					identity_wrt_b = true;
				else
				if (b.is_fully_const() && is_one_or_minus_one(b.as_const(), cell->getParam("\\B_SIGNED").as_bool(), arith_inverse))
					identity_wrt_a = true;
			}

			if (cell->type == "$div")
			{
				RTLIL::SigSpec b = assign_map(cell->getPort("\\B"));

				if (b.is_fully_const() && b.size() <= 32 && b.as_int() == 1)
					identity_wrt_a = true;
			}

			if (identity_wrt_a || identity_wrt_b)
			{
				if (identity_wrt_a)
					cover_list("opt.opt_expr.identwrt.a", "$add", "$sub", "$or", "$xor", "$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx", "$mul", "$div", cell->type.str());
				if (identity_wrt_b)
					cover_list("opt.opt_expr.identwrt.b", "$add", "$sub", "$or", "$xor", "$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx", "$mul", "$div", cell->type.str());

				log("Replacing %s cell `%s' in module `%s' with identity for port %c.\n",
					cell->type.c_str(), cell->name.c_str(), module->name.c_str(), identity_wrt_a ? 'A' : 'B');

				if (!identity_wrt_a) {
					cell->setPort("\\A", cell->getPort("\\B"));
					cell->parameters.at("\\A_WIDTH") = cell->parameters.at("\\B_WIDTH");
					cell->parameters.at("\\A_SIGNED") = cell->parameters.at("\\B_SIGNED");
				}

				cell->type = arith_inverse ? "$neg" : "$pos";
				cell->unsetPort("\\B");
				cell->parameters.erase("\\B_WIDTH");
				cell->parameters.erase("\\B_SIGNED");
				cell->check();

				did_something = true;
				goto next_cell;
			}
		}

		if (mux_bool && (cell->type == "$mux" || cell->type == "$_MUX_") &&
				cell->getPort("\\A") == RTLIL::SigSpec(0, 1) && cell->getPort("\\B") == RTLIL::SigSpec(1, 1)) {
			cover_list("opt.opt_expr.mux_bool", "$mux", "$_MUX_", cell->type.str());
			replace_cell(assign_map, module, cell, "mux_bool", "\\Y", cell->getPort("\\S"));
			goto next_cell;
		}

		if (mux_bool && (cell->type == "$mux" || cell->type == "$_MUX_") &&
				cell->getPort("\\A") == RTLIL::SigSpec(1, 1) && cell->getPort("\\B") == RTLIL::SigSpec(0, 1)) {
			cover_list("opt.opt_expr.mux_invert", "$mux", "$_MUX_", cell->type.str());
			log("Replacing %s cell `%s' in module `%s' with inverter.\n", log_id(cell->type), log_id(cell), log_id(module));
			cell->setPort("\\A", cell->getPort("\\S"));
			cell->unsetPort("\\B");
			cell->unsetPort("\\S");
			if (cell->type == "$mux") {
				Const width = cell->parameters["\\WIDTH"];
				cell->parameters["\\A_WIDTH"] = width;
				cell->parameters["\\Y_WIDTH"] = width;
				cell->parameters["\\A_SIGNED"] = 0;
				cell->parameters.erase("\\WIDTH");
				cell->type = "$not";
			} else
				cell->type = "$_NOT_";
			did_something = true;
			goto next_cell;
		}

		if (consume_x && mux_bool && (cell->type == "$mux" || cell->type == "$_MUX_") && cell->getPort("\\A") == RTLIL::SigSpec(0, 1)) {
			cover_list("opt.opt_expr.mux_and", "$mux", "$_MUX_", cell->type.str());
			log("Replacing %s cell `%s' in module `%s' with and-gate.\n", log_id(cell->type), log_id(cell), log_id(module));
			cell->setPort("\\A", cell->getPort("\\S"));
			cell->unsetPort("\\S");
			if (cell->type == "$mux") {
				Const width = cell->parameters["\\WIDTH"];
				cell->parameters["\\A_WIDTH"] = width;
				cell->parameters["\\B_WIDTH"] = width;
				cell->parameters["\\Y_WIDTH"] = width;
				cell->parameters["\\A_SIGNED"] = 0;
				cell->parameters["\\B_SIGNED"] = 0;
				cell->parameters.erase("\\WIDTH");
				cell->type = "$and";
			} else
				cell->type = "$_AND_";
			did_something = true;
			goto next_cell;
		}

		if (consume_x && mux_bool && (cell->type == "$mux" || cell->type == "$_MUX_") && cell->getPort("\\B") == RTLIL::SigSpec(1, 1)) {
			cover_list("opt.opt_expr.mux_or", "$mux", "$_MUX_", cell->type.str());
			log("Replacing %s cell `%s' in module `%s' with or-gate.\n", log_id(cell->type), log_id(cell), log_id(module));
			cell->setPort("\\B", cell->getPort("\\S"));
			cell->unsetPort("\\S");
			if (cell->type == "$mux") {
				Const width = cell->parameters["\\WIDTH"];
				cell->parameters["\\A_WIDTH"] = width;
				cell->parameters["\\B_WIDTH"] = width;
				cell->parameters["\\Y_WIDTH"] = width;
				cell->parameters["\\A_SIGNED"] = 0;
				cell->parameters["\\B_SIGNED"] = 0;
				cell->parameters.erase("\\WIDTH");
				cell->type = "$or";
			} else
				cell->type = "$_OR_";
			did_something = true;
			goto next_cell;
		}

		if (mux_undef && (cell->type == "$mux" || cell->type == "$pmux")) {
			RTLIL::SigSpec new_a, new_b, new_s;
			int width = cell->getPort("\\A").size();
			if ((cell->getPort("\\A").is_fully_undef() && cell->getPort("\\B").is_fully_undef()) ||
					cell->getPort("\\S").is_fully_undef()) {
				cover_list("opt.opt_expr.mux_undef", "$mux", "$pmux", cell->type.str());
				replace_cell(assign_map, module, cell, "mux_undef", "\\Y", cell->getPort("\\A"));
				goto next_cell;
			}
			for (int i = 0; i < cell->getPort("\\S").size(); i++) {
				RTLIL::SigSpec old_b = cell->getPort("\\B").extract(i*width, width);
				RTLIL::SigSpec old_s = cell->getPort("\\S").extract(i, 1);
				if (old_b.is_fully_undef() || old_s.is_fully_undef())
					continue;
				new_b.append(old_b);
				new_s.append(old_s);
			}
			new_a = cell->getPort("\\A");
			if (new_a.is_fully_undef() && new_s.size() > 0) {
				new_a = new_b.extract((new_s.size()-1)*width, width);
				new_b = new_b.extract(0, (new_s.size()-1)*width);
				new_s = new_s.extract(0, new_s.size()-1);
			}
			if (new_s.size() == 0) {
				cover_list("opt.opt_expr.mux_empty", "$mux", "$pmux", cell->type.str());
				replace_cell(assign_map, module, cell, "mux_empty", "\\Y", new_a);
				goto next_cell;
			}
			if (new_a == RTLIL::SigSpec(RTLIL::State::S0) && new_b == RTLIL::SigSpec(RTLIL::State::S1)) {
				cover_list("opt.opt_expr.mux_sel01", "$mux", "$pmux", cell->type.str());
				replace_cell(assign_map, module, cell, "mux_sel01", "\\Y", new_s);
				goto next_cell;
			}
			if (cell->getPort("\\S").size() != new_s.size()) {
				cover_list("opt.opt_expr.mux_reduce", "$mux", "$pmux", cell->type.str());
				log("Optimized away %d select inputs of %s cell `%s' in module `%s'.\n",
						GetSize(cell->getPort("\\S")) - GetSize(new_s), log_id(cell->type), log_id(cell), log_id(module));
				cell->setPort("\\A", new_a);
				cell->setPort("\\B", new_b);
				cell->setPort("\\S", new_s);
				if (new_s.size() > 1) {
					cell->type = "$pmux";
					cell->parameters["\\S_WIDTH"] = new_s.size();
				} else {
					cell->type = "$mux";
					cell->parameters.erase("\\S_WIDTH");
				}
				did_something = true;
			}
		}

#define FOLD_1ARG_CELL(_t) \
		if (cell->type == "$" #_t) { \
			RTLIL::SigSpec a = cell->getPort("\\A"); \
			assign_map.apply(a); \
			if (a.is_fully_const()) { \
				RTLIL::Const dummy_arg(RTLIL::State::S0, 1); \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.as_const(), dummy_arg, \
						cell->parameters["\\A_SIGNED"].as_bool(), false, \
						cell->parameters["\\Y_WIDTH"].as_int())); \
				cover("opt.opt_expr.const.$" #_t); \
				replace_cell(assign_map, module, cell, stringf("%s", log_signal(a)), "\\Y", y); \
				goto next_cell; \
			} \
		}
#define FOLD_2ARG_CELL(_t) \
		if (cell->type == "$" #_t) { \
			RTLIL::SigSpec a = cell->getPort("\\A"); \
			RTLIL::SigSpec b = cell->getPort("\\B"); \
			assign_map.apply(a), assign_map.apply(b); \
			if (a.is_fully_const() && b.is_fully_const()) { \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.as_const(), b.as_const(), \
						cell->parameters["\\A_SIGNED"].as_bool(), \
						cell->parameters["\\B_SIGNED"].as_bool(), \
						cell->parameters["\\Y_WIDTH"].as_int())); \
				cover("opt.opt_expr.const.$" #_t); \
				replace_cell(assign_map, module, cell, stringf("%s, %s", log_signal(a), log_signal(b)), "\\Y", y); \
				goto next_cell; \
			} \
		}

		FOLD_1ARG_CELL(not)
		FOLD_2ARG_CELL(and)
		FOLD_2ARG_CELL(or)
		FOLD_2ARG_CELL(xor)
		FOLD_2ARG_CELL(xnor)

		FOLD_1ARG_CELL(reduce_and)
		FOLD_1ARG_CELL(reduce_or)
		FOLD_1ARG_CELL(reduce_xor)
		FOLD_1ARG_CELL(reduce_xnor)
		FOLD_1ARG_CELL(reduce_bool)

		FOLD_1ARG_CELL(logic_not)
		FOLD_2ARG_CELL(logic_and)
		FOLD_2ARG_CELL(logic_or)

		FOLD_2ARG_CELL(shl)
		FOLD_2ARG_CELL(shr)
		FOLD_2ARG_CELL(sshl)
		FOLD_2ARG_CELL(sshr)
		FOLD_2ARG_CELL(shift)
		FOLD_2ARG_CELL(shiftx)

		FOLD_2ARG_CELL(lt)
		FOLD_2ARG_CELL(le)
		FOLD_2ARG_CELL(eq)
		FOLD_2ARG_CELL(ne)
		FOLD_2ARG_CELL(gt)
		FOLD_2ARG_CELL(ge)

		FOLD_2ARG_CELL(add)
		FOLD_2ARG_CELL(sub)
		FOLD_2ARG_CELL(mul)
		FOLD_2ARG_CELL(div)
		FOLD_2ARG_CELL(mod)
		FOLD_2ARG_CELL(pow)

		FOLD_1ARG_CELL(pos)
		FOLD_1ARG_CELL(neg)

		// be very conservative with optimizing $mux cells as we do not want to break mux trees
		if (cell->type == "$mux") {
			RTLIL::SigSpec input = assign_map(cell->getPort("\\S"));
			RTLIL::SigSpec inA = assign_map(cell->getPort("\\A"));
			RTLIL::SigSpec inB = assign_map(cell->getPort("\\B"));
			if (input.is_fully_const())
				ACTION_DO("\\Y", input.as_bool() ? cell->getPort("\\B") : cell->getPort("\\A"));
			else if (inA == inB)
				ACTION_DO("\\Y", cell->getPort("\\A"));
		}

		if (!keepdc && cell->type == "$mul")
		{
			bool a_signed = cell->parameters["\\A_SIGNED"].as_bool();
			bool b_signed = cell->parameters["\\B_SIGNED"].as_bool();
			bool swapped_ab = false;

			RTLIL::SigSpec sig_a = assign_map(cell->getPort("\\A"));
			RTLIL::SigSpec sig_b = assign_map(cell->getPort("\\B"));
			RTLIL::SigSpec sig_y = assign_map(cell->getPort("\\Y"));

			if (sig_b.is_fully_const() && sig_b.size() <= 32)
				std::swap(sig_a, sig_b), std::swap(a_signed, b_signed), swapped_ab = true;

			if (sig_a.is_fully_def() && sig_a.size() <= 32)
			{
				int a_val = sig_a.as_int();

				if (a_val == 0)
				{
					cover("opt.opt_expr.mul_shift.zero");

					log("Replacing multiply-by-zero cell `%s' in module `%s' with zero-driver.\n",
							cell->name.c_str(), module->name.c_str());

					module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
					module->remove(cell);

					did_something = true;
					goto next_cell;
				}

				for (int i = 1; i < (a_signed ? sig_a.size()-1 : sig_a.size()); i++)
					if (a_val == (1 << i))
					{
						if (swapped_ab)
							cover("opt.opt_expr.mul_shift.swapped");
						else
							cover("opt.opt_expr.mul_shift.unswapped");

						log("Replacing multiply-by-%d cell `%s' in module `%s' with shift-by-%d.\n",
								a_val, cell->name.c_str(), module->name.c_str(), i);

						if (!swapped_ab) {
							cell->setPort("\\A", cell->getPort("\\B"));
							cell->parameters.at("\\A_WIDTH") = cell->parameters.at("\\B_WIDTH");
							cell->parameters.at("\\A_SIGNED") = cell->parameters.at("\\B_SIGNED");
						}

						std::vector<RTLIL::SigBit> new_b = RTLIL::SigSpec(i, 6);

						while (GetSize(new_b) > 1 && new_b.back() == RTLIL::State::S0)
							new_b.pop_back();

						cell->type = "$shl";
						cell->parameters["\\B_WIDTH"] = GetSize(new_b);
						cell->parameters["\\B_SIGNED"] = false;
						cell->setPort("\\B", new_b);
						cell->check();

						did_something = true;
						goto next_cell;
					}
			}
		}

		if (!keepdc && cell->type.in("$div", "$mod"))
		{
			bool b_signed = cell->parameters["\\B_SIGNED"].as_bool();
			SigSpec sig_b = assign_map(cell->getPort("\\B"));
			SigSpec sig_y = assign_map(cell->getPort("\\Y"));

			if (sig_b.is_fully_def() && sig_b.size() <= 32)
			{
				int b_val = sig_b.as_int();

				if (b_val == 0)
				{
					cover("opt.opt_expr.divmod_zero");

					log("Replacing divide-by-zero cell `%s' in module `%s' with undef-driver.\n",
							cell->name.c_str(), module->name.c_str());

					module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(State::Sx, sig_y.size())));
					module->remove(cell);

					did_something = true;
					goto next_cell;
				}

				for (int i = 1; i < (b_signed ? sig_b.size()-1 : sig_b.size()); i++)
					if (b_val == (1 << i))
					{
						if (cell->type == "$div")
						{
							cover("opt.opt_expr.div_shift");

							log("Replacing divide-by-%d cell `%s' in module `%s' with shift-by-%d.\n",
									b_val, cell->name.c_str(), module->name.c_str(), i);

							std::vector<RTLIL::SigBit> new_b = RTLIL::SigSpec(i, 6);

							while (GetSize(new_b) > 1 && new_b.back() == RTLIL::State::S0)
								new_b.pop_back();

							cell->type = "$shr";
							cell->parameters["\\B_WIDTH"] = GetSize(new_b);
							cell->parameters["\\B_SIGNED"] = false;
							cell->setPort("\\B", new_b);
							cell->check();
						}
						else
						{
							cover("opt.opt_expr.mod_mask");

							log("Replacing modulo-by-%d cell `%s' in module `%s' with bitmask.\n",
									b_val, cell->name.c_str(), module->name.c_str());

							std::vector<RTLIL::SigBit> new_b = RTLIL::SigSpec(State::S1, i);

							if (b_signed)
								new_b.push_back(State::S0);

							cell->type = "$and";
							cell->parameters["\\B_WIDTH"] = GetSize(new_b);
							cell->setPort("\\B", new_b);
							cell->check();
						}

						did_something = true;
						goto next_cell;
					}
			}
		}

	next_cell:;
#undef ACTION_DO
#undef ACTION_DO_Y
#undef FOLD_1ARG_CELL
#undef FOLD_2ARG_CELL
	}
}

struct OptExprPass : public Pass {
	OptExprPass() : Pass("opt_expr", "perform const folding and simple expression rewriting") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_expr [options] [selection]\n");
		log("\n");
		log("This pass performs const folding on internal cell types with constant inputs.\n");
		log("It also performs some simple expression rewritring.\n");
		log("\n");
		log("    -mux_undef\n");
		log("        remove 'undef' inputs from $mux, $pmux and $_MUX_ cells\n");
		log("\n");
		log("    -mux_bool\n");
		log("        replace $mux cells with inverters or buffers when possible\n");
		log("\n");
		log("    -undriven\n");
		log("        replace undriven nets with undef (x) constants\n");
		log("\n");
		log("    -clkinv\n");
		log("        optimize clock inverters by changing FF types\n");
		log("\n");
		log("    -fine\n");
		log("        perform fine-grain optimizations\n");
		log("\n");
		log("    -full\n");
		log("        alias for -mux_undef -mux_bool -undriven -fine\n");
		log("\n");
		log("    -keepdc\n");
		log("        some optimizations change the behavior of the circuit with respect to\n");
		log("        don't-care bits. for example in 'a+0' a single x-bit in 'a' will cause\n");
		log("        all result bits to be set to x. this behavior changes when 'a+0' is\n");
		log("        replaced by 'a'. the -keepdc option disables all such optimizations.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool mux_undef = false;
		bool mux_bool = false;
		bool undriven = false;
		bool clkinv = false;
		bool do_fine = false;
		bool keepdc = false;

		log_header(design, "Executing OPT_EXPR pass (perform const folding).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-mux_undef") {
				mux_undef = true;
				continue;
			}
			if (args[argidx] == "-mux_bool") {
				mux_bool = true;
				continue;
			}
			if (args[argidx] == "-undriven") {
				undriven = true;
				continue;
			}
			if (args[argidx] == "-clkinv") {
				clkinv = true;
				continue;
			}
			if (args[argidx] == "-fine") {
				do_fine = true;
				continue;
			}
			if (args[argidx] == "-full") {
				mux_undef = true;
				mux_bool = true;
				undriven = true;
				do_fine = true;
				continue;
			}
			if (args[argidx] == "-keepdc") {
				keepdc = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			if (undriven)
				replace_undriven(design, module);

			do {
				do {
					did_something = false;
					replace_const_cells(design, module, false, mux_undef, mux_bool, do_fine, keepdc, clkinv);
					if (did_something)
						design->scratchpad_set_bool("opt.did_something", true);
				} while (did_something);
				replace_const_cells(design, module, true, mux_undef, mux_bool, do_fine, keepdc, clkinv);
			} while (did_something);
		}

		log_pop();
	}
} OptExprPass;

PRIVATE_NAMESPACE_END
