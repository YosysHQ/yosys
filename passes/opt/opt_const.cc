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

#include "opt_status.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <algorithm>

static bool did_something;

static void replace_undriven(RTLIL::Design *design, RTLIL::Module *module)
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
		OPT_DID_SOMETHING = true;
	}
}

static void replace_cell(RTLIL::Module *module, RTLIL::Cell *cell, std::string info, std::string out_port, RTLIL::SigSpec out_val)
{
	RTLIL::SigSpec Y = cell->get(out_port);
	out_val.extend_u0(Y.size(), false);

	log("Replacing %s cell `%s' (%s) in module `%s' with constant driver `%s = %s'.\n",
			cell->type.c_str(), cell->name.c_str(), info.c_str(),
			module->name.c_str(), log_signal(Y), log_signal(out_val));
	// ILANG_BACKEND::dump_cell(stderr, "--> ", cell);
	module->connect(RTLIL::SigSig(Y, out_val));
	module->remove(cell);
	OPT_DID_SOMETHING = true;
	did_something = true;
}

static bool group_cell_inputs(RTLIL::Module *module, RTLIL::Cell *cell, bool commutative, bool extend_u0, SigMap &sigmap)
{
	std::string b_name = cell->has("\\B") ? "\\B" : "\\A";

	bool a_signed = cell->parameters.at("\\A_SIGNED").as_bool();
	bool b_signed = cell->parameters.at(b_name + "_SIGNED").as_bool();

	RTLIL::SigSpec sig_a = sigmap(cell->get("\\A"));
	RTLIL::SigSpec sig_b = sigmap(cell->get(b_name));
	RTLIL::SigSpec sig_y = sigmap(cell->get("\\Y"));

	if (extend_u0) {
		sig_a.extend_u0(sig_y.size(), a_signed);
		sig_b.extend_u0(sig_y.size(), b_signed);
	} else {
		sig_a.extend(sig_y.size(), a_signed);
		sig_b.extend(sig_y.size(), b_signed);
	}

	std::vector<RTLIL::SigBit> bits_a = sig_a, bits_b = sig_b, bits_y = sig_y;

	enum { GRP_DYN, GRP_CONST_A, GRP_CONST_B, GRP_CONST_AB, GRP_N };
	std::map<std::pair<RTLIL::SigBit, RTLIL::SigBit>, std::set<RTLIL::SigBit>> grouped_bits[GRP_N];

	for (int i = 0; i < SIZE(bits_y); i++)
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
		if (SIZE(grouped_bits[i]) == SIZE(bits_y))
			return false;

	log("Replacing %s cell `%s' in module `%s' with cells using grouped bits:\n",
			log_id(cell->type), log_id(cell), log_id(module));

	for (int i = 0; i < GRP_N; i++)
	{
		if (grouped_bits[i].empty())
			continue;

		RTLIL::Wire *new_y = module->addWire(NEW_ID, SIZE(grouped_bits[i]));
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

		c->set("\\A", new_a);
		c->parameters["\\A_WIDTH"] = new_a.size();
		c->parameters["\\A_SIGNED"] = false;

		if (b_name == "\\B") {
			c->set("\\B", new_b);
			c->parameters["\\B_WIDTH"] = new_b.size();
			c->parameters["\\B_SIGNED"] = false;
		}

		c->set("\\Y", new_y);
		c->parameters["\\Y_WIDTH"] = new_y->width;
		c->check();

		module->connect(new_conn);

		log("  New cell `%s': A=%s", log_id(c), log_signal(new_a));
		if (b_name == "\\B")
			log(", B=%s", log_signal(new_b));
		log("\n");
	}

	cover_list("opt.opt_const.fine.group", "$not", "$pos", "$bu0", "$and", "$or", "$xor", "$xnor", cell->type);

	module->remove(cell);
	OPT_DID_SOMETHING = true;
	did_something = true;
	return true;
}

static void replace_const_cells(RTLIL::Design *design, RTLIL::Module *module, bool consume_x, bool mux_undef, bool mux_bool, bool do_fine, bool keepdc)
{
	if (!design->selected(module))
		return;

	SigMap assign_map(module);
	std::map<RTLIL::SigSpec, RTLIL::SigSpec> invert_map;

	std::vector<RTLIL::Cell*> cells;
	cells.reserve(module->cells_.size());
	for (auto &cell_it : module->cells_)
		if (design->selected(module, cell_it.second)) {
			if ((cell_it.second->type == "$_INV_" || cell_it.second->type == "$not" || cell_it.second->type == "$logic_not") &&
					cell_it.second->get("\\A").size() == 1 && cell_it.second->get("\\Y").size() == 1)
				invert_map[assign_map(cell_it.second->get("\\Y"))] = assign_map(cell_it.second->get("\\A"));
			cells.push_back(cell_it.second);
		}

	for (auto cell : cells)
	{
#define ACTION_DO(_p_, _s_) do { cover("opt.opt_const.action_" S__LINE__); replace_cell(module, cell, input.as_string(), _p_, _s_); goto next_cell; } while (0)
#define ACTION_DO_Y(_v_) ACTION_DO("\\Y", RTLIL::SigSpec(RTLIL::State::S ## _v_))

		if (do_fine)
		{
			if (cell->type == "$not" || cell->type == "$pos" || cell->type == "$bu0" ||
					cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor")
				if (group_cell_inputs(module, cell, true, cell->type != "$pos", assign_map))
					goto next_cell;

			if (cell->type == "$reduce_and")
			{
				RTLIL::SigSpec sig_a = assign_map(cell->get("\\A"));

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
					cover("opt.opt_const.fine.$reduce_and");
					log("Replacing port A of %s cell `%s' in module `%s' with constant driver: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->name.c_str(), log_signal(sig_a), log_signal(new_a));
					cell->set("\\A", sig_a = new_a);
					cell->parameters.at("\\A_WIDTH") = 1;
					OPT_DID_SOMETHING = true;
					did_something = true;
				}
			}

			if (cell->type == "$logic_not" || cell->type == "$logic_and" || cell->type == "$logic_or" || cell->type == "$reduce_or" || cell->type == "$reduce_bool")
			{
				RTLIL::SigSpec sig_a = assign_map(cell->get("\\A"));

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
					cover_list("opt.opt_const.fine.A", "$logic_not", "$logic_and", "$logic_or", "$reduce_or", "$reduce_bool", cell->type);
					log("Replacing port A of %s cell `%s' in module `%s' with constant driver: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->name.c_str(), log_signal(sig_a), log_signal(new_a));
					cell->set("\\A", sig_a = new_a);
					cell->parameters.at("\\A_WIDTH") = 1;
					OPT_DID_SOMETHING = true;
					did_something = true;
				}
			}

			if (cell->type == "$logic_and" || cell->type == "$logic_or")
			{
				RTLIL::SigSpec sig_b = assign_map(cell->get("\\B"));

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
					cover_list("opt.opt_const.fine.B", "$logic_and", "$logic_or", cell->type);
					log("Replacing port B of %s cell `%s' in module `%s' with constant driver: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->name.c_str(), log_signal(sig_b), log_signal(new_b));
					cell->set("\\B", sig_b = new_b);
					cell->parameters.at("\\B_WIDTH") = 1;
					OPT_DID_SOMETHING = true;
					did_something = true;
				}
			}
		}

		if (cell->type == "$logic_or" && (assign_map(cell->get("\\A")) == RTLIL::State::S1 || assign_map(cell->get("\\B")) == RTLIL::State::S1)) {
			cover("opt.opt_const.one_high");
			replace_cell(module, cell, "one high", "\\Y", RTLIL::State::S1);
			goto next_cell;
		}

		if (cell->type == "$logic_and" && (assign_map(cell->get("\\A")) == RTLIL::State::S0 || assign_map(cell->get("\\B")) == RTLIL::State::S0)) {
			cover("opt.opt_const.one_low");
			replace_cell(module, cell, "one low", "\\Y", RTLIL::State::S0);
			goto next_cell;
		}

		if (cell->type == "$reduce_xor" || cell->type == "$reduce_xnor" ||
				cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr" ||
				cell->type == "$lt" || cell->type == "$le" || cell->type == "$ge" || cell->type == "$gt" ||
				cell->type == "$neg" || cell->type == "$add" || cell->type == "$sub" ||
				cell->type == "$mul" || cell->type == "$div" || cell->type == "$mod" || cell->type == "$pow")
		{
			RTLIL::SigSpec sig_a = assign_map(cell->get("\\A"));
			RTLIL::SigSpec sig_b = cell->has("\\B") ? assign_map(cell->get("\\B")) : RTLIL::SigSpec();

			if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr")
				sig_a = RTLIL::SigSpec();

			for (auto &bit : sig_a.to_sigbit_vector())
				if (bit == RTLIL::State::Sx)
					goto found_the_x_bit;

			for (auto &bit : sig_b.to_sigbit_vector())
				if (bit == RTLIL::State::Sx)
					goto found_the_x_bit;

			if (0) {
		found_the_x_bit:
				cover_list("opt.opt_const.xbit", "$reduce_xor", "$reduce_xnor", "$shl", "$shr", "$sshl", "$sshr", "$lt", "$le", "$ge", "$gt",
						"$neg", "$add", "$sub", "$mul", "$div", "$mod", "$pow", cell->type);
				if (cell->type == "$reduce_xor" || cell->type == "$reduce_xnor" ||
						cell->type == "$lt" || cell->type == "$le" || cell->type == "$ge" || cell->type == "$gt")
					replace_cell(module, cell, "x-bit in input", "\\Y", RTLIL::State::Sx);
				else
					replace_cell(module, cell, "x-bit in input", "\\Y", RTLIL::SigSpec(RTLIL::State::Sx, cell->get("\\Y").size()));
				goto next_cell;
			}
		}

		if ((cell->type == "$_INV_" || cell->type == "$not" || cell->type == "$logic_not") && cell->get("\\Y").size() == 1 &&
				invert_map.count(assign_map(cell->get("\\A"))) != 0) {
			cover_list("opt.opt_const.invert.double", "$_INV_", "$not", "$logic_not", cell->type);
			replace_cell(module, cell, "double_invert", "\\Y", invert_map.at(assign_map(cell->get("\\A"))));
			goto next_cell;
		}

		if ((cell->type == "$_MUX_" || cell->type == "$mux") && invert_map.count(assign_map(cell->get("\\S"))) != 0) {
			cover_list("opt.opt_const.invert.muxsel", "$_MUX_", "$mux", cell->type);
			RTLIL::SigSpec tmp = cell->get("\\A");
			cell->set("\\A", cell->get("\\B"));
			cell->set("\\B", tmp);
			cell->set("\\S", invert_map.at(assign_map(cell->get("\\S"))));
			OPT_DID_SOMETHING = true;
			did_something = true;
			goto next_cell;
		}

		if (cell->type == "$_INV_") {
			RTLIL::SigSpec input = cell->get("\\A");
			assign_map.apply(input);
			if (input.match("1")) ACTION_DO_Y(0);
			if (input.match("0")) ACTION_DO_Y(1);
			if (input.match("*")) ACTION_DO_Y(x);
		}

		if (cell->type == "$_AND_") {
			RTLIL::SigSpec input;
			input.append(cell->get("\\B"));
			input.append(cell->get("\\A"));
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
			input.append(cell->get("\\B"));
			input.append(cell->get("\\A"));
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
			input.append(cell->get("\\B"));
			input.append(cell->get("\\A"));
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
			input.append(cell->get("\\S"));
			input.append(cell->get("\\B"));
			input.append(cell->get("\\A"));
			assign_map.apply(input);
			if (input.extract(2, 1) == input.extract(1, 1))
				ACTION_DO("\\Y", input.extract(2, 1));
			if (input.match("  0")) ACTION_DO("\\Y", input.extract(2, 1));
			if (input.match("  1")) ACTION_DO("\\Y", input.extract(1, 1));
			if (input.match("01 ")) ACTION_DO("\\Y", input.extract(0, 1));
			if (input.match("10 ")) {
				cover("opt.opt_const.mux_to_inv");
				cell->type = "$_INV_";
				cell->set("\\A", input.extract(0, 1));
				cell->unset("\\B");
				cell->unset("\\S");
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
			RTLIL::SigSpec a = cell->get("\\A");
			RTLIL::SigSpec b = cell->get("\\B");

			if (cell->parameters["\\A_WIDTH"].as_int() != cell->parameters["\\B_WIDTH"].as_int()) {
				int width = std::max(cell->parameters["\\A_WIDTH"].as_int(), cell->parameters["\\B_WIDTH"].as_int());
				a.extend_u0(width, cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool());
				b.extend_u0(width, cell->parameters["\\A_SIGNED"].as_bool() && cell->parameters["\\B_SIGNED"].as_bool());
			}

			RTLIL::SigSpec new_a, new_b;

			assert(SIZE(a) == SIZE(b));
			for (int i = 0; i < SIZE(a); i++) {
				if (a[i].wire == NULL && b[i].wire == NULL && a[i] != b[i] && a[i].data <= RTLIL::State::S1 && b[i].data <= RTLIL::State::S1) {
					cover_list("opt.opt_const.eqneq.isneq", "$eq", "$ne", "$eqx", "$nex", cell->type);
					RTLIL::SigSpec new_y = RTLIL::SigSpec((cell->type == "$eq" || cell->type == "$eqx") ?  RTLIL::State::S0 : RTLIL::State::S1);
					new_y.extend(cell->parameters["\\Y_WIDTH"].as_int(), false);
					replace_cell(module, cell, "isneq", "\\Y", new_y);
					goto next_cell;
				}
				if (a[i] == b[i])
					continue;
				new_a.append(a[i]);
				new_b.append(b[i]);
			}

			if (new_a.size() == 0) {
				cover_list("opt.opt_const.eqneq.empty", "$eq", "$ne", "$eqx", "$nex", cell->type);
				RTLIL::SigSpec new_y = RTLIL::SigSpec((cell->type == "$eq" || cell->type == "$eqx") ?  RTLIL::State::S1 : RTLIL::State::S0);
				new_y.extend(cell->parameters["\\Y_WIDTH"].as_int(), false);
				replace_cell(module, cell, "empty", "\\Y", new_y);
				goto next_cell;
			}

			if (new_a.size() < a.size() || new_b.size() < b.size()) {
				cover_list("opt.opt_const.eqneq.resize", "$eq", "$ne", "$eqx", "$nex", cell->type);
				cell->set("\\A", new_a);
				cell->set("\\B", new_b);
				cell->parameters["\\A_WIDTH"] = new_a.size();
				cell->parameters["\\B_WIDTH"] = new_b.size();
			}
		}

		if ((cell->type == "$eq" || cell->type == "$ne") && cell->parameters["\\Y_WIDTH"].as_int() == 1 &&
				cell->parameters["\\A_WIDTH"].as_int() == 1 && cell->parameters["\\B_WIDTH"].as_int() == 1)
		{
			RTLIL::SigSpec a = assign_map(cell->get("\\A"));
			RTLIL::SigSpec b = assign_map(cell->get("\\B"));

			if (a.is_fully_const()) {
				cover_list("opt.opt_const.eqneq.swapconst", "$eq", "$ne", cell->type);
				RTLIL::SigSpec tmp = cell->get("\\A");
				cell->set("\\A", cell->get("\\B"));
				cell->set("\\B", tmp);
			}

			if (b.is_fully_const()) {
				if (b.as_bool() == (cell->type == "$eq")) {
					RTLIL::SigSpec input = b;
					ACTION_DO("\\Y", cell->get("\\A"));
				} else {
					cover_list("opt.opt_const.eqneq.isnot", "$eq", "$ne", cell->type);
					cell->type = "$not";
					cell->parameters.erase("\\B_WIDTH");
					cell->parameters.erase("\\B_SIGNED");
					cell->unset("\\B");
				}
				goto next_cell;
			}
		}

		if (!keepdc)
		{
			bool identity_bu0 = false;
			bool identity_wrt_a = false;
			bool identity_wrt_b = false;

			if (cell->type == "$add" || cell->type == "$sub" || cell->type == "$or" || cell->type == "$xor")
			{
				RTLIL::SigSpec a = assign_map(cell->get("\\A"));
				RTLIL::SigSpec b = assign_map(cell->get("\\B"));

				if (cell->type != "$sub" && a.is_fully_const() && a.as_bool() == false)
					identity_wrt_b = true;

				if (b.is_fully_const() && b.as_bool() == false)
					identity_wrt_a = true;
			}

			if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr")
			{
				RTLIL::SigSpec b = assign_map(cell->get("\\B"));

				if (b.is_fully_const() && b.as_bool() == false)
					identity_wrt_a = true, identity_bu0 = true;
			}

			if (cell->type == "$mul")
			{
				RTLIL::SigSpec a = assign_map(cell->get("\\A"));
				RTLIL::SigSpec b = assign_map(cell->get("\\B"));

				if (a.is_fully_const() && a.size() <= 32 && a.as_int() == 1)
					identity_wrt_b = true;

				if (b.is_fully_const() && b.size() <= 32 && b.as_int() == 1)
					identity_wrt_a = true;
			}

			if (cell->type == "$div")
			{
				RTLIL::SigSpec b = assign_map(cell->get("\\B"));

				if (b.is_fully_const() && b.size() <= 32 && b.as_int() == 1)
					identity_wrt_a = true;
			}

			if (identity_wrt_a || identity_wrt_b)
			{
				if (identity_wrt_a)
					cover_list("opt.opt_const.identwrt.a", "$add", "$sub", "$or", "$xor", "$shl", "$shr", "$sshl", "$sshr", "$mul", "$div", cell->type);
				if (identity_wrt_b)
					cover_list("opt.opt_const.identwrt.b", "$add", "$sub", "$or", "$xor", "$shl", "$shr", "$sshl", "$sshr", "$mul", "$div", cell->type);

				log("Replacing %s cell `%s' in module `%s' with identity for port %c.\n",
					cell->type.c_str(), cell->name.c_str(), module->name.c_str(), identity_wrt_a ? 'A' : 'B');

				if (!identity_wrt_a) {
					cell->set("\\A", cell->get("\\B"));
					cell->parameters.at("\\A_WIDTH") = cell->parameters.at("\\B_WIDTH");
					cell->parameters.at("\\A_SIGNED") = cell->parameters.at("\\B_SIGNED");
				}

				cell->type = identity_bu0 ? "$bu0" : "$pos";
				cell->unset("\\B");
				cell->parameters.erase("\\B_WIDTH");
				cell->parameters.erase("\\B_SIGNED");
				cell->check();

				OPT_DID_SOMETHING = true;
				did_something = true;
				goto next_cell;
			}
		}

		if (mux_bool && (cell->type == "$mux" || cell->type == "$_MUX_") &&
				cell->get("\\A") == RTLIL::SigSpec(0, 1) && cell->get("\\B") == RTLIL::SigSpec(1, 1)) {
			cover_list("opt.opt_const.mux_bool", "$mux", "$_MUX_", cell->type);
			replace_cell(module, cell, "mux_bool", "\\Y", cell->get("\\S"));
			goto next_cell;
		}

		if (mux_bool && (cell->type == "$mux" || cell->type == "$_MUX_") &&
				cell->get("\\A") == RTLIL::SigSpec(1, 1) && cell->get("\\B") == RTLIL::SigSpec(0, 1)) {
			cover_list("opt.opt_const.mux_invert", "$mux", "$_MUX_", cell->type);
			cell->set("\\A", cell->get("\\S"));
			cell->unset("\\B");
			cell->unset("\\S");
			if (cell->type == "$mux") {
				cell->parameters["\\A_WIDTH"] = cell->parameters["\\WIDTH"];
				cell->parameters["\\Y_WIDTH"] = cell->parameters["\\WIDTH"];
				cell->parameters["\\A_SIGNED"] = 0;
				cell->parameters.erase("\\WIDTH");
				cell->type = "$not";
			} else
				cell->type = "$_INV_";
			OPT_DID_SOMETHING = true;
			did_something = true;
			goto next_cell;
		}

		if (consume_x && mux_bool && (cell->type == "$mux" || cell->type == "$_MUX_") && cell->get("\\A") == RTLIL::SigSpec(0, 1)) {
			cover_list("opt.opt_const.mux_and", "$mux", "$_MUX_", cell->type);
			cell->set("\\A", cell->get("\\S"));
			cell->unset("\\S");
			if (cell->type == "$mux") {
				cell->parameters["\\A_WIDTH"] = cell->parameters["\\WIDTH"];
				cell->parameters["\\B_WIDTH"] = cell->parameters["\\WIDTH"];
				cell->parameters["\\Y_WIDTH"] = cell->parameters["\\WIDTH"];
				cell->parameters["\\A_SIGNED"] = 0;
				cell->parameters["\\B_SIGNED"] = 0;
				cell->parameters.erase("\\WIDTH");
				cell->type = "$and";
			} else
				cell->type = "$_AND_";
			OPT_DID_SOMETHING = true;
			did_something = true;
			goto next_cell;
		}

		if (consume_x && mux_bool && (cell->type == "$mux" || cell->type == "$_MUX_") && cell->get("\\B") == RTLIL::SigSpec(1, 1)) {
			cover_list("opt.opt_const.mux_or", "$mux", "$_MUX_", cell->type);
			cell->set("\\B", cell->get("\\S"));
			cell->unset("\\S");
			if (cell->type == "$mux") {
				cell->parameters["\\A_WIDTH"] = cell->parameters["\\WIDTH"];
				cell->parameters["\\B_WIDTH"] = cell->parameters["\\WIDTH"];
				cell->parameters["\\Y_WIDTH"] = cell->parameters["\\WIDTH"];
				cell->parameters["\\A_SIGNED"] = 0;
				cell->parameters["\\B_SIGNED"] = 0;
				cell->parameters.erase("\\WIDTH");
				cell->type = "$or";
			} else
				cell->type = "$_OR_";
			OPT_DID_SOMETHING = true;
			did_something = true;
			goto next_cell;
		}

		if (mux_undef && (cell->type == "$mux" || cell->type == "$pmux")) {
			RTLIL::SigSpec new_a, new_b, new_s;
			int width = cell->get("\\A").size();
			if ((cell->get("\\A").is_fully_undef() && cell->get("\\B").is_fully_undef()) ||
					cell->get("\\S").is_fully_undef()) {
				cover_list("opt.opt_const.mux_undef", "$mux", "$pmux", cell->type);
				replace_cell(module, cell, "mux_undef", "\\Y", cell->get("\\A"));
				goto next_cell;
			}
			for (int i = 0; i < cell->get("\\S").size(); i++) {
				RTLIL::SigSpec old_b = cell->get("\\B").extract(i*width, width);
				RTLIL::SigSpec old_s = cell->get("\\S").extract(i, 1);
				if (old_b.is_fully_undef() || old_s.is_fully_undef())
					continue;
				new_b.append(old_b);
				new_s.append(old_s);
			}
			new_a = cell->get("\\A");
			if (new_a.is_fully_undef() && new_s.size() > 0) {
				new_a = new_b.extract((new_s.size()-1)*width, width);
				new_b = new_b.extract(0, (new_s.size()-1)*width);
				new_s = new_s.extract(0, new_s.size()-1);
			}
			if (new_s.size() == 0) {
				cover_list("opt.opt_const.mux_empty", "$mux", "$pmux", cell->type);
				replace_cell(module, cell, "mux_empty", "\\Y", new_a);
				goto next_cell;
			}
			if (new_a == RTLIL::SigSpec(RTLIL::State::S0) && new_b == RTLIL::SigSpec(RTLIL::State::S1)) {
				cover_list("opt.opt_const.mux_sel01", "$mux", "$pmux", cell->type);
				replace_cell(module, cell, "mux_sel01", "\\Y", new_s);
				goto next_cell;
			}
			if (cell->get("\\S").size() != new_s.size()) {
				cover_list("opt.opt_const.mux_reduce", "$mux", "$pmux", cell->type);
				cell->set("\\A", new_a);
				cell->set("\\B", new_b);
				cell->set("\\S", new_s);
				if (new_s.size() > 1) {
					cell->type = "$pmux";
					cell->parameters["\\S_WIDTH"] = new_s.size();
				} else {
					cell->type = "$mux";
					cell->parameters.erase("\\S_WIDTH");
				}
				OPT_DID_SOMETHING = true;
				did_something = true;
			}
		}

#define FOLD_1ARG_CELL(_t) \
		if (cell->type == "$" #_t) { \
			RTLIL::SigSpec a = cell->get("\\A"); \
			assign_map.apply(a); \
			if (a.is_fully_const()) { \
				RTLIL::Const dummy_arg(RTLIL::State::S0, 1); \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.as_const(), dummy_arg, \
						cell->parameters["\\A_SIGNED"].as_bool(), false, \
						cell->parameters["\\Y_WIDTH"].as_int())); \
				cover("opt.opt_const.const.$" #_t); \
				replace_cell(module, cell, stringf("%s", log_signal(a)), "\\Y", y); \
				goto next_cell; \
			} \
		}
#define FOLD_2ARG_CELL(_t) \
		if (cell->type == "$" #_t) { \
			RTLIL::SigSpec a = cell->get("\\A"); \
			RTLIL::SigSpec b = cell->get("\\B"); \
			assign_map.apply(a), assign_map.apply(b); \
			if (a.is_fully_const() && b.is_fully_const()) { \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.as_const(), b.as_const(), \
						cell->parameters["\\A_SIGNED"].as_bool(), \
						cell->parameters["\\B_SIGNED"].as_bool(), \
						cell->parameters["\\Y_WIDTH"].as_int())); \
				cover("opt.opt_const.const.$" #_t); \
				replace_cell(module, cell, stringf("%s, %s", log_signal(a), log_signal(b)), "\\Y", y); \
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
		FOLD_1ARG_CELL(bu0)
		FOLD_1ARG_CELL(neg)

		// be very conservative with optimizing $mux cells as we do not want to break mux trees
		if (cell->type == "$mux") {
			RTLIL::SigSpec input = assign_map(cell->get("\\S"));
			RTLIL::SigSpec inA = assign_map(cell->get("\\A"));
			RTLIL::SigSpec inB = assign_map(cell->get("\\B"));
			if (input.is_fully_const())
				ACTION_DO("\\Y", input.as_bool() ? cell->get("\\B") : cell->get("\\A"));
			else if (inA == inB)
				ACTION_DO("\\Y", cell->get("\\A"));
		}

		if (!keepdc && cell->type == "$mul")
		{
			bool a_signed = cell->parameters["\\A_SIGNED"].as_bool();
			bool b_signed = cell->parameters["\\B_SIGNED"].as_bool();
			bool swapped_ab = false;

			RTLIL::SigSpec sig_a = assign_map(cell->get("\\A"));
			RTLIL::SigSpec sig_b = assign_map(cell->get("\\B"));
			RTLIL::SigSpec sig_y = assign_map(cell->get("\\Y"));

			if (sig_b.is_fully_const() && sig_b.size() <= 32)
				std::swap(sig_a, sig_b), std::swap(a_signed, b_signed), swapped_ab = true;

			if (sig_a.is_fully_def() && sig_a.size() <= 32)
			{
				int a_val = sig_a.as_int();

				if (a_val == 0)
				{
					cover("opt.opt_const.mul_shift.zero");

					log("Replacing multiply-by-zero cell `%s' in module `%s' with zero-driver.\n",
							cell->name.c_str(), module->name.c_str());

					module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
					module->remove(cell);

					OPT_DID_SOMETHING = true;
					did_something = true;
					goto next_cell;
				}

				for (int i = 1; i < (a_signed ? sig_a.size()-1 : sig_a.size()); i++)
					if (a_val == (1 << i))
					{
						if (swapped_ab)
							cover("opt.opt_const.mul_shift.swapped");
						else
							cover("opt.opt_const.mul_shift.unswapped");

						log("Replacing multiply-by-%d cell `%s' in module `%s' with shift-by-%d.\n",
								a_val, cell->name.c_str(), module->name.c_str(), i);

						if (!swapped_ab) {
							cell->set("\\A", cell->get("\\B"));
							cell->parameters["\\A_WIDTH"] = cell->parameters["\\B_WIDTH"];
							cell->parameters["\\A_SIGNED"] = cell->parameters["\\B_SIGNED"];
						}

						std::vector<RTLIL::SigBit> new_b = RTLIL::SigSpec(i, 6);

						while (SIZE(new_b) > 1 && new_b.back() == RTLIL::State::S0)
							new_b.pop_back();

						cell->type = "$shl";
						cell->parameters["\\B_WIDTH"] = SIZE(new_b);
						cell->parameters["\\B_SIGNED"] = false;
						cell->set("\\B", new_b);
						cell->check();

						OPT_DID_SOMETHING = true;
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

struct OptConstPass : public Pass {
	OptConstPass() : Pass("opt_const", "perform const folding") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_const [options] [selection]\n");
		log("\n");
		log("This pass performs const folding on internal cell types with constant inputs.\n");
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
		log("    -keepdc\n");
		log("        some optimizations change the behavior of the circuit with respect to\n");
		log("        don't-care bits. for example in 'a+0' a single x-bit in 'a' will cause\n");
		log("        all result bits to be set to x. this behavior changes when 'a+0' is\n");
		log("        replaced by 'a'. the -keepdc option disables all such optimizations.\n");
		log("\n");
		log("    -fine\n");
		log("        perform fine-grain optimizations\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool mux_undef = false;
		bool mux_bool = false;
		bool undriven = false;
		bool do_fine = false;
		bool keepdc = false;

		log_header("Executing OPT_CONST pass (perform const folding).\n");
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
			if (args[argidx] == "-fine") {
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

		for (auto &mod_it : design->modules_)
		{
			if (undriven)
				replace_undriven(design, mod_it.second);

			do {
				do {
					did_something = false;
					replace_const_cells(design, mod_it.second, false, mux_undef, mux_bool, do_fine, keepdc);
				} while (did_something);
				replace_const_cells(design, mod_it.second, true, mux_undef, mux_bool, do_fine, keepdc);
			} while (did_something);
		}

		log_pop();
	}
} OptConstPass;

