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

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/celltypes.h"
#include "fsmdata.h"
#include <string.h>

static void implement_pattern_cache(RTLIL::Module *module, std::map<RTLIL::Const, std::set<int>> &pattern_cache, std::set<int> &fullstate_cache, int num_states, RTLIL::Wire *state_onehot, RTLIL::SigSpec &ctrl_in, RTLIL::SigSpec output)
{
	RTLIL::SigSpec cases_vector;

	for (int in_state : fullstate_cache)
		cases_vector.append(RTLIL::SigSpec(state_onehot, in_state));

	for (auto &it : pattern_cache)
	{
		RTLIL::Const pattern = it.first;
		RTLIL::SigSpec eq_sig_a, eq_sig_b, or_sig;

		for (size_t j = 0; j < pattern.bits.size(); j++)
			if (pattern.bits[j] == RTLIL::State::S0 || pattern.bits[j] == RTLIL::State::S1) {
				eq_sig_a.append(ctrl_in.extract(j, 1));
				eq_sig_b.append(RTLIL::SigSpec(pattern.bits[j]));
			}

		for (int in_state : it.second)
			if (fullstate_cache.count(in_state) == 0)
				or_sig.append(RTLIL::SigSpec(state_onehot, in_state));

		if (or_sig.size() == 0)
			continue;

		RTLIL::SigSpec and_sig;

		if (eq_sig_a.size() > 0)
		{
			RTLIL::Wire *eq_wire = module->addWire(NEW_ID);
			and_sig.append(RTLIL::SigSpec(eq_wire));

			RTLIL::Cell *eq_cell = module->addCell(NEW_ID, "$eq");
			eq_cell->connections["\\A"] = eq_sig_a;
			eq_cell->connections["\\B"] = eq_sig_b;
			eq_cell->connections["\\Y"] = RTLIL::SigSpec(eq_wire);
			eq_cell->parameters["\\A_SIGNED"] = RTLIL::Const(false);
			eq_cell->parameters["\\B_SIGNED"] = RTLIL::Const(false);
			eq_cell->parameters["\\A_WIDTH"] = RTLIL::Const(eq_sig_a.size());
			eq_cell->parameters["\\B_WIDTH"] = RTLIL::Const(eq_sig_b.size());
			eq_cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
		}

		if (or_sig.size() < num_states-int(fullstate_cache.size()))
		{
			if (or_sig.size() == 1)
			{
				and_sig.append(or_sig);
			}
			else
			{
				RTLIL::Wire *or_wire = module->addWire(NEW_ID);
				and_sig.append(RTLIL::SigSpec(or_wire));

				RTLIL::Cell *or_cell = module->addCell(NEW_ID, "$reduce_or");
				or_cell->connections["\\A"] = or_sig;
				or_cell->connections["\\Y"] = RTLIL::SigSpec(or_wire);
				or_cell->parameters["\\A_SIGNED"] = RTLIL::Const(false);
				or_cell->parameters["\\A_WIDTH"] = RTLIL::Const(or_sig.size());
				or_cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
			}
		}

		switch (and_sig.size())
		{
		case 2:
			{
				RTLIL::Wire *and_wire = module->addWire(NEW_ID);
				cases_vector.append(RTLIL::SigSpec(and_wire));

				RTLIL::Cell *and_cell = module->addCell(NEW_ID, "$and");
				and_cell->connections["\\A"] = and_sig.extract(0, 1);
				and_cell->connections["\\B"] = and_sig.extract(1, 1);
				and_cell->connections["\\Y"] = RTLIL::SigSpec(and_wire);
				and_cell->parameters["\\A_SIGNED"] = RTLIL::Const(false);
				and_cell->parameters["\\B_SIGNED"] = RTLIL::Const(false);
				and_cell->parameters["\\A_WIDTH"] = RTLIL::Const(1);
				and_cell->parameters["\\B_WIDTH"] = RTLIL::Const(1);
				and_cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
				break;
			}
		case 1:
			cases_vector.append(and_sig);
			break;
		case 0:
			cases_vector.append(RTLIL::SigSpec(1, 1));
			break;
		default:
			log_abort();
		}
	}

	if (cases_vector.size() > 1) {
		RTLIL::Cell *or_cell = module->addCell(NEW_ID, "$reduce_or");
		or_cell->connections["\\A"] = cases_vector;
		or_cell->connections["\\Y"] = output;
		or_cell->parameters["\\A_SIGNED"] = RTLIL::Const(false);
		or_cell->parameters["\\A_WIDTH"] = RTLIL::Const(cases_vector.size());
		or_cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
	} else if (cases_vector.size() == 1) {
		module->connections.push_back(RTLIL::SigSig(output, cases_vector));
	} else {
		module->connections.push_back(RTLIL::SigSig(output, RTLIL::SigSpec(0, 1)));
	}
}

static void map_fsm(RTLIL::Cell *fsm_cell, RTLIL::Module *module)
{
	log("Mapping FSM `%s' from module `%s'.\n", fsm_cell->name.c_str(), module->name.c_str());

	FsmData fsm_data;
	fsm_data.copy_from_cell(fsm_cell);

	RTLIL::SigSpec ctrl_in = fsm_cell->connections["\\CTRL_IN"];
	RTLIL::SigSpec ctrl_out = fsm_cell->connections["\\CTRL_OUT"];

	// create state register

	RTLIL::Wire *state_wire = new RTLIL::Wire;
	state_wire->name = fsm_cell->parameters["\\NAME"].decode_string();
	while (module->count_id(state_wire->name) > 0)
		state_wire->name += "_";
	state_wire->width = fsm_data.state_bits;
	module->add(state_wire);

	RTLIL::Wire *next_state_wire = module->addWire(NEW_ID, fsm_data.state_bits);

	RTLIL::Cell *state_dff = module->addCell(NEW_ID, "");
	if (fsm_cell->connections["\\ARST"].is_fully_const()) {
		state_dff->type = "$dff";
	} else {
		state_dff->type = "$adff";
		state_dff->parameters["\\ARST_POLARITY"] = fsm_cell->parameters["\\ARST_POLARITY"];
		state_dff->parameters["\\ARST_VALUE"] = fsm_data.state_table[fsm_data.reset_state];
		for (auto &bit : state_dff->parameters["\\ARST_VALUE"].bits)
			if (bit != RTLIL::State::S1)
				bit = RTLIL::State::S0;
		state_dff->connections["\\ARST"] = fsm_cell->connections["\\ARST"];
	}
	state_dff->parameters["\\WIDTH"] = RTLIL::Const(fsm_data.state_bits);
	state_dff->parameters["\\CLK_POLARITY"] = fsm_cell->parameters["\\CLK_POLARITY"];
	state_dff->connections["\\CLK"] = fsm_cell->connections["\\CLK"];
	state_dff->connections["\\D"] = RTLIL::SigSpec(next_state_wire);
	state_dff->connections["\\Q"] = RTLIL::SigSpec(state_wire);

	// decode state register

	bool encoding_is_onehot = true;

	RTLIL::Wire *state_onehot = module->addWire(NEW_ID, fsm_data.state_table.size());

	for (size_t i = 0; i < fsm_data.state_table.size(); i++)
	{
		RTLIL::Const state = fsm_data.state_table[i];
		RTLIL::SigSpec sig_a, sig_b;

		for (size_t j = 0; j < state.bits.size(); j++)
			if (state.bits[j] == RTLIL::State::S0 || state.bits[j] == RTLIL::State::S1) {
				sig_a.append(RTLIL::SigSpec(state_wire, j));
				sig_b.append(RTLIL::SigSpec(state.bits[j]));
			}

		if (sig_b == RTLIL::SigSpec(RTLIL::State::S1))
		{
			module->connections.push_back(RTLIL::SigSig(RTLIL::SigSpec(state_onehot, i), sig_a));
		}
		else
		{
			encoding_is_onehot = false;

			RTLIL::Cell *eq_cell = module->addCell(NEW_ID, "$eq");
			eq_cell->connections["\\A"] = sig_a;
			eq_cell->connections["\\B"] = sig_b;
			eq_cell->connections["\\Y"] = RTLIL::SigSpec(state_onehot, i);
			eq_cell->parameters["\\A_SIGNED"] = RTLIL::Const(false);
			eq_cell->parameters["\\B_SIGNED"] = RTLIL::Const(false);
			eq_cell->parameters["\\A_WIDTH"] = RTLIL::Const(sig_a.size());
			eq_cell->parameters["\\B_WIDTH"] = RTLIL::Const(sig_b.size());
			eq_cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
		}
	}

	// generate next_state signal

	RTLIL::Wire *next_state_onehot = new RTLIL::Wire;
	next_state_onehot->name = NEW_ID;
	next_state_onehot->width = fsm_data.state_table.size();
	module->add(next_state_onehot);

	for (size_t i = 0; i < fsm_data.state_table.size(); i++)
	{
		std::map<RTLIL::Const, std::set<int>> pattern_cache;
		std::set<int> fullstate_cache;

		for (size_t j = 0; j < fsm_data.state_table.size(); j++)
			fullstate_cache.insert(j);

		for (auto &tr : fsm_data.transition_table) {
			if (tr.state_out == int(i))
				pattern_cache[tr.ctrl_in].insert(tr.state_in);
			else
				fullstate_cache.erase(tr.state_in);
		}

		implement_pattern_cache(module, pattern_cache, fullstate_cache, fsm_data.state_table.size(), state_onehot, ctrl_in, RTLIL::SigSpec(next_state_onehot, i));
	}

	if (encoding_is_onehot)
	{
		RTLIL::SigSpec next_state_sig(RTLIL::State::Sm, next_state_wire->width);
		for (size_t i = 0; i < fsm_data.state_table.size(); i++) {
			RTLIL::Const state = fsm_data.state_table[i];
			int bit_idx = -1;
			for (size_t j = 0; j < state.bits.size(); j++)
				if (state.bits[j] == RTLIL::State::S1)
					bit_idx = j;
			if (bit_idx >= 0)
				next_state_sig.replace(bit_idx, RTLIL::SigSpec(next_state_onehot, i));
		}
		log_assert(!next_state_sig.has_marked_bits());
		module->connections.push_back(RTLIL::SigSig(next_state_wire, next_state_sig));
	}
	else
	{
		RTLIL::SigSpec sig_a, sig_b, sig_s;
		int reset_state = fsm_data.reset_state;
		if (reset_state < 0)
			reset_state = 0;

		for (size_t i = 0; i < fsm_data.state_table.size(); i++) {
			RTLIL::Const state = fsm_data.state_table[i];
			if (int(i) == fsm_data.reset_state) {
				sig_a = RTLIL::SigSpec(state);
			} else {
				sig_b.append(RTLIL::SigSpec(state));
				sig_s.append(RTLIL::SigSpec(next_state_onehot, i));
			}
		}

		RTLIL::Cell *mux_cell = module->addCell(NEW_ID, "$safe_pmux");
		mux_cell->connections["\\A"] = sig_a;
		mux_cell->connections["\\B"] = sig_b;
		mux_cell->connections["\\S"] = sig_s;
		mux_cell->connections["\\Y"] = RTLIL::SigSpec(next_state_wire);
		mux_cell->parameters["\\WIDTH"] = RTLIL::Const(sig_a.size());
		mux_cell->parameters["\\S_WIDTH"] = RTLIL::Const(sig_s.size());
	}

	// Generate ctrl_out signal

	RTLIL::Wire *ctrl_out_wire = new RTLIL::Wire;
	ctrl_out_wire->name = NEW_ID;
	ctrl_out_wire->width = fsm_data.num_outputs;
	module->add(ctrl_out_wire);

	for (int i = 0; i < fsm_data.num_outputs; i++)
	{
		std::map<RTLIL::Const, std::set<int>> pattern_cache;
		std::set<int> fullstate_cache;

		for (size_t j = 0; j < fsm_data.state_table.size(); j++)
			fullstate_cache.insert(j);

		for (auto &tr : fsm_data.transition_table) {
			if (tr.ctrl_out.bits[i] == RTLIL::State::S1)
				pattern_cache[tr.ctrl_in].insert(tr.state_in);
			else
				fullstate_cache.erase(tr.state_in);
		}

		implement_pattern_cache(module, pattern_cache, fullstate_cache, fsm_data.state_table.size(), state_onehot, ctrl_in, ctrl_out.extract(i, 1));
	}

	// Remove FSM cell

	module->remove(fsm_cell);
}

struct FsmMapPass : public Pass {
	FsmMapPass() : Pass("fsm_map", "mapping FSMs to basic logic") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fsm_map [selection]\n");
		log("\n");
		log("This pass translates FSM cells to flip-flops and logic.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing FSM_MAP pass (mapping FSMs to basic logic).\n");
		extra_args(args, 1, design);

		for (auto &mod_it : design->modules) {
			if (!design->selected(mod_it.second))
				continue;
			std::vector<RTLIL::Cell*> fsm_cells;
			for (auto &cell_it : mod_it.second->cells)
				if (cell_it.second->type == "$fsm" && design->selected(mod_it.second, cell_it.second))
					fsm_cells.push_back(cell_it.second);
			for (auto cell : fsm_cells)
					map_fsm(cell, mod_it.second);
		}
	}
} FsmMapPass;
 
