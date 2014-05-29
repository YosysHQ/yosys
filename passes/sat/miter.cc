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
#include "kernel/rtlil.h"
#include "kernel/log.h"

static void create_miter_equiv(struct Pass *that, std::vector<std::string> args, RTLIL::Design *design)
{
	bool flag_ignore_gold_x = false;
	bool flag_make_outputs = false;
	bool flag_make_outcmp = false;
	bool flag_make_assert = false;

	log_header("Executing MITER pass (creating miter circuit).\n");

	size_t argidx;
	for (argidx = 2; argidx < args.size(); argidx++)
	{
		if (args[argidx] == "-ignore_gold_x") {
			flag_ignore_gold_x = true;
			continue;
		}
		if (args[argidx] == "-make_outputs") {
			flag_make_outputs = true;
			continue;
		}
		if (args[argidx] == "-make_outcmp") {
			flag_make_outcmp = true;
			continue;
		}
		if (args[argidx] == "-make_assert") {
			flag_make_assert = true;
			continue;
		}
		break;
	}
	if (argidx+3 != args.size() || args[argidx].substr(0, 1) == "-")
		that->cmd_error(args, argidx, "command argument error");
	
	std::string gold_name = RTLIL::escape_id(args[argidx++]);
	std::string gate_name = RTLIL::escape_id(args[argidx++]);
	std::string miter_name = RTLIL::escape_id(args[argidx++]);

	if (design->modules.count(gold_name) == 0)
		log_cmd_error("Can't find gold module %s!\n", gold_name.c_str());
	if (design->modules.count(gate_name) == 0)
		log_cmd_error("Can't find gate module %s!\n", gate_name.c_str());
	if (design->modules.count(miter_name) != 0)
		log_cmd_error("There is already a module %s!\n", gate_name.c_str());

	RTLIL::Module *gold_module = design->modules.at(gold_name);
	RTLIL::Module *gate_module = design->modules.at(gate_name);

	for (auto &it : gold_module->wires) {
		RTLIL::Wire *w1 = it.second, *w2;
		if (w1->port_id == 0)
			continue;
		if (gate_module->wires.count(it.second->name) == 0)
			goto match_gold_port_error;
		w2 = gate_module->wires.at(it.second->name);
		if (w1->port_input != w2->port_input)
			goto match_gold_port_error;
		if (w1->port_output != w2->port_output)
			goto match_gold_port_error;
		if (w1->width != w2->width)
			goto match_gold_port_error;
		continue;
	match_gold_port_error:
		log_cmd_error("No matching port in gate module was found for %s!\n", it.second->name.c_str());
	}

	for (auto &it : gate_module->wires) {
		RTLIL::Wire *w1 = it.second, *w2;
		if (w1->port_id == 0)
			continue;
		if (gold_module->wires.count(it.second->name) == 0)
			goto match_gate_port_error;
		w2 = gold_module->wires.at(it.second->name);
		if (w1->port_input != w2->port_input)
			goto match_gate_port_error;
		if (w1->port_output != w2->port_output)
			goto match_gate_port_error;
		if (w1->width != w2->width)
			goto match_gate_port_error;
		continue;
	match_gate_port_error:
		log_cmd_error("No matching port in gold module was found for %s!\n", it.second->name.c_str());
	}

	log("Creating miter cell \"%s\" with gold cell \"%s\" and gate cell \"%s\".\n", RTLIL::id2cstr(miter_name), RTLIL::id2cstr(gold_name), RTLIL::id2cstr(gate_name));

	RTLIL::Module *miter_module = new RTLIL::Module;
	miter_module->name = miter_name;
	design->modules[miter_name] = miter_module;

	RTLIL::Cell *gold_cell = new RTLIL::Cell;
	gold_cell->name = "\\gold";
	gold_cell->type = gold_name;
	miter_module->add(gold_cell);

	RTLIL::Cell *gate_cell = new RTLIL::Cell;
	gate_cell->name = "\\gate";
	gate_cell->type = gate_name;
	miter_module->add(gate_cell);

	RTLIL::SigSpec all_conditions;

	for (auto &it : gold_module->wires)
	{
		RTLIL::Wire *w1 = it.second;

		if (w1->port_input)
		{
			RTLIL::Wire *w2 = new RTLIL::Wire;
			w2->name = "\\in_" + RTLIL::unescape_id(w1->name);
			w2->port_input = true;
			w2->width = w1->width;
			miter_module->add(w2);

			gold_cell->connections[w1->name] = w2;
			gate_cell->connections[w1->name] = w2;
		}

		if (w1->port_output)
		{
			RTLIL::Wire *w2_gold = new RTLIL::Wire;
			w2_gold->name = "\\gold_" + RTLIL::unescape_id(w1->name);
			w2_gold->port_output = flag_make_outputs;
			w2_gold->width = w1->width;
			miter_module->add(w2_gold);

			RTLIL::Wire *w2_gate = new RTLIL::Wire;
			w2_gate->name = "\\gate_" + RTLIL::unescape_id(w1->name);
			w2_gate->port_output = flag_make_outputs;
			w2_gate->width = w1->width;
			miter_module->add(w2_gate);

			gold_cell->connections[w1->name] = w2_gold;
			gate_cell->connections[w1->name] = w2_gate;

			RTLIL::SigSpec this_condition;

			if (flag_ignore_gold_x)
			{
				RTLIL::SigSpec gold_x = miter_module->new_wire(w2_gold->width, NEW_ID);
				for (int i = 0; i < w2_gold->width; i++) {
					RTLIL::Cell *eqx_cell = new RTLIL::Cell;
					eqx_cell->name = NEW_ID;
					eqx_cell->type = "$eqx";
					eqx_cell->parameters["\\A_WIDTH"] = 1;
					eqx_cell->parameters["\\B_WIDTH"] = 1;
					eqx_cell->parameters["\\Y_WIDTH"] = 1;
					eqx_cell->parameters["\\A_SIGNED"] = 0;
					eqx_cell->parameters["\\B_SIGNED"] = 0;
					eqx_cell->connections["\\A"] = RTLIL::SigSpec(w2_gold, 1, i);
					eqx_cell->connections["\\B"] = RTLIL::State::Sx;
					eqx_cell->connections["\\Y"] = gold_x.extract(i, 1);
					miter_module->add(eqx_cell);
				}

				RTLIL::SigSpec gold_masked = miter_module->new_wire(w2_gold->width, NEW_ID);
				RTLIL::SigSpec gate_masked = miter_module->new_wire(w2_gate->width, NEW_ID);

				RTLIL::Cell *or_gold_cell = new RTLIL::Cell;
				or_gold_cell->name = NEW_ID;
				or_gold_cell->type = "$or";
				or_gold_cell->parameters["\\A_WIDTH"] = w2_gold->width;
				or_gold_cell->parameters["\\B_WIDTH"] = w2_gold->width;
				or_gold_cell->parameters["\\Y_WIDTH"] = w2_gold->width;
				or_gold_cell->parameters["\\A_SIGNED"] = 0;
				or_gold_cell->parameters["\\B_SIGNED"] = 0;
				or_gold_cell->connections["\\A"] = w2_gold;
				or_gold_cell->connections["\\B"] = gold_x;
				or_gold_cell->connections["\\Y"] = gold_masked;
				miter_module->add(or_gold_cell);

				RTLIL::Cell *or_gate_cell = new RTLIL::Cell;
				or_gate_cell->name = NEW_ID;
				or_gate_cell->type = "$or";
				or_gate_cell->parameters["\\A_WIDTH"] = w2_gate->width;
				or_gate_cell->parameters["\\B_WIDTH"] = w2_gate->width;
				or_gate_cell->parameters["\\Y_WIDTH"] = w2_gate->width;
				or_gate_cell->parameters["\\A_SIGNED"] = 0;
				or_gate_cell->parameters["\\B_SIGNED"] = 0;
				or_gate_cell->connections["\\A"] = w2_gate;
				or_gate_cell->connections["\\B"] = gold_x;
				or_gate_cell->connections["\\Y"] = gate_masked;
				miter_module->add(or_gate_cell);

				RTLIL::Cell *eq_cell = new RTLIL::Cell;
				eq_cell->name = NEW_ID;
				eq_cell->type = "$eqx";
				eq_cell->parameters["\\A_WIDTH"] = w2_gold->width;
				eq_cell->parameters["\\B_WIDTH"] = w2_gate->width;
				eq_cell->parameters["\\Y_WIDTH"] = 1;
				eq_cell->parameters["\\A_SIGNED"] = 0;
				eq_cell->parameters["\\B_SIGNED"] = 0;
				eq_cell->connections["\\A"] = gold_masked;
				eq_cell->connections["\\B"] = gate_masked;
				eq_cell->connections["\\Y"] = miter_module->new_wire(1, NEW_ID);
				this_condition = eq_cell->connections["\\Y"];
				miter_module->add(eq_cell);
			}
			else
			{
				RTLIL::Cell *eq_cell = new RTLIL::Cell;
				eq_cell->name = NEW_ID;
				eq_cell->type = "$eqx";
				eq_cell->parameters["\\A_WIDTH"] = w2_gold->width;
				eq_cell->parameters["\\B_WIDTH"] = w2_gate->width;
				eq_cell->parameters["\\Y_WIDTH"] = 1;
				eq_cell->parameters["\\A_SIGNED"] = 0;
				eq_cell->parameters["\\B_SIGNED"] = 0;
				eq_cell->connections["\\A"] = w2_gold;
				eq_cell->connections["\\B"] = w2_gate;
				eq_cell->connections["\\Y"] = miter_module->new_wire(1, NEW_ID);
				this_condition = eq_cell->connections["\\Y"];
				miter_module->add(eq_cell);
			}

			if (flag_make_outcmp)
			{
				RTLIL::Wire *w_cmp = new RTLIL::Wire;
				w_cmp->name = "\\cmp_" + RTLIL::unescape_id(w1->name);
				w_cmp->port_output = true;
				miter_module->add(w_cmp);
				miter_module->connections.push_back(RTLIL::SigSig(w_cmp, this_condition));
			}

			all_conditions.append(this_condition);
		}
	}

	if (all_conditions.width != 1) {
		RTLIL::Cell *reduce_cell = new RTLIL::Cell;
		reduce_cell->name = NEW_ID;
		reduce_cell->type = "$reduce_and";
		reduce_cell->parameters["\\A_WIDTH"] = all_conditions.width;
		reduce_cell->parameters["\\Y_WIDTH"] = 1;
		reduce_cell->parameters["\\A_SIGNED"] = 0;
		reduce_cell->connections["\\A"] = all_conditions;
		reduce_cell->connections["\\Y"] = miter_module->new_wire(1, NEW_ID);
		all_conditions = reduce_cell->connections["\\Y"];
		miter_module->add(reduce_cell);
	}

	if (flag_make_assert) {
		RTLIL::Cell *assert_cell = new RTLIL::Cell;
		assert_cell->name = NEW_ID;
		assert_cell->type = "$assert";
		assert_cell->connections["\\A"] = all_conditions;
		assert_cell->connections["\\EN"] = RTLIL::SigSpec(1, 1);
		miter_module->add(assert_cell);
	}

	RTLIL::Wire *w_trigger = new RTLIL::Wire;
	w_trigger->name = "\\trigger";
	w_trigger->port_output = true;
	miter_module->add(w_trigger);

	RTLIL::Cell *not_cell = new RTLIL::Cell;
	not_cell->name = NEW_ID;
	not_cell->type = "$not";
	not_cell->parameters["\\A_WIDTH"] = all_conditions.width;
	not_cell->parameters["\\A_WIDTH"] = all_conditions.width;
	not_cell->parameters["\\Y_WIDTH"] = w_trigger->width;
	not_cell->parameters["\\A_SIGNED"] = 0;
	not_cell->connections["\\A"] = all_conditions;
	not_cell->connections["\\Y"] = w_trigger;
	miter_module->add(not_cell);

	miter_module->fixup_ports();
}

struct MiterPass : public Pass {
	MiterPass() : Pass("miter", "automatically create a miter circuit") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    miter -equiv [options] gold_name gate_name miter_name\n");
		log("\n");
		log("Creates a miter circuit for equivialence checking. The gold- and gate- modules\n");
		log("must have the same interfaces. The miter circuit will have all inputs of the\n");
		log("two source modules, prefixed with 'in_'. The miter circuit has a 'trigger'\n");
		log("output that goes high if an output mismatch between the two source modules is\n");
		log("detected.\n");
		log("\n");
		log("    -ignore_gold_x\n");
		log("        a undef (x) bit in the gold module output will match any value in\n");
		log("        the gate module output.\n");
		log("\n");
		log("    -make_outputs\n");
		log("        also route the gold- and gate-outputs to 'gold_*' and 'gate_*' outputs\n");
		log("        on the miter circuit.\n");
		log("\n");
		log("    -make_outcmp\n");
		log("        also create a cmp_* output for each gold/gate output pair.\n");
		log("\n");
		log("    -make_assert\n");
		log("        also create an 'assert' cell that checks if trigger is always low.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		if (args.size() > 1 && args[1] == "-equiv") {
			create_miter_equiv(this, args, design);
			return;
		}

		log_cmd_error("Missing mode parameter!\n");
	}
} MiterPass;
 
