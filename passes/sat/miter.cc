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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void create_miter_equiv(struct Pass *that, std::vector<std::string> args, RTLIL::Design *design)
{
	bool flag_ignore_gold_x = false;
	bool flag_make_outputs = false;
	bool flag_make_outcmp = false;
	bool flag_make_assert = false;
	bool flag_flatten = false;

	log_header(design, "Executing MITER pass (creating miter circuit).\n");

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
		if (args[argidx] == "-flatten") {
			flag_flatten = true;
			continue;
		}
		break;
	}
	if (argidx+3 != args.size() || args[argidx].compare(0, 1, "-") == 0)
		that->cmd_error(args, argidx, "command argument error");

	RTLIL::IdString gold_name = RTLIL::escape_id(args[argidx++]);
	RTLIL::IdString gate_name = RTLIL::escape_id(args[argidx++]);
	RTLIL::IdString miter_name = RTLIL::escape_id(args[argidx++]);

	if (design->module(gold_name) == nullptr)
		log_cmd_error("Can't find gold module %s!\n", gold_name.c_str());
	if (design->module(gate_name) == nullptr)
		log_cmd_error("Can't find gate module %s!\n", gate_name.c_str());
	if (design->module(miter_name) != nullptr)
		log_cmd_error("There is already a module %s!\n", miter_name.c_str());

	RTLIL::Module *gold_module = design->module(gold_name);
	RTLIL::Module *gate_module = design->module(gate_name);

	for (auto gold_wire : gold_module->wires()) {
		if (gold_wire->port_id == 0)
			continue;
		RTLIL::Wire *gate_wire = gate_module->wire(gold_wire->name);
		if (gate_wire == nullptr)
			goto match_gold_port_error;
		if (gold_wire->port_input != gate_wire->port_input)
			goto match_gold_port_error;
		if (gold_wire->port_output != gate_wire->port_output)
			goto match_gold_port_error;
		if (gold_wire->width != gate_wire->width)
			goto match_gold_port_error;
		continue;
	match_gold_port_error:
		log_cmd_error("No matching port in gate module was found for %s!\n", gold_wire->name.c_str());
	}

	for (auto gate_wire : gate_module->wires()) {
		if (gate_wire->port_id == 0)
			continue;
		RTLIL::Wire *gold_wire = gold_module->wire(gate_wire->name);
		if (gold_wire == nullptr)
			goto match_gate_port_error;
		if (gate_wire->port_input != gold_wire->port_input)
			goto match_gate_port_error;
		if (gate_wire->port_output != gold_wire->port_output)
			goto match_gate_port_error;
		if (gate_wire->width != gold_wire->width)
			goto match_gate_port_error;
		continue;
	match_gate_port_error:
		log_cmd_error("No matching port in gold module was found for %s!\n", gate_wire->name.c_str());
	}

	log("Creating miter cell \"%s\" with gold cell \"%s\" and gate cell \"%s\".\n", RTLIL::id2cstr(miter_name), RTLIL::id2cstr(gold_name), RTLIL::id2cstr(gate_name));

	RTLIL::Module *miter_module = new RTLIL::Module;
	miter_module->name = miter_name;
	design->add(miter_module);

	RTLIL::Cell *gold_cell = miter_module->addCell(ID(gold), gold_name);
	RTLIL::Cell *gate_cell = miter_module->addCell(ID(gate), gate_name);

	RTLIL::SigSpec all_conditions;

	for (auto gold_wire : gold_module->wires())
	{
		if (gold_wire->port_input)
		{
			RTLIL::Wire *w = miter_module->addWire("\\in_" + RTLIL::unescape_id(gold_wire->name), gold_wire->width);
			w->port_input = true;

			gold_cell->setPort(gold_wire->name, w);
			gate_cell->setPort(gold_wire->name, w);
		}

		if (gold_wire->port_output)
		{
			RTLIL::Wire *w_gold = miter_module->addWire("\\gold_" + RTLIL::unescape_id(gold_wire->name), gold_wire->width);
			w_gold->port_output = flag_make_outputs;

			RTLIL::Wire *w_gate = miter_module->addWire("\\gate_" + RTLIL::unescape_id(gold_wire->name), gold_wire->width);
			w_gate->port_output = flag_make_outputs;

			gold_cell->setPort(gold_wire->name, w_gold);
			gate_cell->setPort(gold_wire->name, w_gate);

			RTLIL::SigSpec this_condition;

			if (flag_ignore_gold_x)
			{
				RTLIL::SigSpec gold_x = miter_module->addWire(NEW_ID, w_gold->width);
				for (int i = 0; i < w_gold->width; i++) {
					RTLIL::Cell *eqx_cell = miter_module->addCell(NEW_ID, ID($eqx));
					eqx_cell->parameters[ID::A_WIDTH] = 1;
					eqx_cell->parameters[ID::B_WIDTH] = 1;
					eqx_cell->parameters[ID::Y_WIDTH] = 1;
					eqx_cell->parameters[ID::A_SIGNED] = 0;
					eqx_cell->parameters[ID::B_SIGNED] = 0;
					eqx_cell->setPort(ID::A, RTLIL::SigSpec(w_gold, i));
					eqx_cell->setPort(ID::B, RTLIL::State::Sx);
					eqx_cell->setPort(ID::Y, gold_x.extract(i, 1));
				}

				RTLIL::SigSpec gold_masked = miter_module->addWire(NEW_ID, w_gold->width);
				RTLIL::SigSpec gate_masked = miter_module->addWire(NEW_ID, w_gate->width);

				RTLIL::Cell *or_gold_cell = miter_module->addCell(NEW_ID, ID($or));
				or_gold_cell->parameters[ID::A_WIDTH] = w_gold->width;
				or_gold_cell->parameters[ID::B_WIDTH] = w_gold->width;
				or_gold_cell->parameters[ID::Y_WIDTH] = w_gold->width;
				or_gold_cell->parameters[ID::A_SIGNED] = 0;
				or_gold_cell->parameters[ID::B_SIGNED] = 0;
				or_gold_cell->setPort(ID::A, w_gold);
				or_gold_cell->setPort(ID::B, gold_x);
				or_gold_cell->setPort(ID::Y, gold_masked);

				RTLIL::Cell *or_gate_cell = miter_module->addCell(NEW_ID, ID($or));
				or_gate_cell->parameters[ID::A_WIDTH] = w_gate->width;
				or_gate_cell->parameters[ID::B_WIDTH] = w_gate->width;
				or_gate_cell->parameters[ID::Y_WIDTH] = w_gate->width;
				or_gate_cell->parameters[ID::A_SIGNED] = 0;
				or_gate_cell->parameters[ID::B_SIGNED] = 0;
				or_gate_cell->setPort(ID::A, w_gate);
				or_gate_cell->setPort(ID::B, gold_x);
				or_gate_cell->setPort(ID::Y, gate_masked);

				RTLIL::Cell *eq_cell = miter_module->addCell(NEW_ID, ID($eqx));
				eq_cell->parameters[ID::A_WIDTH] = w_gold->width;
				eq_cell->parameters[ID::B_WIDTH] = w_gate->width;
				eq_cell->parameters[ID::Y_WIDTH] = 1;
				eq_cell->parameters[ID::A_SIGNED] = 0;
				eq_cell->parameters[ID::B_SIGNED] = 0;
				eq_cell->setPort(ID::A, gold_masked);
				eq_cell->setPort(ID::B, gate_masked);
				eq_cell->setPort(ID::Y, miter_module->addWire(NEW_ID));
				this_condition = eq_cell->getPort(ID::Y);
			}
			else
			{
				RTLIL::Cell *eq_cell = miter_module->addCell(NEW_ID, ID($eqx));
				eq_cell->parameters[ID::A_WIDTH] = w_gold->width;
				eq_cell->parameters[ID::B_WIDTH] = w_gate->width;
				eq_cell->parameters[ID::Y_WIDTH] = 1;
				eq_cell->parameters[ID::A_SIGNED] = 0;
				eq_cell->parameters[ID::B_SIGNED] = 0;
				eq_cell->setPort(ID::A, w_gold);
				eq_cell->setPort(ID::B, w_gate);
				eq_cell->setPort(ID::Y, miter_module->addWire(NEW_ID));
				this_condition = eq_cell->getPort(ID::Y);
			}

			if (flag_make_outcmp)
			{
				RTLIL::Wire *w_cmp = miter_module->addWire("\\cmp_" + RTLIL::unescape_id(gold_wire->name));
				w_cmp->port_output = true;
				miter_module->connect(RTLIL::SigSig(w_cmp, this_condition));
			}

			all_conditions.append(this_condition);
		}
	}

	if (all_conditions.size() != 1) {
		RTLIL::Cell *reduce_cell = miter_module->addCell(NEW_ID, ID($reduce_and));
		reduce_cell->parameters[ID::A_WIDTH] = all_conditions.size();
		reduce_cell->parameters[ID::Y_WIDTH] = 1;
		reduce_cell->parameters[ID::A_SIGNED] = 0;
		reduce_cell->setPort(ID::A, all_conditions);
		reduce_cell->setPort(ID::Y, miter_module->addWire(NEW_ID));
		all_conditions = reduce_cell->getPort(ID::Y);
	}

	if (flag_make_assert) {
		RTLIL::Cell *assert_cell = miter_module->addCell(NEW_ID, ID($assert));
		assert_cell->setPort(ID::A, all_conditions);
		assert_cell->setPort(ID::EN, State::S1);
	}

	RTLIL::Wire *w_trigger = miter_module->addWire(ID(trigger));
	w_trigger->port_output = true;

	RTLIL::Cell *not_cell = miter_module->addCell(NEW_ID, ID($not));
	not_cell->parameters[ID::A_WIDTH] = all_conditions.size();
	not_cell->parameters[ID::A_WIDTH] = all_conditions.size();
	not_cell->parameters[ID::Y_WIDTH] = w_trigger->width;
	not_cell->parameters[ID::A_SIGNED] = 0;
	not_cell->setPort(ID::A, all_conditions);
	not_cell->setPort(ID::Y, w_trigger);

	miter_module->fixup_ports();

	if (flag_flatten) {
		log_push();
		Pass::call_on_module(design, miter_module, "flatten -wb; opt_expr -keepdc -undriven;;");
		log_pop();
	}
}

void create_miter_assert(struct Pass *that, std::vector<std::string> args, RTLIL::Design *design)
{
	bool flag_make_outputs = false;
	bool flag_flatten = false;

	log_header(design, "Executing MITER pass (creating miter circuit).\n");

	size_t argidx;
	for (argidx = 2; argidx < args.size(); argidx++)
	{
		if (args[argidx] == "-make_outputs") {
			flag_make_outputs = true;
			continue;
		}
		if (args[argidx] == "-flatten") {
			flag_flatten = true;
			continue;
		}
		break;
	}
	if ((argidx+1 != args.size() && argidx+2 != args.size()) || args[argidx].compare(0, 1, "-") == 0)
		that->cmd_error(args, argidx, "command argument error");

	IdString module_name = RTLIL::escape_id(args[argidx++]);
	IdString miter_name = argidx < args.size() ? RTLIL::escape_id(args[argidx++]) : "";

	if (design->module(module_name) == nullptr)
		log_cmd_error("Can't find module %s!\n", module_name.c_str());
	if (!miter_name.empty() && design->module(miter_name) != nullptr)
		log_cmd_error("There is already a module %s!\n", miter_name.c_str());

	Module *module = design->module(module_name);

	if (!miter_name.empty()) {
		module = module->clone();
		module->name = miter_name;
		design->add(module);
	}

	if (!flag_make_outputs)
		for (auto wire : module->wires())
			wire->port_output = false;

	Wire *trigger = module->addWire(ID(trigger));
	trigger->port_output = true;
	module->fixup_ports();

	if (flag_flatten) {
		log_push();
		Pass::call_on_module(design, module, "flatten -wb;;");
		log_pop();
	}

	SigSpec assert_signals, assume_signals;
	vector<Cell*> cell_list = module->cells();
	for (auto cell : cell_list)
	{
		if (!cell->type.in(ID($assert), ID($assume)))
			continue;

		SigBit is_active = module->Nex(NEW_ID, cell->getPort(ID::A), State::S1);
		SigBit is_enabled = module->Eqx(NEW_ID, cell->getPort(ID::EN), State::S1);

		if (cell->type == ID($assert)) {
			assert_signals.append(module->And(NEW_ID, is_active, is_enabled));
		} else {
			assume_signals.append(module->And(NEW_ID, is_active, is_enabled));
		}

		module->remove(cell);
	}

	if (assume_signals.empty())
	{
		module->addReduceOr(NEW_ID, assert_signals, trigger);
	}
	else
	{
		Wire *assume_q = module->addWire(NEW_ID);
		assume_q->attributes[ID::init] = State::S0;
		assume_signals.append(assume_q);

		SigSpec assume_nok = module->ReduceOr(NEW_ID, assume_signals);
		SigSpec assume_ok = module->Not(NEW_ID, assume_nok);
		module->addFf(NEW_ID, assume_nok, assume_q);

		SigSpec assert_fail = module->ReduceOr(NEW_ID, assert_signals);
		module->addAnd(NEW_ID, assert_fail, assume_ok, trigger);
	}

	if (flag_flatten) {
		log_push();
		Pass::call_on_module(design, module, "opt_expr -keepdc -undriven;;");
		log_pop();
	}
}

struct MiterPass : public Pass {
	MiterPass() : Pass("miter", "automatically create a miter circuit") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    miter -equiv [options] gold_name gate_name miter_name\n");
		log("\n");
		log("Creates a miter circuit for equivalence checking. The gold- and gate- modules\n");
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
		log("    -flatten\n");
		log("        call 'flatten -wb; opt_expr -keepdc -undriven;;' on the miter circuit.\n");
		log("\n");
		log("\n");
		log("    miter -assert [options] module [miter_name]\n");
		log("\n");
		log("Creates a miter circuit for property checking. All input ports are kept,\n");
		log("output ports are discarded. An additional output 'trigger' is created that\n");
		log("goes high when an assert is violated. Without a miter_name, the existing\n");
		log("module is modified.\n");
		log("\n");
		log("    -make_outputs\n");
		log("        keep module output ports.\n");
		log("\n");
		log("    -flatten\n");
		log("        call 'flatten -wb; opt_expr -keepdc -undriven;;' on the miter circuit.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		if (args.size() > 1 && args[1] == "-equiv") {
			create_miter_equiv(this, args, design);
			return;
		}

		if (args.size() > 1 && args[1] == "-assert") {
			create_miter_assert(this, args, design);
			return;
		}

		log_cmd_error("Missing mode parameter!\n");
	}
} MiterPass;

PRIVATE_NAMESPACE_END
