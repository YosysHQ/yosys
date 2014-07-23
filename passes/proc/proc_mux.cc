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
#include "kernel/bitpattern.h"
#include "kernel/log.h"
#include <sstream>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

static RTLIL::SigSpec find_any_lvalue(const RTLIL::CaseRule *cs)
{
	for (auto &action : cs->actions) {
		if (action.first.size())
			return action.first;
	}

	for (auto sw : cs->switches)
	for (auto cs2 : sw->cases) {
		RTLIL::SigSpec sig = find_any_lvalue(cs2);
		if (sig.size())
			return sig;
	}

	return RTLIL::SigSpec();
}

static void extract_core_signal(const RTLIL::CaseRule *cs, RTLIL::SigSpec &sig)
{
	for (auto &action : cs->actions) {
		RTLIL::SigSpec lvalue = action.first.extract(sig);
		if (lvalue.size())
			sig = lvalue;
	}

	for (auto sw : cs->switches)
	for (auto cs2 : sw->cases)
		extract_core_signal(cs2, sig);
}

static RTLIL::SigSpec gen_cmp(RTLIL::Module *mod, const RTLIL::SigSpec &signal, const std::vector<RTLIL::SigSpec> &compare, RTLIL::SwitchRule *sw)
{
	std::stringstream sstr;
	sstr << "$procmux$" << (RTLIL::autoidx++);

	RTLIL::Wire *cmp_wire = new RTLIL::Wire;
	cmp_wire->name = sstr.str() + "_CMP";
	cmp_wire->width = 0;
	mod->wires[cmp_wire->name] = cmp_wire;

	for (auto comp : compare)
	{
		RTLIL::SigSpec sig = signal;

		// get rid of don't-care bits
		assert(sig.size() == comp.size());
		for (int i = 0; i < comp.size(); i++)
			if (comp[i] == RTLIL::State::Sa) {
				sig.remove(i);
				comp.remove(i--);
			}
		if (comp.size() == 0)
			return RTLIL::SigSpec();

		if (sig.size() == 1 && comp == RTLIL::SigSpec(1,1))
		{
			mod->connections.push_back(RTLIL::SigSig(RTLIL::SigSpec(cmp_wire, cmp_wire->width++), sig));
		}
		else
		{
			// create compare cell
			RTLIL::Cell *eq_cell = new RTLIL::Cell;
			std::stringstream sstr2;
			sstr2 << sstr.str() << "_CMP" << cmp_wire->width;
			eq_cell->name = sstr2.str();
			eq_cell->type = "$eq";
			eq_cell->attributes = sw->attributes;
			mod->cells[eq_cell->name] = eq_cell;

			eq_cell->parameters["\\A_SIGNED"] = RTLIL::Const(0);
			eq_cell->parameters["\\B_SIGNED"] = RTLIL::Const(0);

			eq_cell->parameters["\\A_WIDTH"] = RTLIL::Const(sig.size());
			eq_cell->parameters["\\B_WIDTH"] = RTLIL::Const(comp.size());
			eq_cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);

			eq_cell->connections["\\A"] = sig;
			eq_cell->connections["\\B"] = comp;
			eq_cell->connections["\\Y"] = RTLIL::SigSpec(cmp_wire, cmp_wire->width++);
		}
	}

	RTLIL::Wire *ctrl_wire;
	if (cmp_wire->width == 1)
	{
		ctrl_wire = cmp_wire;
	}
	else
	{
		ctrl_wire = new RTLIL::Wire;
		ctrl_wire->name = sstr.str() + "_CTRL";
		ctrl_wire->width = 1;
		mod->wires[ctrl_wire->name] = ctrl_wire;

		// reduce cmp vector to one logic signal
		RTLIL::Cell *any_cell = new RTLIL::Cell;
		any_cell->name = sstr.str() + "_ANY";
		any_cell->type = "$reduce_or";
		any_cell->attributes = sw->attributes;
		mod->cells[any_cell->name] = any_cell;

		any_cell->parameters["\\A_SIGNED"] = RTLIL::Const(0);
		any_cell->parameters["\\A_WIDTH"] = RTLIL::Const(cmp_wire->width);
		any_cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);

		any_cell->connections["\\A"] = cmp_wire;
		any_cell->connections["\\Y"] = RTLIL::SigSpec(ctrl_wire);
	}

	return RTLIL::SigSpec(ctrl_wire);
}

static RTLIL::SigSpec gen_mux(RTLIL::Module *mod, const RTLIL::SigSpec &signal, const std::vector<RTLIL::SigSpec> &compare, RTLIL::SigSpec when_signal, RTLIL::SigSpec else_signal, RTLIL::Cell *&last_mux_cell, RTLIL::SwitchRule *sw)
{
	assert(when_signal.size() == else_signal.size());

	std::stringstream sstr;
	sstr << "$procmux$" << (RTLIL::autoidx++);

	// the trivial cases
	if (compare.size() == 0 || when_signal == else_signal)
		return when_signal;

	// compare results
	RTLIL::SigSpec ctrl_sig = gen_cmp(mod, signal, compare, sw);
	if (ctrl_sig.size() == 0)
		return when_signal;
	assert(ctrl_sig.size() == 1);

	// prepare multiplexer output signal
	RTLIL::Wire *result_wire = new RTLIL::Wire;
	result_wire->name = sstr.str() + "_Y";
	result_wire->width = when_signal.size();
	mod->wires[result_wire->name] = result_wire;

	// create the multiplexer itself
	RTLIL::Cell *mux_cell = new RTLIL::Cell;
	mux_cell->name = sstr.str();
	mux_cell->type = "$mux";
	mux_cell->attributes = sw->attributes;
	mod->cells[mux_cell->name] = mux_cell;

	mux_cell->parameters["\\WIDTH"] = RTLIL::Const(when_signal.size());
	mux_cell->connections["\\A"] = else_signal;
	mux_cell->connections["\\B"] = when_signal;
	mux_cell->connections["\\S"] = ctrl_sig;
	mux_cell->connections["\\Y"] = RTLIL::SigSpec(result_wire);

	last_mux_cell = mux_cell;
	return RTLIL::SigSpec(result_wire);
}

static void append_pmux(RTLIL::Module *mod, const RTLIL::SigSpec &signal, const std::vector<RTLIL::SigSpec> &compare, RTLIL::SigSpec when_signal, RTLIL::Cell *last_mux_cell, RTLIL::SwitchRule *sw)
{
	assert(last_mux_cell != NULL);
	assert(when_signal.size() == last_mux_cell->connections["\\A"].size());

	RTLIL::SigSpec ctrl_sig = gen_cmp(mod, signal, compare, sw);
	assert(ctrl_sig.size() == 1);
	last_mux_cell->type = "$pmux";
	last_mux_cell->connections["\\S"].append(ctrl_sig);
	last_mux_cell->connections["\\B"].append(when_signal);
	last_mux_cell->parameters["\\S_WIDTH"] = last_mux_cell->connections["\\S"].size();
}

static RTLIL::SigSpec signal_to_mux_tree(RTLIL::Module *mod, RTLIL::CaseRule *cs, const RTLIL::SigSpec &sig, const RTLIL::SigSpec &defval)
{
	RTLIL::SigSpec result = defval;

	for (auto &action : cs->actions) {
		sig.replace(action.first, action.second, &result);
		action.first.remove2(sig, &action.second);
	}

	for (auto sw : cs->switches)
	{
		// detect groups of parallel cases
		std::vector<int> pgroups(sw->cases.size());
		if (!sw->get_bool_attribute("\\parallel_case")) {
			BitPatternPool pool(sw->signal.size());
			bool extra_group_for_next_case = false;
			for (size_t i = 0; i < sw->cases.size(); i++) {
				RTLIL::CaseRule *cs2 = sw->cases[i];
				if (i != 0) {
					pgroups[i] = pgroups[i-1];
					if (extra_group_for_next_case) {
						pgroups[i] = pgroups[i-1]+1;
						extra_group_for_next_case = false;
					}
					for (auto pat : cs2->compare)
						if (!pat.is_fully_const() || !pool.has_all(pat))
							pgroups[i] = pgroups[i-1]+1;
					if (cs2->compare.empty())
						pgroups[i] = pgroups[i-1]+1;
					if (pgroups[i] != pgroups[i-1])
						pool = BitPatternPool(sw->signal.size());
				}
				for (auto pat : cs2->compare)
					if (!pat.is_fully_const())
						extra_group_for_next_case = true;
					else
						pool.take(pat);
			}
		}

		// evaluate in reverse order to give the first entry the top priority
		RTLIL::SigSpec initial_val = result;
		RTLIL::Cell *last_mux_cell = NULL;
		for (size_t i = 0; i < sw->cases.size(); i++) {
			int case_idx = sw->cases.size() - i - 1;
			RTLIL::CaseRule *cs2 = sw->cases[case_idx];
			RTLIL::SigSpec value = signal_to_mux_tree(mod, cs2, sig, initial_val);
			if (last_mux_cell && pgroups[case_idx] == pgroups[case_idx+1])
				append_pmux(mod, sw->signal, cs2->compare, value, last_mux_cell, sw);
			else
				result = gen_mux(mod, sw->signal, cs2->compare, value, result, last_mux_cell, sw);
		}
	}

	return result;
}

static void proc_mux(RTLIL::Module *mod, RTLIL::Process *proc)
{
	bool first = true;
	while (1)
	{
		RTLIL::SigSpec sig = find_any_lvalue(&proc->root_case);

		if (sig.size() == 0)
			break;

		if (first) {
			log("Creating decoders for process `%s.%s'.\n", mod->name.c_str(), proc->name.c_str());
			first = false;
		}

		extract_core_signal(&proc->root_case, sig);

		log("  creating decoder for signal `%s'.\n", log_signal(sig));

		RTLIL::SigSpec value = signal_to_mux_tree(mod, &proc->root_case, sig, RTLIL::SigSpec(RTLIL::State::Sx, sig.size()));
		mod->connections.push_back(RTLIL::SigSig(sig, value));
	}
}

struct ProcMuxPass : public Pass {
	ProcMuxPass() : Pass("proc_mux", "convert decision trees to multiplexers") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_mux [selection]\n");
		log("\n");
		log("This pass converts the decision trees in processes (originating from if-else\n");
		log("and case statements) to trees of multiplexer cells.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing PROC_MUX pass (convert decision trees to multiplexers).\n");

		extra_args(args, 1, design);

		for (auto &mod_it : design->modules)
			if (design->selected(mod_it.second))
				for (auto &proc_it : mod_it.second->processes)
					if (design->selected(mod_it.second, proc_it.second))
						proc_mux(mod_it.second, proc_it.second);
	}
} ProcMuxPass;
 
