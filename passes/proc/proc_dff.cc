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
#include "kernel/consteval.h"
#include "kernel/log.h"
#include <sstream>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

static RTLIL::SigSpec find_any_lvalue(const RTLIL::Process *proc)
{
	RTLIL::SigSpec lvalue;

	for (auto sync : proc->syncs)
	for (auto &action : sync->actions)
		if (action.first.width > 0) {
			lvalue = action.first;
			lvalue.sort_and_unify();
			break;
		}

	for (auto sync : proc->syncs) {
		RTLIL::SigSpec this_lvalue;
		for (auto &action : sync->actions)
			this_lvalue.append(action.first);
		this_lvalue.sort_and_unify();
		RTLIL::SigSpec common_sig = this_lvalue.extract(lvalue);
		if (common_sig.width > 0)
			lvalue = common_sig;
	}

	return lvalue;
}

static void gen_dffsr(RTLIL::Module *mod, RTLIL::SigSpec sig_in, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_out,
		bool clk_polarity, bool set_polarity, RTLIL::SigSpec clk, RTLIL::SigSpec set, RTLIL::Process *proc)
{
	std::stringstream sstr;
	sstr << "$procdff$" << (RTLIL::autoidx++);

	RTLIL::SigSpec sig_set_inv = NEW_WIRE(mod, sig_in.width);
	RTLIL::SigSpec sig_sr_set = NEW_WIRE(mod, sig_in.width);
	RTLIL::SigSpec sig_sr_clr = NEW_WIRE(mod, sig_in.width);

	RTLIL::Cell *inv_set = new RTLIL::Cell;
	inv_set->name = NEW_ID;
	inv_set->type = "$not";
	inv_set->parameters["\\A_WIDTH"] = RTLIL::Const(sig_in.width);
	inv_set->parameters["\\Y_WIDTH"] = RTLIL::Const(sig_in.width);
	inv_set->connections["\\A"] = sig_set;
	inv_set->connections["\\Y"] = sig_set_inv;
	mod->add(inv_set);

	RTLIL::Cell *mux_sr_set = new RTLIL::Cell;
	mux_sr_set->name = NEW_ID;
	mux_sr_set->type = "$mux";
	mux_sr_set->parameters["\\WIDTH"] = RTLIL::Const(sig_in.width);
	mux_sr_set->connections[set_polarity ? "\\A" : "\\B"] = RTLIL::Const(0, sig_in.width);
	mux_sr_set->connections[set_polarity ? "\\B" : "\\A"] = sig_set;
	mux_sr_set->connections["\\Y"] = sig_sr_set;
	mux_sr_set->connections["\\S"] = set;
	mod->add(mux_sr_set);

	RTLIL::Cell *mux_sr_clr = new RTLIL::Cell;
	mux_sr_clr->name = NEW_ID;
	mux_sr_clr->type = "$mux";
	mux_sr_clr->parameters["\\WIDTH"] = RTLIL::Const(sig_in.width);
	mux_sr_clr->connections[set_polarity ? "\\A" : "\\B"] = RTLIL::Const(0, sig_in.width);
	mux_sr_clr->connections[set_polarity ? "\\B" : "\\A"] = sig_set_inv;
	mux_sr_clr->connections["\\Y"] = sig_sr_clr;
	mux_sr_clr->connections["\\S"] = set;
	mod->add(mux_sr_clr);

	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = sstr.str();
	cell->type = "$dffsr";
	cell->attributes = proc->attributes;
	mod->add(cell);

	cell->parameters["\\WIDTH"] = RTLIL::Const(sig_in.width);
	cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity, 1);
	cell->parameters["\\SET_POLARITY"] = RTLIL::Const(true, 1);
	cell->parameters["\\CLR_POLARITY"] = RTLIL::Const(true, 1);

	cell->connections["\\D"] = sig_in;
	cell->connections["\\Q"] = sig_out;
	cell->connections["\\CLK"] = clk;
	cell->connections["\\SET"] = sig_sr_set;
	cell->connections["\\CLR"] = sig_sr_clr;

	log("  created %s cell `%s' with %s edge clock and %s level non-const reset.\n", cell->type.c_str(), cell->name.c_str(),
			clk_polarity ? "positive" : "negative", set_polarity ? "positive" : "negative");
}

static void gen_dff(RTLIL::Module *mod, RTLIL::SigSpec sig_in, RTLIL::Const val_rst, RTLIL::SigSpec sig_out,
		bool clk_polarity, bool arst_polarity, RTLIL::SigSpec clk, RTLIL::SigSpec *arst, RTLIL::Process *proc)
{
	std::stringstream sstr;
	sstr << "$procdff$" << (RTLIL::autoidx++);

	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = sstr.str();
	cell->type = arst ? "$adff" : "$dff";
	cell->attributes = proc->attributes;
	mod->cells[cell->name] = cell;

	cell->parameters["\\WIDTH"] = RTLIL::Const(sig_in.width);
	if (arst) {
		cell->parameters["\\ARST_POLARITY"] = RTLIL::Const(arst_polarity, 1);
		cell->parameters["\\ARST_VALUE"] = val_rst;
	}
	cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity, 1);

	cell->connections["\\D"] = sig_in;
	cell->connections["\\Q"] = sig_out;
	if (arst)
		cell->connections["\\ARST"] = *arst;
	cell->connections["\\CLK"] = clk;

	log("  created %s cell `%s' with %s edge clock", cell->type.c_str(), cell->name.c_str(), clk_polarity ? "positive" : "negative");
	if (arst)
		log(" and %s level reset", arst_polarity ? "positive" : "negative");
	log(".\n");
}

static void proc_dff(RTLIL::Module *mod, RTLIL::Process *proc, ConstEval &ce)
{
	while (1)
	{
		RTLIL::SigSpec sig = find_any_lvalue(proc);
		bool free_sync_level = false;

		if (sig.width == 0)
			break;

		log("Creating register for signal `%s.%s' using process `%s.%s'.\n",
				mod->name.c_str(), log_signal(sig), mod->name.c_str(), proc->name.c_str());

		RTLIL::SigSpec insig = RTLIL::SigSpec(RTLIL::State::Sz, sig.width);
		RTLIL::SigSpec rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.width);
		RTLIL::SyncRule *sync_level = NULL;
		RTLIL::SyncRule *sync_edge = NULL;
		RTLIL::SyncRule *sync_always = NULL;

		std::map<RTLIL::SigSpec, std::set<RTLIL::SyncRule*>> many_async_rules;

		for (auto sync : proc->syncs)
		for (auto &action : sync->actions)
		{
			if (action.first.extract(sig).width == 0)
				continue;

			if (sync->type == RTLIL::SyncType::ST0 || sync->type == RTLIL::SyncType::ST1) {
				if (sync_level != NULL && sync_level != sync) {
					// log_error("Multiple level sensitive events found for this signal!\n");
					many_async_rules[rstval].insert(sync_level);
					rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.width);
				}
				rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.width);
				sig.replace(action.first, action.second, &rstval);
				sync_level = sync;
			}
			else if (sync->type == RTLIL::SyncType::STp || sync->type == RTLIL::SyncType::STn) {
				if (sync_edge != NULL && sync_edge != sync)
					log_error("Multiple edge sensitive events found for this signal!\n");
				sig.replace(action.first, action.second, &insig);
				sync_edge = sync;
			}
			else if (sync->type == RTLIL::SyncType::STa) {
				if (sync_always != NULL && sync_always != sync)
					log_error("Multiple always events found for this signal!\n");
				sig.replace(action.first, action.second, &insig);
				sync_always = sync;
			}
			else {
				log_error("Event with any-edge sensitivity found for this signal!\n");
			}

			action.first.remove2(sig, &action.second);
		}

		if (many_async_rules.size() > 0)
		{
			many_async_rules[rstval].insert(sync_level);
			if (many_async_rules.size() == 1)
			{
				sync_level = new RTLIL::SyncRule;
				sync_level->type = RTLIL::SyncType::ST1;
				sync_level->signal = NEW_WIRE(mod, 1);
				sync_level->actions.push_back(RTLIL::SigSig(sig, rstval));
				free_sync_level = true;

				RTLIL::SigSpec inputs, compare;
				for (auto &it : many_async_rules[rstval]) {
					inputs.append(it->signal);
					compare.append(it->type == RTLIL::SyncType::ST0 ? RTLIL::State::S1 : RTLIL::State::S0);
				}
				assert(inputs.width == compare.width);

				RTLIL::Cell *cell = new RTLIL::Cell;
				cell->name = NEW_ID;
				cell->type = "$ne";
				cell->parameters["\\A_SIGNED"] = RTLIL::Const(false, 1);
				cell->parameters["\\B_SIGNED"] = RTLIL::Const(false, 1);
				cell->parameters["\\A_WIDTH"] = RTLIL::Const(inputs.width);
				cell->parameters["\\B_WIDTH"] = RTLIL::Const(inputs.width);
				cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
				cell->connections["\\A"] = inputs;
				cell->connections["\\B"] = compare;
				cell->connections["\\Y"] = sync_level->signal;
				mod->add(cell);

				many_async_rules.clear();
			}
			else
			{
				rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.width);
				sync_level = NULL;
			}
		}

		ce.assign_map.apply(insig);
		ce.assign_map.apply(rstval);
		ce.assign_map.apply(sig);

		insig.optimize();
		rstval.optimize();
		sig.optimize();

		if (sync_always) {
			if (sync_edge || sync_level || many_async_rules.size() > 0)
				log_error("Mixed always event with edge and/or level sensitive events!\n");
			log("  created direct connection (no actual register cell created).\n");
			mod->connections.push_back(RTLIL::SigSig(sig, insig));
			continue;
		}

		if (!sync_edge)
			log_error("Missing edge-sensitive event for this signal!\n");

		if (many_async_rules.size() > 0)
		{
			log_error("Multiple async resets for different values (feature under construction)!\n");
		}
		else if (!rstval.is_fully_const() && !ce.eval(rstval))
		{
			log("WARNING: Async reset value `%s' is not constant!\n", log_signal(rstval));
			gen_dffsr(mod, insig, rstval, sig,
					sync_edge->type == RTLIL::SyncType::STp,
					sync_level && sync_level->type == RTLIL::SyncType::ST1,
					sync_edge->signal, sync_level->signal, proc);
		}
		else
			gen_dff(mod, insig, rstval.chunks[0].data, sig,
					sync_edge->type == RTLIL::SyncType::STp,
					sync_level && sync_level->type == RTLIL::SyncType::ST1,
					sync_edge->signal, sync_level ? &sync_level->signal : NULL, proc);

		if (free_sync_level)
			delete sync_level;
	}
}

struct ProcDffPass : public Pass {
	ProcDffPass() : Pass("proc_dff", "extract flip-flops from processes") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_dff [selection]\n");
		log("\n");
		log("This pass identifies flip-flops in the processes and converts them to\n");
		log("d-type flip-flop cells.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing PROC_DFF pass (convert process syncs to FFs).\n");

		extra_args(args, 1, design);

		for (auto &mod_it : design->modules)
			if (design->selected(mod_it.second)) {
				ConstEval ce(mod_it.second);
				for (auto &proc_it : mod_it.second->processes)
					if (design->selected(mod_it.second, proc_it.second))
						proc_dff(mod_it.second, proc_it.second, ce);
			}
	}
} ProcDffPass;
 
