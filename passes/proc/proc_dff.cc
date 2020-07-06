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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

RTLIL::SigSpec find_any_lvalue(const RTLIL::Process *proc)
{
	RTLIL::SigSpec lvalue;

	for (auto sync : proc->syncs)
	for (auto &action : sync->actions)
		if (action.first.size() > 0) {
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
		if (common_sig.size() > 0)
			lvalue = common_sig;
	}

	return lvalue;
}

void gen_dffsr_complex(RTLIL::Module *mod, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, RTLIL::SigSpec clk, bool clk_polarity,
		std::map<RTLIL::SigSpec, std::set<RTLIL::SyncRule*>> &async_rules, RTLIL::Process *proc)
{
	RTLIL::SigSpec sig_sr_set = RTLIL::SigSpec(0, sig_d.size());
	RTLIL::SigSpec sig_sr_clr = RTLIL::SigSpec(0, sig_d.size());

	for (auto &it : async_rules)
	{
		RTLIL::SigSpec sync_value = it.first;
		RTLIL::SigSpec sync_value_inv;
		RTLIL::SigSpec sync_high_signals;
		RTLIL::SigSpec sync_low_signals;

		for (auto &it2 : it.second)
			if (it2->type == RTLIL::SyncType::ST0)
				sync_low_signals.append(it2->signal);
			else if (it2->type == RTLIL::SyncType::ST1)
				sync_high_signals.append(it2->signal);
			else
				log_abort();

		if (sync_low_signals.size() > 1) {
			RTLIL::Cell *cell = mod->addCell(NEW_ID, "$reduce_or");
			cell->parameters["\\A_SIGNED"] = RTLIL::Const(0);
			cell->parameters["\\A_WIDTH"] = RTLIL::Const(sync_low_signals.size());
			cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
			cell->setPort("\\A", sync_low_signals);
			cell->setPort("\\Y", sync_low_signals = mod->addWire(NEW_ID));
		}

		if (sync_low_signals.size() > 0) {
			RTLIL::Cell *cell = mod->addCell(NEW_ID, "$not");
			cell->parameters["\\A_SIGNED"] = RTLIL::Const(0);
			cell->parameters["\\A_WIDTH"] = RTLIL::Const(sync_low_signals.size());
			cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
			cell->setPort("\\A", sync_low_signals);
			cell->setPort("\\Y", mod->addWire(NEW_ID));
			sync_high_signals.append(cell->getPort("\\Y"));
		}

		if (sync_high_signals.size() > 1) {
			RTLIL::Cell *cell = mod->addCell(NEW_ID, "$reduce_or");
			cell->parameters["\\A_SIGNED"] = RTLIL::Const(0);
			cell->parameters["\\A_WIDTH"] = RTLIL::Const(sync_high_signals.size());
			cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
			cell->setPort("\\A", sync_high_signals);
			cell->setPort("\\Y", sync_high_signals = mod->addWire(NEW_ID));
		}

		RTLIL::Cell *inv_cell = mod->addCell(NEW_ID, "$not");
		inv_cell->parameters["\\A_SIGNED"] = RTLIL::Const(0);
		inv_cell->parameters["\\A_WIDTH"] = RTLIL::Const(sig_d.size());
		inv_cell->parameters["\\Y_WIDTH"] = RTLIL::Const(sig_d.size());
		inv_cell->setPort("\\A", sync_value);
		inv_cell->setPort("\\Y", sync_value_inv = mod->addWire(NEW_ID, sig_d.size()));

		RTLIL::Cell *mux_set_cell = mod->addCell(NEW_ID, "$mux");
		mux_set_cell->parameters["\\WIDTH"] = RTLIL::Const(sig_d.size());
		mux_set_cell->setPort("\\A", sig_sr_set);
		mux_set_cell->setPort("\\B", sync_value);
		mux_set_cell->setPort("\\S", sync_high_signals);
		mux_set_cell->setPort("\\Y", sig_sr_set = mod->addWire(NEW_ID, sig_d.size()));

		RTLIL::Cell *mux_clr_cell = mod->addCell(NEW_ID, "$mux");
		mux_clr_cell->parameters["\\WIDTH"] = RTLIL::Const(sig_d.size());
		mux_clr_cell->setPort("\\A", sig_sr_clr);
		mux_clr_cell->setPort("\\B", sync_value_inv);
		mux_clr_cell->setPort("\\S", sync_high_signals);
		mux_clr_cell->setPort("\\Y", sig_sr_clr = mod->addWire(NEW_ID, sig_d.size()));
	}

	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);

	RTLIL::Cell *cell = mod->addCell(sstr.str(), "$dffsr");
	cell->attributes = proc->attributes;
	cell->parameters["\\WIDTH"] = RTLIL::Const(sig_d.size());
	cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity, 1);
	cell->parameters["\\SET_POLARITY"] = RTLIL::Const(true, 1);
	cell->parameters["\\CLR_POLARITY"] = RTLIL::Const(true, 1);
	cell->setPort("\\D", sig_d);
	cell->setPort("\\Q", sig_q);
	cell->setPort("\\CLK", clk);
	cell->setPort("\\SET", sig_sr_set);
	cell->setPort("\\CLR", sig_sr_clr);

	log("  created %s cell `%s' with %s edge clock and multiple level-sensitive resets.\n",
			cell->type.c_str(), cell->name.c_str(), clk_polarity ? "positive" : "negative");
}

void gen_dffsr(RTLIL::Module *mod, RTLIL::SigSpec sig_in, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_out,
		bool clk_polarity, bool set_polarity, RTLIL::SigSpec clk, RTLIL::SigSpec set, RTLIL::Process *proc)
{
	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);

	RTLIL::SigSpec sig_set_inv = mod->addWire(NEW_ID, sig_in.size());
	RTLIL::SigSpec sig_sr_set = mod->addWire(NEW_ID, sig_in.size());
	RTLIL::SigSpec sig_sr_clr = mod->addWire(NEW_ID, sig_in.size());

	RTLIL::Cell *inv_set = mod->addCell(NEW_ID, "$not");
	inv_set->parameters["\\A_SIGNED"] = RTLIL::Const(0);
	inv_set->parameters["\\A_WIDTH"] = RTLIL::Const(sig_in.size());
	inv_set->parameters["\\Y_WIDTH"] = RTLIL::Const(sig_in.size());
	inv_set->setPort("\\A", sig_set);
	inv_set->setPort("\\Y", sig_set_inv);

	RTLIL::Cell *mux_sr_set = mod->addCell(NEW_ID, "$mux");
	mux_sr_set->parameters["\\WIDTH"] = RTLIL::Const(sig_in.size());
	mux_sr_set->setPort(set_polarity ? "\\A" : "\\B", RTLIL::Const(0, sig_in.size()));
	mux_sr_set->setPort(set_polarity ? "\\B" : "\\A", sig_set);
	mux_sr_set->setPort("\\Y", sig_sr_set);
	mux_sr_set->setPort("\\S", set);

	RTLIL::Cell *mux_sr_clr = mod->addCell(NEW_ID, "$mux");
	mux_sr_clr->parameters["\\WIDTH"] = RTLIL::Const(sig_in.size());
	mux_sr_clr->setPort(set_polarity ? "\\A" : "\\B", RTLIL::Const(0, sig_in.size()));
	mux_sr_clr->setPort(set_polarity ? "\\B" : "\\A", sig_set_inv);
	mux_sr_clr->setPort("\\Y", sig_sr_clr);
	mux_sr_clr->setPort("\\S", set);

	RTLIL::Cell *cell = mod->addCell(sstr.str(), "$dffsr");
	cell->attributes = proc->attributes;
	cell->parameters["\\WIDTH"] = RTLIL::Const(sig_in.size());
	cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity, 1);
	cell->parameters["\\SET_POLARITY"] = RTLIL::Const(true, 1);
	cell->parameters["\\CLR_POLARITY"] = RTLIL::Const(true, 1);
	cell->setPort("\\D", sig_in);
	cell->setPort("\\Q", sig_out);
	cell->setPort("\\CLK", clk);
	cell->setPort("\\SET", sig_sr_set);
	cell->setPort("\\CLR", sig_sr_clr);

	log("  created %s cell `%s' with %s edge clock and %s level non-const reset.\n", cell->type.c_str(), cell->name.c_str(),
			clk_polarity ? "positive" : "negative", set_polarity ? "positive" : "negative");
}

void gen_dff(RTLIL::Module *mod, RTLIL::SigSpec sig_in, RTLIL::Const val_rst, RTLIL::SigSpec sig_out,
		bool clk_polarity, bool arst_polarity, RTLIL::SigSpec clk, RTLIL::SigSpec *arst, RTLIL::Process *proc)
{
	std::stringstream sstr;
	sstr << "$procdff$" << (autoidx++);

	RTLIL::Cell *cell = mod->addCell(sstr.str(), clk.empty() ? "$ff" : arst ? "$adff" : "$dff");
	cell->attributes = proc->attributes;

	cell->parameters["\\WIDTH"] = RTLIL::Const(sig_in.size());
	if (arst) {
		cell->parameters["\\ARST_POLARITY"] = RTLIL::Const(arst_polarity, 1);
		cell->parameters["\\ARST_VALUE"] = val_rst;
	}
	if (!clk.empty()) {
		cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity, 1);
	}

	cell->setPort("\\D", sig_in);
	cell->setPort("\\Q", sig_out);
	if (arst)
		cell->setPort("\\ARST", *arst);
	if (!clk.empty())
		cell->setPort("\\CLK", clk);

	if (!clk.empty())
		log("  created %s cell `%s' with %s edge clock", cell->type.c_str(), cell->name.c_str(), clk_polarity ? "positive" : "negative");
	else
		log("  created %s cell `%s' with global clock", cell->type.c_str(), cell->name.c_str());
	if (arst)
		log(" and %s level reset", arst_polarity ? "positive" : "negative");
	log(".\n");
}

void proc_dff(RTLIL::Module *mod, RTLIL::Process *proc, ConstEval &ce)
{
	while (1)
	{
		RTLIL::SigSpec sig = find_any_lvalue(proc);
		bool free_sync_level = false;

		if (sig.size() == 0)
			break;

		log("Creating register for signal `%s.%s' using process `%s.%s'.\n",
				mod->name.c_str(), log_signal(sig), mod->name.c_str(), proc->name.c_str());

		RTLIL::SigSpec insig = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
		RTLIL::SigSpec rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
		RTLIL::SyncRule *sync_level = NULL;
		RTLIL::SyncRule *sync_edge = NULL;
		RTLIL::SyncRule *sync_always = NULL;
		bool global_clock = false;

		std::map<RTLIL::SigSpec, std::set<RTLIL::SyncRule*>> many_async_rules;

		for (auto sync : proc->syncs)
		for (auto &action : sync->actions)
		{
			if (action.first.extract(sig).size() == 0)
				continue;

			if (sync->type == RTLIL::SyncType::ST0 || sync->type == RTLIL::SyncType::ST1) {
				if (sync_level != NULL && sync_level != sync) {
					// log_error("Multiple level sensitive events found for this signal!\n");
					many_async_rules[rstval].insert(sync_level);
					rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
				}
				rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
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
			else if (sync->type == RTLIL::SyncType::STg) {
				sig.replace(action.first, action.second, &insig);
				global_clock = true;
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
				sync_level->signal = mod->addWire(NEW_ID);
				sync_level->actions.push_back(RTLIL::SigSig(sig, rstval));
				free_sync_level = true;

				RTLIL::SigSpec inputs, compare;
				for (auto &it : many_async_rules[rstval]) {
					inputs.append(it->signal);
					compare.append(it->type == RTLIL::SyncType::ST0 ? RTLIL::State::S1 : RTLIL::State::S0);
				}
				log_assert(inputs.size() == compare.size());

				RTLIL::Cell *cell = mod->addCell(NEW_ID, "$ne");
				cell->parameters["\\A_SIGNED"] = RTLIL::Const(false, 1);
				cell->parameters["\\B_SIGNED"] = RTLIL::Const(false, 1);
				cell->parameters["\\A_WIDTH"] = RTLIL::Const(inputs.size());
				cell->parameters["\\B_WIDTH"] = RTLIL::Const(inputs.size());
				cell->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
				cell->setPort("\\A", inputs);
				cell->setPort("\\B", compare);
				cell->setPort("\\Y", sync_level->signal);

				many_async_rules.clear();
			}
			else
			{
				rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
				sync_level = NULL;
			}
		}

		SigSpec sig_q = sig;
		ce.assign_map.apply(insig);
		ce.assign_map.apply(rstval);
		ce.assign_map.apply(sig);

		if (rstval == sig) {
			rstval = RTLIL::SigSpec(RTLIL::State::Sz, sig.size());
			sync_level = NULL;
		}

		if (sync_always) {
			if (sync_edge || sync_level || many_async_rules.size() > 0)
				log_error("Mixed always event with edge and/or level sensitive events!\n");
			log("  created direct connection (no actual register cell created).\n");
			mod->connect(RTLIL::SigSig(sig, insig));
			continue;
		}

		if (!sync_edge && !global_clock)
			log_error("Missing edge-sensitive event for this signal!\n");

		if (many_async_rules.size() > 0)
		{
			log_warning("Complex async reset for dff `%s'.\n", log_signal(sig));
			gen_dffsr_complex(mod, insig, sig, sync_edge->signal, sync_edge->type == RTLIL::SyncType::STp, many_async_rules, proc);
		}
		else if (!rstval.is_fully_const() && !ce.eval(rstval))
		{
			log_warning("Async reset value `%s' is not constant!\n", log_signal(rstval));
			gen_dffsr(mod, insig, rstval, sig_q,
					sync_edge->type == RTLIL::SyncType::STp,
					sync_level && sync_level->type == RTLIL::SyncType::ST1,
					sync_edge->signal, sync_level->signal, proc);
		}
		else
			gen_dff(mod, insig, rstval.as_const(), sig_q,
					sync_edge && sync_edge->type == RTLIL::SyncType::STp,
					sync_level && sync_level->type == RTLIL::SyncType::ST1,
					sync_edge ? sync_edge->signal : SigSpec(),
					sync_level ? &sync_level->signal : NULL, proc);

		if (free_sync_level)
			delete sync_level;
	}
}

struct ProcDffPass : public Pass {
	ProcDffPass() : Pass("proc_dff", "extract flip-flops from processes") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_dff [selection]\n");
		log("\n");
		log("This pass identifies flip-flops in the processes and converts them to\n");
		log("d-type flip-flop cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing PROC_DFF pass (convert process syncs to FFs).\n");

		extra_args(args, 1, design);

		for (auto mod : design->modules())
			if (design->selected(mod)) {
				ConstEval ce(mod);
				for (auto &proc_it : mod->processes)
					if (design->selected(mod, proc_it.second))
						proc_dff(mod, proc_it.second, ce);
			}
	}
} ProcDffPass;

PRIVATE_NAMESPACE_END
