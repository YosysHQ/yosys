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
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>

static bool check_signal(RTLIL::Module *mod, RTLIL::SigSpec signal, RTLIL::SigSpec ref, bool &polarity)
{
	if (signal.width != 1)
		return false;
	if (signal == ref)
		return true;

	for (auto &cell_it : mod->cells) {
		RTLIL::Cell *cell = cell_it.second;
		if (cell->type == "$reduce_or" && cell->connections["\\Y"] == signal)
			return check_signal(mod, cell->connections["\\A"], ref, polarity);
		if (cell->type == "$reduce_bool" && cell->connections["\\Y"] == signal)
			return check_signal(mod, cell->connections["\\A"], ref, polarity);
		if (cell->type == "$logic_not" && cell->connections["\\Y"] == signal) {
			polarity = !polarity;
			return check_signal(mod, cell->connections["\\A"], ref, polarity);
		}
		if (cell->type == "$not" && cell->connections["\\Y"] == signal) {
			polarity = !polarity;
			return check_signal(mod, cell->connections["\\A"], ref, polarity);
		}
		if (cell->type == "$eq" && cell->connections["\\Y"] == signal) {
			if (cell->connections["\\A"].is_fully_const()) {
				if (!cell->connections["\\A"].as_bool())
					polarity = !polarity;
				return check_signal(mod, cell->connections["\\B"], ref, polarity);
			}
			if (cell->connections["\\B"].is_fully_const()) {
				if (!cell->connections["\\B"].as_bool())
					polarity = !polarity;
				return check_signal(mod, cell->connections["\\A"], ref, polarity);
			}
		}
		if (cell->type == "$ne" && cell->connections["\\Y"] == signal) {
			if (cell->connections["\\A"].is_fully_const()) {
				if (cell->connections["\\A"].as_bool())
					polarity = !polarity;
				return check_signal(mod, cell->connections["\\B"], ref, polarity);
			}
			if (cell->connections["\\B"].is_fully_const()) {
				if (cell->connections["\\B"].as_bool())
					polarity = !polarity;
				return check_signal(mod, cell->connections["\\A"], ref, polarity);
			}
		}
	}

	return false;
}

static void apply_const(RTLIL::Module *mod, const RTLIL::SigSpec rspec, RTLIL::SigSpec &rval, RTLIL::CaseRule *cs, RTLIL::SigSpec const_sig, bool polarity, bool unknown)
{
	for (auto &action : cs->actions) {
		if (unknown)
			rspec.replace(action.first, RTLIL::SigSpec(RTLIL::State::Sm, action.second.width), &rval);
		else
			rspec.replace(action.first, action.second, &rval);
	}

	for (auto sw : cs->switches) {
		if (sw->signal.width == 0) {
			for (auto cs2 : sw->cases)
				apply_const(mod, rspec, rval, cs2, const_sig, polarity, unknown);
		}
		bool this_polarity = polarity;
		if (check_signal(mod, sw->signal, const_sig, this_polarity)) {
			for (auto cs2 : sw->cases) {
				for (auto comp : cs2->compare)
					if (comp == RTLIL::SigSpec(this_polarity, 1))
						goto matched_case;
				if (cs2->compare.size() == 0) {
			matched_case:
					apply_const(mod, rspec, rval, cs2, const_sig, polarity, false);
					break;
				}
			}
		} else {
			for (auto cs2 : sw->cases)
				apply_const(mod, rspec, rval, cs2, const_sig, polarity, true);
		}
	}
}

static void eliminate_const(RTLIL::Module *mod, RTLIL::CaseRule *cs, RTLIL::SigSpec const_sig, bool polarity)
{
	for (auto sw : cs->switches) {
		bool this_polarity = polarity;
		if (check_signal(mod, sw->signal, const_sig, this_polarity)) {
			bool found_rem_path = false;
			for (size_t i = 0; i < sw->cases.size(); i++) {
				RTLIL::CaseRule *cs2 = sw->cases[i];
				for (auto comp : cs2->compare)
					if (comp == RTLIL::SigSpec(this_polarity, 1))
						goto matched_case;
				if (found_rem_path) {
			matched_case:
					sw->cases.erase(sw->cases.begin() + (i--));
					delete cs2;
					continue;
				}
				found_rem_path = true;
				cs2->compare.clear();
			}
			sw->signal = RTLIL::SigSpec();
		} else {
			for (auto cs2 : sw->cases)
				eliminate_const(mod, cs2, const_sig, polarity);
		}
	}
}

static void proc_arst(RTLIL::Module *mod, RTLIL::Process *proc, SigMap &assign_map)
{
	if (proc->root_case.switches.size() != 1)
		return;

	RTLIL::SigSpec root_sig = proc->root_case.switches[0]->signal;

	for (auto &sync : proc->syncs) {
		if (sync->type == RTLIL::SyncType::STp || sync->type == RTLIL::SyncType::STn) {
			bool polarity = sync->type == RTLIL::SyncType::STp;
			if (check_signal(mod, root_sig, sync->signal, polarity)) {
				log("Found async reset %s in `%s.%s'.\n", log_signal(sync->signal), mod->name.c_str(), proc->name.c_str());
				sync->type = sync->type == RTLIL::SyncType::STp ? RTLIL::SyncType::ST1 : RTLIL::SyncType::ST0;
				for (auto &action : sync->actions) {
					RTLIL::SigSpec rspec = action.second;
					RTLIL::SigSpec rval = RTLIL::SigSpec(RTLIL::State::Sm, rspec.width);
					RTLIL::SigSpec last_rval;
					for (int count = 0; rval != last_rval; count++) {
						last_rval = rval;
						apply_const(mod, rspec, rval, &proc->root_case, root_sig, polarity, false);
						assign_map.apply(rval);
						if (rval.is_fully_const())
							break;
						if (count > 100)
							log_error("Async reset %s yields endless loop at value %s for signal %s.\n",
									log_signal(sync->signal), log_signal(rval), log_signal(action.first));
						rspec = rval;
					}
					if (rval.has_marked_bits())
						log_error("Async reset %s yields non-constant value %s for signal %s.\n",
								log_signal(sync->signal), log_signal(rval), log_signal(action.first));
					action.second = rval;
				}
				eliminate_const(mod, &proc->root_case, root_sig, polarity);
			}
		}
	}
}

struct ProcArstPass : public Pass {
	ProcArstPass() : Pass("proc_arst") { }
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing PROC_ARST pass (detect async resets in processes).\n");

		extra_args(args, 1, design);

		for (auto &mod_it : design->modules) {
			SigMap assign_map(mod_it.second);
			for (auto &proc_it : mod_it.second->processes)
				proc_arst(mod_it.second, proc_it.second, assign_map);
		}
	}
} ProcArstPass;
 
