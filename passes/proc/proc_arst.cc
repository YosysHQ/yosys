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

YOSYS_NAMESPACE_BEGIN
extern void proc_clean_case(RTLIL::CaseRule *cs, bool &did_something, int &count, int max_depth);
YOSYS_NAMESPACE_END

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool check_signal(RTLIL::Module *mod, RTLIL::SigSpec signal, RTLIL::SigSpec ref, bool &polarity)
{
	if (signal.size() != 1)
		return false;
	if (signal == ref)
		return true;

	for (auto cell : mod->cells())
	{
		if (cell->type == ID($reduce_or) && cell->getPort(ID::Y) == signal)
			return check_signal(mod, cell->getPort(ID::A), ref, polarity);

		if (cell->type == ID($reduce_bool) && cell->getPort(ID::Y) == signal)
			return check_signal(mod, cell->getPort(ID::A), ref, polarity);

		if (cell->type == ID($logic_not) && cell->getPort(ID::Y) == signal) {
			polarity = !polarity;
			return check_signal(mod, cell->getPort(ID::A), ref, polarity);
		}

		if (cell->type == ID($not) && cell->getPort(ID::Y) == signal) {
			polarity = !polarity;
			return check_signal(mod, cell->getPort(ID::A), ref, polarity);
		}

		if (cell->type.in(ID($eq), ID($eqx)) && cell->getPort(ID::Y) == signal) {
			if (cell->getPort(ID::A).is_fully_const()) {
				if (!cell->getPort(ID::A).as_bool())
					polarity = !polarity;
				return check_signal(mod, cell->getPort(ID::B), ref, polarity);
			}
			if (cell->getPort(ID::B).is_fully_const()) {
				if (!cell->getPort(ID::B).as_bool())
					polarity = !polarity;
				return check_signal(mod, cell->getPort(ID::A), ref, polarity);
			}
		}

		if (cell->type.in(ID($ne), ID($nex)) && cell->getPort(ID::Y) == signal) {
			if (cell->getPort(ID::A).is_fully_const()) {
				if (cell->getPort(ID::A).as_bool())
					polarity = !polarity;
				return check_signal(mod, cell->getPort(ID::B), ref, polarity);
			}
			if (cell->getPort(ID::B).is_fully_const()) {
				if (cell->getPort(ID::B).as_bool())
					polarity = !polarity;
				return check_signal(mod, cell->getPort(ID::A), ref, polarity);
			}
		}
	}

	return false;
}

void apply_const(RTLIL::Module *mod, const RTLIL::SigSpec rspec, RTLIL::SigSpec &rval, RTLIL::CaseRule *cs, RTLIL::SigSpec const_sig, bool polarity, bool unknown)
{
	for (auto &action : cs->actions) {
		if (unknown)
			rspec.replace(action.first, RTLIL::SigSpec(RTLIL::State::Sm, action.second.size()), &rval);
		else
			rspec.replace(action.first, action.second, &rval);
	}

	for (auto sw : cs->switches) {
		if (sw->signal.size() == 0) {
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

void eliminate_const(RTLIL::Module *mod, RTLIL::CaseRule *cs, RTLIL::SigSpec const_sig, bool polarity)
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

	int dummy_count = 0;
	bool did_something = true;
	while (did_something) {
		did_something = false;
		proc_clean_case(cs, did_something, dummy_count, 1);
	}
}

RTLIL::SigSpec apply_reset(RTLIL::Module *mod, RTLIL::Process *proc, RTLIL::SyncRule *sync, SigMap &assign_map, RTLIL::SigSpec root_sig, bool polarity, RTLIL::SigSpec sig, RTLIL::SigSpec log_sig) {
	RTLIL::SigSpec rspec = assign_map(sig);
	RTLIL::SigSpec rval = RTLIL::SigSpec(RTLIL::State::Sm, rspec.size());
	for (int i = 0; i < GetSize(rspec); i++)
		if (rspec[i].wire == NULL)
			rval[i] = rspec[i];
	RTLIL::SigSpec last_rval;
	for (int count = 0; rval != last_rval; count++) {
		last_rval = rval;
		apply_const(mod, rspec, rval, &proc->root_case, root_sig, polarity, false);
		assign_map.apply(rval);
		if (rval.is_fully_const())
			break;
		if (count > 100)
			log_error("Async reset %s yields endless loop at value %s for signal %s.\n",
					log_signal(sync->signal), log_signal(rval), log_signal(log_sig));
		rspec = rval;
	}
	if (rval.has_marked_bits())
		log_error("Async reset %s yields non-constant value %s for signal %s.\n",
				log_signal(sync->signal), log_signal(rval), log_signal(log_sig));
	return rval;
}

void proc_arst(RTLIL::Module *mod, RTLIL::Process *proc, SigMap &assign_map)
{
	std::vector<RTLIL::SyncRule *> arst_syncs;
	std::vector<RTLIL::SyncRule *> edge_syncs;
	std::vector<RTLIL::SyncRule *> other_syncs;

	for (auto &sync : proc->syncs) {
		if (sync->type == RTLIL::SyncType::ST0 || sync->type == RTLIL::SyncType::ST1) {
			arst_syncs.push_back(sync);
		} else if (sync->type == RTLIL::SyncType::STp || sync->type == RTLIL::SyncType::STn) {
			edge_syncs.push_back(sync);
		} else {
			other_syncs.push_back(sync);
		}
	}

	bool did_something = false;

	while (proc->root_case.switches.size() == 1) {
		RTLIL::SigSpec root_sig = proc->root_case.switches[0]->signal;

		bool found = false;
		for (auto it = edge_syncs.begin(); it != edge_syncs.end(); ++it) {
			auto sync = *it;
			bool polarity = sync->type == RTLIL::SyncType::STp;
			if (check_signal(mod, root_sig, sync->signal, polarity)) {
				if (edge_syncs.size() > 1) {
					log("Found async reset %s in `%s.%s'.\n", log_signal(sync->signal), mod->name.c_str(), proc->name.c_str());
					sync->type = sync->type == RTLIL::SyncType::STp ? RTLIL::SyncType::ST1 : RTLIL::SyncType::ST0;
					arst_syncs.push_back(sync);
					edge_syncs.erase(it);
					for (auto &action : sync->actions) {
						action.second = apply_reset(mod, proc, sync, assign_map, root_sig, polarity, action.second, action.first);
					}
					for (auto &memwr : sync->mem_write_actions) {
						RTLIL::SigSpec en = apply_reset(mod, proc, sync, assign_map, root_sig, polarity, memwr.enable, memwr.enable);
						if (!en.is_fully_zero()) {
							log_error("Async reset %s causes memory write to %s.\n",
									log_signal(sync->signal), log_id(memwr.memid));
						}
						apply_reset(mod, proc, sync, assign_map, root_sig, polarity, memwr.address, memwr.address);
						apply_reset(mod, proc, sync, assign_map, root_sig, polarity, memwr.data, memwr.data);
					}
					sync->mem_write_actions.clear();
					eliminate_const(mod, &proc->root_case, root_sig, polarity);
				} else {
					log("Found VHDL-style edge-trigger %s in `%s.%s'.\n", log_signal(sync->signal), mod->name.c_str(), proc->name.c_str());
					eliminate_const(mod, &proc->root_case, root_sig, !polarity);
				}
				did_something = true;
				found = true;
				break;
			}
		}
		if (!found)
			break;
	}

	if (did_something) {
		proc->syncs.clear();
		proc->syncs.insert(proc->syncs.end(), arst_syncs.begin(), arst_syncs.end());
		proc->syncs.insert(proc->syncs.end(), edge_syncs.begin(), edge_syncs.end());
		proc->syncs.insert(proc->syncs.end(), other_syncs.begin(), other_syncs.end());
	}
}

struct ProcArstPass : public Pass {
	ProcArstPass() : Pass("proc_arst", "detect asynchronous resets") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_arst [-global_arst [!]<netname>] [selection]\n");
		log("\n");
		log("This pass identifies asynchronous resets in the processes and converts them\n");
		log("to a different internal representation that is suitable for generating\n");
		log("flip-flop cells with asynchronous resets.\n");
		log("\n");
		log("    -global_arst [!]<netname>\n");
		log("        In modules that have a net with the given name, use this net as async\n");
		log("        reset for registers that have been assign initial values in their\n");
		log("        declaration ('reg foobar = constant_value;'). Use the '!' modifier for\n");
		log("        active low reset signals. Note: the frontend stores the default value\n");
		log("        in the 'init' attribute on the net.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string global_arst;
		bool global_arst_neg = false;

		log_header(design, "Executing PROC_ARST pass (detect async resets in processes).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-global_arst" && argidx+1 < args.size()) {
				global_arst = args[++argidx];
				if (!global_arst.empty() && global_arst[0] == '!') {
					global_arst_neg = true;
					global_arst = global_arst.substr(1);
				}
				global_arst = RTLIL::escape_id(global_arst);
				continue;
			}
			break;
		}

		extra_args(args, argidx, design);
		pool<Wire*> delete_initattr_wires;

		for (auto mod : design->modules())
			if (design->selected(mod)) {
				SigMap assign_map(mod);
				for (auto &proc_it : mod->processes) {
					if (!design->selected(mod, proc_it.second))
						continue;
					proc_arst(mod, proc_it.second, assign_map);
					if (global_arst.empty() || mod->wire(global_arst) == nullptr)
						continue;
					std::vector<RTLIL::SigSig> arst_actions;
					for (auto sync : proc_it.second->syncs)
						if (sync->type == RTLIL::SyncType::STp || sync->type == RTLIL::SyncType::STn)
							for (auto &act : sync->actions) {
								RTLIL::SigSpec arst_sig, arst_val;
								for (auto &chunk : act.first.chunks())
									if (chunk.wire && chunk.wire->attributes.count(ID::init)) {
										RTLIL::SigSpec value = chunk.wire->attributes.at(ID::init);
										value.extend_u0(chunk.wire->width, false);
										arst_sig.append(chunk);
										arst_val.append(value.extract(chunk.offset, chunk.width));
										delete_initattr_wires.insert(chunk.wire);
									}
								if (arst_sig.size()) {
									log("Added global reset to process %s: %s <- %s\n",
											proc_it.first.c_str(), log_signal(arst_sig), log_signal(arst_val));
									arst_actions.push_back(RTLIL::SigSig(arst_sig, arst_val));
								}
							}
					if (!arst_actions.empty()) {
						RTLIL::SyncRule *sync = new RTLIL::SyncRule;
						sync->type = global_arst_neg ? RTLIL::SyncType::ST0 : RTLIL::SyncType::ST1;
						sync->signal = mod->wire(global_arst);
						sync->actions = arst_actions;
						proc_it.second->syncs.push_back(sync);
					}
				}
			}

		for (auto wire : delete_initattr_wires)
			wire->attributes.erase(ID::init);
	}
} ProcArstPass;

PRIVATE_NAMESPACE_END
