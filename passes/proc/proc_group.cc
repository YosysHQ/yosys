/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2019  whitequark <whitequark@whitequark.org>
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
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ProcGroupWorker
{
	bool combine;

	std::vector<pool<RTLIL::SigBit>> lhs_groups;
	dict<RTLIL::SigBit, int> lhs_bits;

	ProcGroupWorker(bool combine = true) : combine(combine) {}

	void collect_case(RTLIL::CaseRule *cs)
	{
		// An action like `assign { \r0 \r0 } 2'01` is valid, although meaningless; normalize everything so that
		// every bit is assigned exactly once.
		pool<RTLIL::SigBit> assigned;
		for (auto &act : cs->actions)
			for (auto &bit : act.first)
				if (bit.wire)
					assigned.insert(bit);

		int new_group = -1;
		dict<int, size_t> group_sizes;
		for (auto &bit : assigned)
		{
			int group;
			if (lhs_bits.count(bit))
				group = lhs_bits[bit];
			else
			{
				if (new_group == -1)
				{
					new_group = lhs_groups.size();
					lhs_groups.push_back({});
				}
				group = new_group;
			}
			group_sizes[group]++;
		}

		for (auto &group_size : group_sizes)
		{
			// Fast path: if we assigned every bit from this group, nothing to do here.
			if (lhs_groups[group_size.first].size() == group_size.second)
				continue;
			// Slow path: if we only assigned some bits from this group, split off these bits into a new group.
			int split_group = lhs_groups.size();
			lhs_groups.push_back({});
			for (auto &bit : assigned)
				if (lhs_bits[bit] == group_size.first)
				{
					lhs_groups[group_size.first].erase(bit);
					lhs_groups[split_group].insert(bit);
					lhs_bits[bit] = split_group;
				}
		}

		for (auto &sw : cs->switches)
			for (auto &cs : sw->cases)
				collect_case(cs);
	}

	void rewrite_actions(dict<int, RTLIL::SigSig> &grouped_actions, std::vector<RTLIL::SigSig> &actions)
	{
		for (auto &it : grouped_actions)
		{
			// Canonicalize bit order.
			dict<RTLIL::SigBit, RTLIL::SigBit> bits = it.second.first.to_sigbit_dict(it.second.second);
			bits.sort();

			RTLIL::SigSig action;
			for (auto &it : bits)
			{
				action.first.append(it.first);
				action.second.append(it.second);
			}
			actions.push_back(action);
		}
		grouped_actions.clear();
	}

	void rewrite_case(RTLIL::CaseRule *cs)
	{
		pool<RTLIL::SigBit> assigned;
		dict<int, RTLIL::SigSig> grouped_actions;
		std::vector<RTLIL::SigSig> new_actions;

		for (auto it = cs->actions.rbegin(); it != cs->actions.rend(); ++it)
		{
			for (int i = 0; i < it->first.size(); i++)
			{
				RTLIL::SigBit act_lhs = it->first[i], act_rhs = it->second[i];
				if (assigned.count(act_lhs))
					continue;
				log_assert(lhs_bits.count(act_lhs));
				RTLIL::SigSig &grouped_action = grouped_actions[lhs_bits[act_lhs]];
				grouped_action.first.append(act_lhs);
				grouped_action.second.append(act_rhs);
				assigned.insert(act_lhs);
			}

			if (!combine)
				rewrite_actions(grouped_actions, new_actions);
		}

		if (combine)
			rewrite_actions(grouped_actions, new_actions);

		cs->actions = {new_actions.rbegin(), new_actions.rend()};

		for (auto &sw : cs->switches)
			for (auto &cs : sw->cases)
				rewrite_case(cs);
	}

	void do_process(RTLIL::Process *pr)
	{
		collect_case(&pr->root_case);
		rewrite_case(&pr->root_case);
	}
};

struct ProcGroupPass : public Pass {
	ProcGroupPass() : Pass("proc_group", "canonicalize assignments in processes") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_group [selection]\n");
		log("\n");
		log("This pass rewrites assignments in processes such that any two assignments assign\n");
		log("to either identical or non-intersecting sequences of bits.\n");
		log("\n");
		log("    -combine\n");
		log("        Combine assignments when possible.\n");
		log("\n");

	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool combine = false;

		log_header(design, "Executing PROC_GROUP pass (canonicalize assignments in processes).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-combine") {
				combine = true;
				continue;
			}
		}
		extra_args(args, argidx, design);

		for (auto mod : design->modules())
			if (design->selected(mod))
				for (auto &proc_it : mod->processes)
					if (design->selected(mod, proc_it.second))
					{
						ProcGroupWorker worker(combine);
						worker.do_process(proc_it.second);
					}
	}
} ProcGroupPass;

PRIVATE_NAMESPACE_END
