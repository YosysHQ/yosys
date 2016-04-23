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
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void proc_rmdead(RTLIL::SwitchRule *sw, int &counter)
{
	BitPatternPool pool(sw->signal);

	for (size_t i = 0; i < sw->cases.size(); i++)
	{
		bool is_default = GetSize(sw->cases[i]->compare) == 0 && (!pool.empty() || GetSize(sw->signal) == 0);

		for (size_t j = 0; j < sw->cases[i]->compare.size(); j++) {
			RTLIL::SigSpec sig = sw->cases[i]->compare[j];
			if (!sig.is_fully_const())
				continue;
			if (!pool.take(sig))
				sw->cases[i]->compare.erase(sw->cases[i]->compare.begin() + (j--));
		}

		if (!is_default) {
			if (sw->cases[i]->compare.size() == 0) {
				delete sw->cases[i];
				sw->cases.erase(sw->cases.begin() + (i--));
				counter++;
				continue;
			}
			// if (pool.empty())
			// 	sw->cases[i]->compare.clear();
		}

		for (auto switch_it : sw->cases[i]->switches)
			proc_rmdead(switch_it, counter);

		if (is_default)
			pool.take_all();
	}
}

struct ProcRmdeadPass : public Pass {
	ProcRmdeadPass() : Pass("proc_rmdead", "eliminate dead trees in decision trees") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_rmdead [selection]\n");
		log("\n");
		log("This pass identifies unreachable branches in decision trees and removes them.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing PROC_RMDEAD pass (remove dead branches from decision trees).\n");

		extra_args(args, 1, design);

		int total_counter = 0;
		for (auto mod : design->modules()) {
			if (!design->selected(mod))
				continue;
			for (auto &proc_it : mod->processes) {
				if (!design->selected(mod, proc_it.second))
					continue;
				int counter = 0;
				for (auto switch_it : proc_it.second->root_case.switches)
					proc_rmdead(switch_it, counter);
				if (counter > 0)
					log("Removed %d dead cases from process %s in module %s.\n", counter,
							proc_it.first.c_str(), log_id(mod));
				total_counter += counter;
			}
		}

		log("Removed a total of %d dead cases.\n", total_counter);
	}
} ProcRmdeadPass;

PRIVATE_NAMESPACE_END
