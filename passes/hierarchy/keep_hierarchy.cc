/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/yosys.h"
#include "kernel/cost.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct KeepHierarchyPass : public Pass {
	KeepHierarchyPass() : Pass("keep_hierarchy", "TODO") {} // TODO
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    keep_hierarchy [options]\n");
		log("\n");
		log("Add the keep_hierarchy attribute.\n");
		log("\n");
		log("    -max_cost <max_cost>\n");
		log("        only add the attribute to modules estimated to have more\n");
		log("        than <max_cost> gates\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		unsigned int max_cost = 0;

		log_header(design, "Executing KEEP_HIERARCHY pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_cost" && argidx+1 < args.size()) {
				max_cost = std::stoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		CellCosts costs(CellCosts::DEFAULT, design);

		for (auto module : design->selected_modules()) {
			if (max_cost) {
				unsigned int cost = costs.get(module);
				if (cost > max_cost) {
					log("Marking %s (module too big: %d > %d).\n", log_id(module), cost, max_cost);
					module->set_bool_attribute(ID::keep_hierarchy);
				}
			} else {
				log("Marking %s.\n", log_id(module));
				module->set_bool_attribute(ID::keep_hierarchy);
			}
		}
	}
} ZinitPass;

PRIVATE_NAMESPACE_END
