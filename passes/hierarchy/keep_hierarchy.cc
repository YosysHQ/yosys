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

#include <inttypes.h>
#include "kernel/yosys.h"
#include "kernel/cost.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ThresholdHierarchyKeeping {
	Design *design;
	CellCosts costs;
	dict<Module *, int> done;
	pool<Module *> in_progress;
	uint64_t threshold;

	ThresholdHierarchyKeeping(Design *design, uint64_t threshold)
		: design(design), costs(design), threshold(threshold) {}

	uint64_t visit(RTLIL::Module *module) {
		if (module->has_attribute(ID(gate_cost_equivalent)))
			return module->attributes[ID(gate_cost_equivalent)].as_int();

		if (module->has_attribute(ID(keep_hierarchy)))
			return 0;

		if (module->get_blackbox_attribute())
			log_error("Missing cost information on instanced blackbox %s\n", log_id(module));

		if (done.count(module))
			return done.at(module);

		if (in_progress.count(module))
			log_error("Circular hierarchy\n");
		in_progress.insert(module);

		uint64_t size = 0;
		module->has_processes_warn();

		for (auto cell : module->cells()) {
			if (!cell->type.isPublic()) {
				size += costs.get(cell);
			} else {
				RTLIL::Module *submodule = design->module(cell->type);
				if (!submodule)
					log_error("Hierarchy contains unknown module '%s' (instanced as %s in %s)\n",
							  log_id(cell->type), log_id(cell), log_id(module));
				size += visit(submodule);
			}
		}

		if (size > threshold) {
			log("Keeping %s (estimated size above threshold: %" PRIu64 " > %" PRIu64 ").\n", log_id(module), size, threshold);
			module->set_bool_attribute(ID::keep_hierarchy);
			size = 0;
		}

		in_progress.erase(module);
		done[module] = size;
		return size;
	}
};

struct KeepHierarchyPass : public Pass {
	KeepHierarchyPass() : Pass("keep_hierarchy", "selectively add the keep_hierarchy attribute") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    keep_hierarchy [options] [selection]\n");
		log("\n");
		log("Add the keep_hierarchy attribute.\n");
		log("\n");
		log("    -min_cost <min_cost>\n");
		log("        only add the attribute to modules estimated to have more than <min_cost>\n");
		log("        gates after simple techmapping. Intended for tuning trade-offs between\n");
		log("        quality and yosys runtime.\n");
		log("\n");
		log("        When evaluating a module's cost, gates which are within a submodule\n");
		log("        which is marked with the keep_hierarchy attribute are not counted\n");
		log("        towards the upper module's cost. This applies to both when the attribute\n");
		log("        was added by this command or was pre-existing.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		unsigned int min_cost = 0;

		log_header(design, "Executing KEEP_HIERARCHY pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-min_cost" && argidx+1 < args.size()) {
				min_cost = std::stoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (min_cost) {
			RTLIL::Module *top = design->top_module();
			if (!top)
				log_cmd_error("'-min_cost' mode requires a single top module in the design\n");

			ThresholdHierarchyKeeping worker(design, min_cost);
			worker.visit(top);
		} else {
			for (auto module : design->selected_modules()) {
				log("Marking %s.\n", log_id(module));
				module->set_bool_attribute(ID::keep_hierarchy);
			}
		}
	}
} KeepHierarchyPass;

PRIVATE_NAMESPACE_END
