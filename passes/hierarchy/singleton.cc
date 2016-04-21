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

#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SingletonPass : public Pass {
	SingletonPass() : Pass("singleton", "create singleton modules") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    singleton [selection]\n");
		log("\n");
		log("By default, a module that is instantiated by several other modules is only\n");
		log("kept once in the design. This preserves the original modularity of the design\n");
		log("and reduces the overall size of the design in memory. But it prevents certain\n");
		log("optimizations and other operations on the design. This pass creates singleton\n");
		log("modules for all selected cells. The created modules are marked with the\n");
		log("'singleton' attribute.\n");
		log("\n");
		log("This commands only operates on modules that by themself have the 'singleton'\n");
		log("attribute set (the 'top' module is a singleton implicitly).\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing SINGLETON pass (creating singleton modules).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-check") {
			// 	flag_check = true;
			// 	continue;
			// }
		}
		extra_args(args, argidx, design);

		bool did_something = true;
		int singleton_cnt = 0;

		while (did_something)
		{
			did_something = false;

			for (auto module : design->selected_modules())
			{
				if (!module->get_bool_attribute("\\singleton") && !module->get_bool_attribute("\\top"))
					continue;

				for (auto cell : module->selected_cells())
				{
					auto tmod = design->module(cell->type);

					if (tmod == nullptr)
						continue;

					if (tmod->get_bool_attribute("\\blackbox"))
						continue;

					if (tmod->get_bool_attribute("\\singleton"))
						continue;

					cell->type = module->name.str() + "." + log_id(cell->name);
					log("Creating singleton '%s'.\n", log_id(cell->type));

					auto smod = tmod->clone();
					smod->name = cell->type;
					smod->set_bool_attribute("\\singleton");
					design->add(smod);

					did_something = true;
					singleton_cnt++;
				}
			}
		}

		log("Created %d singleton modules.\n", singleton_cnt);
	}
} SingletonPass;

PRIVATE_NAMESPACE_END
