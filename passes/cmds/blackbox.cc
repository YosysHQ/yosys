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

struct BlackboxPass : public Pass {
	BlackboxPass() : Pass("blackbox", "convert modules into blackbox modules") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    blackbox [options] [selection]\n");
		log("\n");
		log("Convert modules into blackbox modules (remove contents and set the blackbox\n");
		log("module attribute).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-???") {
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_whole_modules_warn())
		{
			pool<Cell*> remove_cells;
			pool<Wire*> remove_wires;

			for (auto cell : module->cells())
				remove_cells.insert(cell);

			for (auto wire : module->wires())
				if (wire->port_id == 0)
					remove_wires.insert(wire);

			for (auto it = module->memories.begin(); it != module->memories.end(); ++it)
				delete it->second;
			module->memories.clear();

			for (auto it = module->processes.begin(); it != module->processes.end(); ++it)
				delete it->second;
			module->processes.clear();

			module->new_connections(std::vector<RTLIL::SigSig>());

			for (auto cell : remove_cells)
				module->remove(cell);

			module->remove(remove_wires);

			module->set_bool_attribute("\\blackbox");
		}
	}
} BlackboxPass;

PRIVATE_NAMESPACE_END
