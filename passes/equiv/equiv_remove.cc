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

struct EquivRemovePass : public Pass {
	EquivRemovePass() : Pass("equiv_remove", "remove $equiv cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_remove [options] [selection]\n");
		log("\n");
		log("This command removes the selected $equiv cells. If neither -gold nor -gate is\n");
		log("used then only proven cells are removed.\n");
		log("\n");
		log("    -gold\n");
		log("        keep gold circuit\n");
		log("\n");
		log("    -gate\n");
		log("        keep gate circuit\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, Design *design) YS_OVERRIDE
	{
		bool mode_gold = false;
		bool mode_gate = false;
		int remove_count = 0;

		log_header(design, "Executing EQUIV_REMOVE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-gold") {
				mode_gold = true;
				continue;
			}
			if (args[argidx] == "-gate") {
				mode_gate = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (mode_gold && mode_gate)
			log_cmd_error("Options -gold and -gate are exclusive.\n");

		for (auto module : design->selected_modules())
		{
			for (auto cell : module->selected_cells())
				if (cell->type == "$equiv" && (mode_gold || mode_gate || cell->getPort("\\A") == cell->getPort("\\B"))) {
					log("Removing $equiv cell %s.%s (%s).\n", log_id(module), log_id(cell), log_signal(cell->getPort("\\Y")));
					module->connect(cell->getPort("\\Y"), mode_gate ? cell->getPort("\\B") : cell->getPort("\\A"));
					module->remove(cell);
					remove_count++;
				}
		}

		log("Removed a total of %d $equiv cells.\n", remove_count);
	}
} EquivRemovePass;

PRIVATE_NAMESPACE_END
