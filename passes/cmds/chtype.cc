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

struct ChtypePass : public Pass {
	ChtypePass() : Pass("chtype", "change type of cells in the design") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    chtype [options] [selection]\n");
		log("\n");
		log("Change the types of cells in the design.\n");
		log("\n");
		log("    -set <type>\n");
		log("        set the cell type to the given type\n");
		log("\n");
		log("    -map <old_type> <new_type>\n");
		log("        change cells types that match <old_type> to <new_type>\n");
		log("\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		IdString set_type;
		dict<IdString, IdString> map_types;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (set_type == IdString() && args[argidx] == "-set" && argidx+1 < args.size()) {
				set_type = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-map" && argidx+2 < args.size()) {
				IdString old_type = RTLIL::escape_id(args[++argidx]);
				IdString new_type = RTLIL::escape_id(args[++argidx]);
				map_types[old_type] = new_type;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			for (auto cell : module->selected_cells())
			{
				if (map_types.count(cell->type)) {
					cell->type = map_types.at(cell->type);
					continue;
				}

				if (set_type != IdString()) {
					cell->type = set_type;
					continue;
				}
			}
		}
	}
} ChtypePass;

PRIVATE_NAMESPACE_END
