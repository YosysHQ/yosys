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

struct EquivStatusPass : public Pass {
	EquivStatusPass() : Pass("equiv_status", "print status of equivalent checking module") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_status [options] [selection]\n");
		log("\n");
		log("This command prints status information for all selected $equiv cells.\n");
		log("\n");
		log("    -assert\n");
		log("        produce an error if any unproven $equiv cell is found\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, Design *design)
	{
		bool assert_mode = false;
		int unproven_count = 0;

		log_header(design, "Executing EQUIV_STATUS pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-assert") {
				assert_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			vector<Cell*> unproven_equiv_cells;
			int proven_equiv_cells = 0;

			for (auto cell : module->selected_cells())
				if (cell->type == "$equiv") {
					if (cell->getPort("\\A") != cell->getPort("\\B"))
						unproven_equiv_cells.push_back(cell);
					else
						proven_equiv_cells++;
				}

			if (unproven_equiv_cells.empty() && !proven_equiv_cells) {
				log("No $equiv cells found in %s.\n", log_id(module));
				continue;
			}

			log("Found %d $equiv cells in %s:\n", GetSize(unproven_equiv_cells) + proven_equiv_cells, log_id(module));
			log("  Of those cells %d are proven and %d are unproven.\n", proven_equiv_cells, GetSize(unproven_equiv_cells));
			if (unproven_equiv_cells.empty()) {
				log("  Equivalence successfully proven!\n");
			} else {
				for (auto cell : unproven_equiv_cells)
					log("  Unproven $equiv %s: %s %s\n", log_id(cell), log_signal(cell->getPort("\\A")), log_signal(cell->getPort("\\B")));
			}

			unproven_count += GetSize(unproven_equiv_cells);
		}

		if (unproven_count != 0) {
			log("Found a total of %d unproven $equiv cells.\n", unproven_count);
			if (assert_mode && unproven_count != 0)
				log_error("Found %d unproven $equiv cells in 'equiv_status -assert'.\n", unproven_count);
		}
	}
} EquivStatusPass;

PRIVATE_NAMESPACE_END
