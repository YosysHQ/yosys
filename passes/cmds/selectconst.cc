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
#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include <string.h>
#include <errno.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SelectConstPass : public Pass {
	SelectConstPass() : Pass("selectconst", "select objects with (mostly) constant input bits") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    selectconst [ -frac <frac> ] {<selection>}\n");
		log("\n");
		log("Select cells with (mostly) constant input bits.\n");
		log("\n");
		log("    -frac\n");
		log("        the fraction of constant input bits (default: 1.0).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		float frac = 1;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-frac") {
				frac = std::stof(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);

			for (auto cell : module->selected_cells())
			{
				for (auto conn : cell->connections()) {
					if (!cell->input(conn.first) || GetSize(conn.second) == 0)
						continue;

					SigPool sigpool;
					for (int i = 0; i < GetSize(conn.second); i++) {
						if (conn.second[i].wire == nullptr)
							continue;
						sigpool.add(sigmap(conn.second[i]));
					}
					if ((float) GetSize(sigpool) / GetSize(conn.second) >= frac) {
						cell->set_bool_attribute("\\mostlyconst");
						log("Marking %s as mostly constant (%d/%d bits constant).\n", log_id(cell), GetSize(sigpool), GetSize(conn.second));
					}
				}
			}
		}
	}
} SelectConstPass;

PRIVATE_NAMESPACE_END
