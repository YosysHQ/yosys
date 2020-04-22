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
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ScatterPass : public Pass {
	ScatterPass() : Pass("scatter", "add additional intermediate nets") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    scatter [selection]\n");
		log("\n");
		log("This command adds additional intermediate nets on all cell ports. This is used\n");
		log("for testing the correct use of the SigMap helper in passes. If you don't know\n");
		log("what this means: don't worry -- you only need this pass when testing your own\n");
		log("extensions to Yosys.\n");
		log("\n");
		log("Use the opt_clean command to get rid of the additional nets.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		CellTypes ct(design);
		extra_args(args, 1, design);

		for (auto module : design->selected_modules())
		{
			for (auto cell : module->cells()) {
				dict<RTLIL::IdString, RTLIL::SigSig> new_connections;
				for (auto conn : cell->connections())
					new_connections.emplace(conn.first, RTLIL::SigSig(conn.second, module->addWire(NEW_ID, GetSize(conn.second))));
				for (auto &it : new_connections) {
					if (ct.cell_output(cell->type, it.first))
						module->connect(RTLIL::SigSig(it.second.first, it.second.second));
					else
						module->connect(RTLIL::SigSig(it.second.second, it.second.first));
					cell->setPort(it.first, it.second.second);
				}
			}
		}
	}
} ScatterPass;

PRIVATE_NAMESPACE_END
