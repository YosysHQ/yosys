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


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TorderPass : public Pass {
	TorderPass() : Pass("torder", "print cells in topological order") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    torder [options] [selection]\n");
		log("\n");
		log("This command prints the selected cells in topological order.\n");
		log("\n");
		log("    -stop <cell_type> <cell_port>\n");
		log("        do not use the specified cell port in topological sorting\n");
		log("\n");
		log("    -noautostop\n");
		log("        by default Q outputs of internal FF cells and memory read port outputs\n");
		log("        are not used in topological sorting. this option deactivates that.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool noautostop = false;
		dict<IdString, pool<IdString>> stop_db;

		log_header(design, "Executing TORDER pass (print cells in topological order).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-stop" && argidx+2 < args.size()) {
				IdString cell_type = RTLIL::escape_id(args[++argidx]);
				IdString cell_port = RTLIL::escape_id(args[++argidx]);
				stop_db[cell_type].insert(cell_port);
				continue;
			}
			if (args[argidx] == "-noautostop") {
				noautostop = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			log("module %s\n", log_id(module));

			module->run_toposort_cells(noautostop,stop_db);
			for (auto cell : module->cells())
					log("  cell %s\n", log_id(cell));
		}
	}
} TorderPass;

PRIVATE_NAMESPACE_END
