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
#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TorderPass : public Pass {
	TorderPass() : Pass("torder", "print cells in topological order") { }
	virtual void help()
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
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
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

			SigMap sigmap(module);
			dict<SigBit, pool<IdString>> bit_drivers, bit_users;
			TopoSort<IdString, RTLIL::sort_by_id_str> toposort;

			for (auto cell : module->selected_cells())
			for (auto conn : cell->connections())
			{
				if (stop_db.count(cell->type) && stop_db.at(cell->type).count(conn.first))
					continue;

				if (!noautostop && yosys_celltypes.cell_known(cell->type)) {
					if (conn.first.in("\\Q", "\\CTRL_OUT", "\\RD_DATA"))
						continue;
					if (cell->type == "$memrd" && conn.first == "\\DATA")
						continue;
				}

				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						bit_users[bit].insert(cell->name);

				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						bit_drivers[bit].insert(cell->name);

				toposort.node(cell->name);
			}

			for (auto &it : bit_users)
				if (bit_drivers.count(it.first))
					for (auto driver_cell : bit_drivers.at(it.first))
					for (auto user_cell : it.second)
						toposort.edge(driver_cell, user_cell);

			toposort.analyze_loops = true;
			toposort.sort();

			for (auto &it : toposort.loops) {
				log("  loop");
				for (auto cell : it)
					log(" %s", log_id(cell));
				log("\n");
			}

			for (auto cell : toposort.sorted)
					log("  cell %s\n", log_id(cell));
		}
	}
} TorderPass;

PRIVATE_NAMESPACE_END
