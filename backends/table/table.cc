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

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TableBackend : public Backend {
	TableBackend() : Backend("table", "write design as connectivity table") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_table [options] [filename]\n");
		log("\n");
		log("Write the current design as connectivity table. The output is a tab-separated\n");
		log("ASCII table with the following columns:\n");
		log("\n");
		log("  module name\n");
		log("  cell name\n");
		log("  cell type\n");
		log("  cell port\n");
		log("  direction\n");
		log("  signal\n");
		log("\n");
		log("module inputs and outputs are output using cell type and port '-' and with\n");
		log("'pi' (primary input) or 'po' (primary output) or 'pio' as direction.\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing TABLE backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-top" && argidx+1 < args.size()) {
			// 	top_module_name = args[++argidx];
			// 	continue;
			// }
			break;
		}
		extra_args(f, filename, args, argidx);

		design->sort();

		for (auto module : design->modules())
		{
			if (module->get_blackbox_attribute())
				continue;

			SigMap sigmap(module);

			for (auto wire : module->wires())
			{
				if (wire->port_id == 0)
					continue;

				*f << log_id(module) << "\t";
				*f << log_id(wire) << "\t";
				*f << "-" << "\t";
				*f << "-" << "\t";

				if (wire->port_input && wire->port_output)
					*f << "pio" << "\t";
				else if (wire->port_input)
					*f << "pi" << "\t";
				else if (wire->port_output)
					*f << "po" << "\t";
				else
					log_abort();

				*f << log_signal(sigmap(wire)) << "\n";
			}

			for (auto cell : module->cells())
			for (auto conn : cell->connections())
			{
				*f << log_id(module) << "\t";
				*f << log_id(cell) << "\t";
				*f << log_id(cell->type) << "\t";
				*f << log_id(conn.first) << "\t";

				if (cell->input(conn.first) && cell->output(conn.first))
					*f << "inout" << "\t";
				else if (cell->input(conn.first))
					*f << "in" << "\t";
				else if (cell->output(conn.first))
					*f << "out" << "\t";
				else
					*f << "unknown" << "\t";

				*f << log_signal(sigmap(conn.second)) << "\n";
			}
		}
	}
} TableBackend;

PRIVATE_NAMESPACE_END
