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
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct EdgetypePass : public Pass {
	EdgetypePass() : Pass("edgetypes", "list all types of edges in selection") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    edgetypes [options] [selection]\n");
		log("\n");
		log("This command lists all unique types of 'edges' found in the selection. An 'edge'\n");
		log("is a 4-tuple of source and sink cell type and port name.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-ltr") {
			// 	config.ltr = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		pool<string> edge_cache;

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			dict<SigBit, pool<tuple<IdString, IdString, int>>> bit_sources, bit_sinks;
			pool<std::pair<IdString, IdString>> multibit_ports;

			for (auto cell : module->selected_cells())
			for (auto conn : cell->connections())
			{
				IdString cell_type = cell->type;
				IdString port_name = conn.first;
				SigSpec sig = sigmap(conn.second);

				if (GetSize(sig) > 1)
					multibit_ports.insert(std::pair<IdString, IdString>(cell_type, port_name));

				for (int i = 0; i < GetSize(sig); i++) {
					if (cell->output(port_name))
						bit_sources[sig[i]].insert(tuple<IdString, IdString, int>(cell_type, port_name, i));
					if (cell->input(port_name))
						bit_sinks[sig[i]].insert(tuple<IdString, IdString, int>(cell_type, port_name, i));
				}
			}

			for (auto &it : bit_sources)
			for (auto &source : it.second)
			for (auto &sink : bit_sinks[it.first])
			{
				auto source_cell_type = std::get<0>(source);
				auto source_port_name = std::get<1>(source);
				auto source_bit_index = std::get<2>(source);

				auto sink_cell_type = std::get<0>(sink);
				auto sink_port_name = std::get<1>(sink);
				auto sink_bit_index = std::get<2>(sink);

				string source_str = multibit_ports.count(std::pair<IdString, IdString>(source_cell_type, source_port_name)) ?
						stringf("%s.%s[%d]", log_id(source_cell_type), log_id(source_port_name), source_bit_index) :
						stringf("%s.%s", log_id(source_cell_type), log_id(source_port_name));

				string sink_str = multibit_ports.count(std::pair<IdString, IdString>(sink_cell_type, sink_port_name)) ?
						stringf("%s.%s[%d]", log_id(sink_cell_type), log_id(sink_port_name), sink_bit_index) :
						stringf("%s.%s", log_id(sink_cell_type), log_id(sink_port_name));

				edge_cache.insert(source_str + " " + sink_str);
			}
		}

		edge_cache.sort();
		for (auto &str : edge_cache)
			log("%s\n", str.c_str());
	}
} EdgetypePass;

PRIVATE_NAMESPACE_END
