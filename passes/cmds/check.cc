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
#include "kernel/celltypes.h"
#include "kernel/utils.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct CheckPass : public Pass {
	CheckPass() : Pass("check", "check for obvious problems in the design") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    check [options] [selection]\n");
		log("\n");
		log("This pass identifies the following problems in the current design:\n");
		log("\n");
		log(" - combinatorial loops\n");
		log("\n");
		log(" - two or more conflicting drivers for one wire\n");
		log("\n");
		log(" - used wires that do not have a driver\n");
		log("\n");
		log("When called with -noinit then this command also checks for wires which have\n");
		log("the 'init' attribute set.\n");
		log("\n");
		log("When called with -assert then the command will produce an error if any\n");
		log("problems are found in the current design.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		int counter = 0;
		bool noinit = false;
		bool assert_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-noinit") {
				noinit = true;
				continue;
			}
			if (args[argidx] == "-assert") {
				assert_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		log_header(design, "Executing CHECK pass (checking for obvious problems).\n");

		for (auto module : design->selected_whole_modules_warn())
		{
			if (module->has_processes_warn())
				continue;

			log("checking module %s..\n", log_id(module));

			SigMap sigmap(module);
			dict<SigBit, vector<string>> wire_drivers;
			dict<SigBit, int> wire_drivers_count;
			pool<SigBit> used_wires;
			TopoSort<string> topo;

			for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				SigSpec sig = sigmap(conn.second);
				bool logic_cell = yosys_celltypes.cell_evaluable(cell->type);
				if (cell->input(conn.first))
					for (auto bit : sig)
						if (bit.wire) {
							if (logic_cell)
								topo.edge(stringf("wire %s", log_signal(bit)),
										stringf("cell %s (%s)", log_id(cell), log_id(cell->type)));
							used_wires.insert(bit);
						}
				if (cell->output(conn.first))
					for (int i = 0; i < GetSize(sig); i++) {
						if (logic_cell)
							topo.edge(stringf("cell %s (%s)", log_id(cell), log_id(cell->type)),
									stringf("wire %s", log_signal(sig[i])));
						if (sig[i].wire)
							wire_drivers[sig[i]].push_back(stringf("port %s[%d] of cell %s (%s)",
									log_id(conn.first), i, log_id(cell), log_id(cell->type)));
					}
				if (!cell->input(conn.first) && cell->output(conn.first))
					for (auto bit : sig)
						if (bit.wire) wire_drivers_count[bit]++;
			}

			for (auto wire : module->wires()) {
				if (wire->port_input) {
					SigSpec sig = sigmap(wire);
					for (int i = 0; i < GetSize(sig); i++)
						wire_drivers[sig[i]].push_back(stringf("module input %s[%d]", log_id(wire), i));
				}
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						if (bit.wire) used_wires.insert(bit);
				if (wire->port_input && !wire->port_output)
					for (auto bit : sigmap(wire))
						if (bit.wire) wire_drivers_count[bit]++;
				if (noinit && wire->attributes.count("\\init")) {
					log_warning("Wire %s.%s has an unprocessed 'init' attribute.\n", log_id(module), log_id(wire));
					counter++;
				}
			}

			for (auto it : wire_drivers)
				if (wire_drivers_count[it.first] > 1) {
					string message = stringf("multiple conflicting drivers for %s.%s:\n", log_id(module), log_signal(it.first));
					for (auto str : it.second)
						message += stringf("    %s\n", str.c_str());
					log_warning("%s", message.c_str());
					counter++;
				}

			for (auto bit : used_wires)
				if (!wire_drivers.count(bit)) {
					log_warning("Wire %s.%s is used but has no driver.\n", log_id(module), log_signal(bit));
					counter++;
				}

			topo.sort();
			for (auto &loop : topo.loops) {
				string message = stringf("found logic loop in module %s:\n", log_id(module));
				for (auto &str : loop)
					message += stringf("    %s\n", str.c_str());
				log_warning("%s", message.c_str());
				counter++;
			}
		}

		log("found and reported %d problems.\n", counter);

		if (assert_mode && counter > 0)
			log_error("Found %d problems in 'check -assert'.\n", counter);
	}
} CheckPass;

PRIVATE_NAMESPACE_END
