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
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    check [options] [selection]\n");
		log("\n");
		log("This pass identifies the following problems in the current design:\n");
		log("\n");
		log("  - combinatorial loops\n");
		log("  - two or more conflicting drivers for one wire\n");
		log("  - used wires that do not have a driver\n");
		log("\n");
		log("Options:\n");
		log("\n");
		log("    -noinit\n");
		log("        also check for wires which have the 'init' attribute set\n");
		log("\n");
		log("    -initdrv\n");
		log("        also check for wires that have the 'init' attribute set and are not\n");
		log("        driven by an FF cell type\n");
		log("\n");
		log("    -mapped\n");
		log("        also check for internal cells that have not been mapped to cells of the\n");
		log("        target architecture\n");
		log("\n");
		log("    -allow-tbuf\n");
		log("        modify the -mapped behavior to still allow $_TBUF_ cells\n");
		log("\n");
		log("    -assert\n");
		log("        produce a runtime error if any problems are found in the current design\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int counter = 0;
		bool noinit = false;
		bool initdrv = false;
		bool mapped = false;
		bool allow_tbuf = false;
		bool assert_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-noinit") {
				noinit = true;
				continue;
			}
			if (args[argidx] == "-initdrv") {
				initdrv = true;
				continue;
			}
			if (args[argidx] == "-mapped") {
				mapped = true;
				continue;
			}
			if (args[argidx] == "-allow-tbuf") {
				allow_tbuf = true;
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
			log("Checking module %s...\n", log_id(module));

			SigMap sigmap(module);
			dict<SigBit, vector<string>> wire_drivers;
			dict<SigBit, int> wire_drivers_count;
			pool<SigBit> used_wires;
			TopoSort<string> topo;

			for (auto &proc_it : module->processes)
			{
				std::vector<RTLIL::CaseRule*> all_cases = {&proc_it.second->root_case};
				for (size_t i = 0; i < all_cases.size(); i++) {
					for (auto action : all_cases[i]->actions) {
						for (auto bit : sigmap(action.first))
							if (bit.wire) {
								wire_drivers[bit].push_back(
									stringf("action %s <= %s (case rule) in process %s",
									        log_signal(action.first), log_signal(action.second), log_id(proc_it.first)));
							}
						for (auto bit : sigmap(action.second))
							if (bit.wire) used_wires.insert(bit);
					}
					for (auto switch_ : all_cases[i]->switches) {
						for (auto case_ : switch_->cases) {
							all_cases.push_back(case_);
							for (auto compare : case_->compare)
								for (auto bit : sigmap(compare))
									if (bit.wire) used_wires.insert(bit);
						}
					}
				}
				for (auto &sync : proc_it.second->syncs) {
					for (auto bit : sigmap(sync->signal))
						if (bit.wire) used_wires.insert(bit);
					for (auto action : sync->actions) {
						for (auto bit : sigmap(action.first))
							if (bit.wire)
								wire_drivers[bit].push_back(
									stringf("action %s <= %s (sync rule) in process %s",
									        log_signal(action.first), log_signal(action.second), log_id(proc_it.first)));
						for (auto bit : sigmap(action.second))
							if (bit.wire) used_wires.insert(bit);
					}
					for (auto memwr : sync->mem_write_actions) {
						for (auto bit : sigmap(memwr.address))
							if (bit.wire) used_wires.insert(bit);
						for (auto bit : sigmap(memwr.data))
							if (bit.wire) used_wires.insert(bit);
						for (auto bit : sigmap(memwr.enable))
							if (bit.wire) used_wires.insert(bit);
					}
				}
			}

			for (auto cell : module->cells())
			{
				if (mapped && cell->type.begins_with("$") && design->module(cell->type) == nullptr) {
					if (allow_tbuf && cell->type == ID($_TBUF_)) goto cell_allowed;
					log_warning("Cell %s.%s is an unmapped internal cell of type %s.\n", log_id(module), log_id(cell), log_id(cell->type));
					counter++;
				cell_allowed:;
				}
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
			}

			pool<SigBit> init_bits;

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
				if (wire->attributes.count(ID::init)) {
					Const initval = wire->attributes.at(ID::init);
					for (int i = 0; i < GetSize(initval) && i < GetSize(wire); i++)
						if (initval[i] == State::S0 || initval[i] == State::S1)
							init_bits.insert(sigmap(SigBit(wire, i)));
					if (noinit) {
						log_warning("Wire %s.%s has an unprocessed 'init' attribute.\n", log_id(module), log_id(wire));
						counter++;
					}
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

			if (initdrv)
			{
				for (auto cell : module->cells())
				{
					if (RTLIL::builtin_ff_cell_types().count(cell->type) == 0)
						continue;

					for (auto bit : sigmap(cell->getPort(ID::Q)))
						init_bits.erase(bit);
				}

				SigSpec init_sig(init_bits);
				init_sig.sort_and_unify();

				for (auto chunk : init_sig.chunks()) {
					log_warning("Wire %s.%s has 'init' attribute and is not driven by an FF cell.\n", log_id(module), log_signal(chunk));
					counter++;
				}
			}
		}

		log("Found and reported %d problems.\n", counter);

		if (assert_mode && counter > 0)
			log_error("Found %d problems in 'check -assert'.\n", counter);
	}
} CheckPass;

PRIVATE_NAMESPACE_END
