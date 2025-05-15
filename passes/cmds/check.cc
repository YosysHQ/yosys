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
#include "kernel/sigtools.h"
#include "kernel/celledges.h"
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
		log("    -force-detailed-loop-check\n");
		log("        for the detection of combinatorial loops, use a detailed connectivity\n");
		log("        model for all internal cells for which it is available. This disables\n");
		log("        falling back to a simpler overapproximating model for those cells for\n");
		log("        which the detailed model is expected costly.\n");
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
		bool force_detailed_loop_check = false;
		bool suggest_detail = false;

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
			if (args[argidx] == "-force-detailed-loop-check") {
				force_detailed_loop_check = true;
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
			dict<SigBit, Cell *> driver_cells;
			dict<SigBit, int> wire_drivers_count;
			pool<SigBit> used_wires;
			TopoSort<std::pair<RTLIL::IdString, int>> topo;
			for (auto &proc_it : module->processes)
			{
				std::vector<RTLIL::CaseRule*> all_cases = {&proc_it.second->root_case};
				for (size_t i = 0; i < all_cases.size(); i++) {
					for (auto action : all_cases[i]->actions) {
						for (auto bit : sigmap(action.first))
							wire_drivers[bit].push_back(
								stringf("action %s <= %s (case rule) in process %s",
										log_signal(action.first), log_signal(action.second), log_id(proc_it.first)));

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

			struct CircuitEdgesDatabase : AbstractCellEdgesDatabase {
				TopoSort<std::pair<RTLIL::IdString, int>> &topo;
				SigMap sigmap;
				bool force_detail;

				CircuitEdgesDatabase(TopoSort<std::pair<RTLIL::IdString, int>> &topo, SigMap &sigmap, bool force_detail)
					: topo(topo), sigmap(sigmap), force_detail(force_detail) {}

				void add_edge(RTLIL::Cell *cell, RTLIL::IdString from_port, int from_bit,
							  RTLIL::IdString to_port, int to_bit, int) override {
					SigSpec from_portsig = cell->getPort(from_port);
					SigSpec to_portsig = cell->getPort(to_port);
					log_assert(from_bit >= 0 && from_bit < from_portsig.size());
					log_assert(to_bit >= 0 && to_bit < to_portsig.size());
					SigBit from = sigmap(from_portsig[from_bit]);
					SigBit to = sigmap(to_portsig[to_bit]);

					if (from.wire && to.wire)
						topo.edge(std::make_pair(from.wire->name, from.offset), std::make_pair(to.wire->name, to.offset));
				}

				bool detail_costly(Cell *cell) {
					// Only those cell types for which the edge data can expode quadratically
					// in port widths are those for us to check.
					if (!cell->type.in(
							ID($add), ID($sub),
							ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx)))
						return false;

					int in_widths = 0, out_widths = 0;

					for (auto &conn : cell->connections()) {
						if (cell->input(conn.first))
							in_widths += conn.second.size();
						if (cell->output(conn.first))
							out_widths += conn.second.size();
					}

					const int threshold = 1024;

					// if the multiplication may overflow we will catch it here 
					if (in_widths + out_widths >= threshold)
						return true;

					if (in_widths * out_widths >= threshold)
						return true;

					return false;
				}

				bool add_edges_from_cell(Cell *cell) {
					if (force_detail || !detail_costly(cell)) {
						if (AbstractCellEdgesDatabase::add_edges_from_cell(cell))
							return true;
					}

					// We don't have accurate cell edges, do the fallback of all input-output pairs
					for (auto &conn : cell->connections()) {
						if (cell->input(conn.first))
						for (auto bit : sigmap(conn.second))
						if (bit.wire)
							topo.edge(std::make_pair(bit.wire->name, bit.offset),
									  std::make_pair(cell->name, -1));

						if (cell->output(conn.first))
						for (auto bit : sigmap(conn.second))
						if (bit.wire)
							topo.edge(std::make_pair(cell->name, -1),
									  std::make_pair(bit.wire->name, bit.offset));
					}

					// Return false to signify the fallback
					return false;
				}
			};

			CircuitEdgesDatabase edges_db(topo, sigmap, force_detailed_loop_check);

			pool<Cell *> coarsened_cells;
			for (auto cell : module->cells())
			{
				if (mapped && cell->type.begins_with("$") && design->module(cell->type) == nullptr) {
					if (allow_tbuf && cell->type == ID($_TBUF_)) goto cell_allowed;
					log_warning("Cell %s.%s is an unmapped internal cell of type %s.\n", log_id(module), log_id(cell), log_id(cell->type));
					counter++;
				cell_allowed:;
				}

				for (auto &conn : cell->connections()) {
					bool input = cell->input(conn.first);
					bool output = cell->output(conn.first);

					SigSpec sig = sigmap(conn.second);
					for (int i = 0; i < sig.size(); i++) {
						SigBit bit = sig[i];

						if (input && bit.wire)
							used_wires.insert(bit);
						if (output && !input && bit.wire)
							wire_drivers_count[bit]++;
						if (output && (bit.wire || !input))
							wire_drivers[bit].push_back(stringf("port %s[%d] of cell %s (%s)", log_id(conn.first), i,
																log_id(cell), log_id(cell->type)));
						if (output)
							driver_cells[bit] = cell;
					}
				}

				if (yosys_celltypes.cell_evaluable(cell->type) || cell->type.in(ID($mem_v2), ID($memrd), ID($memrd_v2)) \
						|| RTLIL::builtin_ff_cell_types().count(cell->type)) {
					if (!edges_db.add_edges_from_cell(cell))
						coarsened_cells.insert(cell);
				}
			}

			pool<SigBit> init_bits;

			for (auto wire : module->wires()) {
				if (wire->port_input) {
					SigSpec sig = sigmap(wire);
					for (int i = 0; i < GetSize(sig); i++)
						if (sig[i].wire || !wire->port_output)
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

			for (auto state : {State::S0, State::S1, State::Sx})
				if (wire_drivers.count(state)) {
					string message = stringf("Drivers conflicting with a constant %s driver:\n", log_signal(state));
					for (auto str : wire_drivers[state])
						message += stringf("    %s\n", str.c_str());
					log_warning("%s", message.c_str());
					counter++;
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

				// `loop` only contains wire bits, or an occasional special helper node for cells for
				// which we have done the edges fallback. The cell and its ports that led to an edge are
				// a piece of information we need to recover now. For that we need to have the previous
				// wire bit of the loop at hand.
				SigBit prev;
				for (auto it = loop.rbegin(); it != loop.rend(); it++)
				if (it->second != -1) { // skip the fallback helper nodes
					prev = SigBit(module->wire(it->first), it->second);
					break;
				}
				log_assert(prev != SigBit());

				for (auto &pair : loop) {
					if (pair.second == -1)
						continue; // helper node for edges fallback, we can ignore it

					struct MatchingEdgePrinter : AbstractCellEdgesDatabase {
						std::string &message;
						SigMap &sigmap;
						SigBit from, to;
						int nhits;
						const int HITS_LIMIT = 3;

						MatchingEdgePrinter(std::string &message, SigMap &sigmap, SigBit from, SigBit to)
							: message(message), sigmap(sigmap), from(from), to(to), nhits(0) {}

						void add_edge(RTLIL::Cell *cell, RTLIL::IdString from_port, int from_bit,
									  RTLIL::IdString to_port, int to_bit, int) override {
							SigBit edge_from = sigmap(cell->getPort(from_port))[from_bit];
							SigBit edge_to = sigmap(cell->getPort(to_port))[to_bit];

							if (edge_from == from && edge_to == to && nhits++ < HITS_LIMIT)
								message += stringf("      %s[%d] --> %s[%d]\n", log_id(from_port), from_bit,
												   log_id(to_port), to_bit);
							if (nhits == HITS_LIMIT)
								message += "      ...\n";
						}
					};

					Wire *wire = module->wire(pair.first);
					log_assert(wire);
					SigBit bit(module->wire(pair.first), pair.second);
					log_assert(driver_cells.count(bit));
					Cell *driver = driver_cells.at(bit);

					std::string driver_src;
					if (driver->has_attribute(ID::src)) {
						std::string src_attr = driver->get_src_attribute();
						driver_src = stringf(" source: %s", src_attr.c_str());
					}

					message += stringf("    cell %s (%s)%s\n", log_id(driver), log_id(driver->type), driver_src.c_str());

					if (!coarsened_cells.count(driver)) {						
						MatchingEdgePrinter printer(message, sigmap, prev, bit);
						printer.add_edges_from_cell(driver);
					} else {
						message += "      (cell's internal connectivity overapproximated; loop may be a false positive)\n";
						suggest_detail = true;
					}

					if (wire->name.isPublic()) {
						std::string wire_src;
						if (wire->has_attribute(ID::src)) {
							std::string src_attr = wire->get_src_attribute();
							wire_src = stringf(" source: %s", src_attr.c_str());
						}
						message += stringf("    wire %s%s\n", log_signal(SigBit(wire, pair.second)), wire_src.c_str());						
					}

					prev = bit;
				}
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

		if (suggest_detail)
			log("Consider re-running with '-force-detailed-loop-check' to rule out false positives.\n");

		if (assert_mode && counter > 0)
			log_error("Found %d problems in 'check -assert'.\n", counter);
	}
} CheckPass;

PRIVATE_NAMESPACE_END
