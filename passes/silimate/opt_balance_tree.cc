/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2019  Eddie Hung        <eddie@fpgeh.com>
 *                2024  Akash Levy        <akash@silimate.com>
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


struct OptBalanceTreeWorker {
	// Module and signal map
	Module *module;
	SigMap sigmap;

	// Counts of each cell type that are getting balanced
	dict<IdString, int> cell_count;

	// Check if cell is of the right type and has matching input/output widths
	bool is_right_type(Cell* cell, IdString cell_type) {
		return cell->type == cell_type &&
		       cell->getParam(ID::Y_WIDTH).as_int() >= cell->getParam(ID::A_WIDTH).as_int() &&
		       cell->getParam(ID::Y_WIDTH).as_int() >= cell->getParam(ID::B_WIDTH).as_int();
	}

	// Create a balanced binary tree from a vector of source signals
	SigSpec create_balanced_tree(vector<SigSpec> &sources, IdString cell_type, Cell* cell) {
		// Base case: if we have no sources, return an empty signal
		if (sources.size() == 0)
			return SigSpec();

		// Base case: if we have only one source, return it
		if (sources.size() == 1)
			return sources[0];
		
		// Base case: if we have two sources, create a single cell
		if (sources.size() == 2) {
			// Create a new cell of the same type
			Cell* new_cell = module->addCell(NEW_ID2_SUFFIX("tree"), cell_type);
			
			// Copy attributes from reference cell
			new_cell->attributes = cell->attributes;
			
			// Create output wire
			int out_width = cell->getParam(ID::Y_WIDTH).as_int();
			if (cell_type == ID($add))
				out_width = max(sources[0].size(), sources[1].size()) + 1;
			else if (cell_type == ID($mul))
				out_width = sources[0].size() + sources[1].size();
			Wire* out_wire = module->addWire(NEW_ID2_SUFFIX("tree_out"), out_width);
			
			// Connect ports and fix up parameters
			new_cell->setPort(ID::A, sources[0]);
			new_cell->setPort(ID::B, sources[1]);
			new_cell->setPort(ID::Y, out_wire);
			new_cell->fixup_parameters();
			new_cell->setParam(ID::A_SIGNED, cell->getParam(ID::A_SIGNED));
			new_cell->setParam(ID::B_SIGNED, cell->getParam(ID::B_SIGNED));
			
			// Update count and return output wire
			cell_count[cell_type]++;
			return out_wire;
		}
		
		// Recursive case: split sources into two groups and create subtrees
		int mid = (sources.size() + 1) / 2;
		vector<SigSpec> left_sources(sources.begin(), sources.begin() + mid);
		vector<SigSpec> right_sources(sources.begin() + mid, sources.end());
		
		SigSpec left_tree = create_balanced_tree(left_sources, cell_type, cell);
		SigSpec right_tree = create_balanced_tree(right_sources, cell_type, cell);
		
		// Create a cell to combine the two subtrees
		Cell* new_cell = module->addCell(NEW_ID2_SUFFIX("tree"), cell_type);
		
		// Copy attributes from reference cell
		new_cell->attributes = cell->attributes;
		
		// Create output wire
		int out_width = cell->getParam(ID::Y_WIDTH).as_int();
		if (cell_type == ID($add))
			out_width = max(left_tree.size(), right_tree.size()) + 1;
		else if (cell_type == ID($mul))
			out_width = left_tree.size() + right_tree.size();
		Wire* out_wire = module->addWire(NEW_ID2_SUFFIX("tree_out"), out_width);
		
		// Connect ports and fix up parameters
		new_cell->setPort(ID::A, left_tree);
		new_cell->setPort(ID::B, right_tree);
		new_cell->setPort(ID::Y, out_wire);
		new_cell->fixup_parameters();
		new_cell->setParam(ID::A_SIGNED, cell->getParam(ID::A_SIGNED));
		new_cell->setParam(ID::B_SIGNED, cell->getParam(ID::B_SIGNED));
		
		// Update count and return output wire
		cell_count[cell_type]++;
		return out_wire;
	}

	OptBalanceTreeWorker(Module *module, const vector<IdString> cell_types) : module(module), sigmap(module) {
		// Do for each cell type
		for (auto cell_type : cell_types) {
			// Index all of the nets in the module
			dict<SigSpec, Cell*> sig_to_driver;
			dict<SigSpec, pool<Cell*>> sig_to_sink;
			for (auto cell : module->selected_cells())
			{
				for (auto &conn : cell->connections())
				{
					if (cell->output(conn.first))
						sig_to_driver[sigmap(conn.second)] = cell;

					if (cell->input(conn.first))
					{
						SigSpec sig = sigmap(conn.second);
						if (sig_to_sink.count(sig) == 0)
							sig_to_sink[sig] = pool<Cell*>();
						sig_to_sink[sig].insert(cell);
					}
				}
			}

			// Need to check if any wires connect to module ports
			pool<SigSpec> input_port_sigs;
			pool<SigSpec> output_port_sigs;
			for (auto wire : module->selected_wires())
				if (wire->port_input || wire->port_output) {
					SigSpec sig = sigmap(wire);
					for (auto bit : sig) {
						if (wire->port_input)
							input_port_sigs.insert(bit);
						if (wire->port_output)
							output_port_sigs.insert(bit);
					}
				}

			// Actual logic starts here
			pool<Cell*> consumed_cells;
			for (auto cell : module->selected_cells())
			{
				// If consumed or not the correct type, skip
				if (consumed_cells.count(cell) || !is_right_type(cell, cell_type))
					continue;

				// BFS, following all chains until they hit a cell of a different type
				// Pick the longest one
				auto y = sigmap(cell->getPort(ID::Y));
				pool<Cell*> sinks;
				pool<Cell*> current_loads = sig_to_sink[y];
				pool<Cell*> next_loads;
				while (!current_loads.empty())
				{
					// Find each sink and see what they are
					for (auto x : current_loads)
					{
						// If not the correct type, don't follow any further
						// (but add the originating cell to the list of sinks)
						if (!is_right_type(x, cell_type))
						{
							sinks.insert(cell);
							continue;
						}

						auto xy = sigmap(x->getPort(ID::Y));

						// If this signal drives a port, add it to the sinks
						// (even though it may not be the end of a chain)
						for (auto bit : xy) {
							if (output_port_sigs.count(bit) && !consumed_cells.count(x)) {
								sinks.insert(x);
								break;
							}
						}

						// Search signal's fanout
						auto& next = sig_to_sink[xy];
						for (auto z : next)
							next_loads.insert(z);
					}

					// If we couldn't find any downstream loads, stop.
					// Create a reduction for each of the max-length chains we found
					if (next_loads.empty())
					{
						for (auto s : current_loads)
						{
							// Not one of our gates? Don't follow any further
							if (!is_right_type(s, cell_type))
								continue;

							sinks.insert(s);
						}
						break;
					}

					// Otherwise, continue down the chain
					current_loads = next_loads;
					next_loads.clear();
				}

				// We have our list of sinks, now go tree balance the chains
				for (auto head_cell : sinks)
				{
					// Avoid duplication if we already were covered
					if (consumed_cells.count(head_cell))
						continue;

					// Get sources of the chain
					dict<SigSpec, int> sources;
					dict<SigSpec, bool> signeds;
					int inner_cells = 0;
					std::deque<Cell*> bfs_queue = {head_cell};
					while (bfs_queue.size())
					{
						Cell* x = bfs_queue.front();
						bfs_queue.pop_front();

						for (auto port: {ID::A, ID::B}) {
							auto sig = sigmap(x->getPort(port));
							Cell* drv = sig_to_driver[sig];
							bool drv_ok = drv && is_right_type(drv, cell_type);
							for (auto bit : sig) {
								if (input_port_sigs.count(bit) && !consumed_cells.count(drv)) {
									drv_ok = false;
									break;
								}
							}
							if (drv_ok) {
								inner_cells++;
								bfs_queue.push_back(drv);
							} else {
								sources[sig]++;
								signeds[sig] = x->getParam(port == ID::A ? ID::A_SIGNED : ID::B_SIGNED).as_bool();
							}
						}
					}

					if (inner_cells)
					{
						// Create a tree
						log("  Creating tree for %d sources and %d inner cells...\n", GetSize(sources), inner_cells);
						
						// Build a vector of all source signals
						vector<SigSpec> source_signals;
						vector<bool> signed_flags;
						for (auto &source : sources) {
							for (int i = 0; i < source.second; i++) {
								source_signals.push_back(source.first);
								signed_flags.push_back(signeds[source.first]);
							}
						}

						// If not all signed flags are the same, do not balance
						if (!std::all_of(signed_flags.begin(), signed_flags.end(), [&](bool flag) { return flag == signed_flags[0]; })) {
							continue;
						}
						
						// Create the balanced tree
						SigSpec tree_output = create_balanced_tree(source_signals, cell_type, head_cell);
						
						// Connect the tree output to the head cell's output
						SigSpec head_output = sigmap(head_cell->getPort(ID::Y));
						int connect_width = std::min(head_output.size(), tree_output.size());
						log("  Connecting %s to %s\n", log_signal(head_output), log_signal(tree_output));
						log_flush();
						module->connect(head_output.extract(0, connect_width), tree_output.extract(0, connect_width));
						if (head_output.size() > tree_output.size()) {
							SigBit sext_bit = head_cell->getParam(ID::A_SIGNED).as_bool() ? head_output[connect_width - 1] : State::S0;
							module->connect(head_output.extract(connect_width, head_output.size() - connect_width), SigSpec(sext_bit, head_output.size() - connect_width));
						}

						// Mark consumed cell for removal
						consumed_cells.insert(head_cell);
					}
				}
			}
			
			// Remove all consumed cells, which now have been replaced by trees
			for (auto cell : consumed_cells)
				module->remove(cell);
		}
	}
};

struct OptBalanceTreePass : public Pass {
	OptBalanceTreePass() : Pass("opt_balance_tree", "$and/$or/$xor/$add/$mul cascades to trees") { }
	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_balance_tree [options] [selection]\n");
		log("\n");
		log("This pass converts cascaded chains of $and/$or/$xor/$add/$mul cells into\n");
		log("trees of cells to improve timing.\n");
		log("\n");
		log("    -arith\n");
		log("        only convert arithmetic cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_BALANCE_TREE pass (cell cascades to trees).\n");

		// Handle arguments
		size_t argidx;
		vector<IdString> cell_types = {ID($and), ID($or), ID($xor), ID($add), ID($mul)};
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-arith") {
				cell_types = {ID($add), ID($mul)};
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Count of all cells that were packed
		dict<IdString, int> cell_count;
		for (auto module : design->selected_modules()) {
			OptBalanceTreeWorker worker(module, cell_types);
			for (auto cell : worker.cell_count) {
				cell_count[cell.first] += cell.second;
			}
		}

		// Log stats
		for (auto cell_type : cell_types)
			log("Converted %d %s cells into trees.\n", cell_count[cell_type], log_id(cell_type));

		// Clean up
		Yosys::run_pass("clean -purge");
	}
} OptBalanceTreePass;

PRIVATE_NAMESPACE_END
