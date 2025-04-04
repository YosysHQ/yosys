/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2017 Robert Ou <rqou@robertou.com>
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
#include <deque>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MuxpackerPass : public Pass
{
	MuxpackerPass() : Pass("muxpacker", "convert $mux/$pmux trees into $pmux cells") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    muxpacker [options] [selection]\n");
		log("\n");
		log("convert $mux/$pmux trees into $pmux cells\n");
		log("\n");
		log("This command finds chains of $mux and $pmux cells and replaces them\n");
		log("with them with $pmux cells.\n");
		log("\n");
		log("    -allow-off-chain\n");
		log("        Allows matching of cells that have loads outside the chain. These cells\n");
		log("        will be replicated and folded into the $reduce_* cell, but the original\n");
		log("        cell will remain, driving its original loads.\n");
		log("\n");
		log("    -assume-excl\n");
		log("        Assume that $mux select signals are exclusive. Will result in logical\n");
		log("        inequivalence if this assumption is incorrect.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing MUXPACKER pass (convert $mux/$pmux trees into $pmux cells).\n");
		log_push();

		size_t argidx;
		bool allow_off_chain = false, assume_excl = false;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-allow-off-chain")
			{
				allow_off_chain = true;
				continue;
			}
			if (args[argidx] == "-assume-excl")
			{
				assume_excl = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);

			// Index all of the nets in the module
			dict<SigBit, Cell*> sig_to_driver;
			dict<SigBit, pool<Cell*>> sig_to_sink;
			for (auto cell : module->selected_cells())
			{
				for (auto &conn : cell->connections())
				{
					if (cell->output(conn.first))
						for (auto bit : sigmap(conn.second))
							sig_to_driver[bit] = cell;

					if (cell->input(conn.first))
					{
						for (auto bit : sigmap(conn.second))
						{
							if (sig_to_sink.count(bit) == 0)
								sig_to_sink[bit] = pool<Cell*>();
							sig_to_sink[bit].insert(cell);
						}
					}
				}
			}

			// Need to check if any wires connect to module ports
			pool<SigBit> port_sigs;
			for (auto wire : module->selected_wires())
				if (wire->port_input || wire->port_output)
					for (auto bit : sigmap(wire))
						port_sigs.insert(bit);

			// Actual logic starts here
			pool<Cell*> consumed_cells;
			for (auto cell : module->selected_cells())
			{
				// If we already consumed this cell, skip it
				if (consumed_cells.count(cell))
					continue;

				// If this cell is not a mux or pmux, skip it
				if (!cell->type.in(ID($mux), ID($pmux)))
					continue;

				// Work on the cell
				log_debug("Working on cell %s...\n", cell->name.c_str());

				/////////////////////////////////////////////////////////
				// PASS 1: determine the sinks using forward traversal //
				/////////////////////////////////////////////////////////
				// If looking for a single chain, follow linearly to the sink
				pool<Cell*> sinks;
				if (!allow_off_chain)
				{
					Cell* head_cell = cell;
					Cell* x = cell;
					while (true)
					{
						if (!x->type.in(ID($mux), ID($pmux)))
							break;

						head_cell = x;

						auto y = sigmap(x->getPort(ID::Y));
						log_assert(y.size() == 1);

						// Should only continue if there is one fanout back into a cell (not to a port)
						if (sig_to_sink[y].size() != 1 || port_sigs.count(y))
							break;

						// Traverse forward
						x = *sig_to_sink[y].begin();
					}

					sinks.insert(head_cell);
				}
				// If off-chain loads are allowed, do a wider traversal to find longest chain
				else
				{
					// Forward BFS, follow all chains until they hit a cell of a different type
					// Pick the longest one
					auto y = sigmap(cell->getPort(ID::Y));
					pool<Cell*> current_loads = sig_to_sink[y];
					pool<Cell*> next_loads;

					while (!current_loads.empty())
					{
						// Find each sink and see what they are
						for (auto x : current_loads)
						{
							// Not one of our gates? Don't follow any further
							// (but add the originating cell to the list of sinks)
							if (!x->type.in(ID($mux), ID($pmux)))
							{
								sinks.insert(cell);
								continue;
							}

							auto xy = sigmap(x->getPort(ID::Y));

							// If this signal drives a port, add it to the sinks
							// (even though it may not be the end of a chain)
							if (port_sigs.count(xy) && !consumed_cells.count(x))
								sinks.insert(x);

							// It's a match, search everything out from it
							auto& next = sig_to_sink[xy];
							for(auto z : next)
								next_loads.insert(z);
						}

						// If we couldn't find any downstream loads, stop
						// Create a reduction for each of the max-length chains we found
						if (next_loads.empty())
						{
							for(auto s : current_loads)
							{
								//Not one of our gates? Don't follow any further
								if (!x->type.in(ID($mux), ID($pmux)))
									continue;

								sinks.insert(s);
							}
							break;
						}

						// Otherwise, continue down the chain
						current_loads = next_loads;
						next_loads.clear();
					}
				}

				// We have our list, go act on it
				for(auto head_cell : sinks)
				{
					log_debug("  Head cell is %s\n", head_cell->name.c_str());

					// Avoid duplication if we already were covered
					if(consumed_cells.count(head_cell))
						continue;

					dict<SigBit, int> sources;
					dict<SigBit, int> sels;
					int inner_cells = 0;
					std::deque<std::pair<Cell*, SigBit>> bfs_queue = {{head_cell, State::S1}};
					while (bfs_queue.size())
					{
						auto bfs_item = bfs_queue.front();
						bfs_queue.pop_front();

						Cell* x = bfs_item.first;
						SigBit excl = bfs_item.second;

						for (auto port: {ID::B, ID::A}) {
							auto bit = sigmap(x->getPort(port)[0]);

							bool sink_single = sig_to_sink[bit].size() == 1 && !port_sigs.count(bit);

							Cell* drv = sig_to_driver[bit];
							bool drv_ok = drv && IsRightType(drv, gt);

							SigBit s_port;
							SigBit sel_sig;
							if (gt == GateType::Mux) {
								s_port = sigmap(x->getPort(ID::S)[0]);
								if (port == ID::A)
									sel_sig = module->Not(NEW_ID2_SUFFIX("not"), s_port, false, x->get_src_attribute());
								else
									sel_sig = module->Buf(NEW_ID2_SUFFIX("buf"), s_port, false, x->get_src_attribute());
							}

							if (drv_ok && (allow_off_chain || sink_single)) {
								inner_cells++;
								if (gt == GateType::Mux && !assume_excl) { // if not assuming exclusivity, add to excl signal
									SigBit sel_sig_inv = (port == ID::A) ? module->Not(NEW_ID2_SUFFIX("not"), s_port, false, x->get_src_attribute())[0] : s_port;
									bfs_queue.push_back({drv, module->And(NEW_ID2_SUFFIX("excl_and"), sel_sig_inv, excl, false, x->get_src_attribute())});
								} else { // otherwise, just use the drv signal and don't worry about exclusivity
									bfs_queue.push_back({drv, excl});
								}
							} else {
								sources[module->Buf(NEW_ID2_SUFFIX("buf"), bit, false, x->get_src_attribute())]++;
								if (gt == GateType::Mux) {
									if (assume_excl) // if assuming exclusivity, just use select signal
										sels[sel_sig]++;
									else // enforce exclusivity by ANDing with excl signal
										sels[module->And(NEW_ID2_SUFFIX("selex_and"), sel_sig, excl)]++;
								}
							}
						}
					}

					if (inner_cells)
					{
						// Worth it to create reduce cell
						log_debug("Creating reduce_* cell for %s (%s) in %s\n", head_cell->name.c_str(), head_cell->type.c_str(), module->name.c_str());

						SigBit output = sigmap(head_cell->getPort(ID::Y)[0]);

						SigSpec input, sel;
						for (auto it : sources) {
							bool cond;
							if (head_cell->type == ID($_XOR_) || head_cell->type == ID($xor) || head_cell->type == ID($_XNOR_) || head_cell->type == ID($xnor))
								cond = it.second & 1;
							else
								cond = it.second != 0;
							if (cond || head_cell->hasPort(ID::S))
								input.append(it.first);
						}
						if (head_cell->hasPort(ID::S)) {
							for (auto it : sels)
								sel.append(it.first);
							input.reverse();
							sel.reverse();
						}

						if (head_cell->type == ID($_AND_) || head_cell->type == ID($and)) {
							module->addReduceAnd(NEW_ID2_SUFFIX("reduce_and"), input, output, false, cell->get_src_attribute()); // SILIMATE: Improve the naming
						} else if (head_cell->type == ID($_OR_) || head_cell->type == ID($or)) {
							module->addReduceOr(NEW_ID2_SUFFIX("reduce_or"), input, output, false, cell->get_src_attribute()); // SILIMATE: Improve the naming
						} else if (head_cell->type == ID($_XOR_) || head_cell->type == ID($xor)) {
							module->addReduceXor(NEW_ID2_SUFFIX("reduce_xor"), input, output, false, cell->get_src_attribute()); // SILIMATE: Improve the naming
						} else if (head_cell->type == ID($_XNOR_) || head_cell->type == ID($xnor)) {
							module->addReduceXnor(NEW_ID2_SUFFIX("reduce_xnor"), input, output, false, cell->get_src_attribute()); // SILIMATE: Improve the naming
						} else if (head_cell->type == ID($_MUX_) || head_cell->type == ID($mux)) {
							module->addPmux(NEW_ID2_SUFFIX("pmux"), State::Sx, input, sel, output, cell->get_src_attribute()); // SILIMATE: Improve the naming
						} else {
							log_assert(false);
						}

						consumed_cells.insert(head_cell);
					}
				}
			}

			// Remove all of the head cells, since we supplant them.
			// Do not remove the upstream cells since some might still be in use ("clean" will get rid of unused ones)
			for (auto cell : consumed_cells)
				module->remove(cell);
		}

		log_pop();
	}
} MuxpackerPass;

PRIVATE_NAMESPACE_END
