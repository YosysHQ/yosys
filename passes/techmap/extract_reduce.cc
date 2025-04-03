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

struct ExtractReducePass : public Pass
{
	enum GateType {
		And,
		Or,
		Xor,
		Mux
	};

	ExtractReducePass() : Pass("extract_reduce", "converts gate chains into $reduce_*/$pmux cells") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    extract_reduce [options] [selection]\n");
		log("\n");
		log("converts gate chains into $reduce_* cells\n");
		log("\n");
		log("This command finds chains of $_AND_, $_OR_, and $_XOR_ cells and replaces them\n");
		log("with their corresponding $reduce_* cells. Because this command only operates on\n");
		log("these cell types, it is recommended to map the design to only these cell types\n");
		log("using the `abc -g` command. Note that, in some cases, it may be more effective\n");
		log("to map the design to only $_AND_ cells, run extract_reduce, map the remaining\n");
		log("parts of the design to AND/OR/XOR cells, and run extract_reduce a second time.\n");
		log("\n");
		log("Silimate has modified this pass to support word-level cells ($and, $or, \n");
		log("and $xor) as well as the single-bit cells ($_AND_, $_OR_, and $_XOR_).\n");
		log("Mux cells ($mux, $_MUX_) can also be reduced to $pmux cells with the mods.\n");
		log("\n");
		log("    -allow-off-chain\n");
		log("        Allows matching of cells that have loads outside the chain. These cells\n");
		log("        will be replicated and folded into the $reduce_* cell, but the original\n");
		log("        cell will remain, driving its original loads.\n");
		log("\n");
		log("    -mux-only\n");
		log("        Only reduce $mux cells to $pmux cells, ignore other cell types.\n");
		log("\n");
		log("    -no-mux\n");
		log("        Do not reduce $mux cells to $pmux cells, only reduce other cell types.\n");
		log("\n");
		log("    -assume-excl\n");
		log("        Assume that $mux select signals are exclusive. Will result in logical\n");
		log("        inequivalence if this assumption is incorrect.\n");
		log("\n");
	}

	inline bool IsSingleBit(Cell* cell)
	{
		return (cell->hasParam(ID::WIDTH) && cell->getParam(ID::WIDTH).as_int() == 1) ||
					 (cell->hasParam(ID::A_WIDTH) &&
						cell->getParam(ID::A_WIDTH).as_int() == 1 &&
		        cell->getParam(ID::B_WIDTH).as_int() == 1 &&
					  cell->getParam(ID::Y_WIDTH).as_int() == 1);
	}

	inline bool IsRightType(Cell* cell, GateType gt)
	{
		return (cell->type == ID($_AND_) && gt == GateType::And) ||
				(cell->type == ID($_OR_) && gt == GateType::Or) ||
				(cell->type == ID($_XOR_) && gt == GateType::Xor) ||
				(cell->type == ID($_MUX_) && gt == GateType::Mux) ||
				(cell->type == ID($and) && IsSingleBit(cell) && gt == GateType::And) ||
				(cell->type == ID($or) && IsSingleBit(cell) && gt == GateType::Or) ||
				(cell->type == ID($xor) && IsSingleBit(cell) && gt == GateType::Xor) ||
				(cell->type == ID($mux) && IsSingleBit(cell) && gt == GateType::Mux);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing EXTRACT_REDUCE pass.\n");
		log_push();

		size_t argidx;
		bool allow_off_chain = false, mux_only = false, no_mux = false, assume_excl = false;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-allow-off-chain")
			{
				allow_off_chain = true;
				continue;
			}
			if (args[argidx] == "-mux-only")
			{
				mux_only = true;
				continue;
			}
			if (args[argidx] == "-no-mux")
			{
				no_mux = true;
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
				if (consumed_cells.count(cell))
					continue;

				GateType gt;

				if (cell->type == ID($_AND_))
					gt = GateType::And;
				else if (cell->type == ID($_OR_))
					gt = GateType::Or;
				else if (cell->type == ID($_XOR_))
					gt = GateType::Xor;
				else if (cell->type == ID($_MUX_))
					gt = GateType::Mux;
				else if (cell->type == ID($and) && IsSingleBit(cell))
					gt = GateType::And;
				else if (cell->type == ID($or) && IsSingleBit(cell))
					gt = GateType::Or;
				else if (cell->type == ID($xor) && IsSingleBit(cell))
					gt = GateType::Xor;
				else if (cell->type == ID($mux) && IsSingleBit(cell))
					gt = GateType::Mux;
				else
					continue;

				if (mux_only && gt != GateType::Mux)
					continue;

				if (no_mux && gt == GateType::Mux)
					continue;

				log_debug("Working on cell %s...\n", cell->name.c_str());

				// If looking for a single chain, follow linearly to the sink
				pool<Cell*> sinks;
				if(!allow_off_chain)
				{
					Cell* head_cell = cell;
					Cell* x = cell;
					while (true)
					{
						if(!IsRightType(x, gt))
							break;

						head_cell = x;

						auto y = sigmap(x->getPort(ID::Y));
						log_assert(y.size() == 1);

						// Should only continue if there is one fanout back into a cell (not to a port)
						if (sig_to_sink[y].size() != 1 || port_sigs.count(y))
							break;

						x = *sig_to_sink[y].begin();
					}

					sinks.insert(head_cell);
				}

				//If off-chain loads are allowed, we have to do a wider traversal to see what the longest chain is
				else
				{
					//BFS, following all chains until they hit a cell of a different type
					//Pick the longest one
					auto y = sigmap(cell->getPort(ID::Y));
					pool<Cell*> current_loads = sig_to_sink[y];
					pool<Cell*> next_loads;

					while(!current_loads.empty())
					{
						//Find each sink and see what they are
						for(auto x : current_loads)
						{
							//Not one of our gates? Don't follow any further
							//(but add the originating cell to the list of sinks)
							if(!IsRightType(x, gt))
							{
								sinks.insert(cell);
								continue;
							}

							auto xy = sigmap(x->getPort(ID::Y));

							//If this signal drives a port, add it to the sinks
							//(even though it may not be the end of a chain)
							if(port_sigs.count(xy) && !consumed_cells.count(x))
								sinks.insert(x);

							//It's a match, search everything out from it
							auto& next = sig_to_sink[xy];
							for(auto z : next)
								next_loads.insert(z);
						}

						//If we couldn't find any downstream loads, stop.
						//Create a reduction for each of the max-length chains we found
						if(next_loads.empty())
						{
							for(auto s : current_loads)
							{
								//Not one of our gates? Don't follow any further
								if(!IsRightType(s, gt))
									continue;

								sinks.insert(s);
							}
							break;
						}

						//Otherwise, continue down the chain
						current_loads = next_loads;
						next_loads.clear();
					}
				}

				//We have our list, go act on it
				for(auto head_cell : sinks)
				{
					log_debug("  Head cell is %s\n", head_cell->name.c_str());

					//Avoid duplication if we already were covered
					if(consumed_cells.count(head_cell))
						continue;

					dict<SigBit, int> sources;
					dict<SigBit, int> sels;
					int inner_cells = 0;
					std::deque<std::pair<Cell*, SigBit>> bfs_queue = {{head_cell, State::S1}};
					std::set<Cell*> seen_set = {};
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
							bool drv_ok = drv && IsRightType(drv, gt) && !consumed_cells.count(drv) && !seen_set.count(drv);
							seen_set.insert(drv);

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
							if (head_cell->type == ID($_XOR_) || head_cell->type == ID($xor))
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
} ExtractReducePass;

PRIVATE_NAMESPACE_END
