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
		Xor
	};

	ExtractReducePass() : Pass("extract_reduce", "converts gate chains into $reduce_* cells") { }

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
		log("    -allow-off-chain\n");
		log("        Allows matching of cells that have loads outside the chain. These cells\n");
		log("        will be replicated and folded into the $reduce_* cell, but the original\n");
		log("        cell will remain, driving its original loads.\n");
		log("\n");
	}

	inline bool IsRightType(Cell* cell, GateType gt)
	{
		return (cell->type == ID($_AND_) && gt == GateType::And) ||
				(cell->type == ID($_OR_) && gt == GateType::Or) ||
				(cell->type == ID($_XOR_) && gt == GateType::Xor);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing EXTRACT_REDUCE pass.\n");
		log_push();

		size_t argidx;
		bool allow_off_chain = false;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-allow-off-chain")
			{
				allow_off_chain = true;
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
				else
					continue;

				log("Working on cell %s...\n", cell->name.c_str());

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
					log("  Head cell is %s\n", head_cell->name.c_str());

					//Avoid duplication if we already were covered
					if(consumed_cells.count(head_cell))
						continue;

					dict<SigBit, int> sources;
					int inner_cells = 0;
					std::deque<Cell*> bfs_queue = {head_cell};
					while (bfs_queue.size())
					{
						Cell* x = bfs_queue.front();
						bfs_queue.pop_front();

						for (auto port: {ID::A, ID::B}) {
							auto bit = sigmap(x->getPort(port)[0]);

							bool sink_single = sig_to_sink[bit].size() == 1 && !port_sigs.count(bit);

							Cell* drv = sig_to_driver[bit];
							bool drv_ok = drv && drv->type == head_cell->type;

							if (drv_ok && (allow_off_chain || sink_single)) {
								inner_cells++;
								bfs_queue.push_back(drv);
							} else {
								sources[bit]++;
							}
						}
					}

					if (inner_cells)
					{
						// Worth it to create reduce cell
						log("  Creating $reduce_* cell!\n");

						SigBit output = sigmap(head_cell->getPort(ID::Y)[0]);

						SigSpec input;
						for (auto it : sources) {
							bool cond;
							if (head_cell->type == ID($_XOR_))
								cond = it.second & 1;
							else
								cond = it.second != 0;
							if (cond)
								input.append(it.first);
						}

						if (head_cell->type == ID($_AND_)) {
							module->addReduceAnd(NEW_ID, input, output);
						} else if (head_cell->type == ID($_OR_)) {
							module->addReduceOr(NEW_ID, input, output);
						} else if (head_cell->type == ID($_XOR_)) {
							module->addReduceXor(NEW_ID, input, output);
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
