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

	virtual void help()
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
		log("    -debug-verbose\n");
		log("        Debug print internal states.\n");
		log("\n");
	}

	inline bool IsRightType(Cell* cell, GateType gt)
	{
		return (cell->type == "$_AND_" && gt == GateType::And) ||
				(cell->type == "$_OR_" && gt == GateType::Or) ||
				(cell->type == "$_XOR_" && gt == GateType::Xor) ||
				(cell->type == "$and" && gt == GateType::And) ||
				(cell->type == "$or" && gt == GateType::Or) ||
				(cell->type == "$xor" && gt == GateType::Xor);
	}

	bool is_single_bit(Cell *cell, SigMap sigmap)
	{
		bool res = true;
		auto a = sigmap(cell->getPort("\\A"));
		auto b = sigmap(cell->getPort("\\B"));
		auto y = sigmap(cell->getPort("\\Y"));
		if ((GetSize(a) != 1) || (GetSize(b) != 1) || (GetSize(y) != 1))
			res =  false;
		return res;
	}

	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing EXTRACT_REDUCE pass.\n");
		log_push();

		size_t argidx;
		bool allow_off_chain = false;
		bool debug_verbose = false;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-allow-off-chain")
			{
				allow_off_chain = true;
				continue;
			}
			if (args[argidx] == "-debug-verbose")
			{
				debug_verbose = true;
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
				if (debug_verbose)
					log("\n  Index cell is: %s\n", cell->name.c_str());
				for (auto &conn : cell->connections())
				{
					if (cell->output(conn.first))
						if (debug_verbose)
							log("    Output conn: %s\n", log_signal(conn.second));
						for (auto bit : sigmap(conn.second))
							sig_to_driver[bit] = cell;

					if (cell->input(conn.first))
					{
						if (debug_verbose)
							log("    Input conn: %s\n", log_signal(conn.second));
						for (auto bit : sigmap(conn.second))
						{
							if (debug_verbose)
								log("  sig_to_sink: %s\n", log_signal(bit));
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
					{
						port_sigs.insert(bit);
						if (debug_verbose)
							log("  Port bit: %s\n", log_signal(bit));
					}

			// Actual logic starts here
			pool<Cell*> consumed_cells;
			for (auto cell : module->selected_cells())
			{
				if (consumed_cells.count(cell))
					continue;

				GateType gt;

				if (cell->type == "$_AND_")
					gt = GateType::And;
				else if (cell->type == "$_OR_")
					gt = GateType::Or;
				else if (cell->type == "$_XOR_")
					gt = GateType::Xor;
				else if (cell->type == "$and")
					gt = GateType::And;
				else if (cell->type == "$or")
					gt = GateType::Or;
				else if (cell->type == "$xor")
					gt = GateType::Xor;
				else
					continue;

				if (!is_single_bit(cell, sigmap))
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
						if (!is_single_bit(x, sigmap))
							break;

						head_cell = x;

						if (debug_verbose)
						{
							log("  Chain head cell is: %s\n", head_cell->name.c_str());
							log("  Chain head cell Y width: %i\n", GetSize(head_cell->getPort("\\Y")));
						}

						auto y = sigmap(x->getPort("\\Y"));
						log_assert(y.size() == 1);

						// Should only continue if there is one fanout back into a cell (not to a port)
						if (sig_to_sink[y[0]].size() != 1)
							break;

						x = *sig_to_sink[y[0]].begin();
					}

					sinks.insert(head_cell);
				}

				//If off-chain loads are allowed, we have to do a wider traversal to see what the longest chain is
				else
				{
					//BFS, following all chains until they hit a cell of a different type
					//Pick the longest one
					auto y = sigmap(cell->getPort("\\Y"));
					pool<Cell*> current_loads = sig_to_sink[y];
					pool<Cell*> next_loads;

					while(!current_loads.empty())
					{
						//Find each sink and see what they are
						for(auto x : current_loads)
						{
							if (debug_verbose)
							{
								log("  Off-chain current_load is: %s\n", x->name.c_str());
								log("  Off-chain current_load Y width: %i\n", GetSize(x->getPort("\\Y")));
							}

							//Not one of our gates? Don't follow any further
							//(but add the originating cell to the list of sinks)
							if(!IsRightType(x, gt) || (!is_single_bit(cell, sigmap)))
							{
								sinks.insert(cell);
								continue;
							}

							//If this signal drives a port, add it to the sinks
							//(even though it may not be the end of a chain)
							if(port_sigs.count(x) && !consumed_cells.count(x))
								sinks.insert(x);

							//It's a match, search everything out from it
							auto& next = sig_to_sink[x];
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
								if(!IsRightType(s, gt) || (!is_single_bit(cell, sigmap)))
									continue;

								sinks.insert(s);
								if (debug_verbose)
								{
									log("  Insert sink: %s\n", s->name.c_str());
									log("  Insert sink Y width: %i\n", GetSize(s->getPort("\\Y")));
								}
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
					log("  Head cell is: %s\n", head_cell->name.c_str());
					if (debug_verbose)
						log("  Head cell Y width: %i\n", GetSize(head_cell->getPort("\\Y")));

					//Avoid duplication if we already were covered
					if(consumed_cells.count(head_cell))
						continue;

					pool<Cell*> cur_supercell;
					std::deque<Cell*> bfs_queue = {head_cell};
					while (bfs_queue.size())
					{
						Cell* x = bfs_queue.front();
						bfs_queue.pop_front();

						cur_supercell.insert(x);

						if (debug_verbose)
						{
							log("  Super cell is: %s\n", x->name.c_str());
							log("  Super cell Y width: %i\n", GetSize(x->getPort("\\Y")));
						}

						auto a = sigmap(x->getPort("\\A"));
						if (debug_verbose)
							log("Super cell A:%s\n", log_signal(a));
						log_assert(a.size() == 1);

						// Must have only one sink unless we're going off chain
						// XXX: Check that it is indeed this node?
						if( allow_off_chain || (sig_to_sink[a[0]].size() + port_sigs.count(a[0]) == 1) )
						{
							Cell* cell_a = sig_to_driver[a[0]];
							if(cell_a && IsRightType(cell_a, gt) && is_single_bit(cell_a, sigmap))
							{
								if (debug_verbose)
								{
									log("  cell_a is: %s\n", cell_a->name.c_str());
									log("  cell_a Y width: %i\n", GetSize(cell_a->getPort("\\Y")));
								}
								// The cell here is the correct type, and it's definitely driving
								// this current cell.
								bfs_queue.push_back(cell_a);
							}
						}

						auto b = sigmap(x->getPort("\\B"));
						if (debug_verbose)
							log("Super cell B: %s\n", log_signal(b));
						log_assert(b.size() == 1);

						// Must have only one sink
						// XXX: Check that it is indeed this node?
						if( allow_off_chain || (sig_to_sink[b[0]].size() + port_sigs.count(b[0]) == 1) )
						{
							Cell* cell_b = sig_to_driver[b[0]];
							if(cell_b && IsRightType(cell_b, gt) && is_single_bit(cell_b, sigmap))
							{
								if (debug_verbose)
								{
									log("  cell_b is: %s\n", cell_b->name.c_str());
									log("  cell_b Y width: %i\n", GetSize(cell_b->getPort("\\Y")));
								}
								
								// The cell here is the correct type, and it's definitely driving only
								// this current cell.
								bfs_queue.push_back(cell_b);
							}
						}
					}

					log("  Cells:\n");
					for (auto x : cur_supercell)
						log("    %s\n", x->name.c_str());

					if (cur_supercell.size() > 1)
					{
						// Worth it to create reduce cell
						log("  Creating $reduce_* cell!\n");

						pool<SigBit> input_pool;
						pool<SigBit> input_pool_intermed;
						for (auto x : cur_supercell)
						{
							if (debug_verbose)
							{
								log("  R cell is: %s\n", x->name.c_str());
								log("  R cell A width: %i\n", GetSize(x->getPort("\\A")));
								log("  R cell A conn: %s\n", log_signal(x->getPort("\\A")));
								log("  R cell A smap: %s\n", log_signal(sigmap(x->getPort("\\A"))[0]));
								log("  R cell B width: %i\n", GetSize(x->getPort("\\B")));
								log("  R cell B conn: %s\n", log_signal(x->getPort("\\B")));
								log("  R cell B smap: %s\n", log_signal(sigmap(x->getPort("\\B"))[0]));
								log("  R cell Y width: %i\n", GetSize(x->getPort("\\Y")));
							}
							input_pool.insert(sigmap(x->getPort("\\A"))[0]);
							input_pool.insert(sigmap(x->getPort("\\B"))[0]);
							input_pool_intermed.insert(sigmap(x->getPort("\\Y"))[0]);
						}
						SigSpec input;
						for (auto b : input_pool)
							if (input_pool_intermed.count(b) == 0)
								input.append_bit(b);
						if (debug_verbose)
							log("  New input %s\n", log_signal(sigmap(input)));

						SigBit output = sigmap(head_cell->getPort("\\Y")[0]);
						if (debug_verbose)
							log("  Head out %s\n", log_signal(sigmap(head_cell->getPort("\\Y")[0])));

						auto new_reduce_cell = module->addCell(NEW_ID,
							gt == GateType::And ? "$reduce_and" :
							gt == GateType::Or ? "$reduce_or" :
							gt == GateType::Xor ? "$reduce_xor" : "");
						new_reduce_cell->setParam("\\A_SIGNED", 0);
						new_reduce_cell->setParam("\\A_WIDTH", input.size());
						new_reduce_cell->setParam("\\Y_WIDTH", 1);
						new_reduce_cell->setPort("\\A", input);
						new_reduce_cell->setPort("\\Y", output);

						if(allow_off_chain)
							consumed_cells.insert(head_cell);
						else
						{
							for (auto x : cur_supercell)
								consumed_cells.insert(x);
						}
					}
				}
			}

			// Remove all of the head cells, since we supplant them.
			// Do not remove the upstream cells since some might still be in use ("clean" will get rid of unused ones)
			for (auto cell : consumed_cells)
			{
				if (debug_verbose)
				{
					log("  Remove cell.\n");
					log_cell(cell);
				}
				module->remove(cell);
			}
		}

		log_pop();
	}
} ExtractReducePass;

PRIVATE_NAMESPACE_END
