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

struct RecoverReduceCorePass : public Pass {
	enum GateType {
		And,
		Or,
		Xor
	};

	RecoverReduceCorePass() : Pass("recover_reduce_core", "converts gate chains into $reduce_*") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    recover_reduce_core\n");
		log("\n");
		log("converts gate chains into $reduce_*\n");
		log("\n");
		log("This performs the core step of the recover_reduce command. This step recognizes\n");
		log("chains of gates found by the previous steps and converts these chains into one\n");
		log("logical cell.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		(void)args;

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

				if (cell->type == "$_AND_")
					gt = GateType::And;
				else if (cell->type == "$_OR_")
					gt = GateType::Or;
				else if (cell->type == "$_XOR_")
					gt = GateType::Xor;
				else
					continue;

				log("Working on cell %s...\n", cell->name.c_str());

				// Go all the way to the sink
				Cell* head_cell = cell;
				Cell* x = cell;
				while (true)
				{
					if (!((x->type == "$_AND_" && gt == GateType::And) ||
						(x->type == "$_OR_" && gt == GateType::Or) ||
						(x->type == "$_XOR_" && gt == GateType::Xor)))
						break;

					head_cell = x;

					auto y = sigmap(x->getPort("\\Y"));
					log_assert(y.size() == 1);

					// Should only continue if there is one fanout back into a cell (not to a port)
					if (sig_to_sink[y[0]].size() != 1)
						break;

					x = *sig_to_sink[y[0]].begin();
				}

				log("  Head cell is %s\n", head_cell->name.c_str());

				pool<Cell*> cur_supercell;
				std::deque<Cell*> bfs_queue = {head_cell};
				while (bfs_queue.size())
				{
					Cell* x = bfs_queue.front();
					bfs_queue.pop_front();

					cur_supercell.insert(x);

					auto a = sigmap(x->getPort("\\A"));
					log_assert(a.size() == 1);
					// Must have only one sink
					// XXX: Check that it is indeed this node?
					if (sig_to_sink[a[0]].size() + port_sigs.count(a[0]) == 1)
					{
						Cell* cell_a = sig_to_driver[a[0]];
						if (((cell_a->type == "$_AND_" && gt == GateType::And) ||
							(cell_a->type == "$_OR_" && gt == GateType::Or) ||
							(cell_a->type == "$_XOR_" && gt == GateType::Xor)))
						{
							// The cell here is the correct type, and it's definitely driving only
							// this current cell.
							bfs_queue.push_back(cell_a);
						}
					}

					auto b = sigmap(x->getPort("\\B"));
					log_assert(b.size() == 1);
					// Must have only one sink
					// XXX: Check that it is indeed this node?
					if (sig_to_sink[b[0]].size() + port_sigs.count(b[0]) == 1)
					{
						Cell* cell_b = sig_to_driver[b[0]];
						if (((cell_b->type == "$_AND_" && gt == GateType::And) ||
							(cell_b->type == "$_OR_" && gt == GateType::Or) ||
							(cell_b->type == "$_XOR_" && gt == GateType::Xor)))
						{
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
						input_pool.insert(sigmap(x->getPort("\\A"))[0]);
						input_pool.insert(sigmap(x->getPort("\\B"))[0]);
						input_pool_intermed.insert(sigmap(x->getPort("\\Y"))[0]);
					}
					SigSpec input;
					for (auto b : input_pool)
						if (input_pool_intermed.count(b) == 0)
							input.append_bit(b);

					SigBit output = sigmap(head_cell->getPort("\\Y")[0]);

					auto new_reduce_cell = module->addCell(NEW_ID, 
						gt == GateType::And ? "$reduce_and" :
						gt == GateType::Or ? "$reduce_or" :
						gt == GateType::Xor ? "$reduce_xor" : "");
					new_reduce_cell->setParam("\\A_SIGNED", 0);
					new_reduce_cell->setParam("\\A_WIDTH", input.size());
					new_reduce_cell->setParam("\\Y_WIDTH", 1);
					new_reduce_cell->setPort("\\A", input);
					new_reduce_cell->setPort("\\Y", output);

					for (auto x : cur_supercell)
						consumed_cells.insert(x);
					}
				}

			// Remove every cell that we've used up
			for (auto cell : consumed_cells)
				module->remove(cell);
		}
	}
} RecoverReduceCorePass;

PRIVATE_NAMESPACE_END
