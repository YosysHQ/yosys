/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2025  Akash Levy        <akash@silimate.com>
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
#include "kernel/utils.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct FanoutbufPass : public Pass {
	FanoutbufPass() : Pass("fanoutbuf", "insert $buf cells to limit fanout") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fanoutbuf [options] [selection]\n");
		log("\n");
		log("This command inserts $buf cells to limit fanout while minimizing the number of");
		log("buffers inserted.\n");
		log("\n");
		log("    -limit n\n");
		log("        max fanout to allow (default: 4).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int limit = 4;
		log_header(design, "Executing FANOUTBUF pass (inserting buffers to limit fanout).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-limit" && argidx+1 < args.size()) {
				limit = std::stoi(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			// Add $pos cells on input ports and output ports
			vector<Wire *> ports;
			vector<Cell *> iobufs;
			for (auto port : module->ports) {
				auto wire = module->wire(port);
				if (wire->port_input) {
					auto new_in_name = module->uniquify(wire->name.str().replace(0, 1, "$") + "_new");
					auto new_in = module->addWire(new_in_name, wire);
					auto iobuf = module->addPos(module->uniquify(wire->name.str() + "_in"), new_in, wire);
					iobufs.push_back(iobuf);
					module->swap_names(wire, new_in);
					wire->port_input = false;
				}
				if (wire->port_output) {
					auto new_out_name = module->uniquify(wire->name.str().replace(0, 1, "$") + "_new");
					auto new_out = module->addWire(new_out_name, wire);
					auto iobuf = module->addPos(module->uniquify(wire->name.str() + "_out"), wire, new_out);
					iobufs.push_back(iobuf);
					module->swap_names(wire, new_out);
					wire->port_output = false;
				}
			}
			module->fixup_ports();

			// Data structures for splitting fanout
			SigMap sigmap(module);
			dict<SigBit, pool<tuple<IdString,IdString,int>>> bit_users_db;
			int bufcount = 0;

			// Build bit_users_db
			log_debug("Building bit_users_db...\n");
			for (auto cell : module->cells()) {
				for (auto conn : cell->connections()) {
					if (!cell->input(conn.first)) continue;
					for (int i = 0; i < GetSize(conn.second); i++) {
						SigBit bit(sigmap(conn.second[i]));
						bit_users_db[bit].insert(tuple<IdString,IdString,int>(cell->name, conn.first, i));
					}
				}
			}

			// Queue up all cells
			std::set<Cell*, IdString::compare_ptr_by_name<Cell>> work_queue_cells;
			for (auto cell : module->selected_cells())
				work_queue_cells.insert(cell);

			// Split fanout with BFS
			while (!work_queue_cells.empty()) {
				auto cell = *work_queue_cells.begin();
				work_queue_cells.erase(work_queue_cells.begin());
				for (auto conn : cell->connections()) {
					if (!cell->output(conn.first)) continue;
					for (auto bit : sigmap(conn.second)) {
						// Collect targets
						auto targets = bit_users_db[bit];
						bit_users_db[bit].clear();

						// If there are less than limit targets, no need to split
						if (GetSize(targets) <= limit)
							continue;

						// Set up buffers
						int nbufs = std::min(limit, GetSize(targets) / limit);
						vector<Wire *> bufouts(nbufs, nullptr);
						for (int i = 0; i < nbufs; i++) {
							// New buffer name should be unique and short
							IdString buf_name;
							if (cell->type == ID::$buf)
								buf_name = NEW_ID2;
							else
								buf_name = NEW_ID2_SUFFIX("fbuf");
							// Create buffer, connect input to bit and output to new wire
							Wire *bufout = module->addWire(buf_name.str() + "_out");
							Cell *buf = module->addBuf(buf_name, bit, bufout, false, cell->get_src_attribute());
							buf->set_bool_attribute("\\keep", true);
							sigmap.add(bufout);
							work_queue_cells.insert(buf);
							bufouts[i] = bufout;
							bufcount++;
						}

						// Target limit is initialized to limit
						// Gets multiplied by limit each time the current set of buffers is saturated
						int target_limit = limit;
						int target_i = 0;
						int cur_buf_i = 0;
						vector<int> current_fanout(nbufs, 0);
						for (auto target : targets) {
							// If there are less buffers than the limit, keep a few targets on the original cell
							bool skip_target = false;
							if (target_i < limit - nbufs) {
								target_i++;
								skip_target = true;
							}
							if (skip_target)
								continue;
							// Search for a buffer with fanout less than target_limit
							while (current_fanout[cur_buf_i] >= target_limit) {
								cur_buf_i++;
								// If we've reached the end of the buffers, reset to the start
								// and increase target limit
								if (cur_buf_i >= nbufs) {
									cur_buf_i = 0;
									target_limit *= limit;
								}
							}
							// Replace bit in target cell with buffered output
							auto target_cell = module->cell(std::get<0>(target));
							auto target_port = std::get<1>(target);
							auto target_bit_idx = std::get<2>(target);
							auto new_cell_in = target_cell->getPort(target_port);
							new_cell_in[target_bit_idx] = bufouts[cur_buf_i];
							target_cell->setPort(target_port, new_cell_in);
							bit_users_db[bufouts[cur_buf_i]].insert(
								tuple<IdString,IdString,int>(target_cell->name, target_port, target_bit_idx)
							);
							sigmap.add(bufouts[cur_buf_i], new_cell_in[target_bit_idx]);
							// Increment fanout for current buffer
							current_fanout[cur_buf_i]++;
						}
					}
				}
			}
			
			// Log number of buffers inserted
			log("Inserted %d buffers in module '%s'.\n", bufcount, log_id(module));
		}

		// Clean wires
		Yosys::run_pass("clean", design);
	}
} FanoutbufPass;

PRIVATE_NAMESPACE_END
