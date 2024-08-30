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

	// Cells to remove
	pool<Cell*> remove_cells;

	// Signal chain data structures
	dict<SigSpec, Cell*> sig_chain_next;
	dict<SigSpec, Cell*> sig_chain_prev;
	pool<SigBit> sigbit_with_non_chain_users;
	pool<Cell*> chain_start_cells;
	pool<Cell*> candidate_cells;

	void make_sig_chain_next_prev(IdString cell_type) {
		// Mark all wires with keep attribute as having non-chain users
		for (auto wire : module->wires()) {
			if (wire->get_bool_attribute(ID::keep)) {
				for (auto bit : sigmap(wire))
					sigbit_with_non_chain_users.insert(bit);
			}
		}

		// Iterate over all cells in module
		for (auto cell : module->cells()) {
			// If cell matches and not marked as keep
			if (cell->type == cell_type && !cell->get_bool_attribute(ID::keep)) {
				// Get signals for cell ports
				SigSpec a_sig = sigmap(cell->getPort(ID::A));
				SigSpec b_sig = sigmap(cell->getPort(ID::B));
				SigSpec y_sig = sigmap(cell->getPort(ID::Y));
   
	 			// If a_sig already has a chain user, mark its bits as having non-chain users
				if (sig_chain_next.count(a_sig))
					for (auto a_bit : a_sig.bits())
						sigbit_with_non_chain_users.insert(a_bit);
				// Otherwise, mark cell as the next in the chain relative to a_sig
				else {
					sig_chain_next[a_sig] = cell;
				}

				if (!b_sig.empty()) {
					// If b_sig already has a chain user, mark its bits as having non-chain users
					if (sig_chain_next.count(b_sig))
						for (auto b_bit : b_sig.bits())
							sigbit_with_non_chain_users.insert(b_bit);
					// Otherwise, mark cell as the next in the chain relative to b_sig
					else {
						sig_chain_next[b_sig] = cell;
					}
				}
				
				// Add cell as candidate
				candidate_cells.insert(cell);

				// Mark cell as the previous in the chain relative to y_sig
				sig_chain_prev[y_sig] = cell;
			}
			// If cell is not matching type, mark all cell input signals as being non-chain users
			else {
				for (auto conn : cell->connections())
					if (cell->input(conn.first))
						for (auto bit : sigmap(conn.second))
							sigbit_with_non_chain_users.insert(bit);
			}
		}
	}

	void find_chain_start_cells() {
		for (auto cell : candidate_cells) {
			// Log candidate cell
			log("Considering %s (%s)\n", log_id(cell), log_id(cell->type));

			// Get signals for cell ports
			SigSpec a_sig = sigmap(cell->getPort(ID::A));
			SigSpec b_sig = sigmap(cell->getPort(ID::B));
			SigSpec prev_sig = sig_chain_prev.count(a_sig) ? a_sig : b_sig;
			
			// This is a start cell if there was no previous cell in the chain for a_sig or b_sig
			if (sig_chain_prev.count(a_sig) + sig_chain_prev.count(b_sig) != 1) {
				chain_start_cells.insert(cell);
				continue;
			}

			// If any bits in previous cell signal have non-chain users, this is a start cell
			for (auto bit : prev_sig.bits())
				if (sigbit_with_non_chain_users.count(bit)) {
					chain_start_cells.insert(cell);
					continue;
				}
		}
	}

	vector<Cell*> create_chain(Cell *start_cell) {
		// Chain of cells
		vector<Cell*> chain;

		// Current cell
		Cell *c = start_cell;

		// Iterate over cells and add to chain
		while (c != nullptr) {
			chain.push_back(c);

			SigSpec y_sig = sigmap(c->getPort(ID::Y));

			if (sig_chain_next.count(y_sig) == 0)
				break;

			c = sig_chain_next.at(y_sig);
			if (chain_start_cells.count(c) != 0)
				break;
		}

		// Return chain of cells
		return chain;
	}

	void wreduce(Cell *cell) {
		// If cell is arithmetic, remove leading zeros from inputs, then clean up outputs
		if (cell->type.in(ID($add), ID($mul))) {
			// Remove leading zeros from inputs
			for (auto inport : {ID::A, ID::B}) {
				// Record number of bits removed
				int bits_removed = 0;
				IdString inport_signed = (inport == ID::A) ? ID::A_SIGNED : ID::B_SIGNED;
				IdString inport_width = (inport == ID::A) ? ID::A_WIDTH : ID::B_WIDTH;
				SigSpec inport_sig = sigmap(cell->getPort(inport));
				cell->unsetPort(inport);
				if (cell->getParam((inport == ID::A) ? ID::A_SIGNED : ID::B_SIGNED).as_bool()) {
					while (GetSize(inport_sig) > 1 && inport_sig[GetSize(inport_sig)-1] == State::S0 && inport_sig[GetSize(inport_sig)-2] == State::S0) {
						inport_sig.remove(GetSize(inport_sig)-1, 1);
						bits_removed++;
					}
				} else {
					while (GetSize(inport_sig) > 0 && inport_sig[GetSize(inport_sig)-1] == State::S0) {
						inport_sig.remove(GetSize(inport_sig)-1, 1);
						bits_removed++;
					}
				}
				cell->setPort(inport, inport_sig);
				cell->setParam(inport_width, GetSize(inport_sig));
				log("Width reduced %s/%s by %d bits\n", log_id(cell), log_id(inport), bits_removed);
			}

			// Record number of bits removed from output
			int bits_removed = 0;

			// Remove unnecessary bits from output
			SigSpec y_sig = sigmap(cell->getPort(ID::Y));
			cell->unsetPort(ID::Y);
			int width;
			if (cell->type == ID($add))
				width = std::max(cell->getParam(ID::A_WIDTH).as_int(), cell->getParam(ID::B_WIDTH).as_int()) + 1;
			else if (cell->type == ID($mul))
				width = cell->getParam(ID::A_WIDTH).as_int() + cell->getParam(ID::B_WIDTH).as_int();
			else log_abort();
			for (int i = GetSize(y_sig) - 1; i >= width; i--) {
				module->connect(y_sig[i], State::S0);
				y_sig.remove(i, 1);
				bits_removed++;
			}
			cell->setPort(ID::Y, y_sig);
			cell->setParam(ID::Y_WIDTH, GetSize(y_sig));
			log("Width reduced %s/Y by %d bits\n", log_id(cell), bits_removed);
		}
	}

	void process_chain(vector<Cell*> &chain) {
		// If chain size is less than 3, no balancing needed
		if (GetSize(chain) < 3)
			return;

		// Get mid, midnext (at index mid+1) and end of chain
		Cell *mid_cell = chain[GetSize(chain) / 2];
		Cell *midnext_cell = chain[GetSize(chain) / 2 + 1];
		Cell *end_cell = chain.back();
		log("Balancing chain of %d cells: mid=%s, midnext=%s, endcell=%s\n",
		    GetSize(chain), log_id(mid_cell), log_id(midnext_cell), log_id(end_cell));

		// Get mid signals
		SigSpec mid_a_sig = sigmap(mid_cell->getPort(ID::A));
		SigSpec mid_b_sig = sigmap(mid_cell->getPort(ID::B));
		SigSpec mid_non_chain_sig = sig_chain_prev.count(mid_a_sig) ? mid_b_sig : mid_a_sig;
		IdString mid_non_chain_port = sig_chain_prev.count(mid_a_sig) ? ID::B : ID::A;

		// Get midnext signals
		SigSpec midnext_a_sig = sigmap(midnext_cell->getPort(ID::A));
		SigSpec midnext_b_sig = sigmap(midnext_cell->getPort(ID::B));
		IdString midnext_chain_port = sig_chain_prev.count(midnext_a_sig) ? ID::A : ID::B;

		// Get output signal
		SigSpec end_y_sig = sigmap(end_cell->getPort(ID::Y));

		// Create new mid wire
		Wire *mid_wire = module->addWire(NEW_ID, GetSize(end_y_sig));

		// Perform rotation
		mid_cell->setPort(mid_non_chain_port, mid_wire);
		mid_cell->setPort(ID::Y, end_y_sig);
		midnext_cell->setPort(midnext_chain_port, mid_non_chain_sig);
		end_cell->setPort(ID::Y, mid_wire);

		// Recreate sigmap
		sigmap.set(module);

		// Get subtrees
		vector<Cell*> left_chain(chain.begin(), chain.begin() + GetSize(chain) / 2);
		vector<Cell*> right_chain(chain.begin() + GetSize(chain) / 2 + 1, chain.end());

		// Recurse on subtrees
		process_chain(left_chain);
		process_chain(right_chain);
		
		// Width reduce left subtree
		for (auto c : left_chain)
			wreduce(c);
		
		// Width reduce right subtree
		for (auto c : right_chain)
			wreduce(c);

		// Recreate sigmap
		sigmap.set(module);

		// Width reduce mid cell
		wreduce(mid_cell);
	}

	void cleanup() {
		// Remove cells
		for (auto cell : remove_cells)
			module->remove(cell);

		// Fix ports
		module->fixup_ports();

		// Clear data structures
		remove_cells.clear();
		sig_chain_next.clear();
		sig_chain_prev.clear();
		sigbit_with_non_chain_users.clear();
		chain_start_cells.clear();
		candidate_cells.clear();
	}

	OptBalanceTreeWorker(Module *module, const vector<IdString> cell_types) : module(module), sigmap(module) {
		// Do for each cell type
		for (auto cell_type : cell_types) {
			// Find chains of ops
			make_sig_chain_next_prev(cell_type);
			find_chain_start_cells();

			// For each chain, if len >= 3, convert to tree via "rotation" and recurse on subtrees
			for (auto c : chain_start_cells) {
				vector<Cell*> chain = create_chain(c);
				process_chain(chain);
				cell_count[cell_type] += GetSize(chain);
			}

			// Clean up
			cleanup();
		}
	}
};

struct OptBalanceTreePass : public Pass {
	OptBalanceTreePass() : Pass("opt_balance_tree", "$and/$or/$xor/$xnor/$add/$mul cascades to trees") { }
	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_balance_tree [options] [selection]\n");
		log("\n");
		log("This pass converts cascaded chains of $and/$or/$xor/$xnor/$add/$mul cells into\n");
		log("trees of cells to improve timing.\n");
		log("\n");
		log("    -splitfanout\n");
		log("        run splitfanout pass first\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		bool splitfanout = false;

		log_header(design, "Executing OPT_BALANCE_TREE pass (cell cascades to trees).\n");

		// Handle arguments
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-splitfanout") {
				splitfanout = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Run splitfanout pass first
		if (splitfanout)
			Pass::call(design, "splitfanout t:$and t:$or t:$xor t:$add t:$mul");

		// Count of all cells that were packed
		dict<IdString, int> cell_count;
		const vector<IdString> cell_types = {ID($and), ID($or), ID($xor), ID($xnor), ID($add), ID($mul)};
		for (auto module : design->selected_modules()) {
			OptBalanceTreeWorker worker(module, cell_types);
			for (auto cell : worker.cell_count) {
				cell_count[cell.first] += cell.second;
			}
		}

		// Log stats
		for (auto cell_type : cell_types)
			log("Converted %d %s cells into trees.\n", cell_count[cell_type], log_id(cell_type));
	}
} OptBalanceTreePass;

PRIVATE_NAMESPACE_END
