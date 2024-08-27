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
	Module *module;
	SigMap sigmap;

	dict<IdString, int> cell_count;

	pool<Cell*> remove_cells;

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
				if (sig_chain_next.count(a_sig) && !a_sig.is_fully_const()) // also ok if a_sig is fully const
					for (auto a_bit : a_sig.bits())
						sigbit_with_non_chain_users.insert(a_bit);
				// Otherwise, mark cell as the next in the chain relative to a_sig
				else {
					sig_chain_next[a_sig] = cell;
					candidate_cells.insert(cell);
				}

				if (!b_sig.empty()) {
					// If b_sig already has a chain user, mark its bits as having non-chain users
					if (sig_chain_next.count(b_sig) && !b_sig.is_fully_const()) // also ok if b_sig is fully const
						for (auto b_bit : b_sig.bits())
							sigbit_with_non_chain_users.insert(b_bit);
					// Otherwise, mark cell as the next in the chain relative to b_sig
					else {
						sig_chain_next[b_sig] = cell;
						candidate_cells.insert(cell);
					}
				}

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

	void process_chain(vector<Cell*> &chain) {
		// If chain size is less than 3, no balancing needed
		if (GetSize(chain) < 3)
			return;

		// Get mid, midnext (at index mid+1) and end of chain
		Cell *mid_cell = chain[GetSize(chain) / 2];
		Cell *midnext_cell = chain[GetSize(chain) / 2 + 1];
		Cell *end_cell = chain.back();

		// Get mid signals
		SigSpec mid_a_sig = sigmap(mid_cell->getPort(ID::A));
		SigSpec mid_b_sig = sigmap(mid_cell->getPort(ID::B));
		SigSpec mid_non_chain_sig = sig_chain_prev.count(mid_a_sig) ? mid_b_sig : mid_a_sig;
		IdString mid_non_chain_port = sig_chain_prev.count(mid_a_sig) ? ID::B : ID::A;

		// Get midnext signals
		SigSpec midnext_a_sig = sigmap(midnext_cell->getPort(ID::A));
		SigSpec midnext_b_sig = sigmap(midnext_cell->getPort(ID::B));
		IdString midnext_chain_port = sig_chain_next.count(midnext_a_sig) ? ID::A : ID::B;

		// Get output signal
		SigSpec end_y_sig = sigmap(end_cell->getPort(ID::Y));

		// Unset ports involved in rotation
		mid_cell->unsetPort(mid_non_chain_port);
		mid_cell->unsetPort(ID::Y);
		midnext_cell->unsetPort(midnext_chain_port);
		end_cell->unsetPort(ID::Y);

		// Perform rotation
		mid_cell->setPort(ID::Y, end_y_sig);
		midnext_cell->setPort(midnext_chain_port, mid_non_chain_sig);
		end_cell->setPort(ID::Y, mid_cell->getPort(mid_non_chain_port));

		// Recurse on subtrees
		vector<Cell*> left_chain(chain.begin(), chain.begin() + GetSize(chain) / 2);
		vector<Cell*> right_chain(chain.begin() + GetSize(chain) / 2 + 1, chain.end());
		process_chain(left_chain);
		process_chain(right_chain);
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
		if (splitfanout) {
			string cmd = "splitfanout t:$and t:$or t:$xor t:$add t:$mul";
			Pass::call(design, cmd);
		}

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
			log("Converted %d %s cells into %s trees.\n", cell_count[cell_type], log_id(cell_type), log_id(cell_type.str() + "_tree"));
	}
} OptBalanceTreePass;

PRIVATE_NAMESPACE_END
