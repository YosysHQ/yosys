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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

typedef struct name_proposal {
	string name;
	unsigned int score;
	name_proposal() : name(""), score(-1) { }
	name_proposal(string name, unsigned int score) : name(name), score(score) { }
	bool operator<(const name_proposal &other) const {
		if (score != other.score)
			return score < other.score;
		else
			return name.length() < other.name.length();
	}
} name_proposal;

// Recompute the current best name proposal for a single $-named cell, using
// only that cell's own connections (bounded by its arity, not module size).
// Mirrors the per-cell inner loop of the original single-pass algorithm.
bool recompute_cell_proposal(Cell *cell, const dict<Wire*, unsigned int> &wire_score, name_proposal &out)
{
	bool found = false;
	for (auto &conn : cell->connections()) {
		string suffix;
		for (auto bit : conn.second)
			if (bit.wire != nullptr && bit.wire->name[0] != '$') {
				if (suffix.empty())
					suffix = stringf("_%s_%s", cell->type.unescape(), conn.first.unescape());
				name_proposal proposed_name(
					bit.wire->name.str() + suffix,
					cell->output(conn.first) ? 0 : wire_score.at(bit.wire)
				);
				if (!found || proposed_name < out) {
					out = proposed_name;
					found = true;
				}
			}
	}
	return found;
}

// Recompute the current best name proposal for a single $-named, non-port
// wire, using only the (public-named) cells connected to it. Bounded by the
// wire's fanout, not module size.
//
// module->selected(cell) is re-checked here (not just cached from the initial
// module->selected_cells() scan) because a cell renamed earlier in this same
// autoname invocation can fall out of a name/type-based selection (e.g.
// "t:$or") -- Module::selected() looks the cell up by its *current* name, so
// a rename can make an otherwise-matching cell invisible to it. The original
// full-rescan algorithm calls module->selected_cells() fresh every round and
// so naturally observes the same drop-out; this targeted recheck reproduces
// it without having to rescan the whole module.
bool recompute_wire_proposal(Module *module, Wire *wire, const pool<Cell*> &touching_cells, const dict<Wire*, unsigned int> &wire_score, name_proposal &out)
{
	bool found = false;
	for (auto cell : touching_cells) {
		if (cell->name[0] == '$' || !module->selected(cell))
			continue;
		for (auto &conn : cell->connections()) {
			bool touches = false;
			for (auto bit : conn.second)
				if (bit.wire == wire) {
					touches = true;
					break;
				}
			if (!touches)
				continue;
			name_proposal proposed_name(
				cell->name.str() + stringf("_%s", conn.first.unescape()),
				cell->output(conn.first) ? 0 : wire_score.at(wire)
			);
			if (!found || proposed_name < out) {
				out = proposed_name;
				found = true;
			}
		}
	}
	return found;
}

struct AutonamePass : public Pass {
	AutonamePass() : Pass("autoname", "automatically assign names to objects") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    autoname [selection]\n");
		log("\n");
		log("Assign auto-generated public names to objects with private names (the ones\n");
		log("with $-prefix).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-foo") {
			// 	foo = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		log_header(design, "Executing AUTONAME pass.\n");

		for (auto module : design->selected_modules())
		{
			// wire_score, and the wire<->cell adjacency needed to know which
			// objects to re-examine when a neighbor gets renamed, are each
			// computed once up front (same complexity as a single pass of
			// the original algorithm's inner loop).
			dict<Wire*, unsigned int> wire_score;
			dict<Wire*, pool<Cell*>> wire_users;
			dict<Cell*, pool<Wire*>> cell_wires;

			for (auto cell : module->selected_cells())
				for (auto &conn : cell->connections())
					for (auto bit : conn.second)
						if (bit.wire != nullptr) {
							wire_score[bit.wire]++;
							wire_users[bit.wire].insert(cell);
							cell_wires[cell].insert(bit.wire);
						}

			// pending_cells/pending_wires hold the *current* best proposal
			// for every $-named object that is currently reachable from a
			// public name at all (objects with no path to any public name
			// never enter these maps, unlike a naive "still unresolved"
			// worklist would). This persists across rounds instead of being
			// rebuilt via a full module rescan every round -- the original
			// algorithm recomputes every object's proposal every round, but
			// an object's proposal only ever changes when a directly
			// connected neighbor is renamed, so incrementally maintaining it
			// here yields the identical fixed point (same round-by-round
			// "accept everything within 2x of this round's best" commit
			// decisions) without the O(iterations x module size) rescan.
			dict<Cell*, name_proposal> pending_cells;
			dict<Wire*, name_proposal> pending_wires;

			for (auto cell : module->selected_cells()) {
				if (cell->name[0] != '$')
					continue;
				name_proposal p;
				if (recompute_cell_proposal(cell, wire_score, p))
					pending_cells[cell] = p;
			}
			for (auto &it : wire_users) {
				Wire *wire = it.first;
				if (wire->name[0] != '$' || wire->port_id)
					continue;
				name_proposal p;
				if (recompute_wire_proposal(module, wire, it.second, wire_score, p))
					pending_wires[wire] = p;
			}

			int count = 0, iter = 0;
			while (!pending_cells.empty() || !pending_wires.empty()) {
				iter++;

				// compare against double best score for following comparisons
				// so we don't pre-empt a future iteration
				name_proposal best_name;
				for (auto &it : pending_cells)
					if (it.second < best_name)
						best_name = it.second;
				for (auto &it : pending_wires)
					if (it.second < best_name)
						best_name = it.second;
				best_name.score *= 2;

				pool<Cell*> committed_cells;
				pool<Wire*> committed_wires;

				for (auto &it : pending_cells)
					if (!(best_name < it.second)) {
						IdString n = module->uniquify(IdString(it.second.name));
						log_debug("Rename cell %s in %s to %s.\n", it.first, module, n.unescape());
						module->rename(it.first, n);
						committed_cells.insert(it.first);
						count++;
					}

				for (auto &it : pending_wires)
					if (!(best_name < it.second)) {
						IdString n = module->uniquify(IdString(it.second.name));
						log_debug("Rename wire %s in %s to %s.\n", it.first, module, n.unescape());
						module->rename(it.first, n);
						committed_wires.insert(it.first);
						count++;
					}

				// Committing a cell/wire can only change the reachability of
				// its direct neighbors, so only those need their proposal
				// recomputed for the next round.
				pool<Cell*> cells_to_recompute;
				pool<Wire*> wires_to_recompute;

				for (auto cell : committed_cells) {
					pending_cells.erase(cell);
					if (cell_wires.count(cell))
						for (auto wire : cell_wires.at(cell))
							if (wire->name[0] == '$' && !wire->port_id)
								wires_to_recompute.insert(wire);
				}
				for (auto wire : committed_wires) {
					pending_wires.erase(wire);
					if (wire_users.count(wire))
						for (auto cell : wire_users.at(wire))
							if (cell->name[0] == '$')
								cells_to_recompute.insert(cell);
				}

				for (auto cell : cells_to_recompute) {
					name_proposal p;
					if (recompute_cell_proposal(cell, wire_score, p))
						pending_cells[cell] = p;
				}
				for (auto wire : wires_to_recompute) {
					name_proposal p;
					if (recompute_wire_proposal(module, wire, wire_users.at(wire), wire_score, p))
						pending_wires[wire] = p;
				}
			}
			if (count > 0)
				log("Renamed %d objects in module %s (%d iterations).\n", count, module, iter);
		}
	}
} AutonamePass;

PRIVATE_NAMESPACE_END
