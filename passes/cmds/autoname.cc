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

// -----------------------------------------------------------------------
// Algorithm
//
// A cell or wire with a private ($-prefixed) name becomes nameable once it
// has at least one directly connected neighbour with a public name: the
// proposed name is that neighbour's name plus a short suffix (cell/port
// derived). Renaming an object can make ITS neighbours nameable in turn,
// so public names propagate outward one hop per round. Each round, every
// currently-nameable object within 2x the round's best score is renamed
// together (this batches together names that are equally good, instead of
// only ever renaming the single best one).
//
// Naively, each round would recompute every $-named object's proposal by
// walking every selected cell/wire from scratch. Since the number of
// rounds equals the propagation depth through the design's connectivity
// graph, that costs O(rounds x module size) -- on a design with long
// dependency chains, rounds scales with module size too, so this becomes
// O(module size^2).
//
// Instead, ModuleAutonamer keeps a worklist (pending_cells/pending_wires)
// of only the objects that currently have a proposal at all. Renaming an
// object cannot change any proposal other than its direct neighbours', so
// after each round only those neighbours are recomputed. This produces the
// identical sequence of renames as the naive full rescan, without ever
// looking at objects that were not affected by the round.
// -----------------------------------------------------------------------

#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct name_proposal {
	string name;
	// Smaller is better. Default is the worst possible score, so any real
	// proposal wins a min-comparison against a default-constructed one.
	unsigned int score;
	name_proposal() : name(""), score(-1) { }
	name_proposal(string name, unsigned int score) : name(name), score(score) { }
	bool operator<(const name_proposal &other) const {
		if (score != other.score)
			return score < other.score;
		else
			return name.length() < other.name.length();
	}
};

// A cell's `port` connects to `wire` (in at least one bit). `cell_is_output`
// says whether `port` is an output of the cell, i.e. whether `wire` is
// driven by `cell` on that port.
struct Edge {
	Cell *cell;
	IdString port;
	Wire *wire;
	bool cell_is_output;
};

// Runs the propagation described above for a single module.
struct ModuleAutonamer
{
	Module *module;

	// How many (selected) connections reference each wire. Used to prefer
	// low-fanout wires as naming sources, and to make output ports "free"
	// (score 0) since a cell's output name is the more natural choice.
	dict<Wire*, unsigned int> wire_score;

	// Adjacency, built once up front: which edges touch each cell/wire.
	// A cell/wire's proposal only ever depends on its own edges, so this
	// is all recompute() ever needs to look at -- it never walks the rest
	// of the module.
	dict<Cell*, vector<Edge>> edges_of_cell;
	dict<Wire*, vector<Edge>> edges_of_wire;

	// The current best proposal for every $-named object that is
	// currently reachable from a public name at all. Objects with no path
	// to any public name (yet) simply never appear here, rather than being
	// tracked as "still unresolved".
	dict<Cell*, name_proposal> pending_cells;
	dict<Wire*, name_proposal> pending_wires;

	int renamed = 0;
	int rounds = 0;

	ModuleAutonamer(Module *module) : module(module)
	{
		build_adjacency();
		seed();
	}

	static bool is_private(IdString name) { return name[0] == '$'; }

	// Module ports are never renamed, even if $-named; cells have no
	// equivalent exemption.
	static bool exempt_from_rename(Wire *wire) { return wire->port_id != 0; }
	static bool exempt_from_rename(Cell *) { return false; }

	void build_adjacency()
	{
		for (auto cell : module->selected_cells())
			for (auto &conn : cell->connections()) {
				bool cell_is_output = cell->output(conn.first);
				pool<Wire*> seen_in_this_port;
				for (auto bit : conn.second) {
					if (bit.wire == nullptr)
						continue;
					// Scored per bit (a wire used twice in one connection
					// counts twice), but only one Edge per distinct wire a
					// port touches -- a wide port entirely wired to a
					// single bus does not need one edge per bit.
					wire_score[bit.wire]++;
					if (!seen_in_this_port.insert(bit.wire).second)
						continue;
					Edge edge{cell, conn.first, bit.wire, cell_is_output};
					edges_of_cell[cell].push_back(edge);
					edges_of_wire[bit.wire].push_back(edge);
				}
			}
	}

	// Best current proposal for a $-named cell, from its public-named
	// neighbour wires (bounded by the cell's arity, not module size).
	bool recompute(Cell *cell, name_proposal &out)
	{
		bool found = false;
		for (auto &edge : edges_of_cell.at(cell)) {
			if (is_private(edge.wire->name))
				continue; // only a *public* neighbour can lend us a name
			name_proposal proposed(
				edge.wire->name.str() + stringf("_%s_%s", cell->type.unescape(), edge.port.unescape()),
				edge.cell_is_output ? 0 : wire_score.at(edge.wire)
			);
			if (!found || proposed < out) {
				out = proposed;
				found = true;
			}
		}
		return found;
	}

	// Best current proposal for a $-named, non-port wire, from its
	// public-named neighbour cells (bounded by the wire's fanout, not
	// module size).
	bool recompute(Wire *wire, name_proposal &out)
	{
		bool found = false;
		for (auto &edge : edges_of_wire.at(wire)) {
			Cell *cell = edge.cell;
			if (is_private(cell->name))
				continue; // still $-named itself, cannot lend a name yet
			// module->selected() is re-checked here, not just assumed from
			// the initial build_adjacency() scan, because a cell renamed
			// earlier in this same run can fall out of a name/type-based
			// selection (e.g. "autoname t:$or"): Module::selected() looks
			// the cell up by its *current* name, so renaming it can make
			// an otherwise-matching cell invisible to that selection. A
			// naive full-rescan implementation calls selected_cells()
			// fresh every round and so naturally observes the same
			// drop-out; this recheck reproduces that without rescanning.
			if (!module->selected(cell))
				continue;
			name_proposal proposed(
				cell->name.str() + stringf("_%s", edge.port.unescape()),
				edge.cell_is_output ? 0 : wire_score.at(wire)
			);
			if (!found || proposed < out) {
				out = proposed;
				found = true;
			}
		}
		return found;
	}

	template<typename T>
	static pool<T*> private_candidates(const dict<T*, vector<Edge>> &edges_of)
	{
		pool<T*> result;
		for (auto &it : edges_of)
			if (is_private(it.first->name) && !exempt_from_rename(it.first))
				result.insert(it.first);
		return result;
	}

	void seed()
	{
		refresh_pending(pending_cells, private_candidates(edges_of_cell));
		refresh_pending(pending_wires, private_candidates(edges_of_wire));
	}

	template<typename T>
	static void update_best(const dict<T*, name_proposal> &pending, name_proposal &best)
	{
		for (auto &it : pending)
			if (it.second < best)
				best = it.second;
	}

	name_proposal best_pending() const
	{
		name_proposal best;
		update_best(pending_cells, best);
		update_best(pending_wires, best);
		return best;
	}

	static const char *kind(Cell *) { return "cell"; }
	static const char *kind(Wire *) { return "wire"; }

	template<typename T>
	IdString commit(T *obj, const name_proposal &p)
	{
		IdString n = module->uniquify(IdString(p.name));
		log_debug("Rename %s %s in %s to %s.\n", kind(obj), obj, module, n.unescape());
		module->rename(obj, n);
		return n;
	}

	// Commit every proposal within `cutoff`, cell or wire alike.
	template<typename T>
	pool<T*> commit_all(dict<T*, name_proposal> &pending, const name_proposal &cutoff)
	{
		pool<T*> committed;
		for (auto &it : pending)
			if (!(cutoff < it.second)) {
				commit(it.first, it.second);
				committed.insert(it.first);
				renamed++;
			}
		return committed;
	}

	// Drop the just-committed T objects from `pending` (they're done), and
	// collect their direct neighbours of type U -- the only ones whose
	// proposal a commit can possibly have changed.
	template<typename T, typename U>
	pool<U*> neighbors_to_recompute(dict<T*, name_proposal> &pending, const pool<T*> &committed,
	                                 dict<T*, vector<Edge>> &edges_of, U* Edge::*neighbor)
	{
		pool<U*> to_recompute;
		for (auto obj : committed) {
			pending.erase(obj);
			for (auto &edge : edges_of.at(obj)) {
				U *n = edge.*neighbor;
				if (is_private(n->name) && !exempt_from_rename(n))
					to_recompute.insert(n);
			}
		}
		return to_recompute;
	}

	// Recompute a proposal for exactly the given objects, cell or wire alike.
	template<typename T>
	void refresh_pending(dict<T*, name_proposal> &pending, const pool<T*> &to_recompute)
	{
		for (auto obj : to_recompute) {
			name_proposal p;
			if (recompute(obj, p))
				pending[obj] = p;
		}
	}

	// One round: rename everything within 2x of this round's best score,
	// then recompute proposals for their direct neighbours only.
	void step()
	{
		rounds++;

		// Compare against double the best score for this round's cutoff,
		// so we don't pre-empt a future round's batch.
		name_proposal cutoff = best_pending();
		cutoff.score *= 2;

		auto committed_cells = commit_all(pending_cells, cutoff);
		auto committed_wires = commit_all(pending_wires, cutoff);

		auto wires_to_recompute = neighbors_to_recompute(pending_cells, committed_cells, edges_of_cell, &Edge::wire);
		auto cells_to_recompute = neighbors_to_recompute(pending_wires, committed_wires, edges_of_wire, &Edge::cell);

		refresh_pending(pending_cells, cells_to_recompute);
		refresh_pending(pending_wires, wires_to_recompute);
	}

	void run()
	{
		while (!pending_cells.empty() || !pending_wires.empty())
			step();
		if (renamed > 0)
			log("Renamed %d objects in module %s (%d iterations).\n", renamed, module, rounds);
	}
};

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
			ModuleAutonamer(module).run();
	}
} AutonamePass;

PRIVATE_NAMESPACE_END
