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
#include <functional>
#include <queue>
#include <ranges>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// An "object" is a cell or a wire.
// An object is "private" if its name starts with a '$'.
//
// The "autoname" pass renames private objects based on public object names,
// with suffixes added to show the relationship to the public objects.
// The pass chooses the "best" names based on minimizing their "cost".

// The cost of a new name for a private object is the cost along a path
// to a publicly named object.
struct cost {
	// score is a property of one "edge", not of the entire path.
	// 0 if the neighbour drives the object, and the wire's fanout otherwise
	unsigned int score = UINT_MAX;
	// New name length
	size_t length = SIZE_MAX;
	// Earlier discovered connection wins
	int edge_pos = 0;

	auto operator<=>(const cost &) const = default;
};

// Endpoints of an "edge" are always a cell index and a wire index. Goofy, I know.
// SigSig connections (module->connections()) don't count
// as neighbors. This means that the equivalent of `assign $w1 = \w2;` won't lead
// to $w1 being renamed.
struct Edge {
	// Cell port name at which the wire connects to the cell
	IdString port;
	int cell;
	int wire;
	bool cell_is_output;
	unsigned int score;
	// Edge's position in the edge list
	int pos_in_cell;
	int pos_in_wire;
};

// decide() finds shortest names for every object reachable from a public name,
// cheapest-first. It doesn't apply the renames to the objects yet.
//
// commit() then renames in decide() order, which is topological, so a source
// neighbour always already carries its final uniquify()d name.

// A selected cell or wire
struct node {
	// Exactly one of cell/wire is set
	Cell *cell = nullptr;
	Wire *wire = nullptr;
	vector<Edge> edges;
	// Ignores module->connections() just as the rest of the code
	unsigned int fanout = 0;
	bool is_public = false;
	bool renameable = false;
	bool selected = false;

	size_t name_length = 0;
	// Node index from which we want to construct the rename
	int from_node = -1;
	// Cost for the edge from that node
	cost c;
	// Suffix to append to the name of that node
	string suffix;
	// Is this name final?
	bool decided = false;

	const IdString& name() const { return cell ? cell->name : wire->name; }
};

// Decides the order of exploring neighbors
struct queue_item {
	unsigned int score;
	size_t length;
	int index;

	auto operator<=>(const queue_item &) const = default;
};

struct ModuleAutonamer
{
	Module *module;

	// Cells in module order, then wires in the order that they're seen from cells.
	// The index doubles as the tie-break between equally good
	// proposals for different nodes
	vector<node> nodes;
	vector<int> decided;
	std::priority_queue<queue_item, std::vector<queue_item>, std::greater<>> queue;
	int renamed = 0;

	ModuleAutonamer(Module *module) : module(module) { build_adjacency(); }

	void build_adjacency()
	{
		vector<Cell*> cells(module->cells().begin(), module->cells().end());
		// Arbitrary. Kinda just for passing tests without modifying them
		for (auto cell : cells | std::views::reverse)
			nodes.emplace_back().cell = cell;
		int ncells = GetSize(nodes);

		idict<Wire*> wire_ids;

		for (int ci = 0; ci < ncells; ci++) {
			Cell *cell = nodes[ci].cell;
			for (auto &conn : cell->connections()) {
				bool cell_is_output = cell->output(conn.first);
				pool<Wire*> seen_in_this_port;
				for (auto bit : conn.second) {
					if (bit.wire == nullptr)
						continue;
					int wi = ncells + wire_ids(bit.wire);
					if (wi == GetSize(nodes))
						nodes.emplace_back().wire = bit.wire;
					nodes[wi].fanout++;
					if (!seen_in_this_port.insert(bit.wire).second)
						continue;
					Edge edge{
						.port = conn.first,
						.cell = ci,
						.wire = wi,
						.cell_is_output = cell_is_output,
						.score = 0, // no fanouts are final yet
						.pos_in_cell = GetSize(nodes[ci].edges),
						.pos_in_wire = GetSize(nodes[wi].edges),
					};
					nodes[ci].edges.push_back(edge);
					nodes[wi].edges.push_back(edge);
				}
			}
		}

		// Resolve selection before renaming
		for (auto &nd : nodes) {
			IdString name = nd.name();
			nd.selected = nd.cell ? module->selected(nd.cell) : module->selected(nd.wire);
			nd.is_public = (name[0] != '$');
			nd.renameable = !nd.is_public && (nd.cell || nd.wire->port_id == 0);
			if (nd.is_public)
				nd.name_length = name.str().size();
		}

		// Only possible once every fanout is known
		for (auto &nd : nodes)
			for (auto &edge : nd.edges)
				edge.score = edge.cell_is_output ? 0 : nodes[edge.wire].fanout;
	}

	void offer(int from, int to, const Edge &edge, int edge_pos)
	{
		node &nd = nodes[to];
		if (!nd.renameable || nd.decided)
			return;
		string suffix = nd.cell
			? stringf("_%s_%s", nd.cell->type.unescape(), edge.port.unescape())
			: stringf("_%s", edge.port.unescape());
		cost c{edge.score, nodes[from].name_length + suffix.length(), edge_pos};
		if (c >= nd.c)
			return;
		nd.c = c;
		nd.from_node = from;
		nd.name_length = c.length;
		nd.suffix = std::move(suffix);
		queue.push(queue_item{c.score, c.length, to});
	}

	// Expand a public (or newly decided) node. The name it lends
	// is already settled and the neighbour can keep what offer() built
	void expand(int n)
	{
		const node &nd = nodes[n];
		for (auto &edge : nd.edges)
			if (nd.cell)
				offer(n, edge.wire, edge, edge.pos_in_wire);
			else
				offer(n, edge.cell, edge, edge.pos_in_cell);
	}

	void decide()
	{
		for (int n = 0; n < GetSize(nodes); n++)
			if (nodes[n].is_public)
				expand(n);

		while (!queue.empty()) {
			int n = queue.top().index;
			queue.pop();
			if (nodes[n].decided)
				continue;
			nodes[n].decided = true;
			decided.push_back(n);
			expand(n);
		}
	}

	void append_name(int n, string &out)
	{
		const node &nd = nodes[n];
		if (nd.is_public || nd.selected)
			return nd.name().append_to(&out);
		append_name(nd.from_node, out);
		out += nd.suffix;
	}

	void commit(int n)
	{
		node &nd = nodes[n];
		if (!nd.selected)
			return;
		string full;
		full.reserve(nd.name_length);
		append_name(nd.from_node, full);
		full += nd.suffix;
		IdString name = module->uniquify(IdString(full));
		if (nd.cell) {
			log_debug("Rename cell %s in %s to %s.\n", nd.cell, module, name.unescape());
			module->rename(nd.cell, name);
		} else {
			log_debug("Rename wire %s in %s to %s.\n", nd.wire, module, name.unescape());
			module->rename(nd.wire, name);
		}
		renamed++;
	}

	void run()
	{
		decide();
		for (int n : decided)
			commit(n);
		if (renamed > 0)
			log("Renamed %d objects in module %s.\n", renamed, module);
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
