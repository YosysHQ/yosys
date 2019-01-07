/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2018  whitequark <whitequark@whitequark.org>
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

// [[CITE]]
// Jason Cong; Yuzheng Ding, "An Optimal Technology Mapping Algorithm for Delay Optimization in Lookup-Table Based FPGA Designs,"
// Computer-Aided Design of Integrated Circuits and Systems, IEEE Transactions on, Vol. 13, pp. 1-12, Jan. 1994.
// doi: 10.1109/43.273754

// Required reading material:
//
// Min-cut max-flow theorem:
//   https://www.coursera.org/lecture/algorithms-part2/maxflow-mincut-theorem-beb9G
// FlowMap paper:
//   http://cadlab.cs.ucla.edu/~cong/papers/iccad92.pdf   (short version)
//   https://limsk.ece.gatech.edu/book/papers/flowmap.pdf (long version)

// Notes on implementation:
//
// 1. In the paper, the nodes are logic elements (analogous to Yosys cells) and edges are wires. However, in our implementation, we use
// an inverted approach: the nodes are Yosys wire bits, and the edges are derived from (but aren't represented by) Yosys cells.
// This may seem counterintuitive. Three observations may help understanding this. First, for a cell with a 1-bit Y output that is
// the sole driver of its output net (which is the typical case), these representations are equivalent, because there is an exact
// correspondence between cells and output wires. Second, in the paper, primary inputs (analogous to Yosys cell or module ports) are
// nodes, and in Yosys, inputs are wires; our approach allows a direct mapping from both primary inputs and 1-output logic elements to
// flow graph nodes. Third, Yosys cells may have multiple outputs or multi-bit outputs, and by using Yosys wire bits as flow graph nodes,
// such cells are supported without any additional effort; any Yosys cell with n output wire bits ends up being split into n flow graph
// nodes.
//
// 2. The paper introduces three networks: Nt, Nt', and Nt''. The network Nt is directly represented by a subgraph of RTLIL graph,
// which is parsed into an equivalent but easier to traverse representation in FlowmapWorker. The network Nt' is built explicitly
// from a subgraph of Nt, and uses a similar representation in FlowGraph. The network Nt'' is implicit in FlowGraph, which is possible
// because of the following observation: each Nt' node corresponds to an Nt'' edge of capacity 1, and each Nt' edge corresponds to
// an Nt'' edge of capacity ∞. Therefore, we only need to explicitly record flow for Nt' edges and through Nt' nodes.
//
// 3. The paper ambiguously states: "Moreover, we can find such a cut (X′′, X̅′′) by performing a depth first search starting at the source s,
// and including in X′′ all the nodes which are reachable from s." This actually refers to a specific kind of search, mincut computation.
// Mincut computation involves computing the set of nodes reachable from s by an undirected path with no full (i.e. zero capacity) forward
// edges or empty (i.e. no flow) backward edges. In addition, the depth first search is required to compute a max-volume max-flow min-cut
// specifically, because a max-flow min-cut is not, in general, unique.

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/modtools.h"
#include "kernel/consteval.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct GraphStyle
{
	string label;
	string color, fillcolor;

	GraphStyle(string label = "", string color = "black", string fillcolor = "") :
		label(label), color(color), fillcolor(fillcolor) {}
};

static string dot_escape(string value)
{
	std::string escaped;
	for (char c : value) {
		if (c == '\n')
		{
			escaped += "\\n";
			continue;
		}
		if (c == '\\' || c == '"')
			escaped += "\\";
		escaped += c;
	}
	return escaped;
}

static void dump_dot_graph(string filename,
                           pool<RTLIL::SigBit> nodes, dict<RTLIL::SigBit, pool<RTLIL::SigBit>> edges,
                           pool<RTLIL::SigBit> inputs, pool<RTLIL::SigBit> outputs,
                           std::function<GraphStyle(RTLIL::SigBit)> node_style =
                           		[](RTLIL::SigBit) { return GraphStyle{}; },
                           std::function<GraphStyle(RTLIL::SigBit, RTLIL::SigBit)> edge_style =
                           		[](RTLIL::SigBit, RTLIL::SigBit) { return GraphStyle{}; },
                           string name = "")
{
	FILE *f = fopen(filename.c_str(), "w");
	fprintf(f, "digraph \"%s\" {\n", name.c_str());
	fprintf(f, "  rankdir=\"TB\";\n");

	dict<RTLIL::SigBit, int> ids;
	for (auto node : nodes)
	{
		ids[node] = ids.size();

		string shape = "ellipse";
		if (inputs[node])
			shape = "box";
		if (outputs[node])
			shape = "octagon";
		auto prop = node_style(node);
		string style = "";
		if (!prop.fillcolor.empty())
			style = "filled";
		fprintf(f, "  n%d [ shape=%s, fontname=\"Monospace\", label=\"%s\", color=\"%s\", fillcolor=\"%s\", style=\"%s\" ];\n",
		        ids[node], shape.c_str(), dot_escape(prop.label.c_str()).c_str(), prop.color.c_str(), prop.fillcolor.c_str(), style.c_str());
	}

	fprintf(f, "  { rank=\"source\"; ");
	for (auto input : inputs)
		if (nodes[input])
			fprintf(f, "n%d; ", ids[input]);
	fprintf(f, "}\n");

	fprintf(f, "  { rank=\"sink\"; ");
	for (auto output : outputs)
		if (nodes[output])
			fprintf(f, "n%d; ", ids[output]);
	fprintf(f, "}\n");

	for (auto edge : edges)
	{
		auto source = edge.first;
		for (auto sink : edge.second) {
			if (nodes[source] && nodes[sink])
			{
				auto prop = edge_style(source, sink);
				fprintf(f, "  n%d -> n%d [ label=\"%s\", color=\"%s\", fillcolor=\"%s\" ];\n",
				        ids[source], ids[sink], dot_escape(prop.label.c_str()).c_str(), prop.color.c_str(), prop.fillcolor.c_str());
			}
		}
	}

	fprintf(f, "}\n");
	fclose(f);
}

struct FlowGraph
{
	const RTLIL::SigBit source;
	RTLIL::SigBit sink;
	pool<RTLIL::SigBit> nodes = {source};
	dict<RTLIL::SigBit, pool<RTLIL::SigBit>> edges_fw, edges_bw;

	const int MAX_NODE_FLOW = 1;
	dict<RTLIL::SigBit, int> node_flow;
	dict<pair<RTLIL::SigBit, RTLIL::SigBit>, int> edge_flow;

	dict<RTLIL::SigBit, pool<RTLIL::SigBit>> collapsed;

	void dump_dot_graph(string filename)
	{
		auto node_style = [&](RTLIL::SigBit node) {
			string label = (node == source) ? "(source)" : log_signal(node);
			for (auto collapsed_node : collapsed[node])
				label += stringf(" %s", log_signal(collapsed_node));
			int flow = node_flow[node];
			if (node != source && node != sink)
				label += stringf("\n%d/%d", flow, MAX_NODE_FLOW);
			else
				label += stringf("\n%d/∞", flow);
			return GraphStyle{label, flow < MAX_NODE_FLOW ? "green" : "black"};
		};
		auto edge_style = [&](RTLIL::SigBit source, RTLIL::SigBit sink) {
			int flow = edge_flow[{source, sink}];
			return GraphStyle{stringf("%d/∞", flow), flow > 0 ? "blue" : "black"};
		};
		::dump_dot_graph(filename, nodes, edges_fw, {source}, {sink}, node_style, edge_style);
	}

	// Here, we are working on the Nt'' network, but our representation is the Nt' network.
	// The difference between these is that where in Nt' we have a subgraph:
	//
	//   v1 -> v2 -> v3
	//
	// in Nt'' we have a corresponding subgraph:
	//
	//   v'1b -∞-> v'2t -f-> v'2b -∞-> v'3t
	//
	// To address this, we split each node v into two nodes, v't and v'b. This representation is virtual,
	// in the sense that nodes v't and v'b are overlaid on top of the original node v, and only exist
	// in paths and worklists.

	struct NodePrime
	{
		RTLIL::SigBit node;
		bool is_bottom;

		NodePrime(RTLIL::SigBit node, bool is_bottom) :
			node(node), is_bottom(is_bottom) {}

		bool operator==(const NodePrime &other) const
		{
			return node == other.node && is_bottom == other.is_bottom;
		}
		bool operator!=(const NodePrime &other) const
		{
			return !(*this == other);
		}
		unsigned int hash() const
		{
			return hash_ops<pair<RTLIL::SigBit, int>>::hash({node, is_bottom});
		}

		static NodePrime top(RTLIL::SigBit node)
		{
			return NodePrime(node, /*is_bottom=*/false);
		}

		static NodePrime bottom(RTLIL::SigBit node)
		{
			return NodePrime(node, /*is_bottom=*/true);
		}

		NodePrime as_top() const
		{
			log_assert(is_bottom);
			return top(node);
		}

		NodePrime as_bottom() const
		{
			log_assert(!is_bottom);
			return bottom(node);
		}
	};

	bool find_augmenting_path(bool commit)
	{
		NodePrime source_prime = {source, true};
		NodePrime sink_prime = {sink, false};
		vector<NodePrime> path = {source_prime};
		pool<NodePrime> visited = {};
		bool found;
		do {
			found = false;

			auto node_prime = path.back();
			visited.insert(node_prime);

			if (!node_prime.is_bottom) // vt
			{
				if (!visited[node_prime.as_bottom()] && node_flow[node_prime.node] < MAX_NODE_FLOW)
				{
					path.push_back(node_prime.as_bottom());
					found = true;
				}
				else
				{
					for (auto node_pred : edges_bw[node_prime.node])
					{
						if (!visited[NodePrime::bottom(node_pred)] && edge_flow[{node_pred, node_prime.node}] > 0)
						{
							path.push_back(NodePrime::bottom(node_pred));
							found = true;
							break;
						}
					}
				}
			}
			else // vb
			{
				if (!visited[node_prime.as_top()] && node_flow[node_prime.node] > 0)
				{
					path.push_back(node_prime.as_top());
					found = true;
				}
				else
				{
					for (auto node_succ : edges_fw[node_prime.node])
					{
						if (!visited[NodePrime::top(node_succ)] /* && edge_flow[...] < ∞ */)
						{
							path.push_back(NodePrime::top(node_succ));
							found = true;
							break;
						}
					}
				}
			}

			if (!found && path.size() > 1)
			{
				path.pop_back();
				found = true;
			}
		} while(path.back() != sink_prime && found);

		if (commit && path.back() == sink_prime)
		{
			auto prev_prime = path.front();
			for (auto node_prime : path)
			{
				if (node_prime == source_prime)
					continue;

				log_assert(prev_prime.is_bottom ^ node_prime.is_bottom);
				if (prev_prime.node == node_prime.node)
				{
					auto node = node_prime.node;
					if (!prev_prime.is_bottom && node_prime.is_bottom)
					{
						log_assert(node_flow[node] == 0);
						node_flow[node]++;
					}
					else
					{
						log_assert(node_flow[node] != 0);
						node_flow[node]--;
					}
				}
				else
				{
					if (prev_prime.is_bottom && !node_prime.is_bottom)
					{
						log_assert(true /* edge_flow[...] < ∞ */);
						edge_flow[{prev_prime.node, node_prime.node}]++;
					}
					else
					{
						log_assert((edge_flow[{node_prime.node, prev_prime.node}] > 0));
						edge_flow[{node_prime.node, prev_prime.node}]--;
					}
				}
				prev_prime = node_prime;
			}

			node_flow[source]++;
			node_flow[sink]++;
		}
		return path.back() == sink_prime;
	}

	int maximum_flow(int order)
	{
		int flow = 0;
		while (flow < order && find_augmenting_path(/*commit=*/true))
			flow++;
		return flow + find_augmenting_path(/*commit=*/false);
	}

	pair<pool<RTLIL::SigBit>, pool<RTLIL::SigBit>> edge_cut()
	{
		pool<RTLIL::SigBit> x, xi;

		NodePrime source_prime = {source, true};
		NodePrime sink_prime = {sink, false};
		pool<NodePrime> visited;
		vector<NodePrime> worklist = {source_prime};
		while (!worklist.empty())
		{
			auto node_prime = worklist.back();
			worklist.pop_back();
			if (visited[node_prime])
				continue;
			visited.insert(node_prime);

			if (!node_prime.is_bottom)
				x.insert(node_prime.node);

			// Mincut is constructed by traversing a graph in an undirected way along forward edges that aren't full, or backward edges
			// that aren't empty.
			if (!node_prime.is_bottom) // top
			{
				if (node_flow[node_prime.node] < MAX_NODE_FLOW)
					worklist.push_back(node_prime.as_bottom());
				for (auto node_pred : edges_bw[node_prime.node])
					if (edge_flow[{node_pred, node_prime.node}] > 0)
						worklist.push_back(NodePrime::bottom(node_pred));
			}
			else // bottom
			{
				if (node_flow[node_prime.node] > 0)
					worklist.push_back(node_prime.as_top());
				for (auto node_succ : edges_fw[node_prime.node])
					if (true /* edge_flow[...] < ∞ */)
						worklist.push_back(NodePrime::top(node_succ));
			}
		}

		for (auto node : nodes)
			if (!x[node])
				xi.insert(node);

		for (auto collapsed_node : collapsed[sink])
			xi.insert(collapsed_node);

		log_assert(!x[sink] && xi[sink]);
		return {x, xi};
	}
};

struct FlowmapWorker
{
	int order;
	bool debug;

	RTLIL::Module *module;
	SigMap sigmap;
	ModIndex index;

	dict<RTLIL::SigBit, ModIndex::PortInfo> node_origins;

	pool<RTLIL::SigBit> nodes, inputs, outputs;
	dict<RTLIL::SigBit, pool<RTLIL::SigBit>> edges_fw, edges_bw;
	dict<RTLIL::SigBit, int> labels;

	pool<RTLIL::SigBit> lut_nodes;
	dict<RTLIL::SigBit, pool<RTLIL::SigBit>> lut_gates;
	dict<RTLIL::SigBit, pool<RTLIL::SigBit>> lut_edges_fw, lut_edges_bw;

	int gate_count = 0, lut_count = 0, packed_count = 0;
	int gate_area = 0, lut_area = 0;

	enum class GraphMode {
		Label,
		Cut,
	};

	void dump_dot_graph(string filename, GraphMode mode,
	                    pool<RTLIL::SigBit> subgraph_nodes = {}, dict<RTLIL::SigBit, pool<RTLIL::SigBit>> subgraph_edges = {},
	                    dict<RTLIL::SigBit, pool<RTLIL::SigBit>> collapsed = {},
	                    pair<pool<RTLIL::SigBit>, pool<RTLIL::SigBit>> cut = {})
	{
		if (subgraph_nodes.empty())
			subgraph_nodes = nodes;
		if (subgraph_edges.empty())
			subgraph_edges = edges_fw;

		auto node_style = [&](RTLIL::SigBit node) {
			string label = log_signal(node);
			for (auto collapsed_node : collapsed[node])
				if (collapsed_node != node)
					label += stringf(" %s", log_signal(collapsed_node));
			switch (mode)
			{
				case GraphMode::Label:
					if (labels[node] == -1)
					{
						label += "\nl=?";
						return GraphStyle{label};
					}
					else
					{
						label += stringf("\nl=%d", labels[node]);
						string fillcolor = stringf("/set311/%d", 1 + labels[node] % 11);
						return GraphStyle{label, "", fillcolor};
					}

				case GraphMode::Cut:
					if (cut.first[node])
						return GraphStyle{label, "blue"};
					if (cut.second[node])
						return GraphStyle{label, "red"};
					return GraphStyle{label};
			}
			return GraphStyle{label};
		};
		auto edge_style = [&](RTLIL::SigBit, RTLIL::SigBit) {
			return GraphStyle{};
		};
		::dump_dot_graph(filename, subgraph_nodes, subgraph_edges, inputs, outputs, node_style, edge_style, module->name.str());
	}

	pool<RTLIL::SigBit> find_subgraph(RTLIL::SigBit sink)
	{
		pool<RTLIL::SigBit> subgraph;
		pool<RTLIL::SigBit> worklist = {sink};
		while (!worklist.empty())
		{
			auto node = worklist.pop();
			subgraph.insert(node);
			for (auto source : edges_bw[node])
			{
				if (!subgraph[source])
					worklist.insert(source);
			}
		}
		return subgraph;
	}

	FlowGraph build_flow_graph(RTLIL::SigBit sink, int p)
	{
		FlowGraph flow_graph;
		flow_graph.sink = sink;

		pool<RTLIL::SigBit> worklist = {sink}, visited;
		while (!worklist.empty())
		{
			auto node = worklist.pop();
			visited.insert(node);

			auto collapsed_node = labels[node] == p ? sink : node;
			if (node != collapsed_node)
				flow_graph.collapsed[collapsed_node].insert(node);
			flow_graph.nodes.insert(collapsed_node);

			for (auto node_pred : edges_bw[node])
			{
				auto collapsed_node_pred = labels[node_pred] == p ? sink : node_pred;
				if (node_pred != collapsed_node_pred)
					flow_graph.collapsed[collapsed_node_pred].insert(node_pred);
				if (collapsed_node != collapsed_node_pred)
				{
					flow_graph.edges_bw[collapsed_node].insert(collapsed_node_pred);
					flow_graph.edges_fw[collapsed_node_pred].insert(collapsed_node);
				}
				if (inputs[node_pred])
				{
					flow_graph.edges_bw[collapsed_node_pred].insert(flow_graph.source);
					flow_graph.edges_fw[flow_graph.source].insert(collapsed_node_pred);
				}

				if (!visited[node_pred])
					worklist.insert(node_pred);
			}
		}
		return flow_graph;
	}

	void discover_nodes(pool<IdString> cell_types)
	{
		for (auto cell : module->selected_cells())
		{
			if (!cell_types[cell->type])
				continue;

			if (!cell->known())
				log_error("Cell %s (%s.%s) is unknown.\n", cell->type.c_str(), log_id(module), log_id(cell));

			pool<RTLIL::SigBit> fanout;
			for (auto conn : cell->connections())
			{
				if (!cell->output(conn.first)) continue;
				int offset = -1;
				for (auto bit : conn.second)
				{
					offset++;
					if (!bit.wire) continue;
					auto mapped_bit = sigmap(bit);
					if (nodes[mapped_bit])
						log_error("Multiple drivers found for wire %s.\n", log_signal(mapped_bit));
					nodes.insert(mapped_bit);
					node_origins[mapped_bit] = ModIndex::PortInfo(cell, conn.first, offset);
					fanout.insert(mapped_bit);
				}
			}

			int fanin = 0;
			for (auto conn : cell->connections())
			{
				if (!cell->input(conn.first)) continue;
				for (auto bit : sigmap(conn.second))
				{
					if (!bit.wire) continue;
					for (auto fanout_bit : fanout)
					{
						edges_fw[bit].insert(fanout_bit);
						edges_bw[fanout_bit].insert(bit);
					}
					fanin++;
				}
			}

			if (fanin > order)
				log_error("Cell %s (%s.%s) with fan-in %d cannot be mapped to a %d-LUT.\n",
				          cell->type.c_str(), log_id(module), log_id(cell), fanin, order);

			gate_count++;
			gate_area += 1 << fanin;
		}

		for (auto edge : edges_fw)
		{
			if (!nodes[edge.first])
			{
				inputs.insert(edge.first);
				nodes.insert(edge.first);
			}
		}

		for (auto node : nodes)
		{
			auto node_info = index.query(node);
			if (node_info->is_output && !inputs[node])
				outputs.insert(node);
			for (auto port : node_info->ports)
				if (!cell_types[port.cell->type] && !inputs[node])
					outputs.insert(node);
		}

		if (debug)
		{
			dump_dot_graph("flowmap-initial.dot", GraphMode::Label);
			log("Dumped initial graph to `flowmap-initial.dot`.\n");
		}
	}

	void label_nodes()
	{
		for (auto node : nodes)
			labels[node] = -1;
		for (auto input : inputs)
		{
			if (input.wire->attributes.count("\\$flowmap_level"))
				labels[input] = input.wire->attributes["\\$flowmap_level"].as_int();
			else
				labels[input] = 0;
		}

		pool<RTLIL::SigBit> worklist = nodes;
		int debug_num = 0;
		while (!worklist.empty())
		{
			auto sink = worklist.pop();
			if (labels[sink] != -1)
				continue;

			bool inputs_have_labels = true;
			for (auto sink_input : edges_bw[sink])
			{
				if (labels[sink_input] == -1)
				{
					inputs_have_labels = false;
					break;
				}
			}
			if (!inputs_have_labels)
				continue;

			if (debug)
			{
				debug_num++;
				log("Examining subgraph %d rooted in %s.\n", debug_num, log_signal(sink));
			}

			pool<RTLIL::SigBit> subgraph = find_subgraph(sink);

			int p = 1;
			for (auto subgraph_node : subgraph)
				p = max(p, labels[subgraph_node]);

			FlowGraph flow_graph = build_flow_graph(sink, p);
			int flow = flow_graph.maximum_flow(order);
			pool<RTLIL::SigBit> x, xi;
			if (flow <= order)
			{
				labels[sink] = p;
				auto cut = flow_graph.edge_cut();
				x = cut.first;
				xi = cut.second;
			}
			else
			{
				labels[sink] = p + 1;
				x = subgraph;
				x.erase(sink);
				xi.insert(sink);
			}
			lut_gates[sink] = xi;

			pool<RTLIL::SigBit> k;
			for (auto xi_node : xi)
			{
				for (auto xi_node_pred : edges_bw[xi_node])
					if (x[xi_node_pred])
						k.insert(xi_node_pred);
			}
			log_assert((int)k.size() <= order);
			lut_edges_bw[sink] = k;
			for (auto k_node : k)
				lut_edges_fw[k_node].insert(sink);

			if (debug)
			{
				log("  Maximum flow: %d. Assigned label %d.\n", flow, labels[sink]);
				dump_dot_graph(stringf("flowmap-%d-sub.dot", debug_num), GraphMode::Cut, subgraph, {}, {}, {x, xi});
				log("  Dumped subgraph to `flowmap-%d-sub.dot`.\n", debug_num);
				flow_graph.dump_dot_graph(stringf("flowmap-%d-flow.dot", debug_num));
				log("  Dumped flow graph to `flowmap-%d-flow.dot`.\n", debug_num);
				log("    LUT inputs:");
				for (auto k_node : k)
					log(" %s", log_signal(k_node));
				log(".\n");
				log("    LUT packed gates:");
				for (auto xi_node : xi)
					log(" %s", log_signal(xi_node));
				log(".\n");
			}

			for (auto sink_succ : edges_fw[sink])
				worklist.insert(sink_succ);
		}

		if (debug)
		{
			dump_dot_graph("flowmap-labeled.dot", GraphMode::Label);
			log("Dumped labeled graph to `flowmap-labeled.dot`.\n");
		}
	}

	int pack_luts()
	{
		pool<RTLIL::SigBit> worklist = outputs;
		while (!worklist.empty())
		{
			auto lut_node = worklist.pop();
			lut_nodes.insert(lut_node);
			for (auto input_node : lut_edges_bw[lut_node])
				if (!lut_nodes[input_node] && !inputs[input_node])
					worklist.insert(input_node);
		}

		int depth = 0;
		for (auto label : labels)
			depth = max(depth, label.second);
		log("Solved to %d LUTs in %d levels.\n", (int)lut_nodes.size(), depth);

		if (debug)
		{
			pool<RTLIL::SigBit> lut_and_input_nodes;
			lut_and_input_nodes.insert(lut_nodes.begin(), lut_nodes.end());
			lut_and_input_nodes.insert(inputs.begin(), inputs.end());
			dump_dot_graph("flowmap-packed.dot", GraphMode::Label, lut_and_input_nodes, lut_edges_fw, lut_gates);
			log("Dumped packed graph to `flowmap-packed.dot`.\n");
		}

		return depth;
	}

	void map_cells(int minlut)
	{
		ConstEval ce(module);
		for (auto input_node : inputs)
			ce.stop(input_node);

		pool<RTLIL::SigBit> mapped_nodes;
		for (auto node : lut_nodes)
		{
			if (node_origins.count(node))
			{
				auto origin = node_origins[node];
				if (origin.cell->getPort(origin.port).size() == 1)
					log("Mapping %s.%s.%s (%s).\n",
					    log_id(module), log_id(origin.cell), origin.port.c_str(), log_signal(node));
				else
					log("Mapping %s.%s.%s [%d] (%s).\n",
					    log_id(module), log_id(origin.cell), origin.port.c_str(), origin.offset, log_signal(node));
			}
			else
			{
				log("Mapping %s.%s.\n", log_id(module), log_signal(node));
			}

			for (auto gate_node : lut_gates[node])
			{
				log_assert(node_origins.count(gate_node));

				if (gate_node == node)
					continue;

				auto gate_origin = node_origins[gate_node];
				if (gate_origin.cell->getPort(gate_origin.port).size() == 1)
					log("  Packing %s.%s.%s (%s).\n",
					    log_id(module), log_id(gate_origin.cell), gate_origin.port.c_str(), log_signal(gate_node));
				else
					log("  Packing %s.%s.%s [%d] (%s).\n",
					    log_id(module), log_id(gate_origin.cell), gate_origin.port.c_str(), gate_origin.offset, log_signal(gate_node));
			}

			vector<RTLIL::SigBit> input_nodes(lut_edges_bw[node].begin(), lut_edges_bw[node].end());
			RTLIL::Const lut_table(State::Sx, max(1 << input_nodes.size(), 1 << minlut));
			for (unsigned i = 0; i < (1 << input_nodes.size()); i++)
			{
				ce.push();
				for (size_t n = 0; n < input_nodes.size(); n++)
					ce.set(input_nodes[n], ((i >> n) & 1) ? State::S1 : State::S0);

				RTLIL::SigSpec value = node, undef;
				if (!ce.eval(value, undef))
				{
					string env;
					for (auto input_node : input_nodes)
						env += stringf("  %s = %s\n", log_signal(input_node), log_signal(ce.values_map(input_node)));
					log_error("Cannot evaluate %s because %s is not defined.\nEvaluation environment:\n%s",
					          log_signal(node), log_signal(undef), env.c_str());
				}

				lut_table[i] = value.as_bool() ? State::S1 : State::S0;
				ce.pop();
			}

			RTLIL::SigSpec lut_a, lut_y = node;
			for (auto input_node : input_nodes)
				lut_a.append_bit(input_node);
			lut_a.append(RTLIL::Const(State::Sx, minlut - input_nodes.size()));

			RTLIL::Cell *lut = module->addLut(NEW_ID, lut_a, lut_y, lut_table);
			mapped_nodes.insert(node);
			for (auto gate_node : lut_gates[node])
			{
				auto gate_origin = node_origins[gate_node];
				lut->add_strpool_attribute("\\src", gate_origin.cell->get_strpool_attribute("\\src"));
				packed_count++;
			}
			lut_count++;
			lut_area += lut_table.size();

			if ((int)input_nodes.size() >= minlut)
				log("  Packed into a %d-LUT %s.%s.\n", (int)input_nodes.size(), log_id(module), log_id(lut));
			else
				log("  Packed into a %d-LUT %s.%s (implemented as %d-LUT).\n", (int)input_nodes.size(), log_id(module), log_id(lut), minlut);
		}

		for (auto node : mapped_nodes)
		{
			auto origin = node_origins[node];
			RTLIL::SigSpec driver = origin.cell->getPort(origin.port);
			driver[origin.offset] = module->addWire(NEW_ID);
			origin.cell->setPort(origin.port, driver);
		}
	}

	FlowmapWorker(int order, int minlut, pool<IdString> cell_types, bool debug, RTLIL::Module *module) :
		order(order), debug(debug), module(module), sigmap(module), index(module)
	{
		log("Labeling cells.\n");
		discover_nodes(cell_types);
		label_nodes();
		pack_luts();

		log("\n");
		log("Mapping cells.\n");
		map_cells(minlut);
	}
};

static void split(std::vector<std::string> &tokens, const std::string &text, char sep)
{
	size_t start = 0, end = 0;
	while ((end = text.find(sep, start)) != std::string::npos) {
		tokens.push_back(text.substr(start, end - start));
		start = end + 1;
	}
	tokens.push_back(text.substr(start));
}

struct FlowmapPass : public Pass {
	FlowmapPass() : Pass("flowmap", "pack LUTs with FlowMap") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    flowmap [options] [selection]\n");
		log("\n");
		log("This pass uses the FlowMap technology mapping algorithm to pack logic gates\n");
		log("into k-LUTs with optimal depth. It allows mapping any circuit elements that can\n");
		log("be evaluated with the `eval` pass, including cells with multiple output ports\n");
		log("and multi-bit input and output ports.\n");
		log("\n");
		log("    -maxlut k\n");
		log("        perform technology mapping for a k-LUT architecture. if not specified,\n");
		log("        defaults to 3.\n");
		log("\n");
		log("    -minlut n\n");
		log("        only produce n-input or larger LUTs. if not specified, defaults to 1.\n");
		log("\n");
		log("    -cells <cell>[,<cell>,...]\n");
		log("        map specified cells. if not specified, maps $_NOT_, $_AND_, $_OR_,\n");
		log("        $_XOR_ and $_MUX_, which are the outputs of the `simplemap` pass.\n");
		log("\n");
		log("    -debug\n");
		log("        dump intermediate graphs.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		int order = 3;
		int minlut = 1;
		vector<string> cells;
		bool debug = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-maxlut" && argidx + 1 < args.size())
			{
				order = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-minlut" && argidx + 1 < args.size())
			{
				minlut = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-cells" && argidx + 1 < args.size())
			{
				split(cells, args[++argidx], ',');
				continue;
			}
			if (args[argidx] == "-debug")
			{
				debug = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		pool<IdString> cell_types;
		if (!cells.empty())
		{
			for (auto &cell : cells)
				cell_types.insert(cell);
		}
		else
		{
			cell_types = {"$_NOT_", "$_AND_", "$_OR_", "$_XOR_", "$_MUX_"};
		}

		log_header(design, "Executing FLOWMAP pass (pack LUTs with FlowMap).\n");

		int gate_count = 0, lut_count = 0, packed_count = 0;
		int gate_area = 0, lut_area = 0;
		for (auto module : design->selected_modules())
		{
			FlowmapWorker worker(order, minlut, cell_types, debug, module);
			gate_count += worker.gate_count;
			lut_count += worker.lut_count;
			packed_count += worker.packed_count;
			gate_area += worker.gate_area;
			lut_area += worker.lut_area;
		}

		log("\n");
		log("Mapped %d LUTs.\n", lut_count);
		log("Packed %d cells; duplicated %d cells.\n", packed_count, packed_count - gate_count);
		log("Solution has %.1f%% area overhead.\n", (lut_area - gate_area) * 100.0 / gate_area);
	}
} FlowmapPass;

PRIVATE_NAMESPACE_END
