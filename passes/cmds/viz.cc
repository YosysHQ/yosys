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
#include "kernel/sigtools.h"

#ifndef _WIN32
#  include <dirent.h>
#endif

#ifdef __APPLE__
#  include <unistd.h>
#endif

#ifdef YOSYS_ENABLE_READLINE
#  include <readline/readline.h>
#endif

#ifdef YOSYS_ENABLE_EDITLINE
#  include <editline/readline.h>
#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct VizConfig {
	enum group_type_t {
		TYPE_G,
		TYPE_U,
		TYPE_X,
		TYPE_S
	};

	int effort = 9;
	int similar_thresh = 30;
	int small_group_thresh = 10;
	int large_group_count = 10;
	std::vector<std::pair<group_type_t, RTLIL::Selection>> groups;
};

struct GraphNode {
	int index = -1;
	bool nomerge = false;
	bool terminal = false;
	bool excluded = false;
	bool special = false;
	GraphNode *replaced = nullptr;

	GraphNode *get() {
		if (replaced == nullptr)
			return this;
		return replaced = replaced->get();
	}

	pool<IdString> names_;
	dict<int, uint8_t> tags_;
	pool<GraphNode*, hash_ptr_ops> upstream_;
	pool<GraphNode*, hash_ptr_ops> downstream_;

	pool<IdString> &names() { return get()->names_; }
	dict<int, uint8_t> &tags() { return get()->tags_; }
	pool<GraphNode*, hash_ptr_ops> &upstream() { return get()->upstream_; }
	pool<GraphNode*, hash_ptr_ops> &downstream() { return get()->downstream_; }

	uint8_t tag(int index) {
		return tags().at(index, 0);
	}

	bool tag(int index, uint8_t mask) {
		if (!mask) return false;
		uint8_t &v = tags()[index];
		if (v == (v|mask)) return false;
		v |= mask;
		return true;
	}
};

struct Graph {
	bool dirty = true;
	int phase_counter = 0;

	vector<GraphNode*> nodes;
	vector<GraphNode*> term_nodes;
	vector<GraphNode*> nonterm_nodes;
	vector<GraphNode*> replaced_nodes;

	Module *module;
	const VizConfig &config;

	// statistics and indices, updated by update()
	std::vector<int> max_group_sizes;
	double mean_group_size;
	double rms_group_size;
	int edge_count, tag_count;

	~Graph()
	{
		for (auto n : nodes) delete n;
		for (auto n : replaced_nodes) delete n;
	}

	GraphNode *node(int index)
	{
		if (index)
			return nodes[index-1]->get();
		return nullptr;
	}

	void update_nodes()
	{
		// Filter-out replaced nodes

		term_nodes.clear();
		nonterm_nodes.clear();

		for (auto n : nodes) {
			if (n->replaced)
				replaced_nodes.push_back(n);
			else if (n->terminal)
				term_nodes.push_back(n);
			else
				nonterm_nodes.push_back(n);
		}

		// Re-index the remaining nodes

		nodes.clear();

		max_group_sizes.clear();
		max_group_sizes.resize(config.large_group_count);

		mean_group_size = 0;
		rms_group_size = 0;
		edge_count = 0;

		auto update_node = [&](GraphNode *n)
		{
			nodes.push_back(n);
			n->index = GetSize(nodes);

			pool<GraphNode*, hash_ptr_ops> new_upstream;
			pool<GraphNode*, hash_ptr_ops> new_downstream;

			for (auto g : n->upstream()) {
				if (n != (g = g->get()))
					new_upstream.insert(g);
			}
			for (auto g : n->downstream()) {
				if (n != (g = g->get()))
					new_downstream.insert(g), edge_count++;
			}

			new_upstream.sort();
			new_downstream.sort();

			std::swap(n->upstream(), new_upstream);
			std::swap(n->downstream(), new_downstream);

			if (!n->terminal) {
				int t = GetSize(n->names());
				mean_group_size += t;
				rms_group_size += t*t;
				for (int i = 0; i < config.large_group_count; i++)
					if (t >= max_group_sizes[i])
						std::swap(t, max_group_sizes[i]);
			}
		};

		for (auto n : term_nodes)
			update_node(n);

		for (auto n : nonterm_nodes)
			update_node(n);

		mean_group_size /= GetSize(nonterm_nodes);
		rms_group_size = sqrt(rms_group_size / GetSize(nonterm_nodes));
	}

	void update_tags()
	{
		std::function<void(GraphNode*,int,bool)> up_down_prop_tag =
				[&](GraphNode *g, int index, bool down)
		{
			for (auto n : (down ? g->downstream_ : g->upstream_)) {
				if (n->tag(index, down ? 2 : 1)) {
					if (!n->terminal)
						up_down_prop_tag(n, index, down);
					tag_count++;
				}
			}
		};

		tag_count = 0;
		for (auto g : nodes)
			g->tags().clear();

		for (auto g : term_nodes) {
			up_down_prop_tag(g, g->index, false);
			up_down_prop_tag(g, g->index, true);
		}

		for (auto g : nodes)
			g->tags().sort();
	}

	bool update()
	{
		if (!dirty) {
			log("    Largest non-term group sizes: ");
			for (int i = 0; i < config.large_group_count; i++)
				log("%d%s", max_group_sizes[i], i+1 == config.large_group_count ? ".\n" : " ");

			// log("    Mean and Root-Mean-Square group sizes: %.1f and %.1f\n", mean_group_size, rms_group_size);

			return false;
		}

		dirty = false;
		update_nodes();
		update_tags();

		log("    Status: %d nodes (%d term and %d non-term), %d edges, and %d tags\n",
				GetSize(nodes), GetSize(term_nodes), GetSize(nonterm_nodes), edge_count, tag_count);
		return true;
	}

	void merge(GraphNode *g, GraphNode *n)
	{
		g = g->get();
		n = n->get();

		log_assert(!g->nomerge);
		log_assert(!n->nomerge);
		log_assert(g->terminal == n->terminal);

		if (g == n) return;

		for (auto v : n->names_)
			g->names_.insert(v);

		for (auto v : n->tags_)
			g->tags_[v.first] |= v.second;

		for (auto v : n->upstream_) {
			if (g != (v = v->get()))
				g->upstream_.insert(v);
		}

		for (auto v : n->downstream_) {
			if (g != (v = v->get()))
				g->downstream_.insert(v);
		}

		n->names_.clear();
		n->tags_.clear();
		n->upstream_.clear();
		n->downstream_.clear();

		dirty = true;
		n->replaced = g;
	}

	Graph(Module *module, const VizConfig &config) : module(module), config(config)
	{
		log("Running 'viz -%d' for module %s:\n", config.effort, log_id(module));
		log("  Phase %d: Construct initial graph\n", phase_counter++);

		SigMap sigmap(module);
		dict<SigBit, GraphNode*> wire_nodes;

		for (auto wire : module->selected_wires())
		{
			if (!wire->name.isPublic()) continue;
			auto g = new GraphNode;
			g->terminal = true;
			g->names().insert(wire->name);
			nodes.push_back(g);

			for (auto bit : sigmap(wire)) {
				if (!bit.wire) continue;
				auto it = wire_nodes.find(bit);
				if (it == wire_nodes.end())
					wire_nodes[bit] = g;
				else
					merge(g, it->second);
			}
		}

		pool<GraphNode*, hash_ptr_ops> excluded;

		for (auto grp : config.groups)
		{
			GraphNode *g = nullptr;

			if (!grp.second.selected_module(module->name))
				continue;

			for (auto wire : module->wires()) {
				if (!wire->name.isPublic()) continue;
				if (!grp.second.selected_member(module->name, wire->name)) continue;
				for (auto bit : sigmap(wire)) {
					auto it = wire_nodes.find(bit);
					if (it == wire_nodes.end())
						continue;
					auto n = it->second->get();
					if (n->nomerge)
						continue;
					if (grp.first == VizConfig::TYPE_G || grp.first == VizConfig::TYPE_S) {
						if (g) {
							if (!n->nomerge)
								merge(g, n);
						} else
							g = n;
					} else if (grp.first == VizConfig::TYPE_U) {
						n->nomerge = true;
					} else if (grp.first == VizConfig::TYPE_X) {
						n->nomerge = true;
						excluded.insert(n);
					} else
						log_abort();
				}
			}

			if (g) {
				if (grp.first == VizConfig::TYPE_S)
					g->special = true;
				g->nomerge = true;
			}
		}

		for (auto g : excluded)
			excluded.insert(g->get());

		dict<Cell*, GraphNode*> cell_nodes;
		dict<SigBit, pool<GraphNode*, hash_ptr_ops>> sig_users;

		for (auto cell : module->selected_cells()) {
			auto g = new GraphNode;
			cell_nodes[cell] = g;
			g->names().insert(cell->name);
			nodes.push_back(g);

			for (auto &conn : cell->connections()) {
				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second)) {
						if (!bit.wire) continue;
						auto it = wire_nodes.find(bit);
						if (it != wire_nodes.end()) {
							auto n = it->second->get();
							if (!excluded.count(n)) {
								g->upstream().insert(n);
								n->downstream().insert(g);
							}
						} else {
							sig_users[bit].insert(g);
						}
					}
				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second)) {
						if (!bit.wire) continue;
						auto it = wire_nodes.find(bit);
						if (it != wire_nodes.end()) {
							auto n = it->second->get();
							if (!excluded.count(n)) {
								g->downstream().insert(n);
								n->upstream().insert(g);
							}
						}
					}
			}
		}

		for (auto cell : module->selected_cells()) {
			auto g = cell_nodes.at(cell);

			for (auto &conn : cell->connections()) {
				if (!cell->output(conn.first)) continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire) continue;
					for (auto u : sig_users[bit]) {
						g->downstream().insert(u);
						u->upstream().insert(g);
					}
				}
			}
		}

		update();
	}

	int compare_tags(GraphNode *g, GraphNode *n, bool strict_mode)
	{
		if (GetSize(g->tags()) > GetSize(n->tags()))
			return compare_tags(n, g, strict_mode);

		if (g->tags().empty())
			return 100;

		bool gn_specials = true;
		bool g_nonspecials = false;
		bool n_nonspecials = false;

		int score = 0;
		for (auto it : g->tags()) {
			auto g_tag = it.second;
			auto n_tag = n->tag(it.first);
			log_assert(g_tag != 0);
			if (node(it.first)->special) {
				gn_specials = true;
				if (g_tag != n_tag) return 0;
			} else
				g_nonspecials = true;
			if (n_tag == 0) continue;
			if (g_tag == n_tag)
				score += 2;
			else if (!strict_mode && (g_tag + n_tag == 4))
				score += 1;
			else
				return 0;
		}
		for (auto it : n->tags()) {
			auto n_tag = it.second;
			log_assert(n_tag != 0);
			if (node(it.first)->special) {
				gn_specials = true;
				auto g_tag = g->tag(it.first);
				if (g_tag != n_tag) return 0;
			} else
				n_nonspecials = true;
		}

		if (gn_specials && (g_nonspecials != n_nonspecials))
			return 0;

		return (100*score) / GetSize(g->tags());
	}

	int phase(bool term, int effort)
	{
		log("  Phase %d: Merge %sterminal nodes with effort level %d\n", phase_counter++, term ? "" : "non-", effort);
		int start_replaced_nodes = GetSize(replaced_nodes);

		do {
			dict<int,pool<pair<int,int>>> candidates;
			auto queue = [&](GraphNode *g, GraphNode *n) -> bool {
				if (g->terminal != n->terminal)
					return false;
				if (g->nomerge || n->nomerge)
					return false;
				int sz = GetSize(g->names()) + GetSize(n->names());
				if (g->index < n->index)
					candidates[sz].insert(pair<int,int>(g->index, n->index));
				else if (g->index != n->index)
					candidates[sz].insert(pair<int,int>(n->index, g->index));
				return true;
			};

			int last_candidates_size = 0;
			const char *last_section_header = nullptr;
			auto header = [&](const char *p = nullptr) {
				if (GetSize(candidates) != last_candidates_size && last_section_header)
					log("    Found %d cadidates of type '%s'.\n",
							GetSize(candidates) - last_candidates_size, last_section_header);
				last_candidates_size = GetSize(candidates);
				last_section_header = p;
			};

			{
				header("Any nodes with identical connections");
				typedef pair<pool<GraphNode*, hash_ptr_ops>, pool<GraphNode*, hash_ptr_ops>> node_conn_t;
				dict<node_conn_t, pool<GraphNode*, hash_ptr_ops>> nodes_by_conn;
				for (auto g : term ? term_nodes : nonterm_nodes) {
					auto &entry = nodes_by_conn[node_conn_t(g->upstream(), g->downstream())];
					for (auto n : entry)
						queue(g, n);
					entry.insert(g);
				}
			}

			if (!candidates.empty() || effort < 1) goto execute;

			if (!term) {
				header("Source-Sink with identical tags");
				for (auto g : nonterm_nodes) {
					for (auto n : g->downstream()) {
						if (n->terminal) continue;
						if (g->tags() == n->tags()) queue(g, n);
					}
				}

				header("Sibblings with identical tags");
				for (auto g : nonterm_nodes) {
					auto process_conns = [&](const pool<GraphNode*, hash_ptr_ops> &stream) {
						dict<std::vector<int>, pool<GraphNode*, hash_ptr_ops>> nodes_by_tags;
						for (auto n : stream) {
							if (n->terminal) continue;
							std::vector<int> key;
							for (auto kv : n->tags())
								key.push_back(kv.first), key.push_back(kv.second);
							auto &entry = nodes_by_tags[key];
							for (auto m : entry) queue(n, m);
							entry.insert(n);
						}
					};
					process_conns(g->upstream());
					process_conns(g->downstream());
				}
			}

			if (!candidates.empty() || effort < 2) goto execute;

			if (!term) {
				header("Nodes with single fan-out and compatible tags");
				for (auto g : nonterm_nodes) {
					if (GetSize(g->downstream()) != 1) continue;
					auto n = *g->downstream().begin();
					if (!n->terminal && compare_tags(g, n, true)) queue(g, n);
				}

				header("Nodes with single fan-in and compatible tags");
				for (auto g : nonterm_nodes) {
					if (GetSize(g->upstream()) != 1) continue;
					auto n = *g->upstream().begin();
					if (!n->terminal && compare_tags(g, n, true)) queue(g, n);
				}
			}

			if (!candidates.empty() || effort < 3) goto execute;

			if (!term) {
				header("Connected nodes with similar tags (strict)");
				for (auto g : nonterm_nodes) {
					for (auto n : g->downstream())
						if (!n->terminal && compare_tags(g, n, true) > config.similar_thresh) queue(g, n);
				}
			}

			if (!candidates.empty() || effort < 4) goto execute;

			if (!term) {
				header("Sibblings with similar tags (strict)");
				for (auto g : nonterm_nodes) {
					auto process_conns = [&](const pool<GraphNode*, hash_ptr_ops> &stream) {
						std::vector<GraphNode*> nodes;
						for (auto n : stream)
							if (!n->terminal) nodes.push_back(n);
						for (int i = 0; i < GetSize(nodes); i++)
							for (int j = 0; j < i; j++)
								if (compare_tags(nodes[i], nodes[j], true) > config.similar_thresh)
									queue(nodes[i], nodes[j]);
					};
					process_conns(g->upstream());
					process_conns(g->downstream());
				}
			}

			if (!candidates.empty() || effort < 5) goto execute;

			if (!term) {
				header("Connected nodes with similar tags (non-strict)");
				for (auto g : nonterm_nodes) {
					for (auto n : g->downstream())
						if (!n->terminal && compare_tags(g, n, false) > config.similar_thresh) queue(g, n);
				}
			}

			if (!candidates.empty() || effort < 6) goto execute;

			if (!term) {
				header("Sibblings with similar tags (non-strict)");
				for (auto g : nonterm_nodes) {
					auto process_conns = [&](const pool<GraphNode*, hash_ptr_ops> &stream) {
						std::vector<GraphNode*> nodes;
						for (auto n : stream)
							if (!n->terminal) nodes.push_back(n);
						for (int i = 0; i < GetSize(nodes); i++)
							for (int j = 0; j < i; j++)
								if (compare_tags(nodes[i], nodes[j], false) > config.similar_thresh)
									queue(nodes[i], nodes[j]);
					};
					process_conns(g->upstream());
					process_conns(g->downstream());
				}
			}

			if (!candidates.empty() || effort < 7) goto execute;

			{
				header("Any nodes with identical fan-in or fan-out");
				dict<pool<GraphNode*, hash_ptr_ops>, pool<GraphNode*, hash_ptr_ops>> nodes_by_conn[2];
				for (auto g : term ? term_nodes : nonterm_nodes) {
					auto &up_entry = nodes_by_conn[0][g->upstream()];
					auto &down_entry = nodes_by_conn[1][g->downstream()];
					for (auto n : up_entry) queue(g, n);
					for (auto n : down_entry) queue(g, n);
					up_entry.insert(g);
					down_entry.insert(g);
				}
			}

			if (!candidates.empty() || effort < 8) goto execute;

			if (!term) {
				header("Connected nodes with similar tags (lax)");
				for (auto g : nonterm_nodes) {
					for (auto n : g->downstream())
						if (!n->terminal && compare_tags(g, n, false)) queue(g, n);
				}
			}

			if (!candidates.empty() || effort < 9) goto execute;

			if (!term) {
				header("Sibblings with similar tags (lax)");
				for (auto g : nonterm_nodes) {
					auto process_conns = [&](const pool<GraphNode*, hash_ptr_ops> &stream) {
						std::vector<GraphNode*> nodes;
						for (auto n : stream)
							if (!n->terminal) nodes.push_back(n);
						for (int i = 0; i < GetSize(nodes); i++)
							for (int j = 0; j < i; j++)
								if (compare_tags(nodes[i], nodes[j], false))
									queue(nodes[i], nodes[j]);
					};
					process_conns(g->upstream());
					process_conns(g->downstream());
				}
			}

		execute:
			header();
			candidates.sort();
			bool small_mode = false;
			bool medium_mode = false;
			for (auto &candidate_group : candidates) {
				for (auto &candidate : candidate_group.second) {
					auto g = node(candidate.first);
					auto n = node(candidate.second);
					if (!term) {
						int sz = GetSize(g->names()) + GetSize(n->names());
						if (sz <= config.small_group_thresh)
							small_mode = true;
						else if (small_mode && sz >= max_group_sizes.back())
							continue;
						if (sz <= max_group_sizes.front())
							medium_mode = true;
						else if (medium_mode && sz > max_group_sizes.front())
							continue;
					}
					merge(g, n);
				}
			}
			if (small_mode)
				log("    Using 'small-mode' to prevent big groups.\n");
			else if (medium_mode)
				log("    Using 'medium-mode' to prevent big groups.\n");
		} while (update());

		int merged_nodes = GetSize(replaced_nodes) - start_replaced_nodes;
		log("    Merged a total of %d nodes.\n", merged_nodes);
		return merged_nodes;
	}
};

struct VizWorker
{
	VizConfig config;
	Module *module;
	Graph graph;

	VizWorker(Module *module, const VizConfig &cfg) : config(cfg), module(module), graph(module, config)
	{
		for (int effort = 0; effort <= config.effort; effort++) {
			bool first = true;
			while (1) {
				if (!graph.phase(false, effort) && !first) break;
				if (!graph.phase(true, effort)) break;
				first = false;
			}
			log("  %s: %d nodes (%d term and %d non-term), %d edges, and %d tags\n",
					effort == config.effort ? "Final" : "Status", GetSize(graph.nodes),
					GetSize(graph.term_nodes), GetSize(graph.nonterm_nodes),
					graph.edge_count, graph.tag_count);
		}
	}

	void update_attrs()
	{
		IdString vg_id("\\vg");
		for (auto c : module->cells())
			c->attributes.erase(vg_id);
		for (auto g : graph.nodes) {
			for (auto name : g->names()) {
				auto w = module->wire(name);
				auto c = module->cell(name);
				if (w) w->attributes[vg_id] = g->index;
				if (c) c->attributes[vg_id] = g->index;
			}
		}
	}

	void write_dot(FILE *f)
	{
		fprintf(f, "digraph \"%s\" {\n", log_id(module));
		fprintf(f, "  rankdir = LR;\n");

		dict<GraphNode*, std::vector<std::vector<std::string>>, hash_ptr_ops> extra_lines;
		dict<GraphNode*, GraphNode*, hash_ptr_ops> bypass_nodes;
		pool<GraphNode*, hash_ptr_ops> bypass_candidates;

		auto bypass = [&](GraphNode *g, GraphNode *n) {
			log_assert(g->terminal);
			log_assert(!n->terminal);
			bypass_nodes[g] = n;

			auto &buffer = extra_lines[n];
			buffer.emplace_back();

			for (auto name : g->names())
				buffer.back().push_back(log_id(name));

			std::sort(buffer.back().begin(), buffer.back().end());
			std::sort(buffer.begin(), buffer.end());
		};

		for (auto g : graph.nonterm_nodes) {
			for (auto n : g->downstream())
				if (!n->terminal) goto not_a_candidate;
			bypass_candidates.insert(g);
		not_a_candidate:;
		}

		for (auto g : graph.term_nodes)
		{
			if (g->special || bypass_nodes.count(g)) continue;
			if (GetSize(g->upstream()) != 1) continue;
			if (!g->downstream().empty() && g->downstream() != g->upstream()) continue;

			auto n = *(g->upstream().begin());
			if (n->terminal || !bypass_candidates.count(n)) continue;

			bypass(g, n);
		}

		for (auto g : graph.term_nodes)
		{
			if (g->special || bypass_nodes.count(g)) continue;
			if (GetSize(g->upstream()) != 1) continue;

			auto n = *(g->upstream().begin());
			if (n->terminal || !bypass_candidates.count(n)) continue;

			if (GetSize(n->downstream()) != 1) continue;
			if (extra_lines.count(n)) continue;

			bypass(g, n);
		}

		for (auto g : graph.nodes) {
			if (g->downstream().empty() && g->upstream().empty())
				continue;
			if (bypass_nodes.count(g))
				continue;
			if (g->terminal) {
				g->names().sort();
				std::string label; // = stringf("vg=%d\\n", g->index);
				for (auto n : g->names())
					label = label + (label.empty() ? "" : "\\n") + log_id(n);
				fprintf(f, "\tn%d [shape=rectangle,label=\"%s\"];\n", g->index, label.c_str());
			} else {
				std::string label = stringf("vg=%d | %d cells", g->index, GetSize(g->names()));
				std::string shape = "oval";
				if (extra_lines.count(g)) {
					for (auto &block : extra_lines.at(g)) {
						label += label.empty() ? "" : "\\n";
						for (auto &line : block)
							label = label + (label.empty() ? "" : "\\n") + line;
						shape = "octagon";
					}
				}
				fprintf(f, "\tn%d [shape=%s,label=\"%s\"];\n", g->index, shape.c_str(), label.c_str());
			}
		}

		pool<std::string> edges;
		for (auto g : graph.nodes) {
			auto p = bypass_nodes.at(g, g);
			for (auto n : g->downstream()) {
				auto q = bypass_nodes.at(n, n);
				if (p == q) continue;
				edges.insert(stringf("n%d -> n%d", p->index, q->index));
			}
		}
		edges.sort();
		for (auto e : edges)
			fprintf(f, "\t%s;\n", e.c_str());

		fprintf(f, "}\n");
	}
};

struct VizPass : public Pass {
	VizPass() : Pass("viz", "visualize data flow graph") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    viz [options] [selection]\n");
		log("\n");
		log("Create a graphviz DOT file for the selected part of the design, showing the\n");
		log("relationships between the selected wires, and compile it to a graphics\n");
		log("file (usually SVG or PostScript).\n");
		log("\n");
		log("    -viewer <viewer>\n");
		log("        Run the specified command with the graphics file as parameter.\n");
		log("        On Windows, this pauses yosys until the viewer exits.\n");
		log("\n");
		log("    -format <format>\n");
		log("        Generate a graphics file in the specified format. Use 'dot' to just\n");
		log("        generate a .dot file, or other <format> strings such as 'svg' or 'ps'\n");
		log("        to generate files in other formats (this calls the 'dot' command).\n");
		log("\n");
		log("    -prefix <prefix>\n");
		log("        generate <prefix>.* instead of ~/.yosys_viz.*\n");
		log("\n");
		log("    -pause\n");
		log("        wait for the user to press enter to before returning\n");
		log("\n");
		log("    -nobg\n");
		log("        don't run viewer in the background, IE wait for the viewer tool to\n");
		log("        exit before returning\n");
		log("\n");
		log("    -set-vg-attr\n");
		log("        set their group index as 'vg' attribute on cells and wires\n");
		log("\n");
		log("    -g <selection>\n");
		log("        manually define a group of terminal signals. this group is not being\n");
		log("        merged with other terminal groups.\n");
		log("\n");
		log("    -u <selection>\n");
		log("        manually define a unique group for each wire in the selection.\n");
		log("\n");
		log("    -x <selection>\n");
		log("        manually exclude wires from being considered. (usually this is\n");
		log("        used for global signals, such as reset.)\n");
		log("\n");
		log("    -s <selection>\n");
		log("        like -g, but mark group as 'special', changing the algorithm to\n");
		log("        preserve as much info about this groups connectivity as possible.\n");
		log("\n");
		log("    -G <selection_expr> .\n");
		log("    -U <selection_expr> .\n");
		log("    -X <selection_expr> .\n");
		log("    -S <selection_expr> .\n");
		log("        like -u, -g, -x, and -s, but parse all arguments up to a terminating .\n");
		log("        as a single select expression. (see 'help select' for details)\n");
		log("\n");
		log("    -0, -1, -2, -3, -4, -5, -6, -7, -8, -9\n");
		log("        select effort level. each level corresponds to an incresingly more\n");
		log("        aggressive sequence of strategies for merging nodes of the data flow\n");
		log("        graph. (default: %d)\n", VizConfig().effort);
		log("\n");
		log("When no <format> is specified, 'dot' is used. When no <format> and <viewer> is\n");
		log("specified, 'xdot' is used to display the schematic (POSIX systems only).\n");
		log("\n");
		log("The generated output files are '~/.yosys_viz.dot' and '~/.yosys_viz.<format>',\n");
		log("unless another prefix is specified using -prefix <prefix>.\n");
		log("\n");
		log("Yosys on Windows and YosysJS use different defaults: The output is written\n");
		log("to 'show.dot' in the current directory and new viewer is launched each time\n");
		log("the 'show' command is executed.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Generating Graphviz representation of design.\n");
		log_push();

#if defined(_WIN32) || defined(YOSYS_DISABLE_SPAWN)
		std::string format = "dot";
		std::string prefix = "show";
#else
		std::string format;
		std::string prefix = stringf("%s/.yosys_viz", getenv("HOME") ? getenv("HOME") : ".");
#endif
		std::string viewer_exe;
		bool flag_pause = false;
		bool flag_attr = false;
		bool custom_prefix = false;
		std::string background = "&";

		VizConfig config;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-viewer" && argidx+1 < args.size()) {
				viewer_exe = args[++argidx];
				continue;
			}
			if (arg == "-prefix" && argidx+1 < args.size()) {
				prefix = args[++argidx];
				custom_prefix = true;
				continue;
			}
			if (arg == "-format" && argidx+1 < args.size()) {
				format = args[++argidx];
				continue;
			}
			if (arg == "-pause") {
				flag_pause= true;
				continue;
			}
			if (arg == "-set-vg-attr") {
				flag_attr= true;
				continue;
			}
			if (arg == "-nobg") {
				background= "";
				continue;
			}
			if ((arg == "-g" || arg == "-u" || arg == "-x" || arg == "-s" ||
					arg == "-G" || arg == "-U" || arg == "-X" || arg == "-S") && argidx+1 < args.size()) {
				int numargs = 1;
				int first_arg = ++argidx;
				if (arg == "-G" || arg == "-U" || arg == "-X" || arg == "-S") {
					while (argidx+1 < args.size()) {
						if (args[++argidx] == ".") break;
						numargs++;
					}
				}
				handle_extra_select_args(this, args, first_arg, first_arg+numargs, design);
				auto type = arg == "-g" || arg == "-G" ? VizConfig::TYPE_G :
					arg == "-u" || arg == "-U" ? VizConfig::TYPE_U :
					arg == "-x" || arg == "-X" ? VizConfig::TYPE_X : VizConfig::TYPE_S;
				config.groups.push_back({type, design->selection_stack.back()});
				design->selection_stack.pop_back();
				continue;
			}
			if (arg == "-0" || arg == "-1" || arg == "-2" || arg == "-3" || arg == "-4" ||
					arg == "-5" || arg == "-6" || arg == "-7" || arg == "-8" || arg == "-9") {
				config.effort = arg[1] - '0';
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::vector<Module*> modlist;
		for (auto module : design->selected_modules()) {
			if (module->get_blackbox_attribute())
				continue;
			if (module->cells().size() == 0 && module->connections().empty())
				continue;
			modlist.push_back(module);
		}
		if (format != "ps" && format != "dot" && GetSize(modlist) > 1)
			log_cmd_error("For formats different than 'ps' or 'dot' only one module must be selected.\n");
		if (modlist.empty())
			log_cmd_error("Nothing there to show.\n");

		std::string dot_file = stringf("%s.dot", prefix.c_str());
		std::string out_file = stringf("%s.%s", prefix.c_str(), format.empty() ? "svg" : format.c_str());

		if (custom_prefix)
			yosys_output_files.insert(dot_file);

		log("Writing dot description to `%s'.\n", dot_file.c_str());
		FILE *f = nullptr;
		auto open_dot_file = [&]() {
			if (f != nullptr) return;
			f = fopen(dot_file.c_str(), "w");
			if (f == nullptr)
				log_cmd_error("Can't open dot file `%s' for writing.\n", dot_file.c_str());
		};
		for (auto module : modlist) {
			VizWorker worker(module, config);

			if (flag_attr)
				worker.update_attrs();

			if (format != "dot" && GetSize(worker.graph.nodes) > 200) {
				if (format.empty()) {
					log_warning("Suppressing module in output as graph size exceeds 200 nodes.\n");
					continue;
				} else {
					log_warning("Changing format to 'dot' as graph size exceeds 200 nodes.\n");
					format = "dot";
				}
			}

			// delay opening of output file until we have something to write, to avoid race with xdot
			open_dot_file();
			worker.write_dot(f);
		}
		open_dot_file();
		fclose(f);

		if (format != "dot" && !format.empty()) {
			#ifdef _WIN32
				// system()/cmd.exe does not understand single quotes on Windows.
				#define DOT_CMD "dot -T%s \"%s\" > \"%s.new\" && move \"%s.new\" \"%s\""
			#else
				#define DOT_CMD "dot -T%s '%s' > '%s.new' && mv '%s.new' '%s'"
			#endif
			std::string cmd = stringf(DOT_CMD, format.c_str(), dot_file.c_str(), out_file.c_str(), out_file.c_str(), out_file.c_str());
			#undef DOT_CMD
			log("Exec: %s\n", cmd.c_str());
			#if !defined(YOSYS_DISABLE_SPAWN)
				if (run_command(cmd) != 0)
					log_cmd_error("Shell command failed!\n");
			#endif
		}

		#if defined(YOSYS_DISABLE_SPAWN)
			log_assert(viewer_exe.empty() && !format.empty());
		#else
		if (!viewer_exe.empty()) {
			#ifdef _WIN32
				// system()/cmd.exe does not understand single quotes nor
				// background tasks on Windows. So we have to pause yosys
				// until the viewer exits.
				std::string cmd = stringf("%s \"%s\"", viewer_exe.c_str(), out_file.c_str());
			#else
				std::string cmd = stringf("%s '%s' %s", viewer_exe.c_str(), out_file.c_str(), background.c_str());
			#endif
			log("Exec: %s\n", cmd.c_str());
			if (run_command(cmd) != 0)
				log_cmd_error("Shell command failed!\n");
		} else
		if (format.empty()) {
			#ifdef __APPLE__
			std::string cmd = stringf("ps -fu %d | grep -q '[ ]%s' || xdot '%s' %s", getuid(), dot_file.c_str(), dot_file.c_str(), background.c_str());
			#else
			std::string cmd = stringf("{ test -f '%s.pid' && fuser -s '%s.pid' 2> /dev/null; } || ( echo $$ >&3; exec xdot '%s'; ) 3> '%s.pid' %s", dot_file.c_str(), dot_file.c_str(), dot_file.c_str(), dot_file.c_str(), background.c_str());
			#endif
			log("Exec: %s\n", cmd.c_str());
			if (run_command(cmd) != 0)
				log_cmd_error("Shell command failed!\n");
		}
		#endif

		if (flag_pause) {
		#ifdef YOSYS_ENABLE_READLINE
			char *input = nullptr;
			while ((input = readline("Press ENTER to continue (or type 'shell' to open a shell)> ")) != nullptr) {
				if (input[strspn(input, " \t\r\n")] == 0)
					break;
				char *p = input + strspn(input, " \t\r\n");
				if (!strcmp(p, "shell")) {
					Pass::call(design, "shell");
					break;
				}
			}
		#else
			log_cmd_error("This version of yosys is built without readline support => 'show -pause' is not available.\n");
		#endif
		}

		log_pop();
	}
} VizPass;

PRIVATE_NAMESPACE_END
