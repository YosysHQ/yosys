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
		TYPE_U
	};

	int script = 9;
	std::vector<std::pair<group_type_t, RTLIL::Selection>> groups;

	int max_size = -1;

	int max_fanout = 10;
	int max_fanin = 10;
	int max_conns = 15;
};

struct GraphNode {
	int index = -1;
	bool nomerge = false;
	bool terminal = false;
	GraphNode *replaced = nullptr;

	GraphNode *get() {
		if (replaced == nullptr)
			return this;
		return replaced = replaced->get();
	}

	pool<IdString> names_;
	pool<GraphNode*, hash_ptr_ops> upstream_;
	pool<GraphNode*, hash_ptr_ops> downstream_;

	pool<IdString> &names() { return get()->names_; }
	pool<GraphNode*, hash_ptr_ops> &upstream() { return get()->upstream_; }
	pool<GraphNode*, hash_ptr_ops> &downstream() { return get()->downstream_; }

	void replace(GraphNode *g) {
		if (replaced)
			return get()->replace(g);

		log_assert(!nomerge);
		log_assert(!g->get()->nomerge);
		log_assert(terminal == g->terminal);

		if (this == g->get()) return;

		for (auto v : g->names())
			names().insert(v);

		for (auto v : g->upstream()) {
			auto n = v->get();
			if (n == this) continue;
			upstream().insert(n);
		}

		for (auto v : g->downstream()) {
			auto n = v->get();
			if (n == this) continue;
			downstream().insert(n);
		}

		g->names().clear();
		g->upstream().clear();
		g->downstream().clear();

		g->get()->replaced = this;
	}

	void cleanup() {
		if (replaced) return;

		pool<GraphNode*, hash_ptr_ops> new_upstream;
		pool<GraphNode*, hash_ptr_ops> new_downstream;

		for (auto g : upstream_) {
			auto n = g->get();
			if (n == this) continue;
			new_upstream.insert(n);
		}
		for (auto g : downstream_) {
			auto n = g->get();
			if (n == this) continue;
			new_downstream.insert(n);
		}

		std::swap(upstream_, new_upstream);
		std::swap(downstream_, new_downstream);
	}
};

struct Graph {
	vector<GraphNode*> nodes;
	vector<GraphNode*> replaced_nodes;

	Module *module;
	const VizConfig &config;

	// statistics, updated by cleanup()
	int term_nodes_cnt;
	int nonterm_nodes_cnt;
	int max_group_sizes[5];

	~Graph()
	{
		for (auto n : nodes) delete n;
		for (auto n : replaced_nodes) delete n;
	}

	void cleanup()
	{
		vector<GraphNode*> new_nodes;

		term_nodes_cnt = 0;
		nonterm_nodes_cnt = 0;
		for (int i = 0; i < 5; i++)
			max_group_sizes[i] = 0;

		for (auto n : nodes) {
			if (n->replaced) {
				replaced_nodes.push_back(n);
			} else {
				new_nodes.push_back(n);
				n->index = GetSize(new_nodes);
				n->cleanup();

				if (n->terminal) {
					term_nodes_cnt++;
				} else {
					nonterm_nodes_cnt++;
					int pivot = GetSize(n->names());
					for (int i = 0; i < 5; i++)
						if (pivot >= max_group_sizes[i])
							std::swap(pivot, max_group_sizes[i]);
				}
			}
		}

		std::swap(nodes, new_nodes);
	}

	enum merge_flags_t : uint32_t {
		merge_tag_any = 0x00000001,
		merge_tag_buf = 0x00000002,
		merge_dbl_buf = 0x00000004,
		merge_bi_conn = 0x00000008,
		merge_id_conn = 0x00000010,
		merge_term    = 0x00000020,
		merge_small   = 0x00000040,
		merge_maxfan  = 0x00000080,
	};

	static const std::vector<std::vector<Graph::merge_flags_t>>& scripts()
	{
		static std::vector<std::vector<merge_flags_t>> buffer;

		if (buffer.empty()) {
			auto next_script = [&]() { buffer.push_back({}); };
			auto cmd = [&](uint32_t flags) { buffer.back().push_back(merge_flags_t(flags)); };

			// viz -0
			next_script();
			cmd(merge_dbl_buf | merge_id_conn | merge_maxfan);

			// viz -1
			next_script();
			cmd(merge_dbl_buf | merge_id_conn | merge_tag_any | merge_maxfan);

			// viz -2
			next_script();
			cmd(merge_tag_buf | merge_dbl_buf | merge_bi_conn | merge_id_conn | merge_term);
			cmd(merge_tag_any | merge_dbl_buf | merge_bi_conn | merge_id_conn | merge_maxfan);
			cmd(merge_id_conn | merge_term | merge_small | merge_maxfan);

			// viz -3
			next_script();
			cmd(merge_tag_buf | merge_dbl_buf | merge_bi_conn | merge_id_conn | merge_term);
			cmd(merge_tag_any | merge_dbl_buf | merge_bi_conn | merge_id_conn);
			cmd(merge_id_conn | merge_term | merge_small | merge_maxfan);
		}

		return buffer;
	};

	bool merge(merge_flags_t flags)
	{
		dict<GraphNode*, pool<int>, hash_ptr_ops> node_tags;

		bool did_something = false;
		while (true)
		{
			if (node_tags.empty() || (flags & merge_tag_buf) != 0) {
				std::function<void(GraphNode*,int,bool)> downprop_tag = [&](GraphNode *g, int tag, bool last) {
					auto &tags = node_tags[g];
					auto it = tags.find(tag);
					if (it != tags.end()) return;
					tags.insert(tag);
					if (last) return;
					for (auto n : g->downstream())
						downprop_tag(n->get(), tag, n->terminal);
				};

				std::function<void(GraphNode*,int,bool)> upprop_tag = [&](GraphNode *g, int tag, bool last) {
					auto &tags = node_tags[g];
					auto it = tags.find(tag);
					if (it != tags.end()) return;
					tags.insert(tag);
					if (last) return;
					for (auto n : g->upstream())
						upprop_tag(n->get(), tag, n->terminal);
				};

				int tag = 0;
				node_tags.clear();
				for (auto g : nodes) {
					if (g->replaced || !g->terminal) continue;
					downprop_tag(g, ++tag, false);
					upprop_tag(g, ++tag, false);
				}
			}

			vector<pair<GraphNode*,GraphNode*>> queued_merges;
			typedef pair<pool<GraphNode*, hash_ptr_ops>, pool<GraphNode*, hash_ptr_ops>> node_conn_t;
			dict<node_conn_t, pool<GraphNode*, hash_ptr_ops>> nodes_by_conn[2];

			for (auto g : nodes) {
				if (g->replaced || g->nomerge) continue;
				if ((flags & merge_term) == 0 && g->terminal) continue;

				if ((flags & merge_id_conn) != 0)
					nodes_by_conn[g->terminal][node_conn_t(g->upstream(), g->downstream())].insert(g);

				if ((flags & merge_tag_any) != 0 || ((flags & merge_tag_buf) != 0 && GetSize(g->downstream()) == 1)) {
					for (auto n : g->downstream()) {
						if (g->terminal != n->terminal || n->nomerge) continue;
						if (node_tags[g] != node_tags[n->get()]) continue;
						queued_merges.push_back(pair<GraphNode*,GraphNode*>(g, n->get()));
					}
				}

				if ((flags & merge_dbl_buf) != 0) {
					if (GetSize(g->downstream()) == 1) {
						auto n = (*g->downstream().begin())->get();
						if (g->terminal != n->terminal || n->nomerge) continue;
						if (GetSize(n->downstream()) != 1) continue;
						queued_merges.push_back(pair<GraphNode*,GraphNode*>(g, n));
					}
				}

				if ((flags & merge_bi_conn) != 0) {
					for (auto n : g->downstream()) {
						if (g->terminal != n->terminal || n->nomerge) continue;
						if (!n->downstream().count(g)) continue;
						queued_merges.push_back(pair<GraphNode*,GraphNode*>(g, n));
					}
				}

				if ((flags & merge_small) != 0 && !g->terminal && GetSize(g->names()) < 10) {
					GraphNode *best = nullptr;
					for (auto n : g->downstream()) {
						if (n->terminal || n->nomerge || GetSize(n->names()) > 10-GetSize(g->names())) continue;
						if (best && GetSize(best->names()) <= GetSize(n->names())) continue;
						best = n;
					}
					for (auto n : g->upstream()) {
						if (n->terminal || n->nomerge || GetSize(n->names()) > 10-GetSize(g->names())) continue;
						if (best && GetSize(best->names()) <= GetSize(n->names())) continue;
						best = n;
					}
					if (best) queued_merges.push_back(pair<GraphNode*,GraphNode*>(g, best));
				}
			}

			if ((flags & merge_id_conn) != 0) {
				for (int term = 0; term < 2; term++) {
					for (auto &grp : nodes_by_conn[term]) {
						auto it = grp.second.begin();
						auto first = *it;
						while (++it != grp.second.end())
							queued_merges.push_back(pair<GraphNode*,GraphNode*>(first, *it));
					}
				}
			}

			int count_merges = 0;
			int smallest_merge_idx = -1;
			int smallest_merge_size = 0;
			for (int merge_idx = 0; merge_idx < GetSize(queued_merges); merge_idx++) {
				auto &m = queued_merges[merge_idx];
				auto g = m.first->get(), n = m.second->get();
				if (g == n) continue;

				if (!g->terminal)
				{
					int g_size = GetSize(g->names());
					int n_size = GetSize(n->names());
					int total_size = g_size + n_size;

					if (total_size > config.max_size) continue;

					if (smallest_merge_idx < 0 || total_size < smallest_merge_size) {
						smallest_merge_idx = merge_idx;
						smallest_merge_size = total_size;
					}

					if (total_size > max_group_sizes[1] + max_group_sizes[4]) continue;
					if (g_size >= max_group_sizes[0] && max_group_sizes[0] != max_group_sizes[4]) continue;
					if (n_size >= max_group_sizes[0] && max_group_sizes[0] != max_group_sizes[4]) continue;

					if ((flags & merge_maxfan) != 0) {
						auto &g_upstream = g->upstream(), &g_downstream = g->downstream();
						auto &n_upstream = n->upstream(), &n_downstream = n->downstream();

						if (GetSize(g_upstream) > config.max_fanin) continue;
						if (GetSize(n_upstream) > config.max_fanin) continue;

						if (GetSize(g_downstream) > config.max_fanout) continue;
						if (GetSize(n_downstream) > config.max_fanout) continue;

						pool<GraphNode*, hash_ptr_ops> combined_upstream = g_upstream;
						combined_upstream.insert(n_upstream.begin(), n_upstream.end());

						pool<GraphNode*, hash_ptr_ops> combined_downstream = g_downstream;
						combined_downstream.insert(n_downstream.begin(), n_downstream.end());

						pool<GraphNode*, hash_ptr_ops> combined_conns = combined_upstream;
						combined_conns.insert(combined_downstream.begin(), combined_downstream.end());

						if (GetSize(combined_upstream) > config.max_fanin) continue;
						if (GetSize(combined_downstream) > config.max_fanout) continue;
						if (GetSize(combined_conns) > config.max_conns) continue;
					}
				}

				g->replace(n);
				count_merges++;
			}
			if (count_merges == 0 && smallest_merge_idx >= 0) {
				auto &m = queued_merges[smallest_merge_idx];
				auto g = m.first->get(), n = m.second->get();
				log("    Merging only the smallest node pair: %d + %d -> %d\n",
						GetSize(g->names()), GetSize(n->names()), smallest_merge_size);
				g->replace(n);
				count_merges++;
			} else {
				if (count_merges == 0) return did_something;
				log("    Merged %d node pairs.\n", count_merges);
			}
			did_something = true;
			cleanup();
		}
	}

	Graph(Module *module, const VizConfig &config) : module(module), config(config)
	{
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
					g->replace(it->second);
			}
		}

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
					if (grp.first == VizConfig::TYPE_G) {
						if (g) {
							if (!n->nomerge)
								g->replace(n);
						} else
							g = n;
					} else { // VizConfig::TYPE_U
						n->nomerge = true;
					}
				}
			}

			if (g)
				g->nomerge = true;
		}

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
							g->upstream().insert(it->second);
							it->second->downstream().insert(g);
						}
						sig_users[bit].insert(g);
					}
				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second)) {
						if (!bit.wire) continue;
						auto it = wire_nodes.find(bit);
						if (it != wire_nodes.end()) {
							g->downstream().insert(it->second);
							it->second->upstream().insert(g);
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

		cleanup();
	}
};

struct VizWorker
{
	VizConfig config;
	Module *module;
	Graph graph;

	VizWorker(Module *module, const VizConfig &cfg) : config(cfg), module(module), graph(module, config)
	{
		auto &scripts = Graph::scripts();
		config.script = std::min(GetSize(scripts)-1, config.script);
		auto &script = scripts.at(config.script);

		if (config.max_size < 0)
			config.max_size = graph.nonterm_nodes_cnt / 3;

		auto log_stats = [&](const char *sp, const char *p) {
			log("%s%s maximum group sizes are ", sp, p);
			for (int i = 0; i < 5; i++)
				log("%d%s", graph.max_group_sizes[i], i==3 ? ", and " : i == 4 ? ".\n" : ", ");
			log("%s%s number of terminal nodes is %d.\n", sp, p, graph.term_nodes_cnt);
			log("%s%s number of non-terminal nodes is %d.\n", sp, p, graph.nonterm_nodes_cnt);
		};

		log("Running 'viz -%d' for module %s:\n", config.script, log_id(module));
		log_stats("  ", "Initial");

		for (int i = 0; i < GetSize(script); i++) {
			log("  Stage-%d merge loop:\n", i+1);
			graph.merge(script[i]);
			log_stats("    ", i+1 == GetSize(script) ? "Final" : "New");
		}
	}

	void write_dot(FILE *f)
	{
		fprintf(f, "digraph \"%s\" {\n", log_id(module));
		fprintf(f, "  rankdir = LR;\n");

		dict<GraphNode*, std::vector<std::string>, hash_ptr_ops> extra_lines;
		dict<GraphNode*, GraphNode*, hash_ptr_ops> bypass_nodes;

		for (auto g : graph.nodes) {
			if (!g->terminal || g->nomerge) continue;
			if (GetSize(g->upstream()) != 1) continue;
			if (!g->downstream().empty() && g->downstream() != g->upstream()) continue;
			auto n = *(g->upstream().begin());
			if (n->terminal) continue;
			for (auto name : g->names())
				extra_lines[n].push_back(log_id(name));
			bypass_nodes[g] = n;
		}

		for (int i = 0; i < GetSize(graph.nodes); i++) {
			auto g = graph.nodes[i];
			if (g->downstream().empty() && g->upstream().empty())
				continue;
			if (bypass_nodes.count(g))
				continue;
			if (g->terminal) {
				std::string label; // = stringf("[%d]\\n", g->index);
				for (auto n : g->names())
					label = label + (label.empty() ? "" : "\\n") + log_id(n);
				fprintf(f, "\tn%d [shape=rectangle,label=\"%s\"];\n", g->index, label.c_str());
			} else {
				std::string label = stringf("grp=%d | %d cells", g->index, GetSize(g->names()));
				std::string shape = "oval";
				if (extra_lines.count(g)) {
					label += label.empty() ? "" : "\\n";
					for (auto line : extra_lines.at(g))
						label = label + (label.empty() ? "" : "\\n") + line;
					shape = "octagon";
				}
				fprintf(f, "\tn%d [shape=%s,label=\"%s\"];\n", g->index, shape.c_str(), label.c_str());
			}
		}

		pool<std::string> edges;
		for (int i = 0; i < GetSize(graph.nodes); i++) {
			auto g = graph.nodes[i];
			g = bypass_nodes.at(g, g);
			for (auto n : g->downstream()) {
				n = bypass_nodes.at(n, n);
				if (g == n) continue;
				edges.insert(stringf("n%d -> n%d", g->index, n->index));
			}
		}
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
		log("    -g <selection>\n");
		log("        manually define a group of terminal signals. this group is not being\n");
		log("        merged with other terminal groups.\n");
		log("\n");
		log("    -u <selection>\n");
		log("        manually define a unique group for each wire in the selection.\n");
		log("\n");
		log("    -G <selection_expr> .\n");
		log("    -U <selection_expr> .\n");
		log("        like -u and -g, but parse all arguments up to a terminating . argument\n");
		log("        as a single select expression. (see 'help select' for details)\n");
		log("\n");
		log("    -0, -1, -2, -3, -4, -5, -6, -7, -8, -9\n");
		log("        select effort level. each level corresponds to an incresingly more\n");
		log("        aggressive sequence of strategies for merging nodes of the data flow\n");
		log("        graph. (default: %d)\n", VizConfig().script);
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
			if (arg == "-nobg") {
				background= "";
				continue;
			}
			if ((arg == "-g" || arg == "-u" || arg == "-G" || arg == "-U") && argidx+1 < args.size()) {
				int numargs = 1;
				int first_arg = ++argidx;
				if (arg == "-G" || arg == "-U") {
					while (argidx+1 < args.size()) {
						if (args[++argidx] == ".") break;
						numargs++;
					}
				}
				handle_extra_select_args(this, args, first_arg, first_arg+numargs, design);
				auto type = arg == "-g" || arg == "-G" ? VizConfig::TYPE_G : VizConfig::TYPE_U;
				config.groups.push_back({type, design->selection_stack.back()});
				design->selection_stack.pop_back();
				continue;
			}
			if (arg == "-0" || arg == "-1" || arg == "-2" || arg == "-3" || arg == "-4" ||
					arg == "-5" || arg == "-6" || arg == "-7" || arg == "-8" || arg == "-9") {
				config.script = arg[1] - '0';
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

			if (format != "dot" && worker.graph.term_nodes_cnt + worker.graph.nonterm_nodes_cnt > 150) {
				if (format.empty()) {
					log_warning("Suppressing module in output as graph size exceeds 150 nodes.\n");
					continue;
				} else {
					log_warning("Changing format to 'dot' as graph size exceeds 150 nodes.\n");
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
