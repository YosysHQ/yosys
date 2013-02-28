/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string.h>
#include <dirent.h>

#undef CLUSTER_CELLS_AND_PORTBOXES

struct ShowWorker
{
	CellTypes ct;

	std::vector<std::string> dot_escape_store;
	std::map<RTLIL::IdString, int> dot_id2num_store;
	std::map<RTLIL::IdString, int> autonames;
	int single_idx_count;

	struct net_conn { std::set<std::string> in, out; };
	std::map<std::string, net_conn> net_conn_map;

	FILE *f;
	RTLIL::Design *design;
	RTLIL::Module *module;
	int page_counter;

	const char *escape(std::string id, bool is_name = false)
	{
		if (id.size() == 0)
			return "";

		if (id[0] == '$' && is_name) {
			if (autonames.count(id) == 0) {
				autonames[id] = autonames.size() + 1;
				log("Generated short name for internal identifier: _%d_ -> %s\n", autonames[id], id.c_str());
			}
			id = stringf("_%d_", autonames[id]);
		}

		if (id[0] == '\\')
			id = id.substr(1);

		std::string str;
		for (char ch : id) {
			if (ch == '\\' || ch == '"')
				str += "\\";
			str += ch;
		}

		dot_escape_store.push_back(str);
		return dot_escape_store.back().c_str();
	}

	int id2num(RTLIL::IdString id)
	{
		if (dot_id2num_store.count(id) > 0)
			return dot_id2num_store[id];
		return dot_id2num_store[id] = dot_id2num_store.size() + 1;
	}

	std::string gen_signode_simple(RTLIL::SigSpec sig, bool range_check = true)
	{
		sig.optimize();

		if (sig.chunks.size() == 0) {
			fprintf(f, "v%d [ label=\"\" ];\n", single_idx_count);
			return stringf("v%d", single_idx_count++);
		}

		if (sig.chunks.size() == 1) {
			RTLIL::SigChunk &c = sig.chunks[0];
			if (c.wire != NULL && design->selected_member(module->name, c.wire->name)) {
				if (!range_check || c.wire->width == c.width)
						return stringf("n%d", id2num(c.wire->name));
			} else {
				fprintf(f, "v%d [ label=\"%s\" ];\n", single_idx_count, escape(log_signal(c), true));
				return stringf("v%d", single_idx_count++);
			}
		}

		return std::string();
	}

	std::string gen_portbox(std::string port, RTLIL::SigSpec sig, bool driver, std::string *node = NULL)
	{
		std::string code;
		std::string net = gen_signode_simple(sig);
		if (net.empty())
		{
			std::string label_string;
			sig.optimize();
			int pos = sig.width-1;
			int idx = single_idx_count++;
			for (int i = int(sig.chunks.size())-1; i >= 0; i--) {
				RTLIL::SigChunk &c = sig.chunks[i];
				net = gen_signode_simple(c, false);
				assert(!net.empty());
				if (driver) {
					label_string += stringf("<s%d> %d:%d - %d:%d |", i, pos, pos-c.width+1, c.offset+c.width-1, c.offset);
					net_conn_map[net].in.insert(stringf("x%d:s%d", idx, i));
				} else {
					label_string += stringf("<s%d> %d:%d - %d:%d |", i, c.offset+c.width-1, c.offset, pos, pos-c.width+1);
					net_conn_map[net].out.insert(stringf("x%d:s%d", idx, i));
				}
				pos -= c.width;
			}
			if (label_string[label_string.size()-1] == '|')
				label_string = label_string.substr(0, label_string.size()-1);
			code += stringf("x%d [ shape=record, style=rounded, label=\"%s\" ];\n", idx, label_string.c_str());
			if (!port.empty()) {
				if (driver)
					code += stringf("%s:e -> x%d:w [arrowhead=odiamond, arrowtail=odiamond, dir=both];\n", port.c_str(), idx);
				else
					code += stringf("x%d:e -> %s:w [arrowhead=odiamond, arrowtail=odiamond, dir=both];\n", idx, port.c_str());
			}
			if (node != NULL)
				*node = stringf("x%d", idx);
		}
		else
		{
			if (!port.empty()) {
				if (driver)
					net_conn_map[net].in.insert(port);
				else
					net_conn_map[net].out.insert(port);
			}
			if (node != NULL)
				*node = net;
		}
		return code;
	}

	void handle_module()
	{
		single_idx_count = 0;
		dot_escape_store.clear();
		dot_id2num_store.clear();
		net_conn_map.clear();

		fprintf(f, "digraph \"%s\" {\n", escape(module->name));
		fprintf(f, "rankdir=\"LR\";\n");
		fprintf(f, "remincross=true;\n");

		std::map<std::string, std::string> wires_on_demand;
		for (auto &it : module->wires) {
			if (!design->selected_member(module->name, it.first))
				continue;
			const char *shape = "diamond";
			if (it.second->port_input || it.second->port_output)
				shape = "octagon";
			if (it.first[0] == '\\')
				fprintf(f, "n%d [ shape=%s, label=\"%s\" ];\n",
						id2num(it.first), shape, escape(it.first));
			else {
				wires_on_demand[stringf("n%d", id2num(it.first))] = it.first;
			}
		}

		for (auto &it : module->cells)
		{
			if (!design->selected_member(module->name, it.first))
				continue;

			std::vector<RTLIL::IdString> in_ports, out_ports;

			for (auto &conn : it.second->connections) {
				if (ct.cell_input(it.second->type, conn.first))
					in_ports.push_back(conn.first);
				else
					out_ports.push_back(conn.first);
			}

			std::string label_string = "{{";

			for (auto &p : in_ports)
				label_string += stringf("<p%d> %s|", id2num(p), escape(p));
			if (label_string[label_string.size()-1] == '|')
				label_string = label_string.substr(0, label_string.size()-1);

			label_string += stringf("}|%s\\n%s|{", escape(it.first, true), escape(it.second->type));

			for (auto &p : out_ports)
				label_string += stringf("<p%d> %s|", id2num(p), escape(p));
			if (label_string[label_string.size()-1] == '|')
				label_string = label_string.substr(0, label_string.size()-1);

			label_string += "}}";

			std::string code;
			for (auto &conn : it.second->connections) {
				code += gen_portbox(stringf("c%d:p%d", id2num(it.first), id2num(conn.first)),
						conn.second, !ct.cell_input(it.second->type, conn.first));
			}

#ifdef CLUSTER_CELLS_AND_PORTBOXES
			if (!code.empty())
				fprintf(f, "subgraph cluster_c%d {\nc%d [ shape=record, label=\"%s\" ];\n%s}\n",
						id2num(it.first), id2num(it.first), label_string.c_str(), code.c_str());
			else
#endif
				fprintf(f, "c%d [ shape=record, label=\"%s\" ];\n%s",
						id2num(it.first), label_string.c_str(), code.c_str());
		}

		for (auto &conn : module->connections)
		{
			bool found_lhs_wire = false;
			for (auto &c : conn.first.chunks) {
				if (c.wire != NULL && design->selected_member(module->name, c.wire->name))
					found_lhs_wire = true;
			}
			bool found_rhs_wire = false;
			for (auto &c : conn.second.chunks) {
				if (c.wire != NULL && design->selected_member(module->name, c.wire->name))
					found_rhs_wire = true;
			}
			if (!found_lhs_wire || !found_rhs_wire)
				continue;

			std::string code, left_node, right_node;
			code += gen_portbox("", conn.second, false, &left_node);
			code += gen_portbox("", conn.first, true, &right_node);
			fprintf(f, "%s", code.c_str());

			if (left_node[0] == 'x' && right_node[0] == 'x')
				fprintf(f, "%s:e -> %s:w [arrowhead=odiamond, arrowtail=odiamond, dir=both];\n", left_node.c_str(), right_node.c_str());
			else if (left_node[0] == 'x')
				net_conn_map[right_node].in.insert(left_node);
			else if (right_node[0] == 'x')
				net_conn_map[left_node].out.insert(right_node);
			else {
				net_conn_map[right_node].in.insert(stringf("x%d:e", single_idx_count));
				net_conn_map[left_node].out.insert(stringf("x%d:w", single_idx_count));
				fprintf(f, "x%d [shape=box, style=rounded, label=\"BUF\"];\n", single_idx_count++);
			}
		}

		for (auto &it : net_conn_map)
		{
			if (wires_on_demand.count(it.first) > 0) {
				if (it.second.in.size() == 1 && it.second.out.size() == 1) {
					fprintf(f, "%s:e -> %s:w;\n", it.second.in.begin()->c_str(), it.second.out.begin()->c_str());
					continue;
				}
				if (it.second.in.size() == 0 || it.second.out.size() == 0)
					fprintf(f, "%s [ shape=diamond, label=\"%s\" ];\n", it.first.c_str(), escape(wires_on_demand[it.first], true));
				else
					fprintf(f, "%s [ shape=point ];\n", it.first.c_str());
			}
			for (auto &it2 : it.second.in)
				fprintf(f, "%s:e -> %s:w;\n", it2.c_str(), it.first.c_str());
			for (auto &it2 : it.second.out)
				fprintf(f, "%s:e -> %s:w;\n", it.first.c_str(), it2.c_str());
		}

		fprintf(f, "};\n");
	}

	ShowWorker(FILE *f, RTLIL::Design *design) : f(f), design(design)
	{
		ct.setup_internals();
		ct.setup_internals_mem();
		ct.setup_stdcells();
		ct.setup_stdcells_mem();

		design->optimize();
		page_counter = 0;
		for (auto &mod_it : design->modules)
		{
			module = mod_it.second;
			if (!design->selected_module(module->name))
				continue;
			if (design->selected_whole_module(module->name))
				log("Dumping module %s to page %d.\n", module->name.c_str(), ++page_counter);
			else
				log("Dumping selected parts of module %s to page %d.\n", module->name.c_str(), ++page_counter);
			handle_module();
		}
	}
};

struct ShowPass : public Pass {
	ShowPass() : Pass("show", "generate schematics using graphviz") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    show [-viewer <command>] [selection]\n");
		log("\n");
		log("Create a graphviz DOT file for the selected part of the design and compile it\n");
		log("to a postscript file.\n");
		log("\n");
		log("    -viewer <command>\n");
		log("         Also run the specified command with the postscript file as parameter.\n");
		log("\n");
		log("The generated output files are `yosys-show.dot' and `yosys-show.ps'.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Generating Graphviz representation of design.\n");

		std::string viewer_exe;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-viewer" && argidx+1 < args.size()) {
				viewer_exe = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		log("Writing dot description to `yosys-show.dot'.\n");
		FILE *f = fopen("yosys-show.dot", "w");
		if (f == NULL)
			log_cmd_error("Can't open dot file `yosys-show.dot' for writing.\n");
		ShowWorker worker(f, design);
		fclose(f);

		if (worker.page_counter == 0)
			log_cmd_error("Nothing there to show.\n");

		std::string cmd = stringf("dot -Tps -o yosys-show.ps yosys-show.dot");
		log("Exec: %s\n", cmd.c_str());
		if (system(cmd.c_str()) != 0)
			log_cmd_error("Shell command failed!\n");

		if (!viewer_exe.empty()) {
			cmd = stringf("%s yosys-show.ps &", viewer_exe.c_str());
			log("Exec: %s\n", cmd.c_str());
			if (system(cmd.c_str()) != 0)
				log_cmd_error("Shell command failed!\n");
		}
	}
} ShowPass;
 
