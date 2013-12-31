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

// [[CITE]] ABC
// Berkeley Logic Synthesis and Verification Group, ABC: A System for Sequential Synthesis and Verification
// http://www.eecs.berkeley.edu/~alanmi/abc/

// [[CITE]] Kahn's Topological sorting algorithm
// Kahn, Arthur B. (1962), "Topological sorting of large networks", Communications of the ACM 5 (11): 558–562, doi:10.1145/368996.369025
// http://en.wikipedia.org/wiki/Topological_sorting

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <unistd.h>
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <dirent.h>
#include <sstream>

#include "blifparse.h"

struct gate_t
{
	int id;
	char type;
	int in1, in2, in3;
	bool is_port;
	RTLIL::SigSpec sig;
};

static int map_autoidx;
static SigMap assign_map;
static RTLIL::Module *module;
static std::vector<gate_t> signal_list;
static std::map<RTLIL::SigSpec, int> signal_map;

static int map_signal(RTLIL::SigSpec sig, char gate_type = -1, int in1 = -1, int in2 = -1, int in3 = -1)
{
	assert(sig.width == 1);
	assert(sig.chunks.size() == 1);

	assign_map.apply(sig);

	if (signal_map.count(sig) == 0) {
		gate_t gate;
		gate.id = signal_list.size();
		gate.type = -1;
		gate.in1 = -1;
		gate.in2 = -1;
		gate.in3 = -1;
		gate.is_port = false;
		gate.sig = sig;
		signal_list.push_back(gate);
		signal_map[sig] = gate.id;
	}

	gate_t &gate = signal_list[signal_map[sig]];

	if (gate_type >= 0)
		gate.type = gate_type;
	if (in1 >= 0)
		gate.in1 = in1;
	if (in2 >= 0)
		gate.in2 = in2;
	if (in3 >= 0)
		gate.in3 = in3;

	return gate.id;
}

static void mark_port(RTLIL::SigSpec sig)
{
	assign_map.apply(sig);
	sig.expand();
	for (auto &c : sig.chunks) {
		if (c.wire != NULL && signal_map.count(c) > 0)
			signal_list[signal_map[c]].is_port = true;
	}
}

static void extract_cell(RTLIL::Cell *cell)
{
	if (cell->type == "$_INV_")
	{
		RTLIL::SigSpec sig_a = cell->connections["\\A"];
		RTLIL::SigSpec sig_y = cell->connections["\\Y"];

		assign_map.apply(sig_a);
		assign_map.apply(sig_y);

		map_signal(sig_y, 'n', map_signal(sig_a));

		module->cells.erase(cell->name);
		delete cell;
		return;
	}

	if (cell->type == "$_AND_" || cell->type == "$_OR_" || cell->type == "$_XOR_")
	{
		RTLIL::SigSpec sig_a = cell->connections["\\A"];
		RTLIL::SigSpec sig_b = cell->connections["\\B"];
		RTLIL::SigSpec sig_y = cell->connections["\\Y"];

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);

		if (cell->type == "$_AND_")
			map_signal(sig_y, 'a', mapped_a, mapped_b);
		else if (cell->type == "$_OR_")
			map_signal(sig_y, 'o', mapped_a, mapped_b);
		else if (cell->type == "$_XOR_")
			map_signal(sig_y, 'x', mapped_a, mapped_b);
		else
			abort();

		module->cells.erase(cell->name);
		delete cell;
		return;
	}

	if (cell->type == "$_MUX_")
	{
		RTLIL::SigSpec sig_a = cell->connections["\\A"];
		RTLIL::SigSpec sig_b = cell->connections["\\B"];
		RTLIL::SigSpec sig_s = cell->connections["\\S"];
		RTLIL::SigSpec sig_y = cell->connections["\\Y"];

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_s);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);
		int mapped_s = map_signal(sig_s);

		map_signal(sig_y, 'm', mapped_a, mapped_b, mapped_s);

		module->cells.erase(cell->name);
		delete cell;
		return;
	}
}

static std::string remap_name(std::string abc_name)
{
	std::stringstream sstr;
	sstr << "$abc$" << map_autoidx << "$" << abc_name.substr(1);
	return sstr.str();
}

static void dump_loop_graph(FILE *f, int &nr, std::map<int, std::set<int>> &edges, std::set<int> &workpool, std::vector<int> &in_counts)
{
	if (f == NULL)
		return;

	log("Dumping loop state graph to slide %d.\n", ++nr);

	fprintf(f, "digraph slide%d {\n", nr);
	fprintf(f, "  rankdir=\"LR\";\n");

	std::set<int> nodes;
	for (auto &e : edges) {
		nodes.insert(e.first);
		for (auto n : e.second)
			nodes.insert(n);
	}

	for (auto n : nodes)
		fprintf(f, "  n%d [label=\"%s\\nid=%d, count=%d\"%s];\n", n, log_signal(signal_list[n].sig),
				n, in_counts[n], workpool.count(n) ? ", shape=box" : "");

	for (auto &e : edges)
	for (auto n : e.second)
		fprintf(f, "  n%d -> n%d;\n", e.first, n);

	fprintf(f, "}\n");
}

static void handle_loops()
{
	// http://en.wikipedia.org/wiki/Topological_sorting
	// (Kahn, Arthur B. (1962), "Topological sorting of large networks")

	std::map<int, std::set<int>> edges;
	std::vector<int> in_edges_count(signal_list.size());
	std::set<int> workpool;

	FILE *dot_f = NULL;
	int dot_nr = 0;

	// uncomment for troubleshooting the loop detection code
	// dot_f = fopen("test.dot", "w");

	for (auto &g : signal_list) {
		if (g.type == -1) {
			workpool.insert(g.id);
		}
		if (g.in1 >= 0) {
			edges[g.in1].insert(g.id);
			in_edges_count[g.id]++;
		}
		if (g.in2 >= 0 && g.in2 != g.in1) {
			edges[g.in2].insert(g.id);
			in_edges_count[g.id]++;
		}
		if (g.in3 >= 0 && g.in3 != g.in2 && g.in3 != g.in1) {
			edges[g.in3].insert(g.id);
			in_edges_count[g.id]++;
		}
	}

	dump_loop_graph(dot_f, dot_nr, edges, workpool, in_edges_count);

	while (workpool.size() > 0)
	{
		int id = *workpool.begin();
		workpool.erase(id);

		// log("Removing non-loop node %d from graph: %s\n", id, log_signal(signal_list[id].sig));

		for (int id2 : edges[id]) {
			assert(in_edges_count[id2] > 0);
			if (--in_edges_count[id2] == 0)
				workpool.insert(id2);
		}
		edges.erase(id);

		dump_loop_graph(dot_f, dot_nr, edges, workpool, in_edges_count);

		while (workpool.size() == 0)
		{
			if (edges.size() == 0)
				break;

			int id1 = edges.begin()->first;

			for (auto &edge_it : edges) {
				int id2 = edge_it.first;
				RTLIL::Wire *w1 = signal_list[id1].sig.chunks[0].wire;
				RTLIL::Wire *w2 = signal_list[id2].sig.chunks[0].wire;
				if (w1 != NULL)
					continue;
				else if (w2 == NULL)
					id1 = id2;
				else if (w1->name[0] == '$' && w2->name[0] == '\\')
					id1 = id2;
				else if (w1->name[0] == '\\' && w2->name[0] == '$')
					continue;
				else if (edges[id1].size() < edges[id2].size())
					id1 = id2;
				else if (edges[id1].size() > edges[id2].size())
					continue;
				else if (w1->name > w2->name)
					id1 = id2;
			}

			if (edges[id1].size() == 0) {
				edges.erase(id1);
				continue;
			}

			RTLIL::Wire *wire = new RTLIL::Wire;
			std::stringstream sstr;
			sstr << "$abcloop$" << (RTLIL::autoidx++);
			wire->name = sstr.str();
			module->wires[wire->name] = wire;

			bool first_line = true;
			for (int id2 : edges[id1]) {
				if (first_line)
					log("Breaking loop using new signal %s: %s -> %s\n", log_signal(RTLIL::SigSpec(wire)),
							log_signal(signal_list[id1].sig), log_signal(signal_list[id2].sig));
				else
					log("                               %*s  %s -> %s\n", int(strlen(log_signal(RTLIL::SigSpec(wire)))), "",
							log_signal(signal_list[id1].sig), log_signal(signal_list[id2].sig));
				first_line = false;
			}

			int id3 = map_signal(RTLIL::SigSpec(wire));
			signal_list[id1].is_port = true;
			signal_list[id3].is_port = true;
			assert(id3 == int(in_edges_count.size()));
			in_edges_count.push_back(0);
			workpool.insert(id3);

			for (int id2 : edges[id1]) {
				if (signal_list[id2].in1 == id1)
					signal_list[id2].in1 = id3;
				if (signal_list[id2].in2 == id1)
					signal_list[id2].in2 = id3;
				if (signal_list[id2].in3 == id1)
					signal_list[id2].in3 = id3;
			}
			edges[id1].swap(edges[id3]);

			module->connections.push_back(RTLIL::SigSig(signal_list[id3].sig, signal_list[id1].sig));
			dump_loop_graph(dot_f, dot_nr, edges, workpool, in_edges_count);
		}
	}

	if (dot_f != NULL)
		fclose(dot_f);
}

static void abc_module(RTLIL::Design *design, RTLIL::Module *current_module, std::string script_file, std::string exe_file, std::string liberty_file, std::string constr_file, bool cleanup, int lut_mode)
{
	module = current_module;
	map_autoidx = RTLIL::autoidx++;

	signal_map.clear();
	signal_list.clear();
	assign_map.set(module);

	char tempdir_name[] = "/tmp/yosys-abc-XXXXXX";
	if (!cleanup)
		tempdir_name[0] = tempdir_name[4] = '_';
	char *p = mkdtemp(tempdir_name);
	log_header("Extracting gate netlist of module `%s' to `%s/input.v'..\n", module->name.c_str(), tempdir_name);
	if (p == NULL)
		log_error("For some reason mkdtemp() failed!\n");

	std::vector<RTLIL::Cell*> cells;
	cells.reserve(module->cells.size());
	for (auto &it : module->cells)
		if (design->selected(current_module, it.second))
			cells.push_back(it.second);
	for (auto c : cells)
		extract_cell(c);

	for (auto &wire_it : module->wires) {
		if (wire_it.second->port_id > 0)
			mark_port(RTLIL::SigSpec(wire_it.second));
	}

	for (auto &cell_it : module->cells)
	for (auto &port_it : cell_it.second->connections)
		mark_port(port_it.second);
	
	handle_loops();

	if (asprintf(&p, "%s/input.v", tempdir_name) < 0) abort();
	FILE *f = fopen(p, "wt");
	if (f == NULL)
		log_error("Opening %s for writing failed: %s\n", p, strerror(errno));
	free(p);

	fprintf(f, "module netlist (");
	bool first = true;
	for (auto &si : signal_list) {
		if (!si.is_port)
			continue;
		if (!first)
			fprintf(f, ", ");
		fprintf(f, "n%d", si.id);
		first = false;
	}
	fprintf(f, "); // %s\n", module->name.c_str());

	int count_input = 0, count_output = 0;
	for (auto &si : signal_list) {
		if (si.is_port) {
			if (si.type >= 0)
				count_output++;
			else
				count_input++;
		}
		fprintf(f, "%s n%d; // %s\n", si.is_port ? si.type >= 0 ?
				"output" : "input" : "wire", si.id, log_signal(si.sig));
	}
	for (auto &si : signal_list) {
		assert(si.sig.width == 1 && si.sig.chunks.size() == 1);
		if (si.sig.chunks[0].wire == NULL)
			fprintf(f, "assign n%d = %c;\n", si.id, si.sig.chunks[0].data.bits[0] == RTLIL::State::S1 ? '1' : '0');
	}

	int count_gates = 0;
	for (auto &si : signal_list) {
		if (si.type == 'n')
			fprintf(f, "not (n%d, n%d);\n", si.id, si.in1);
		else if (si.type == 'a')
			fprintf(f, "and (n%d, n%d, n%d);\n", si.id, si.in1, si.in2);
		else if (si.type == 'o')
			fprintf(f, "or (n%d, n%d, n%d);\n", si.id, si.in1, si.in2);
		else if (si.type == 'x')
			fprintf(f, "xor (n%d, n%d, n%d);\n", si.id, si.in1, si.in2);
		else if (si.type == 'm')
			fprintf(f, "assign n%d = n%d ? n%d : n%d;\n", si.id, si.in3, si.in2, si.in1);
		else if (si.type >= 0)
			abort();
		if (si.type >= 0)
			count_gates++;
	}

	fprintf(f, "endmodule\n");
	fclose(f);

	log("Extracted %d gates and %zd wires to a netlist network with %d inputs and %d outputs.\n",
			count_gates, signal_list.size(), count_input, count_output);
	log_push();
	
	if (count_output > 0)
	{
		log_header("Executing ABC.\n");

		if (asprintf(&p, "%s/stdcells.genlib", tempdir_name) < 0) abort();
		f = fopen(p, "wt");
		if (f == NULL)
			log_error("Opening %s for writing failed: %s\n", p, strerror(errno));
		fprintf(f, "GATE ZERO 1 Y=CONST0;\n");
		fprintf(f, "GATE ONE  1 Y=CONST1;\n");
		fprintf(f, "GATE BUF  1 Y=A;                  PIN * NONINV  1 999 1 0 1 0\n");
		fprintf(f, "GATE INV  1 Y=!A;                 PIN * INV     1 999 1 0 1 0\n");
		fprintf(f, "GATE AND  1 Y=A*B;                PIN * NONINV  1 999 1 0 1 0\n");
		fprintf(f, "GATE OR   1 Y=A+B;                PIN * NONINV  1 999 1 0 1 0\n");
		fprintf(f, "GATE XOR  1 Y=(A*!B)+(!A*B);      PIN * UNKNOWN 1 999 1 0 1 0\n");
		fprintf(f, "GATE MUX  1 Y=(A*B)+(S*B)+(!S*A); PIN * UNKNOWN 1 999 1 0 1 0\n");
		fclose(f);
		free(p);

		if (lut_mode) {
			if (asprintf(&p, "%s/lutdefs.txt", tempdir_name) < 0) abort();
			f = fopen(p, "wt");
			if (f == NULL)
				log_error("Opening %s for writing failed: %s\n", p, strerror(errno));
			for (int i = 0; i < lut_mode; i++)
				fprintf(f, "%d 1.00 1.00\n", i+1);
			fclose(f);
			free(p);
		}

		char buffer[1024];
		int buffer_pos = 0;
		if (!liberty_file.empty()) {
			buffer_pos += snprintf(buffer+buffer_pos, 1024-buffer_pos,
					"%s -s -c 'read_verilog %s/input.v; read_lib %s; ",
					exe_file.c_str(), tempdir_name, liberty_file.c_str());
			if (!constr_file.empty())
				buffer_pos += snprintf(buffer+buffer_pos, 1024-buffer_pos,
						"read_constr %s; ", constr_file.c_str());
			buffer_pos += snprintf(buffer+buffer_pos, 1024-buffer_pos,
					"strash; balance; dch; map; topo; ");
			if (!constr_file.empty())
				buffer_pos += snprintf(buffer+buffer_pos, 1024-buffer_pos,
						"buffer; upsize; dnsize; stime; ");
		} else
		if (!script_file.empty())
			buffer_pos += snprintf(buffer+buffer_pos, 1024-buffer_pos,
					"%s -s -c 'read_verilog %s/input.v; source %s; ",
					exe_file.c_str(), tempdir_name, script_file.c_str());
		else
		if (lut_mode)
			buffer_pos += snprintf(buffer+buffer_pos, 1024-buffer_pos,
					"%s -s -c 'read_verilog %s/input.v; read_lut %s/lutdefs.txt; strash; balance; dch; if; ",
					exe_file.c_str(), tempdir_name, tempdir_name);
		else
			buffer_pos += snprintf(buffer+buffer_pos, 1024-buffer_pos,
					"%s -s -c 'read_verilog %s/input.v; read_library %s/stdcells.genlib; strash; balance; dch; map; ",
					exe_file.c_str(), tempdir_name, tempdir_name);
		buffer_pos += snprintf(buffer+buffer_pos, 1024-buffer_pos, "write_blif %s/output.blif' 2>&1", tempdir_name);

		errno = ENOMEM;  // popen does not set errno if memory allocation fails, therefore set it by hand
		f = popen(buffer, "r");
		if (f == NULL)
			log_error("Opening pipe to `%s' for reading failed: %s\n", buffer, strerror(errno));
		while (fgets(buffer, 1024, f) != NULL)
			log("ABC: %s", buffer);
		errno = 0;
		int ret = pclose(f);
		if (ret < 0)
			log_error("Closing pipe to `%s' failed: %s\n", buffer, strerror(errno));
		if (WEXITSTATUS(ret) != 0) {
			switch (WEXITSTATUS(ret)) {
				case 127: log_error("ABC: execution of command \"%s\" failed: Command not found\n", exe_file.c_str()); break;
				case 126: log_error("ABC: execution of command \"%s\" failed: Command not executable\n", exe_file.c_str()); break;
				default:  log_error("ABC: execution of command \"%s\" failed: the shell returned %d\n", exe_file.c_str(), WEXITSTATUS(ret)); break;
			}
		}

		if (asprintf(&p, "%s/%s", tempdir_name, "output.blif") < 0) log_abort();
		f = fopen(p, "rt");
		if (f == NULL)
			log_error("Can't open ABC output file `%s'.\n", p);

		RTLIL::Design *mapped_design = abc_parse_blif(f);

		fclose(f);
		free(p);

		log_header("Re-integrating ABC results.\n");
		RTLIL::Module *mapped_mod = mapped_design->modules["\\netlist"];
		if (mapped_mod == NULL)
			log_error("ABC output file does not contain a module `netlist'.\n");
		for (auto &it : mapped_mod->wires) {
			RTLIL::Wire *w = it.second;
			RTLIL::Wire *wire = new RTLIL::Wire;
			wire->name = remap_name(w->name);
			module->wires[wire->name] = wire;
			design->select(module, wire);
		}

		std::map<std::string, int> cell_stats;
		if (liberty_file.empty() && script_file.empty() && !lut_mode)
		{
			for (auto &it : mapped_mod->cells) {
				RTLIL::Cell *c = it.second;
				cell_stats[c->type.substr(1)]++;
				if (c->type == "\\ZERO" || c->type == "\\ONE") {
					RTLIL::SigSig conn;
					conn.first = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\Y"].chunks[0].wire->name)]);
					conn.second = RTLIL::SigSpec(c->type == "\\ZERO" ? 0 : 1, 1);
					module->connections.push_back(conn);
					continue;
				}
				if (c->type == "\\BUF") {
					RTLIL::SigSig conn;
					conn.first = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\Y"].chunks[0].wire->name)]);
					conn.second = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\A"].chunks[0].wire->name)]);
					module->connections.push_back(conn);
					continue;
				}
				if (c->type == "\\INV") {
					RTLIL::Cell *cell = new RTLIL::Cell;
					cell->type = "$_INV_";
					cell->name = remap_name(c->name);
					cell->connections["\\A"] = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\A"].chunks[0].wire->name)]);
					cell->connections["\\Y"] = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\Y"].chunks[0].wire->name)]);
					module->cells[cell->name] = cell;
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\AND" || c->type == "\\OR" || c->type == "\\XOR") {
					RTLIL::Cell *cell = new RTLIL::Cell;
					cell->type = "$_" + c->type.substr(1) + "_";
					cell->name = remap_name(c->name);
					cell->connections["\\A"] = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\A"].chunks[0].wire->name)]);
					cell->connections["\\B"] = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\B"].chunks[0].wire->name)]);
					cell->connections["\\Y"] = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\Y"].chunks[0].wire->name)]);
					module->cells[cell->name] = cell;
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\MUX") {
					RTLIL::Cell *cell = new RTLIL::Cell;
					cell->type = "$_MUX_";
					cell->name = remap_name(c->name);
					cell->connections["\\A"] = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\A"].chunks[0].wire->name)]);
					cell->connections["\\B"] = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\B"].chunks[0].wire->name)]);
					cell->connections["\\S"] = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\S"].chunks[0].wire->name)]);
					cell->connections["\\Y"] = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\Y"].chunks[0].wire->name)]);
					module->cells[cell->name] = cell;
					design->select(module, cell);
					continue;
				}
				assert(0);
			}
		}
		else
		{
			for (auto &it : mapped_mod->cells) {
				RTLIL::Cell *c = it.second;
				cell_stats[c->type.substr(1)]++;
				if (c->type == "$_const0_" || c->type == "$_const1_") {
					RTLIL::SigSig conn;
					conn.first = RTLIL::SigSpec(module->wires[remap_name(c->connections["\\Y"].chunks[0].wire->name)]);
					conn.second = RTLIL::SigSpec(c->type == "$_const0_" ? 0 : 1, 1);
					module->connections.push_back(conn);
					continue;
				}
				RTLIL::Cell *cell = new RTLIL::Cell;
				cell->type = c->type;
				cell->parameters = c->parameters;
				cell->name = remap_name(c->name);
				for (auto &conn : c->connections) {
					RTLIL::SigSpec newsig;
					for (auto &c : conn.second.chunks) {
						if (c.width == 0)
							continue;
						assert(c.width == 1);
						newsig.append(module->wires[remap_name(c.wire->name)]);
					}
					cell->connections[conn.first] = newsig;
				}
				module->cells[cell->name] = cell;
				design->select(module, cell);
			}
		}

		for (auto conn : mapped_mod->connections) {
			if (!conn.first.is_fully_const())
				conn.first = RTLIL::SigSpec(module->wires[remap_name(conn.first.chunks[0].wire->name)]);
			if (!conn.second.is_fully_const())
				conn.second = RTLIL::SigSpec(module->wires[remap_name(conn.second.chunks[0].wire->name)]);
			module->connections.push_back(conn);
		}

		for (auto &it : cell_stats)
			log("ABC RESULTS:   %15s cells: %8d\n", it.first.c_str(), it.second);
		int in_wires = 0, out_wires = 0;
		for (auto &si : signal_list)
			if (si.is_port) {
				char buffer[100];
				snprintf(buffer, 100, "\\n%d", si.id);
				RTLIL::SigSig conn;
				if (si.type >= 0) {
					conn.first = si.sig;
					conn.second = RTLIL::SigSpec(module->wires[remap_name(buffer)]);
					out_wires++;
				} else {
					conn.first = RTLIL::SigSpec(module->wires[remap_name(buffer)]);
					conn.second = si.sig;
					in_wires++;
				}
				module->connections.push_back(conn);
			}
		log("ABC RESULTS:        internal signals: %8d\n", int(signal_list.size()) - in_wires - out_wires);
		log("ABC RESULTS:           input signals: %8d\n", in_wires);
		log("ABC RESULTS:          output signals: %8d\n", out_wires);

		delete mapped_design;
	}
	else
	{
		log("Don't call ABC as there is nothing to map.\n");
	}

	if (cleanup)
	{
		log_header("Removing temp directory `%s':\n", tempdir_name);

		struct dirent **namelist;
		int n = scandir(tempdir_name, &namelist, 0, alphasort);
		assert(n >= 0);
		for (int i = 0; i < n; i++) {
			if (strcmp(namelist[i]->d_name, ".") && strcmp(namelist[i]->d_name, "..")) {
				if (asprintf(&p, "%s/%s", tempdir_name, namelist[i]->d_name) < 0) abort();
				log("Removing `%s'.\n", p);
				remove(p);
				free(p);
			}
			free(namelist[i]);
		}
		free(namelist);
		log("Removing `%s'.\n", tempdir_name);
		rmdir(tempdir_name);
	}

	log_pop();
}

struct AbcPass : public Pass {
	AbcPass() : Pass("abc", "use ABC for technology mapping") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc [options] [selection]\n");
		log("\n");
		log("This pass uses the ABC tool [1] for technology mapping of yosys's internal gate\n");
		log("library to a target architecture.\n");
		log("\n");
		log("    -exe <command>\n");
		log("        use the specified command name instead of \"yosys-abc\" to execute ABC.\n");
		log("        This can e.g. be used to call a specific version of ABC or a wrapper.\n");
		log("\n");
		log("    -script <file>\n");
		log("        use the specified ABC script file instead of the default script.\n");
		log("\n");
		log("    -liberty <file>\n");
		log("        generate netlists for the specified cell library (using the liberty\n");
		log("        file format). Without this option, ABC is used to optimize the netlist\n");
		log("        but keeps using yosys's internal gate library. This option is ignored if\n");
		log("        the -script option is also used.\n");
		log("\n");
		log("    -constr <file>\n");
		log("        pass this file with timing constraints to ABC\n");
		log("\n");
		log("    -lut <width>\n");
		log("        generate netlist using luts of (max) the specified width.\n");
		log("\n");
		log("    -nocleanup\n");
		log("        when this option is used, the temporary files created by this pass\n");
		log("        are not removed. this is useful for debugging.\n");
		log("\n");
		log("This pass does not operate on modules with unprocessed processes in it.\n");
		log("(I.e. the 'proc' pass should be used first to convert processes to netlists.)\n");
		log("\n");
		log("[1] http://www.eecs.berkeley.edu/~alanmi/abc/\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing ABC pass (technology mapping using ABC).\n");
		log_push();

		std::string exe_file = rewrite_yosys_exe("yosys-abc");
		std::string script_file, liberty_file, constr_file;
		bool cleanup = true;
		int lut_mode = 0;

		size_t argidx;
		char *pwd = get_current_dir_name();
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-exe" && argidx+1 < args.size()) {
				exe_file = args[++argidx];
				continue;
			}
			if (arg == "-script" && argidx+1 < args.size() && liberty_file.empty() && constr_file.empty()) {
				script_file = args[++argidx];
				if (!script_file.empty() && script_file[0] != '/')
					script_file = std::string(pwd) + "/" + script_file;
				continue;
			}
			if (arg == "-liberty" && argidx+1 < args.size() && script_file.empty() && liberty_file.empty()) {
				liberty_file = args[++argidx];
				if (!liberty_file.empty() && liberty_file[0] != '/')
					liberty_file = std::string(pwd) + "/" + liberty_file;
				continue;
			}
			if (arg == "-constr" && argidx+1 < args.size() && script_file.empty() && constr_file.empty()) {
				constr_file = args[++argidx];
				if (!constr_file.empty() && constr_file[0] != '/')
					constr_file = std::string(pwd) + "/" + constr_file;
				continue;
			}
			if (arg == "-lut" && argidx+1 < args.size() && lut_mode == 0) {
				lut_mode = atoi(args[++argidx].c_str());
				continue;
			}
			if (arg == "-nocleanup") {
				cleanup = false;
				continue;
			}
			break;
		}
		free(pwd);
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules)
			if (design->selected(mod_it.second)) {
				if (mod_it.second->processes.size() > 0)
					log("Skipping module %s as it contains processes.\n", mod_it.second->name.c_str());
				else
					abc_module(design, mod_it.second, script_file, exe_file, liberty_file, constr_file, cleanup, lut_mode);
			}

		assign_map.clear();
		signal_list.clear();
		signal_map.clear();

		log_pop();
	}
} AbcPass;
 
