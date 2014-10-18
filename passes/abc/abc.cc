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

// [[CITE]] Berkeley Logic Interchange Format (BLIF)
// University of California. Berkeley. July 28, 1992
// http://www.ece.cmu.edu/~ee760/760docs/blif.pdf

// [[CITE]] Kahn's Topological sorting algorithm
// Kahn, Arthur B. (1962), "Topological sorting of large networks", Communications of the ACM 5 (11): 558–562, doi:10.1145/368996.369025
// http://en.wikipedia.org/wiki/Topological_sorting

#define ABC_COMMAND_LIB "strash; scorr -v; ifraig -v; retime -v {D}; strash; dch -vf; map -v {D}"
#define ABC_COMMAND_CTR "strash; scorr -v; ifraig -v; retime -v {D}; strash; dch -vf; map -v {D}; buffer -v; upsize -v {D}; dnsize -v {D}; stime -p"
#define ABC_COMMAND_LUT "strash; scorr -v; ifraig -v; retime -v; strash; dch -vf; if -v"
#define ABC_COMMAND_DFL "strash; scorr -v; ifraig -v; retime -v; strash; dch -vf; map -v"

#define ABC_FAST_COMMAND_LIB "retime -v {D}; map -v {D}"
#define ABC_FAST_COMMAND_CTR "retime -v {D}; map -v {D}; buffer -v; upsize -v {D}; dnsize -v {D}; stime -p"
#define ABC_FAST_COMMAND_LUT "retime -v; if -v"
#define ABC_FAST_COMMAND_DFL "retime -v; map -v"

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/cost.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <cerrno>
#include <sstream>
#include <climits>

#ifndef _WIN32
#  include <unistd.h>
#  include <dirent.h>
#endif

#include "blifparse.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

enum class gate_type_t {
	G_NONE,
	G_FF,
	G_BUF,
	G_NOT,
	G_AND,
	G_NAND,
	G_OR,
	G_NOR,
	G_XOR,
	G_XNOR,
	G_MUX,
	G_AOI3,
	G_OAI3,
	G_AOI4,
	G_OAI4
};

#define G(_name) gate_type_t::G_ ## _name

struct gate_t
{
	int id;
	gate_type_t type;
	int in1, in2, in3, in4;
	bool is_port;
	RTLIL::SigBit bit;
};

int map_autoidx;
SigMap assign_map;
RTLIL::Module *module;
std::vector<gate_t> signal_list;
std::map<RTLIL::SigBit, int> signal_map;

bool clk_polarity;
RTLIL::SigSpec clk_sig;

int map_signal(RTLIL::SigBit bit, gate_type_t gate_type = G(NONE), int in1 = -1, int in2 = -1, int in3 = -1, int in4 = -1)
{
	assign_map.apply(bit);

	if (signal_map.count(bit) == 0) {
		gate_t gate;
		gate.id = signal_list.size();
		gate.type = G(NONE);
		gate.in1 = -1;
		gate.in2 = -1;
		gate.in3 = -1;
		gate.in4 = -1;
		gate.is_port = false;
		gate.bit = bit;
		signal_list.push_back(gate);
		signal_map[bit] = gate.id;
	}

	gate_t &gate = signal_list[signal_map[bit]];

	if (gate_type != G(NONE))
		gate.type = gate_type;
	if (in1 >= 0)
		gate.in1 = in1;
	if (in2 >= 0)
		gate.in2 = in2;
	if (in3 >= 0)
		gate.in3 = in3;
	if (in4 >= 0)
		gate.in4 = in4;

	return gate.id;
}

void mark_port(RTLIL::SigSpec sig)
{
	for (auto &bit : assign_map(sig))
		if (bit.wire != NULL && signal_map.count(bit) > 0)
			signal_list[signal_map[bit]].is_port = true;
}

void extract_cell(RTLIL::Cell *cell, bool keepff)
{
	if (cell->type == "$_DFF_N_" || cell->type == "$_DFF_P_")
	{
		if (clk_polarity != (cell->type == "$_DFF_P_"))
			return;
		if (clk_sig != assign_map(cell->getPort("\\C")))
			return;

		RTLIL::SigSpec sig_d = cell->getPort("\\D");
		RTLIL::SigSpec sig_q = cell->getPort("\\Q");

		if (keepff)
			for (auto &c : sig_q.chunks())
				if (c.wire != NULL)
					c.wire->attributes["\\keep"] = 1;

		assign_map.apply(sig_d);
		assign_map.apply(sig_q);

		map_signal(sig_q, G(FF), map_signal(sig_d));

		module->remove(cell);
		return;
	}

	if (cell->type.in("$_BUF_", "$_NOT_"))
	{
		RTLIL::SigSpec sig_a = cell->getPort("\\A");
		RTLIL::SigSpec sig_y = cell->getPort("\\Y");

		assign_map.apply(sig_a);
		assign_map.apply(sig_y);

		map_signal(sig_y, cell->type == "$_BUF_" ? G(BUF) : G(NOT), map_signal(sig_a));

		module->remove(cell);
		return;
	}

	if (cell->type.in("$_AND_", "$_NAND_", "$_OR_", "$_NOR_", "$_XOR_", "$_XNOR_"))
	{
		RTLIL::SigSpec sig_a = cell->getPort("\\A");
		RTLIL::SigSpec sig_b = cell->getPort("\\B");
		RTLIL::SigSpec sig_y = cell->getPort("\\Y");

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);

		if (cell->type == "$_AND_")
			map_signal(sig_y, G(AND), mapped_a, mapped_b);
		else if (cell->type == "$_NAND_")
			map_signal(sig_y, G(NAND), mapped_a, mapped_b);
		else if (cell->type == "$_OR_")
			map_signal(sig_y, G(OR), mapped_a, mapped_b);
		else if (cell->type == "$_NOR_")
			map_signal(sig_y, G(NOR), mapped_a, mapped_b);
		else if (cell->type == "$_XOR_")
			map_signal(sig_y, G(XOR), mapped_a, mapped_b);
		else if (cell->type == "$_XNOR_")
			map_signal(sig_y, G(XNOR), mapped_a, mapped_b);
		else
			log_abort();

		module->remove(cell);
		return;
	}

	if (cell->type == "$_MUX_")
	{
		RTLIL::SigSpec sig_a = cell->getPort("\\A");
		RTLIL::SigSpec sig_b = cell->getPort("\\B");
		RTLIL::SigSpec sig_s = cell->getPort("\\S");
		RTLIL::SigSpec sig_y = cell->getPort("\\Y");

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_s);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);
		int mapped_s = map_signal(sig_s);

		map_signal(sig_y, G(MUX), mapped_a, mapped_b, mapped_s);

		module->remove(cell);
		return;
	}

	if (cell->type.in("$_AOI3_", "$_OAI3_"))
	{
		RTLIL::SigSpec sig_a = cell->getPort("\\A");
		RTLIL::SigSpec sig_b = cell->getPort("\\B");
		RTLIL::SigSpec sig_c = cell->getPort("\\C");
		RTLIL::SigSpec sig_y = cell->getPort("\\Y");

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_c);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);
		int mapped_c = map_signal(sig_c);

		map_signal(sig_y, cell->type == "$_AOI3_" ? G(AOI3) : G(OAI3), mapped_a, mapped_b, mapped_c);

		module->remove(cell);
		return;
	}

	if (cell->type.in("$_AOI4_", "$_OAI4_"))
	{
		RTLIL::SigSpec sig_a = cell->getPort("\\A");
		RTLIL::SigSpec sig_b = cell->getPort("\\B");
		RTLIL::SigSpec sig_c = cell->getPort("\\C");
		RTLIL::SigSpec sig_d = cell->getPort("\\D");
		RTLIL::SigSpec sig_y = cell->getPort("\\Y");

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_c);
		assign_map.apply(sig_d);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);
		int mapped_c = map_signal(sig_c);
		int mapped_d = map_signal(sig_d);

		map_signal(sig_y, cell->type == "$_AOI4_" ? G(AOI4) : G(OAI4), mapped_a, mapped_b, mapped_c, mapped_d);

		module->remove(cell);
		return;
	}
}

std::string remap_name(RTLIL::IdString abc_name)
{
	std::stringstream sstr;
	sstr << "$abc$" << map_autoidx << "$" << abc_name.substr(1);
	return sstr.str();
}

void dump_loop_graph(FILE *f, int &nr, std::map<int, std::set<int>> &edges, std::set<int> &workpool, std::vector<int> &in_counts)
{
	if (f == NULL)
		return;

	log("Dumping loop state graph to slide %d.\n", ++nr);

	fprintf(f, "digraph \"slide%d\" {\n", nr);
	fprintf(f, "  label=\"slide%d\";\n", nr);
	fprintf(f, "  rankdir=\"TD\";\n");

	std::set<int> nodes;
	for (auto &e : edges) {
		nodes.insert(e.first);
		for (auto n : e.second)
			nodes.insert(n);
	}

	for (auto n : nodes)
		fprintf(f, "  n%d [label=\"%s\\nid=%d, count=%d\"%s];\n", n, log_signal(signal_list[n].bit),
				n, in_counts[n], workpool.count(n) ? ", shape=box" : "");

	for (auto &e : edges)
	for (auto n : e.second)
		fprintf(f, "  n%d -> n%d;\n", e.first, n);

	fprintf(f, "}\n");
}

void handle_loops()
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
		if (g.type == G(NONE) || g.type == G(FF)) {
			workpool.insert(g.id);
		} else {
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
			if (g.in4 >= 0 && g.in4 != g.in3 && g.in4 != g.in2 && g.in4 != g.in1) {
				edges[g.in4].insert(g.id);
				in_edges_count[g.id]++;
			}
		}
	}

	dump_loop_graph(dot_f, dot_nr, edges, workpool, in_edges_count);

	while (workpool.size() > 0)
	{
		int id = *workpool.begin();
		workpool.erase(id);

		// log("Removing non-loop node %d from graph: %s\n", id, log_signal(signal_list[id].bit));

		for (int id2 : edges[id]) {
			log_assert(in_edges_count[id2] > 0);
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
				RTLIL::Wire *w1 = signal_list[id1].bit.wire;
				RTLIL::Wire *w2 = signal_list[id2].bit.wire;
				if (w1 == NULL)
					id1 = id2;
				else if (w2 == NULL)
					continue;
				else if (w1->name[0] == '$' && w2->name[0] == '\\')
					id1 = id2;
				else if (w1->name[0] == '\\' && w2->name[0] == '$')
					continue;
				else if (edges[id1].size() < edges[id2].size())
					id1 = id2;
				else if (edges[id1].size() > edges[id2].size())
					continue;
				else if (w2->name.str() < w1->name.str())
					id1 = id2;
			}

			if (edges[id1].size() == 0) {
				edges.erase(id1);
				continue;
			}

			log_assert(signal_list[id1].bit.wire != NULL);

			std::stringstream sstr;
			sstr << "$abcloop$" << (autoidx++);
			RTLIL::Wire *wire = module->addWire(sstr.str());

			bool first_line = true;
			for (int id2 : edges[id1]) {
				if (first_line)
					log("Breaking loop using new signal %s: %s -> %s\n", log_signal(RTLIL::SigSpec(wire)),
							log_signal(signal_list[id1].bit), log_signal(signal_list[id2].bit));
				else
					log("                               %*s  %s -> %s\n", int(strlen(log_signal(RTLIL::SigSpec(wire)))), "",
							log_signal(signal_list[id1].bit), log_signal(signal_list[id2].bit));
				first_line = false;
			}

			int id3 = map_signal(RTLIL::SigSpec(wire));
			signal_list[id1].is_port = true;
			signal_list[id3].is_port = true;
			log_assert(id3 == int(in_edges_count.size()));
			in_edges_count.push_back(0);
			workpool.insert(id3);

			for (int id2 : edges[id1]) {
				if (signal_list[id2].in1 == id1)
					signal_list[id2].in1 = id3;
				if (signal_list[id2].in2 == id1)
					signal_list[id2].in2 = id3;
				if (signal_list[id2].in3 == id1)
					signal_list[id2].in3 = id3;
				if (signal_list[id2].in4 == id1)
					signal_list[id2].in4 = id3;
			}
			edges[id1].swap(edges[id3]);

			module->connect(RTLIL::SigSig(signal_list[id3].bit, signal_list[id1].bit));
			dump_loop_graph(dot_f, dot_nr, edges, workpool, in_edges_count);
		}
	}

	if (dot_f != NULL)
		fclose(dot_f);
}

std::string add_echos_to_abc_cmd(std::string str)
{
	std::string new_str, token;
	for (size_t i = 0; i < str.size(); i++) {
		token += str[i];
		if (str[i] == ';') {
			while (i+1 < str.size() && str[i+1] == ' ')
				i++;
			if (!new_str.empty())
				new_str += "echo; ";
			new_str += "echo + " + token + " " + token + " ";
			token.clear();
		}
	}

	if (!token.empty()) {
		if (!new_str.empty())
			new_str += "echo; echo + " + token + "; ";
		new_str += token;
	}

	return new_str;
}

std::string fold_abc_cmd(std::string str)
{
	std::string token, new_str = "          ";
	int char_counter = 10;

	for (size_t i = 0; i <= str.size(); i++) {
		if (i < str.size())
			token += str[i];
		if (i == str.size() || str[i] == ';') {
			if (char_counter + token.size() > 75)
				new_str += "\n              ", char_counter = 14;
			new_str += token, char_counter += token.size();
			token.clear();
		}
	}

	return new_str;
}

struct abc_output_filter
{
	bool got_cr;
	int escape_seq_state;
	std::string linebuf;

	abc_output_filter()
	{
		got_cr = false;
		escape_seq_state = 0;
	}

	void next_char(char ch)
	{
		if (escape_seq_state == 0 && ch == '\033') {
			escape_seq_state = 1;
			return;
		}
		if (escape_seq_state == 1) {
			escape_seq_state = ch == '[' ? 2 : 0;
			return;
		}
		if (escape_seq_state == 2) {
			if ((ch < '0' || '9' < ch) && ch != ';')
				escape_seq_state = 0;
			return;
		}
		escape_seq_state = 0;
		if (ch == '\r') {
			got_cr = true;
			return;
		}
		if (ch == '\n') {
			log("ABC: %s\n", linebuf.c_str());
			got_cr = false, linebuf.clear();
			return;
		}
		if (got_cr)
			got_cr = false, linebuf.clear();
		linebuf += ch;
	}

	void next_line(const std::string &line)
	{
		for (char ch : line)
			next_char(ch);
	}
};

void abc_module(RTLIL::Design *design, RTLIL::Module *current_module, std::string script_file, std::string exe_file,
		std::string liberty_file, std::string constr_file, bool cleanup, int lut_mode, bool dff_mode, std::string clk_str,
		bool keepff, std::string delay_target, bool fast_mode)
{
	module = current_module;
	map_autoidx = autoidx++;

	signal_map.clear();
	signal_list.clear();
	assign_map.set(module);

	clk_polarity = true;
	clk_sig = RTLIL::SigSpec();

	std::string tempdir_name = "/tmp/yosys-abc-XXXXXX";
	if (!cleanup)
		tempdir_name[0] = tempdir_name[4] = '_';
	tempdir_name = make_temp_dir(tempdir_name);
	log_header("Extracting gate netlist of module `%s' to `%s/input.blif'..\n", module->name.c_str(), tempdir_name.c_str());

	std::string abc_script = stringf("read_blif %s/input.blif; ", tempdir_name.c_str());

	if (!liberty_file.empty()) {
		abc_script += stringf("read_lib -w %s; ", liberty_file.c_str());
		if (!constr_file.empty())
			abc_script += stringf("read_constr -v %s; ", constr_file.c_str());
	} else
	if (lut_mode)
		abc_script += stringf("read_lut %s/lutdefs.txt; ", tempdir_name.c_str());
	else
		abc_script += stringf("read_library %s/stdcells.genlib; ", tempdir_name.c_str());

	if (!script_file.empty()) {
		if (script_file[0] == '+') {
			for (size_t i = 1; i < script_file.size(); i++)
				if (script_file[i] == '\'')
					abc_script += "'\\''";
				else if (script_file[i] == ',')
					abc_script += " ";
				else
					abc_script += script_file[i];
		} else
			abc_script += stringf("source %s", script_file.c_str());
	} else if (lut_mode)
		abc_script += fast_mode ? ABC_FAST_COMMAND_LUT : ABC_COMMAND_LUT;
	else if (!liberty_file.empty())
		abc_script += constr_file.empty() ? (fast_mode ? ABC_FAST_COMMAND_LIB : ABC_COMMAND_LIB) : (fast_mode ? ABC_FAST_COMMAND_CTR : ABC_COMMAND_CTR);
	else
		abc_script += fast_mode ? ABC_FAST_COMMAND_DFL : ABC_COMMAND_DFL;

	for (size_t pos = abc_script.find("{D}"); pos != std::string::npos; pos = abc_script.find("{D}", pos))
		abc_script = abc_script.substr(0, pos) + delay_target + abc_script.substr(pos+3);

	abc_script += stringf("; write_blif %s/output.blif", tempdir_name.c_str());
	abc_script = add_echos_to_abc_cmd(abc_script);

	for (size_t i = 0; i+1 < abc_script.size(); i++)
		if (abc_script[i] == ';' && abc_script[i+1] == ' ')
			abc_script[i+1] = '\n';

	FILE *f = fopen(stringf("%s/abc.script", tempdir_name.c_str()).c_str(), "wt");
	fprintf(f, "%s\n", abc_script.c_str());
	fclose(f);

	if (clk_str.empty()) {
		if (clk_str[0] == '!') {
			clk_polarity = false;
			clk_str = clk_str.substr(1);
		}
		if (module->wires_.count(RTLIL::escape_id(clk_str)) != 0)
			clk_sig = assign_map(RTLIL::SigSpec(module->wires_.at(RTLIL::escape_id(clk_str)), 0));
	}

	if (dff_mode && clk_sig.size() == 0)
	{
		int best_dff_counter = 0;
		std::map<std::pair<bool, RTLIL::SigSpec>, int> dff_counters;

		for (auto &it : module->cells_)
		{
			RTLIL::Cell *cell = it.second;
			if (cell->type != "$_DFF_N_" && cell->type != "$_DFF_P_")
				continue;

			std::pair<bool, RTLIL::SigSpec> key(cell->type == "$_DFF_P_", assign_map(cell->getPort("\\C")));
			if (++dff_counters[key] > best_dff_counter) {
				best_dff_counter = dff_counters[key];
				clk_polarity = key.first;
				clk_sig = key.second;
			}
		}
	}

	if (dff_mode || !clk_str.empty()) {
		if (clk_sig.size() == 0)
			log("No (matching) clock domain found. Not extracting any FF cells.\n");
		else
			log("Found (matching) %s clock domain: %s\n", clk_polarity ? "posedge" : "negedge", log_signal(clk_sig));
	}

	if (clk_sig.size() != 0)
		mark_port(clk_sig);

	std::vector<RTLIL::Cell*> cells;
	cells.reserve(module->cells_.size());
	for (auto &it : module->cells_)
		if (design->selected(current_module, it.second))
			cells.push_back(it.second);
	for (auto c : cells)
		extract_cell(c, keepff);

	for (auto &wire_it : module->wires_) {
		if (wire_it.second->port_id > 0 || wire_it.second->get_bool_attribute("\\keep"))
			mark_port(RTLIL::SigSpec(wire_it.second));
	}

	for (auto &cell_it : module->cells_)
	for (auto &port_it : cell_it.second->connections())
		mark_port(port_it.second);
	
	handle_loops();

	std::string buffer = stringf("%s/input.blif", tempdir_name.c_str());
	f = fopen(buffer.c_str(), "wt");
	if (f == NULL)
		log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));

	fprintf(f, ".model netlist\n");

	int count_input = 0;
	fprintf(f, ".inputs");
	for (auto &si : signal_list) {
		if (!si.is_port || si.type != G(NONE))
			continue;
		fprintf(f, " n%d", si.id);
		count_input++;
	}
	if (count_input == 0)
		fprintf(f, " dummy_input\n");
	fprintf(f, "\n");

	int count_output = 0;
	fprintf(f, ".outputs");
	for (auto &si : signal_list) {
		if (!si.is_port || si.type == G(NONE))
			continue;
		fprintf(f, " n%d", si.id);
		count_output++;
	}
	fprintf(f, "\n");

	for (auto &si : signal_list)
		fprintf(f, "# n%-5d %s\n", si.id, log_signal(si.bit));

	for (auto &si : signal_list) {
		if (si.bit.wire == NULL) {
			fprintf(f, ".names n%d\n", si.id);
			if (si.bit == RTLIL::State::S1)
				fprintf(f, "1\n");
		}
	}

	int count_gates = 0;
	for (auto &si : signal_list) {
		if (si.type == G(BUF)) {
			fprintf(f, ".names n%d n%d\n", si.in1, si.id);
			fprintf(f, "1 1\n");
		} else if (si.type == G(NOT)) {
			fprintf(f, ".names n%d n%d\n", si.in1, si.id);
			fprintf(f, "0 1\n");
		} else if (si.type == G(AND)) {
			fprintf(f, ".names n%d n%d n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "11 1\n");
		} else if (si.type == G(NAND)) {
			fprintf(f, ".names n%d n%d n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "0- 1\n");
			fprintf(f, "-0 1\n");
		} else if (si.type == G(OR)) {
			fprintf(f, ".names n%d n%d n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "-1 1\n");
			fprintf(f, "1- 1\n");
		} else if (si.type == G(NOR)) {
			fprintf(f, ".names n%d n%d n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "00 1\n");
		} else if (si.type == G(XOR)) {
			fprintf(f, ".names n%d n%d n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "01 1\n");
			fprintf(f, "10 1\n");
		} else if (si.type == G(XNOR)) {
			fprintf(f, ".names n%d n%d n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "00 1\n");
			fprintf(f, "11 1\n");
		} else if (si.type == G(MUX)) {
			fprintf(f, ".names n%d n%d n%d n%d\n", si.in1, si.in2, si.in3, si.id);
			fprintf(f, "1-0 1\n");
			fprintf(f, "-11 1\n");
		} else if (si.type == G(AOI3)) {
			fprintf(f, ".names n%d n%d n%d n%d\n", si.in1, si.in2, si.in3, si.id);
			fprintf(f, "-00 1\n");
			fprintf(f, "0-0 1\n");
		} else if (si.type == G(OAI3)) {
			fprintf(f, ".names n%d n%d n%d n%d\n", si.in1, si.in2, si.in3, si.id);
			fprintf(f, "00- 1\n");
			fprintf(f, "--0 1\n");
		} else if (si.type == G(AOI4)) {
			fprintf(f, ".names n%d n%d n%d n%d n%d\n", si.in1, si.in2, si.in3, si.in4, si.id);
			fprintf(f, "-0-0 1\n");
			fprintf(f, "-00- 1\n");
			fprintf(f, "0--0 1\n");
			fprintf(f, "0-0- 1\n");
		} else if (si.type == G(OAI4)) {
			fprintf(f, ".names n%d n%d n%d n%d n%d\n", si.in1, si.in2, si.in3, si.in4, si.id);
			fprintf(f, "00-- 1\n");
			fprintf(f, "--00 1\n");
		} else if (si.type == G(FF)) {
			fprintf(f, ".latch n%d n%d\n", si.in1, si.id);
		} else if (si.type != G(NONE))
			log_abort();
		if (si.type != G(NONE))
			count_gates++;
	}

	fprintf(f, ".end\n");
	fclose(f);

	log("Extracted %d gates and %d wires to a netlist network with %d inputs and %d outputs.\n",
			count_gates, GetSize(signal_list), count_input, count_output);
	log_push();
	
	if (count_output > 0)
	{
		log_header("Executing ABC.\n");

		buffer = stringf("%s/stdcells.genlib", tempdir_name.c_str());
		f = fopen(buffer.c_str(), "wt");
		if (f == NULL)
			log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));
		fprintf(f, "GATE ZERO  1 Y=CONST0;\n");
		fprintf(f, "GATE ONE   1 Y=CONST1;\n");
		fprintf(f, "GATE BUF  %d Y=A;                  PIN * NONINV  1 999 1 0 1 0\n", get_cell_cost("$_BUF_"));
		fprintf(f, "GATE NOT  %d Y=!A;                 PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_NOT_"));
		fprintf(f, "GATE AND  %d Y=A*B;                PIN * NONINV  1 999 1 0 1 0\n", get_cell_cost("$_AND_"));
		fprintf(f, "GATE NAND %d Y=!(A*B);             PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_NAND_"));
		fprintf(f, "GATE OR   %d Y=A+B;                PIN * NONINV  1 999 1 0 1 0\n", get_cell_cost("$_OR_"));
		fprintf(f, "GATE NOR  %d Y=!(A+B);             PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_NOR_"));
		fprintf(f, "GATE XOR  %d Y=(A*!B)+(!A*B);      PIN * UNKNOWN 1 999 1 0 1 0\n", get_cell_cost("$_XOR_"));
		fprintf(f, "GATE XNOR %d Y=(A*B)+(!A*!B);      PIN * UNKNOWN 1 999 1 0 1 0\n", get_cell_cost("$_XNOR_"));
		fprintf(f, "GATE AOI3 %d Y=!((A*B)+C);         PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_AOI3_"));
		fprintf(f, "GATE OAI3 %d Y=!((A+B)*C);         PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_OAI3_"));
		fprintf(f, "GATE AOI4 %d Y=!((A*B)+(C*D));     PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_AOI4_"));
		fprintf(f, "GATE OAI4 %d Y=!((A+B)*(C+D));     PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_OAI4_"));
		fprintf(f, "GATE MUX  %d Y=(A*B)+(S*B)+(!S*A); PIN * UNKNOWN 1 999 1 0 1 0\n", get_cell_cost("$_MUX_"));
		fclose(f);

		if (lut_mode) {
			buffer = stringf("%s/lutdefs.txt", tempdir_name.c_str());
			f = fopen(buffer.c_str(), "wt");
			if (f == NULL)
				log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));
			for (int i = 0; i < lut_mode; i++)
				fprintf(f, "%d 1.00 1.00\n", i+1);
			fclose(f);
		}

		buffer = stringf("%s -s -f %s/abc.script 2>&1", exe_file.c_str(), tempdir_name.c_str());
		log("Running ABC command: %s\n", buffer.c_str());

		abc_output_filter filt;
		int ret = run_command(buffer, std::bind(&abc_output_filter::next_line, filt, std::placeholders::_1));
		if (ret != 0)
			log_error("ABC: execution of command \"%s\" failed: return code %d.\n", buffer.c_str(), ret);

		buffer = stringf("%s/%s", tempdir_name.c_str(), "output.blif");
		f = fopen(buffer.c_str(), "rt");
		if (f == NULL)
			log_error("Can't open ABC output file `%s'.\n", buffer.c_str());

		bool builtin_lib = liberty_file.empty() && script_file.empty() && !lut_mode;
		RTLIL::Design *mapped_design = abc_parse_blif(f, builtin_lib ? "\\DFF" : "\\_dff_");

		fclose(f);

		log_header("Re-integrating ABC results.\n");
		RTLIL::Module *mapped_mod = mapped_design->modules_["\\netlist"];
		if (mapped_mod == NULL)
			log_error("ABC output file does not contain a module `netlist'.\n");
		for (auto &it : mapped_mod->wires_) {
			RTLIL::Wire *w = it.second;
			RTLIL::Wire *wire = module->addWire(remap_name(w->name));
			design->select(module, wire);
		}

		std::map<std::string, int> cell_stats;
		if (builtin_lib)
		{
			for (auto &it : mapped_mod->cells_) {
				RTLIL::Cell *c = it.second;
				cell_stats[RTLIL::unescape_id(c->type)]++;
				if (c->type == "\\ZERO" || c->type == "\\ONE") {
					RTLIL::SigSig conn;
					conn.first = RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]);
					conn.second = RTLIL::SigSpec(c->type == "\\ZERO" ? 0 : 1, 1);
					module->connect(conn);
					continue;
				}
				if (c->type == "\\BUF") {
					RTLIL::SigSig conn;
					conn.first = RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]);
					conn.second = RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]);
					module->connect(conn);
					continue;
				}
				if (c->type == "\\NOT") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_NOT_");
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\AND" || c->type == "\\OR" || c->type == "\\XOR" || c->type == "\\NAND" || c->type == "\\NOR" || c->type == "\\XNOR") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_" + c->type.substr(1) + "_");
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\MUX") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_MUX_");
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\S", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\S").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\AOI3" || c->type == "\\OAI3") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_" + c->type.substr(1) + "_");
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\C", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\C").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\AOI4" || c->type == "\\OAI4") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_" + c->type.substr(1) + "_");
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\C", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\C").as_wire()->name)]));
					cell->setPort("\\D", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\D").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\DFF") {
					log_assert(clk_sig.size() == 1);
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), clk_polarity ? "$_DFF_P_" : "$_DFF_N_");
					cell->setPort("\\D", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\D").as_wire()->name)]));
					cell->setPort("\\Q", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Q").as_wire()->name)]));
					cell->setPort("\\C", clk_sig);
					design->select(module, cell);
					continue;
				}
				log_abort();
			}
		}
		else
		{
			for (auto &it : mapped_mod->cells_)
			{
				RTLIL::Cell *c = it.second;
				cell_stats[RTLIL::unescape_id(c->type)]++;
				if (c->type == "\\_const0_" || c->type == "\\_const1_") {
					RTLIL::SigSig conn;
					conn.first = RTLIL::SigSpec(module->wires_[remap_name(c->connections().begin()->second.as_wire()->name)]);
					conn.second = RTLIL::SigSpec(c->type == "\\_const0_" ? 0 : 1, 1);
					module->connect(conn);
					continue;
				}
				if (c->type == "\\_dff_") {
					log_assert(clk_sig.size() == 1);
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), clk_polarity ? "$_DFF_P_" : "$_DFF_N_");
					cell->setPort("\\D", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\D").as_wire()->name)]));
					cell->setPort("\\Q", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Q").as_wire()->name)]));
					cell->setPort("\\C", clk_sig);
					design->select(module, cell);
					continue;
				}
				RTLIL::Cell *cell = module->addCell(remap_name(c->name), c->type);
				cell->parameters = c->parameters;
				for (auto &conn : c->connections()) {
					RTLIL::SigSpec newsig;
					for (auto &c : conn.second.chunks()) {
						if (c.width == 0)
							continue;
						log_assert(c.width == 1);
						newsig.append(module->wires_[remap_name(c.wire->name)]);
					}
					cell->setPort(conn.first, newsig);
				}
				design->select(module, cell);
			}
		}

		for (auto conn : mapped_mod->connections()) {
			if (!conn.first.is_fully_const())
				conn.first = RTLIL::SigSpec(module->wires_[remap_name(conn.first.as_wire()->name)]);
			if (!conn.second.is_fully_const())
				conn.second = RTLIL::SigSpec(module->wires_[remap_name(conn.second.as_wire()->name)]);
			module->connect(conn);
		}

		for (auto &it : cell_stats)
			log("ABC RESULTS:   %15s cells: %8d\n", it.first.c_str(), it.second);
		int in_wires = 0, out_wires = 0;
		for (auto &si : signal_list)
			if (si.is_port) {
				char buffer[100];
				snprintf(buffer, 100, "\\n%d", si.id);
				RTLIL::SigSig conn;
				if (si.type != G(NONE)) {
					conn.first = si.bit;
					conn.second = RTLIL::SigSpec(module->wires_[remap_name(buffer)]);
					out_wires++;
				} else {
					conn.first = RTLIL::SigSpec(module->wires_[remap_name(buffer)]);
					conn.second = si.bit;
					in_wires++;
				}
				module->connect(conn);
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
		log_header("Removing temp directory `%s':\n", tempdir_name.c_str());
		remove_directory(tempdir_name);
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
		log("        if <file> starts with a plus sign (+), then the rest of the filename\n");
		log("        string is interprated as the command string to be passed to ABC. the\n");
		log("        leading plus sign is removed and all commas (,) in the string are\n");
		log("        replaced with blanks before the string is passed to ABC.\n");
		log("\n");
		log("        if no -script parameter is given, the following scripts are used:\n");
		log("\n");
		log("        for -liberty without -constr:\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_LIB).c_str());
		log("\n");
		log("        for -liberty with -constr:\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_CTR).c_str());
		log("\n");
		log("        for -lut:\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_LUT).c_str());
		log("\n");
		log("        otherwise:\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_DFL).c_str());
		log("\n");
		log("    -fast\n");
		log("        use different default scripts that are slightly faster (at the cost\n");
		log("        of output quality):\n");
		log("\n");
		log("        for -liberty without -constr:\n");
		log("%s\n", fold_abc_cmd(ABC_FAST_COMMAND_LIB).c_str());
		log("\n");
		log("        for -liberty with -constr:\n");
		log("%s\n", fold_abc_cmd(ABC_FAST_COMMAND_CTR).c_str());
		log("\n");
		log("        for -lut:\n");
		log("%s\n", fold_abc_cmd(ABC_FAST_COMMAND_LUT).c_str());
		log("\n");
		log("        otherwise:\n");
		log("%s\n", fold_abc_cmd(ABC_FAST_COMMAND_DFL).c_str());
		log("\n");
		log("    -liberty <file>\n");
		log("        generate netlists for the specified cell library (using the liberty\n");
		log("        file format).\n");
		log("\n");
		log("    -constr <file>\n");
		log("        pass this file with timing constraints to ABC. use with -liberty.\n");
		log("\n");
		log("        a constr file contains two lines:\n");
		log("            set_driving_cell <cell_name>\n");
		log("            set_load <floating_point_number>\n");
		log("\n");
		log("        the set_driving_cell statement defines which cell type is assumed to\n");
		log("        drive the primary inputs and the set_load statement sets the load in\n");
		log("        femtofarads for each primary output.\n");
		log("\n");
		log("    -D <picoseconds>\n");
		log("        set delay target. the string {D} in the default scripts above is\n");
		log("        replaced by this option when used, and an empty string otherwise.\n");
		log("\n");
		log("    -lut <width>\n");
		log("        generate netlist using luts of (max) the specified width.\n");
		log("\n");
		log("    -dff\n");
		log("        also pass $_DFF_?_ cells through ABC (only one clock domain, if many\n");
		log("        clock domains are present in a module, the one with the largest number\n");
		log("        of $_DFF_?_ cells in it is used)\n");
		log("\n");
		log("    -clk [!]<signal-name>\n");
		log("        use the specified clock domain. (when this option is used in combination\n");
		log("        with -dff, then it falls back to the automatic dection of clock domain\n");
		log("        if the specified clock is not found in a module.)\n");
		log("\n");
		log("    -keepff\n");
		log("        set the \"keep\" attribute on flip-flop output wires. (and thus preserve\n");
		log("        them, for example for equivialence checking.)\n");
		log("\n");
		log("    -nocleanup\n");
		log("        when this option is used, the temporary files created by this pass\n");
		log("        are not removed. this is useful for debugging.\n");
		log("\n");
		log("When neither -liberty nor -lut is used, the Yosys standard cell library is\n");
		log("loaded into ABC before the ABC script is executed.\n");
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

		std::string exe_file = proc_self_dirname() + "yosys-abc";
		std::string script_file, liberty_file, constr_file, clk_str, delay_target;
		bool fast_mode = false, dff_mode = false, keepff = false, cleanup = true;
		int lut_mode = 0;

#ifdef _WIN32
		if (!check_file_exists(exe_file + ".exe") && check_file_exists(proc_self_dirname() + "..\\yosys-abc.exe"))
			exe_file = proc_self_dirname() + "..\\yosys-abc";
#endif

		size_t argidx;
		char pwd [PATH_MAX];
		if (!getcwd(pwd, sizeof(pwd))) {
			log_cmd_error("getcwd failed: %s\n", strerror(errno));
			log_abort();
		}
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-exe" && argidx+1 < args.size()) {
				exe_file = args[++argidx];
				continue;
			}
			if (arg == "-script" && argidx+1 < args.size()) {
				script_file = args[++argidx];
				if (!script_file.empty() && script_file[0] != '/' && script_file[0] != '+')
					script_file = std::string(pwd) + "/" + script_file;
				continue;
			}
			if (arg == "-liberty" && argidx+1 < args.size()) {
				liberty_file = args[++argidx];
				if (!liberty_file.empty() && liberty_file[0] != '/')
					liberty_file = std::string(pwd) + "/" + liberty_file;
				continue;
			}
			if (arg == "-constr" && argidx+1 < args.size()) {
				constr_file = args[++argidx];
				if (!constr_file.empty() && constr_file[0] != '/')
					constr_file = std::string(pwd) + "/" + constr_file;
				continue;
			}
			if (arg == "-D" && argidx+1 < args.size()) {
				delay_target = "-D " + args[++argidx];
				continue;
			}
			if (arg == "-lut" && argidx+1 < args.size()) {
				lut_mode = atoi(args[++argidx].c_str());
				continue;
			}
			if (arg == "-fast") {
				fast_mode = true;
				continue;
			}
			if (arg == "-dff") {
				dff_mode = true;
				continue;
			}
			if (arg == "-clk" && argidx+1 < args.size()) {
				clk_str = args[++argidx];
				continue;
			}
			if (arg == "-keepff") {
				keepff = true;
				continue;
			}
			if (arg == "-nocleanup") {
				cleanup = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (lut_mode != 0 && !liberty_file.empty())
			log_cmd_error("Got -lut and -liberty! This two options are exclusive.\n");
		if (!constr_file.empty() && liberty_file.empty())
			log_cmd_error("Got -constr but no -liberty!\n");

		for (auto &mod_it : design->modules_)
			if (design->selected(mod_it.second)) {
				if (mod_it.second->processes.size() > 0)
					log("Skipping module %s as it contains processes.\n", mod_it.second->name.c_str());
				else
					abc_module(design, mod_it.second, script_file, exe_file, liberty_file, constr_file, cleanup, lut_mode, dff_mode, clk_str, keepff, delay_target, fast_mode);
			}

		assign_map.clear();
		signal_list.clear();
		signal_map.clear();

		log_pop();
	}
} AbcPass;
 
PRIVATE_NAMESPACE_END
