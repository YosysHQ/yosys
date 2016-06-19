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
// Kahn, Arthur B. (1962), "Topological sorting of large networks", Communications of the ACM 5 (11): 558-562, doi:10.1145/368996.369025
// http://en.wikipedia.org/wiki/Topological_sorting

#define ABC_COMMAND_LIB "strash; dc2; scorr; ifraig; retime -o {D}; strash; dch -f; map {D}"
#define ABC_COMMAND_CTR "strash; dc2; scorr; ifraig; retime -o {D}; strash; dch -f; map {D}; buffer; upsize {D}; dnsize {D}; stime -p"
#define ABC_COMMAND_LUT "strash; dc2; scorr; ifraig; retime -o; strash; dch -f; if; mfs"
#define ABC_COMMAND_SOP "strash; dc2; scorr; ifraig; retime -o; strash; dch -f; cover {I} {P}"
#define ABC_COMMAND_DFL "strash; dc2; scorr; ifraig; retime -o; strash; dch -f; map"

#define ABC_FAST_COMMAND_LIB "retime -o {D}; map {D}"
#define ABC_FAST_COMMAND_CTR "retime -o {D}; map {D}; buffer; upsize {D}; dnsize {D}; stime -p"
#define ABC_FAST_COMMAND_LUT "retime -o; if"
#define ABC_FAST_COMMAND_SOP "retime -o; cover -I {I} -P {P}"
#define ABC_FAST_COMMAND_DFL "retime -o; map"

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
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

#include "frontends/blif/blifparse.h"

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

bool map_mux4;
bool map_mux8;
bool map_mux16;

bool markgroups;
int map_autoidx;
SigMap assign_map;
RTLIL::Module *module;
std::vector<gate_t> signal_list;
std::map<RTLIL::SigBit, int> signal_map;
pool<std::string> enabled_gates;

bool clk_polarity, en_polarity;
RTLIL::SigSpec clk_sig, en_sig;

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
		if (GetSize(en_sig) != 0)
			return;
		goto matching_dff;
	}

	if (cell->type == "$_DFFE_NN_" || cell->type == "$_DFFE_NP_" || cell->type == "$_DFFE_PN_" || cell->type == "$_DFFE_PP_")
	{
		if (clk_polarity != (cell->type == "$_DFFE_PN_" || cell->type == "$_DFFE_PP_"))
			return;
		if (en_polarity != (cell->type == "$_DFFE_NP_" || cell->type == "$_DFFE_PP_"))
			return;
		if (clk_sig != assign_map(cell->getPort("\\C")))
			return;
		if (en_sig != assign_map(cell->getPort("\\E")))
			return;
		goto matching_dff;
	}

	if (0) {
	matching_dff:
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
			new_str += "echo + " + token + " " + token + " ";
			token.clear();
		}
	}

	if (!token.empty()) {
		if (!new_str.empty())
			new_str += "echo + " + token + "; ";
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

std::string replace_tempdir(std::string text, std::string tempdir_name, bool show_tempdir)
{
	if (show_tempdir)
		return text;

	while (1) {
		size_t pos = text.find(tempdir_name);
		if (pos == std::string::npos)
			break;
		text = text.substr(0, pos) + "<abc-temp-dir>" + text.substr(pos + GetSize(tempdir_name));
	}

	std::string  selfdir_name = proc_self_dirname();
	while (1) {
		size_t pos = text.find(selfdir_name);
		if (pos == std::string::npos)
			break;
		text = text.substr(0, pos) + "<yosys-exe-dir>/" + text.substr(pos + GetSize(selfdir_name));
	}

	return text;
}

struct abc_output_filter
{
	bool got_cr;
	int escape_seq_state;
	std::string linebuf;
	std::string tempdir_name;
	bool show_tempdir;

	abc_output_filter(std::string tempdir_name, bool show_tempdir) : tempdir_name(tempdir_name), show_tempdir(show_tempdir)
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
			log("ABC: %s\n", replace_tempdir(linebuf, tempdir_name, show_tempdir).c_str());
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
		std::string liberty_file, std::string constr_file, bool cleanup, vector<int> lut_costs, bool dff_mode, std::string clk_str,
		bool keepff, std::string delay_target, std::string sop_inputs, std::string sop_products, bool fast_mode,
		const std::vector<RTLIL::Cell*> &cells, bool show_tempdir, bool sop_mode)
{
	module = current_module;
	map_autoidx = autoidx++;

	signal_map.clear();
	signal_list.clear();

	if (clk_str != "$")
	{
		assign_map.set(module);

		clk_polarity = true;
		clk_sig = RTLIL::SigSpec();

		en_polarity = true;
		en_sig = RTLIL::SigSpec();
	}

	std::string tempdir_name = "/tmp/yosys-abc-XXXXXX";
	if (!cleanup)
		tempdir_name[0] = tempdir_name[4] = '_';
	tempdir_name = make_temp_dir(tempdir_name);
	log_header(design, "Extracting gate netlist of module `%s' to `%s/input.blif'..\n",
			module->name.c_str(), replace_tempdir(tempdir_name, tempdir_name, show_tempdir).c_str());

	std::string abc_script = stringf("read_blif %s/input.blif; ", tempdir_name.c_str());

	if (!liberty_file.empty()) {
		abc_script += stringf("read_lib -w %s; ", liberty_file.c_str());
		if (!constr_file.empty())
			abc_script += stringf("read_constr -v %s; ", constr_file.c_str());
	} else
	if (!lut_costs.empty())
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
	} else if (!lut_costs.empty()) {
		bool all_luts_cost_same = true;
		for (int this_cost : lut_costs)
			if (this_cost != lut_costs.front())
				all_luts_cost_same = false;
		abc_script += fast_mode ? ABC_FAST_COMMAND_LUT : ABC_COMMAND_LUT;
		if (all_luts_cost_same && !fast_mode)
			abc_script += "; lutpack";
	} else if (!liberty_file.empty())
		abc_script += constr_file.empty() ? (fast_mode ? ABC_FAST_COMMAND_LIB : ABC_COMMAND_LIB) : (fast_mode ? ABC_FAST_COMMAND_CTR : ABC_COMMAND_CTR);
	else if (sop_mode)
		abc_script += fast_mode ? ABC_FAST_COMMAND_SOP : ABC_COMMAND_SOP;
	else
		abc_script += fast_mode ? ABC_FAST_COMMAND_DFL : ABC_COMMAND_DFL;

	for (size_t pos = abc_script.find("{D}"); pos != std::string::npos; pos = abc_script.find("{D}", pos))
		abc_script = abc_script.substr(0, pos) + delay_target + abc_script.substr(pos+3);

	for (size_t pos = abc_script.find("{I}"); pos != std::string::npos; pos = abc_script.find("{D}", pos))
		abc_script = abc_script.substr(0, pos) + sop_inputs + abc_script.substr(pos+3);

	for (size_t pos = abc_script.find("{P}"); pos != std::string::npos; pos = abc_script.find("{D}", pos))
		abc_script = abc_script.substr(0, pos) + sop_products + abc_script.substr(pos+3);

	abc_script += stringf("; write_blif %s/output.blif", tempdir_name.c_str());
	abc_script = add_echos_to_abc_cmd(abc_script);

	for (size_t i = 0; i+1 < abc_script.size(); i++)
		if (abc_script[i] == ';' && abc_script[i+1] == ' ')
			abc_script[i+1] = '\n';

	FILE *f = fopen(stringf("%s/abc.script", tempdir_name.c_str()).c_str(), "wt");
	fprintf(f, "%s\n", abc_script.c_str());
	fclose(f);

	if (!clk_str.empty() && clk_str != "$")
	{
		if (clk_str.find(',') != std::string::npos) {
			int pos = clk_str.find(',');
			std::string en_str = clk_str.substr(pos+1);
			clk_str = clk_str.substr(0, pos);
			if (en_str[0] == '!') {
				en_polarity = false;
				en_str = en_str.substr(1);
			}
			if (module->wires_.count(RTLIL::escape_id(en_str)) != 0)
				en_sig = assign_map(RTLIL::SigSpec(module->wires_.at(RTLIL::escape_id(en_str)), 0));
		}
		if (clk_str[0] == '!') {
			clk_polarity = false;
			clk_str = clk_str.substr(1);
		}
		if (module->wires_.count(RTLIL::escape_id(clk_str)) != 0)
			clk_sig = assign_map(RTLIL::SigSpec(module->wires_.at(RTLIL::escape_id(clk_str)), 0));
	}

	if (dff_mode && clk_sig.empty())
		log_error("Clock domain %s not found.\n", clk_str.c_str());

	if (dff_mode || !clk_str.empty())
	{
		if (clk_sig.size() == 0)
			log("No%s clock domain found. Not extracting any FF cells.\n", clk_str.empty() ? "" : " matching");
		else {
			log("Found%s %s clock domain: %s", clk_str.empty() ? "" : " matching", clk_polarity ? "posedge" : "negedge", log_signal(clk_sig));
			if (en_sig.size() != 0)
				log(", enabled by %s%s", en_polarity ? "" : "!", log_signal(en_sig));
			log("\n");
		}
	}

	for (auto c : cells)
		extract_cell(c, keepff);

	for (auto &wire_it : module->wires_) {
		if (wire_it.second->port_id > 0 || wire_it.second->get_bool_attribute("\\keep"))
			mark_port(RTLIL::SigSpec(wire_it.second));
	}

	for (auto &cell_it : module->cells_)
	for (auto &port_it : cell_it.second->connections())
		mark_port(port_it.second);

	if (clk_sig.size() != 0)
		mark_port(clk_sig);

	if (en_sig.size() != 0)
		mark_port(en_sig);

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
		log_header(design, "Executing ABC.\n");

		buffer = stringf("%s/stdcells.genlib", tempdir_name.c_str());
		f = fopen(buffer.c_str(), "wt");
		if (f == NULL)
			log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));
		fprintf(f, "GATE ZERO  1 Y=CONST0;\n");
		fprintf(f, "GATE ONE   1 Y=CONST1;\n");
		fprintf(f, "GATE BUF  %d Y=A;                  PIN * NONINV  1 999 1 0 1 0\n", get_cell_cost("$_BUF_"));
		fprintf(f, "GATE NOT  %d Y=!A;                 PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_NOT_"));
		if (enabled_gates.empty() || enabled_gates.count("AND"))
			fprintf(f, "GATE AND  %d Y=A*B;                PIN * NONINV  1 999 1 0 1 0\n", get_cell_cost("$_AND_"));
		if (enabled_gates.empty() || enabled_gates.count("NAND"))
			fprintf(f, "GATE NAND %d Y=!(A*B);             PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_NAND_"));
		if (enabled_gates.empty() || enabled_gates.count("OR"))
			fprintf(f, "GATE OR   %d Y=A+B;                PIN * NONINV  1 999 1 0 1 0\n", get_cell_cost("$_OR_"));
		if (enabled_gates.empty() || enabled_gates.count("NOR"))
			fprintf(f, "GATE NOR  %d Y=!(A+B);             PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_NOR_"));
		if (enabled_gates.empty() || enabled_gates.count("XOR"))
			fprintf(f, "GATE XOR  %d Y=(A*!B)+(!A*B);      PIN * UNKNOWN 1 999 1 0 1 0\n", get_cell_cost("$_XOR_"));
		if (enabled_gates.empty() || enabled_gates.count("XNOR"))
			fprintf(f, "GATE XNOR %d Y=(A*B)+(!A*!B);      PIN * UNKNOWN 1 999 1 0 1 0\n", get_cell_cost("$_XNOR_"));
		if (enabled_gates.empty() || enabled_gates.count("AOI3"))
			fprintf(f, "GATE AOI3 %d Y=!((A*B)+C);         PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_AOI3_"));
		if (enabled_gates.empty() || enabled_gates.count("OAI3"))
			fprintf(f, "GATE OAI3 %d Y=!((A+B)*C);         PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_OAI3_"));
		if (enabled_gates.empty() || enabled_gates.count("AOI4"))
			fprintf(f, "GATE AOI4 %d Y=!((A*B)+(C*D));     PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_AOI4_"));
		if (enabled_gates.empty() || enabled_gates.count("OAI4"))
			fprintf(f, "GATE OAI4 %d Y=!((A+B)*(C+D));     PIN * INV     1 999 1 0 1 0\n", get_cell_cost("$_OAI4_"));
		if (enabled_gates.empty() || enabled_gates.count("MUX"))
			fprintf(f, "GATE MUX  %d Y=(A*B)+(S*B)+(!S*A); PIN * UNKNOWN 1 999 1 0 1 0\n", get_cell_cost("$_MUX_"));
		if (map_mux4)
			fprintf(f, "GATE MUX4 %d Y=(!S*!T*A)+(S*!T*B)+(!S*T*C)+(S*T*D); PIN * UNKNOWN 1 999 1 0 1 0\n", 2*get_cell_cost("$_MUX_"));
		if (map_mux8)
			fprintf(f, "GATE MUX8 %d Y=(!S*!T*!U*A)+(S*!T*!U*B)+(!S*T*!U*C)+(S*T*!U*D)+(!S*!T*U*E)+(S*!T*U*F)+(!S*T*U*G)+(S*T*U*H); PIN * UNKNOWN 1 999 1 0 1 0\n", 4*get_cell_cost("$_MUX_"));
		if (map_mux16)
			fprintf(f, "GATE MUX16 %d Y=(!S*!T*!U*!V*A)+(S*!T*!U*!V*B)+(!S*T*!U*!V*C)+(S*T*!U*!V*D)+(!S*!T*U*!V*E)+(S*!T*U*!V*F)+(!S*T*U*!V*G)+(S*T*U*!V*H)+(!S*!T*!U*V*I)+(S*!T*!U*V*J)+(!S*T*!U*V*K)+(S*T*!U*V*L)+(!S*!T*U*V*M)+(S*!T*U*V*N)+(!S*T*U*V*O)+(S*T*U*V*P); PIN * UNKNOWN 1 999 1 0 1 0\n", 8*get_cell_cost("$_MUX_"));
		fclose(f);

		if (!lut_costs.empty()) {
			buffer = stringf("%s/lutdefs.txt", tempdir_name.c_str());
			f = fopen(buffer.c_str(), "wt");
			if (f == NULL)
				log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));
			for (int i = 0; i < GetSize(lut_costs); i++)
				fprintf(f, "%d %d.00 1.00\n", i+1, lut_costs.at(i));
			fclose(f);
		}

		buffer = stringf("%s -s -f %s/abc.script 2>&1", exe_file.c_str(), tempdir_name.c_str());
		log("Running ABC command: %s\n", replace_tempdir(buffer, tempdir_name, show_tempdir).c_str());

		abc_output_filter filt(tempdir_name, show_tempdir);
		int ret = run_command(buffer, std::bind(&abc_output_filter::next_line, filt, std::placeholders::_1));
		if (ret != 0)
			log_error("ABC: execution of command \"%s\" failed: return code %d.\n", buffer.c_str(), ret);

		buffer = stringf("%s/%s", tempdir_name.c_str(), "output.blif");
		std::ifstream ifs;
		ifs.open(buffer);
		if (ifs.fail())
			log_error("Can't open ABC output file `%s'.\n", buffer.c_str());

		bool builtin_lib = liberty_file.empty();
		RTLIL::Design *mapped_design = new RTLIL::Design;
		parse_blif(mapped_design, ifs, builtin_lib ? "\\DFF" : "\\_dff_", false, sop_mode);

		ifs.close();

		log_header(design, "Re-integrating ABC results.\n");
		RTLIL::Module *mapped_mod = mapped_design->modules_["\\netlist"];
		if (mapped_mod == NULL)
			log_error("ABC output file does not contain a module `netlist'.\n");
		for (auto &it : mapped_mod->wires_) {
			RTLIL::Wire *w = it.second;
			RTLIL::Wire *wire = module->addWire(remap_name(w->name));
			if (markgroups) wire->attributes["\\abcgroup"] = map_autoidx;
			design->select(module, wire);
		}

		std::map<std::string, int> cell_stats;
		for (auto c : mapped_mod->cells())
		{
			if (builtin_lib)
			{
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
					if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\AND" || c->type == "\\OR" || c->type == "\\XOR" || c->type == "\\NAND" || c->type == "\\NOR" || c->type == "\\XNOR") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_" + c->type.substr(1) + "_");
					if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\MUX") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_MUX_");
					if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\S", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\S").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\MUX4") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_MUX4_");
					if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\C", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\C").as_wire()->name)]));
					cell->setPort("\\D", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\D").as_wire()->name)]));
					cell->setPort("\\S", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\S").as_wire()->name)]));
					cell->setPort("\\T", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\T").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\MUX8") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_MUX8_");
					if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\C", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\C").as_wire()->name)]));
					cell->setPort("\\D", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\D").as_wire()->name)]));
					cell->setPort("\\E", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\E").as_wire()->name)]));
					cell->setPort("\\F", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\F").as_wire()->name)]));
					cell->setPort("\\G", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\G").as_wire()->name)]));
					cell->setPort("\\H", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\H").as_wire()->name)]));
					cell->setPort("\\S", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\S").as_wire()->name)]));
					cell->setPort("\\T", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\T").as_wire()->name)]));
					cell->setPort("\\U", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\U").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\MUX16") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_MUX16_");
					if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\C", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\C").as_wire()->name)]));
					cell->setPort("\\D", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\D").as_wire()->name)]));
					cell->setPort("\\E", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\E").as_wire()->name)]));
					cell->setPort("\\F", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\F").as_wire()->name)]));
					cell->setPort("\\G", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\G").as_wire()->name)]));
					cell->setPort("\\H", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\H").as_wire()->name)]));
					cell->setPort("\\I", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\I").as_wire()->name)]));
					cell->setPort("\\J", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\J").as_wire()->name)]));
					cell->setPort("\\K", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\K").as_wire()->name)]));
					cell->setPort("\\L", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\L").as_wire()->name)]));
					cell->setPort("\\M", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\M").as_wire()->name)]));
					cell->setPort("\\N", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\N").as_wire()->name)]));
					cell->setPort("\\O", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\O").as_wire()->name)]));
					cell->setPort("\\P", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\P").as_wire()->name)]));
					cell->setPort("\\S", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\S").as_wire()->name)]));
					cell->setPort("\\T", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\T").as_wire()->name)]));
					cell->setPort("\\U", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\U").as_wire()->name)]));
					cell->setPort("\\V", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\V").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\AOI3" || c->type == "\\OAI3") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_" + c->type.substr(1) + "_");
					if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
					cell->setPort("\\A", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\A").as_wire()->name)]));
					cell->setPort("\\B", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\B").as_wire()->name)]));
					cell->setPort("\\C", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\C").as_wire()->name)]));
					cell->setPort("\\Y", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)]));
					design->select(module, cell);
					continue;
				}
				if (c->type == "\\AOI4" || c->type == "\\OAI4") {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), "$_" + c->type.substr(1) + "_");
					if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
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
					RTLIL::Cell *cell;
					if (en_sig.size() == 0) {
						cell = module->addCell(remap_name(c->name), clk_polarity ? "$_DFF_P_" : "$_DFF_N_");
					} else {
						log_assert(en_sig.size() == 1);
						cell = module->addCell(remap_name(c->name), stringf("$_DFFE_%c%c_", clk_polarity ? 'P' : 'N', en_polarity ? 'P' : 'N'));
						cell->setPort("\\E", en_sig);
					}
					if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
					cell->setPort("\\D", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\D").as_wire()->name)]));
					cell->setPort("\\Q", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Q").as_wire()->name)]));
					cell->setPort("\\C", clk_sig);
					design->select(module, cell);
					continue;
				}
			}

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
				RTLIL::Cell *cell;
				if (en_sig.size() == 0) {
					cell = module->addCell(remap_name(c->name), clk_polarity ? "$_DFF_P_" : "$_DFF_N_");
				} else {
					log_assert(en_sig.size() == 1);
					cell = module->addCell(remap_name(c->name), stringf("$_DFFE_%c%c_", clk_polarity ? 'P' : 'N', en_polarity ? 'P' : 'N'));
					cell->setPort("\\E", en_sig);
				}
				if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
				cell->setPort("\\D", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\D").as_wire()->name)]));
				cell->setPort("\\Q", RTLIL::SigSpec(module->wires_[remap_name(c->getPort("\\Q").as_wire()->name)]));
				cell->setPort("\\C", clk_sig);
				design->select(module, cell);
				continue;
			}

			if (c->type == "$lut" && GetSize(c->getPort("\\A")) == 1 && c->getParam("\\LUT").as_int() == 2) {
				SigSpec my_a = module->wires_[remap_name(c->getPort("\\A").as_wire()->name)];
				SigSpec my_y = module->wires_[remap_name(c->getPort("\\Y").as_wire()->name)];
				module->connect(my_y, my_a);
				continue;
			}

			RTLIL::Cell *cell = module->addCell(remap_name(c->name), c->type);
			if (markgroups) cell->attributes["\\abcgroup"] = map_autoidx;
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
		log("Removing temp directory.\n");
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
#ifdef ABCEXTERNAL
		log("        use the specified command instead of \"" ABCEXTERNAL "\" to execute ABC.\n");
#else
		log("        use the specified command instead of \"<yosys-bindir>/yosys-abc\" to execute ABC.\n");
#endif
		log("        This can e.g. be used to call a specific version of ABC or a wrapper.\n");
		log("\n");
		log("    -script <file>\n");
		log("        use the specified ABC script file instead of the default script.\n");
		log("\n");
		log("        if <file> starts with a plus sign (+), then the rest of the filename\n");
		log("        string is interpreted as the command string to be passed to ABC. The\n");
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
		log("        for -lut/-luts (only one LUT size):\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_LUT "; lutpack").c_str());
		log("\n");
		log("        for -lut/-luts (different LUT sizes):\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_LUT).c_str());
		log("\n");
		log("        for -sop:\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_SOP).c_str());
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
		log("        for -lut/-luts:\n");
		log("%s\n", fold_abc_cmd(ABC_FAST_COMMAND_LUT).c_str());
		log("\n");
		log("        for -sop:\n");
		log("%s\n", fold_abc_cmd(ABC_FAST_COMMAND_SOP).c_str());
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
		log("    -I <num>\n");
		log("        maximum number of SOP inputs.\n");
		log("        (replaces {I} in the default scripts above)\n");
		log("\n");
		log("    -P <num>\n");
		log("        maximum number of SOP products.\n");
		log("        (replaces {P} in the default scripts above)\n");
		log("\n");
		log("    -lut <width>\n");
		log("        generate netlist using luts of (max) the specified width.\n");
		log("\n");
		log("    -lut <w1>:<w2>\n");
		log("        generate netlist using luts of (max) the specified width <w2>. All\n");
		log("        luts with width <= <w1> have constant cost. for luts larger than <w1>\n");
		log("        the area cost doubles with each additional input bit. the delay cost\n");
		log("        is still constant for all lut widths.\n");
		log("\n");
		log("    -luts <cost1>,<cost2>,<cost3>,<sizeN>:<cost4-N>,..\n");
		log("        generate netlist using luts. Use the specified costs for luts with 1,\n");
		log("        2, 3, .. inputs.\n");
		log("\n");
		log("    -sop\n");
		log("        map to sum-of-product cells and inverters\n");
		log("\n");
		// log("    -mux4, -mux8, -mux16\n");
		// log("        try to extract 4-input, 8-input, and/or 16-input muxes\n");
		// log("        (ignored when used with -liberty or -lut)\n");
		// log("\n");
		log("    -g type1,type2,...\n");
		log("        Map the the specified list of gate types. Supported gates types are:\n");
		log("        AND, NAND, OR, NOR, XOR, XNOR, MUX, AOI3, OAI3, AOI4, OAI4.\n");
		log("        (The NOT gate is always added to this list automatically.)\n");
		log("\n");
		log("    -dff\n");
		log("        also pass $_DFF_?_ and $_DFFE_??_ cells through ABC. modules with many\n");
		log("        clock domains are automatically partitioned in clock domains and each\n");
		log("        domain is passed through ABC independently.\n");
		log("\n");
		log("    -clk [!]<clock-signal-name>[,[!]<enable-signal-name>]\n");
		log("        use only the specified clock domain. this is like -dff, but only FF\n");
		log("        cells that belong to the specified clock domain are used.\n");
		log("\n");
		log("    -keepff\n");
		log("        set the \"keep\" attribute on flip-flop output wires. (and thus preserve\n");
		log("        them, for example for equivalence checking.)\n");
		log("\n");
		log("    -nocleanup\n");
		log("        when this option is used, the temporary files created by this pass\n");
		log("        are not removed. this is useful for debugging.\n");
		log("\n");
		log("    -showtmp\n");
		log("        print the temp dir name in log. usually this is suppressed so that the\n");
		log("        command output is identical across runs.\n");
		log("\n");
		log("    -markgroups\n");
		log("        set a 'abcgroup' attribute on all objects created by ABC. The value of\n");
		log("        this attribute is a unique integer for each ABC process started. This\n");
		log("        is useful for debugging the partitioning of clock domains.\n");
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
		log_header(design, "Executing ABC pass (technology mapping using ABC).\n");
		log_push();

#ifdef ABCEXTERNAL
		std::string exe_file = ABCEXTERNAL;
#else
		std::string exe_file = proc_self_dirname() + "yosys-abc";
#endif
		std::string script_file, liberty_file, constr_file, clk_str;
		std::string delay_target, sop_inputs, sop_products;
		bool fast_mode = false, dff_mode = false, keepff = false, cleanup = true;
		bool show_tempdir = false, sop_mode = false;
		vector<int> lut_costs;
		markgroups = false;

		map_mux4 = false;
		map_mux8 = false;
		map_mux16 = false;
		enabled_gates.clear();

#ifdef _WIN32
#ifndef ABCEXTERNAL
		if (!check_file_exists(exe_file + ".exe") && check_file_exists(proc_self_dirname() + "..\\yosys-abc.exe"))
			exe_file = proc_self_dirname() + "..\\yosys-abc";
#endif
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
				if (!script_file.empty() && !is_absolute_path(script_file) && script_file[0] != '+')
					script_file = std::string(pwd) + "/" + script_file;
				continue;
			}
			if (arg == "-liberty" && argidx+1 < args.size()) {
				liberty_file = args[++argidx];
				if (!liberty_file.empty() && !is_absolute_path(liberty_file))
					liberty_file = std::string(pwd) + "/" + liberty_file;
				continue;
			}
			if (arg == "-constr" && argidx+1 < args.size()) {
				constr_file = args[++argidx];
				if (!constr_file.empty() && !is_absolute_path(constr_file))
					constr_file = std::string(pwd) + "/" + constr_file;
				continue;
			}
			if (arg == "-D" && argidx+1 < args.size()) {
				delay_target = "-D " + args[++argidx];
				continue;
			}
			if (arg == "-I" && argidx+1 < args.size()) {
				sop_inputs = "-I " + args[++argidx];
				continue;
			}
			if (arg == "-P" && argidx+1 < args.size()) {
				sop_products = "-P " + args[++argidx];
				continue;
			}
			if (arg == "-lut" && argidx+1 < args.size()) {
				string arg = args[++argidx];
				size_t pos = arg.find_first_of(':');
				int lut_mode = 0, lut_mode2 = 0;
				if (pos != string::npos) {
					lut_mode = atoi(arg.substr(0, pos).c_str());
					lut_mode2 = atoi(arg.substr(pos+1).c_str());
				} else {
					lut_mode = atoi(arg.c_str());
					lut_mode2 = lut_mode;
				}
				lut_costs.clear();
				for (int i = 0; i < lut_mode; i++)
					lut_costs.push_back(1);
				for (int i = lut_mode; i < lut_mode2; i++)
					lut_costs.push_back(2 << (i - lut_mode));
				continue;
			}
			if (arg == "-luts" && argidx+1 < args.size()) {
				lut_costs.clear();
				for (auto &tok : split_tokens(args[++argidx], ",")) {
					auto parts = split_tokens(tok, ":");
					if (GetSize(parts) == 0 && !lut_costs.empty())
						lut_costs.push_back(lut_costs.back());
					else if (GetSize(parts) == 1)
						lut_costs.push_back(atoi(parts.at(0).c_str()));
					else if (GetSize(parts) == 2)
						while (GetSize(lut_costs) < atoi(parts.at(0).c_str()))
							lut_costs.push_back(atoi(parts.at(1).c_str()));
					else
						log_cmd_error("Invalid -luts syntax.\n");
				}
				continue;
			}
			if (arg == "-sop") {
				sop_mode = true;
				continue;
			}
			if (arg == "-mux4") {
				map_mux4 = true;
				continue;
			}
			if (arg == "-mux8") {
				map_mux8 = true;
				continue;
			}
			if (arg == "-mux16") {
				map_mux16 = true;
				continue;
			}
			if (arg == "-g" && argidx+1 < args.size()) {
				for (auto g : split_tokens(args[++argidx], ",")) {
					if (g == "AND") goto ok_gate;
					if (g == "NAND") goto ok_gate;
					if (g == "OR") goto ok_gate;
					if (g == "NOR") goto ok_gate;
					if (g == "XOR") goto ok_gate;
					if (g == "XNOR") goto ok_gate;
					if (g == "MUX") goto ok_gate;
					if (g == "AOI3") goto ok_gate;
					if (g == "OAI3") goto ok_gate;
					if (g == "AOI4") goto ok_gate;
					if (g == "OAI4") goto ok_gate;
					cmd_error(args, argidx, stringf("Unsupported gate type: %s", g.c_str()));
				ok_gate:
					enabled_gates.insert(g);
				}
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
				dff_mode = true;
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
			if (arg == "-showtmp") {
				show_tempdir = true;
				continue;
			}
			if (arg == "-markgroups") {
				markgroups = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!lut_costs.empty() && !liberty_file.empty())
			log_cmd_error("Got -lut and -liberty! This two options are exclusive.\n");
		if (!constr_file.empty() && liberty_file.empty())
			log_cmd_error("Got -constr but no -liberty!\n");

		for (auto mod : design->selected_modules())
			if (mod->processes.size() > 0)
				log("Skipping module %s as it contains processes.\n", log_id(mod));
			else if (!dff_mode || !clk_str.empty())
				abc_module(design, mod, script_file, exe_file, liberty_file, constr_file, cleanup, lut_costs, dff_mode, clk_str, keepff,
						delay_target, sop_inputs, sop_products, fast_mode, mod->selected_cells(), show_tempdir, sop_mode);
			else
			{
				assign_map.set(mod);
				CellTypes ct(design);

				std::vector<RTLIL::Cell*> all_cells = mod->selected_cells();
				std::set<RTLIL::Cell*> unassigned_cells(all_cells.begin(), all_cells.end());

				std::set<RTLIL::Cell*> expand_queue, next_expand_queue;
				std::set<RTLIL::Cell*> expand_queue_up, next_expand_queue_up;
				std::set<RTLIL::Cell*> expand_queue_down, next_expand_queue_down;

				typedef tuple<bool, RTLIL::SigSpec, bool, RTLIL::SigSpec> clkdomain_t;
				std::map<clkdomain_t, std::vector<RTLIL::Cell*>> assigned_cells;
				std::map<RTLIL::Cell*, clkdomain_t> assigned_cells_reverse;

				std::map<RTLIL::Cell*, std::set<RTLIL::SigBit>> cell_to_bit, cell_to_bit_up, cell_to_bit_down;
				std::map<RTLIL::SigBit, std::set<RTLIL::Cell*>> bit_to_cell, bit_to_cell_up, bit_to_cell_down;

				for (auto cell : all_cells)
				{
					clkdomain_t key;

					for (auto &conn : cell->connections())
					for (auto bit : conn.second) {
						bit = assign_map(bit);
						if (bit.wire != nullptr) {
							cell_to_bit[cell].insert(bit);
							bit_to_cell[bit].insert(cell);
							if (ct.cell_input(cell->type, conn.first)) {
								cell_to_bit_up[cell].insert(bit);
								bit_to_cell_down[bit].insert(cell);
							}
							if (ct.cell_output(cell->type, conn.first)) {
								cell_to_bit_down[cell].insert(bit);
								bit_to_cell_up[bit].insert(cell);
							}
						}
					}

					if (cell->type == "$_DFF_N_" || cell->type == "$_DFF_P_")
					{
						key = clkdomain_t(cell->type == "$_DFF_P_", assign_map(cell->getPort("\\C")), true, RTLIL::SigSpec());
					}
					else
					if (cell->type == "$_DFFE_NN_" || cell->type == "$_DFFE_NP_" || cell->type == "$_DFFE_PN_" || cell->type == "$_DFFE_PP_")
					{
						bool this_clk_pol = cell->type == "$_DFFE_PN_" || cell->type == "$_DFFE_PP_";
						bool this_en_pol = cell->type == "$_DFFE_NP_" || cell->type == "$_DFFE_PP_";
						key = clkdomain_t(this_clk_pol, assign_map(cell->getPort("\\C")), this_en_pol, assign_map(cell->getPort("\\E")));
					}
					else
						continue;

					unassigned_cells.erase(cell);
					expand_queue.insert(cell);
					expand_queue_up.insert(cell);
					expand_queue_down.insert(cell);

					assigned_cells[key].push_back(cell);
					assigned_cells_reverse[cell] = key;
				}

				while (!expand_queue_up.empty() || !expand_queue_down.empty())
				{
					if (!expand_queue_up.empty())
					{
						RTLIL::Cell *cell = *expand_queue_up.begin();
						clkdomain_t key = assigned_cells_reverse.at(cell);
						expand_queue_up.erase(cell);

						for (auto bit : cell_to_bit_up[cell])
						for (auto c : bit_to_cell_up[bit])
							if (unassigned_cells.count(c)) {
								unassigned_cells.erase(c);
								next_expand_queue_up.insert(c);
								assigned_cells[key].push_back(c);
								assigned_cells_reverse[c] = key;
								expand_queue.insert(c);
							}
					}

					if (!expand_queue_down.empty())
					{
						RTLIL::Cell *cell = *expand_queue_down.begin();
						clkdomain_t key = assigned_cells_reverse.at(cell);
						expand_queue_down.erase(cell);

						for (auto bit : cell_to_bit_down[cell])
						for (auto c : bit_to_cell_down[bit])
							if (unassigned_cells.count(c)) {
								unassigned_cells.erase(c);
								next_expand_queue_up.insert(c);
								assigned_cells[key].push_back(c);
								assigned_cells_reverse[c] = key;
								expand_queue.insert(c);
							}
					}

					if (expand_queue_up.empty() && expand_queue_down.empty()) {
						expand_queue_up.swap(next_expand_queue_up);
						expand_queue_down.swap(next_expand_queue_down);
					}
				}

				while (!expand_queue.empty())
				{
					RTLIL::Cell *cell = *expand_queue.begin();
					clkdomain_t key = assigned_cells_reverse.at(cell);
					expand_queue.erase(cell);

					for (auto bit : cell_to_bit.at(cell)) {
						for (auto c : bit_to_cell[bit])
							if (unassigned_cells.count(c)) {
								unassigned_cells.erase(c);
								next_expand_queue.insert(c);
								assigned_cells[key].push_back(c);
								assigned_cells_reverse[c] = key;
							}
						bit_to_cell[bit].clear();
					}

					if (expand_queue.empty())
						expand_queue.swap(next_expand_queue);
				}

				clkdomain_t key(true, RTLIL::SigSpec(), true, RTLIL::SigSpec());
				for (auto cell : unassigned_cells) {
					assigned_cells[key].push_back(cell);
					assigned_cells_reverse[cell] = key;
				}

				log_header(design, "Summary of detected clock domains:\n");
				for (auto &it : assigned_cells)
					log("  %d cells in clk=%s%s, en=%s%s\n", GetSize(it.second),
							std::get<0>(it.first) ? "" : "!", log_signal(std::get<1>(it.first)),
							std::get<2>(it.first) ? "" : "!", log_signal(std::get<3>(it.first)));

				for (auto &it : assigned_cells) {
					clk_polarity = std::get<0>(it.first);
					clk_sig = assign_map(std::get<1>(it.first));
					en_polarity = std::get<2>(it.first);
					en_sig = assign_map(std::get<3>(it.first));
					abc_module(design, mod, script_file, exe_file, liberty_file, constr_file, cleanup, lut_costs, !clk_sig.empty(), "$",
							keepff, delay_target, sop_inputs, sop_products, fast_mode, it.second, show_tempdir, sop_mode);
					assign_map.set(mod);
				}
			}

		assign_map.clear();
		signal_list.clear();
		signal_map.clear();

		log_pop();
	}
} AbcPass;

PRIVATE_NAMESPACE_END
