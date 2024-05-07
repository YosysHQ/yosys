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

// [[CITE]] ABC
// Berkeley Logic Synthesis and Verification Group, ABC: A System for Sequential Synthesis and Verification
// http://www.eecs.berkeley.edu/~alanmi/abc/

// [[CITE]] Berkeley Logic Interchange Format (BLIF)
// University of California. Berkeley. July 28, 1992
// http://www.ece.cmu.edu/~ee760/760docs/blif.pdf

// [[CITE]] Kahn's Topological sorting algorithm
// Kahn, Arthur B. (1962), "Topological sorting of large networks", Communications of the ACM 5 (11): 558-562, doi:10.1145/368996.369025
// http://en.wikipedia.org/wiki/Topological_sorting

#define ABC_COMMAND_LIB "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; &dch -f; &nf {D}; &put"
#define ABC_COMMAND_CTR "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; &dch -f; &nf {D}; &put; buffer; upsize {D}; dnsize {D}; stime -p"
#define ABC_COMMAND_LUT "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; dch -f; if; mfs2"
#define ABC_COMMAND_SOP "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; dch -f; cover {I} {P}"
#define ABC_COMMAND_DFL "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; &dch -f; &nf {D}; &put"

#define ABC_FAST_COMMAND_LIB "strash; dretime; map {D}"
#define ABC_FAST_COMMAND_CTR "strash; dretime; map {D}; buffer; upsize {D}; dnsize {D}; stime -p"
#define ABC_FAST_COMMAND_LUT "strash; dretime; if"
#define ABC_FAST_COMMAND_SOP "strash; dretime; cover {I} {P}"
#define ABC_FAST_COMMAND_DFL "strash; dretime; map"

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"
#include "kernel/cost.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <cctype>
#include <cerrno>
#include <sstream>
#include <climits>
#include <vector>

#ifndef _WIN32
#  include <unistd.h>
#  include <dirent.h>
#endif

#include "frontends/blif/blifparse.h"

#ifdef YOSYS_LINK_ABC
namespace abc {
	int Abc_RealMain(int argc, char *argv[]);
}
#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

enum class gate_type_t {
	G_NONE,
	G_FF,
	G_FF0,
	G_FF1,
	G_BUF,
	G_NOT,
	G_AND,
	G_NAND,
	G_OR,
	G_NOR,
	G_XOR,
	G_XNOR,
	G_ANDNOT,
	G_ORNOT,
	G_MUX,
	G_NMUX,
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
	RTLIL::State init;
};

bool map_mux4;
bool map_mux8;
bool map_mux16;

bool markgroups;
int map_autoidx;
SigMap assign_map;
RTLIL::Module *module;
std::vector<gate_t> signal_list;
dict<RTLIL::SigBit, int> signal_map;
FfInitVals initvals;
pool<std::string> enabled_gates;
bool cmos_cost;
bool had_init;

bool clk_polarity, en_polarity, arst_polarity, srst_polarity;
RTLIL::SigSpec clk_sig, en_sig, arst_sig, srst_sig;
dict<int, std::string> pi_map, po_map;

int undef_bits_lost;

int map_signal(RTLIL::SigBit bit, gate_type_t gate_type = G(NONE), int in1 = -1, int in2 = -1, int in3 = -1, int in4 = -1)
{
	assign_map.apply(bit);

	if (bit == State::Sx)
		undef_bits_lost++;

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
		gate.init = initvals(bit);
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
		if (bit.wire != nullptr && signal_map.count(bit) > 0)
			signal_list[signal_map[bit]].is_port = true;
}

void extract_cell(RTLIL::Cell *cell, bool keepff)
{
	if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
		FfData ff(&initvals, cell);
		gate_type_t type = G(FF);
		if (!ff.has_clk)
			return;
		if (ff.has_gclk)
			return;
		if (ff.has_aload)
			return;
		if (ff.has_sr)
			return;
		if (!ff.is_fine)
			return;
		if (clk_polarity != ff.pol_clk)
			return;
		if (clk_sig != assign_map(ff.sig_clk))
			return;
		if (ff.has_ce) {
			if (en_polarity != ff.pol_ce)
				return;
			if (en_sig != assign_map(ff.sig_ce))
				return;
		} else {
			if (GetSize(en_sig) != 0)
				return;
		}
		if (ff.val_init == State::S1) {
			type = G(FF1);
			had_init = true;
		} else if (ff.val_init == State::S0) {
			type = G(FF0);
			had_init = true;
		}
		if (ff.has_arst) {
			if (arst_polarity != ff.pol_arst)
				return;
			if (arst_sig != assign_map(ff.sig_arst))
				return;
			if (ff.val_arst == State::S1) {
				if (type == G(FF0))
					return;
				type = G(FF1);
			} else if (ff.val_arst == State::S0) {
				if (type == G(FF1))
					return;
				type = G(FF0);
			}
		} else {
			if (GetSize(arst_sig) != 0)
				return;
		}
		if (ff.has_srst) {
			if (srst_polarity != ff.pol_srst)
				return;
			if (srst_sig != assign_map(ff.sig_srst))
				return;
			if (ff.val_srst == State::S1) {
				if (type == G(FF0))
					return;
				type = G(FF1);
			} else if (ff.val_srst == State::S0) {
				if (type == G(FF1))
					return;
				type = G(FF0);
			}
		} else {
			if (GetSize(srst_sig) != 0)
				return;
		}

		if (keepff)
			for (auto &c : ff.sig_q.chunks())
				if (c.wire != nullptr)
					c.wire->attributes[ID::keep] = 1;

		map_signal(ff.sig_q, type, map_signal(ff.sig_d));

		ff.remove();
		return;
	}

	if (cell->type.in(ID($_BUF_), ID($_NOT_)))
	{
		RTLIL::SigSpec sig_a = cell->getPort(ID::A);
		RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

		assign_map.apply(sig_a);
		assign_map.apply(sig_y);

		map_signal(sig_y, cell->type == ID($_BUF_) ? G(BUF) : G(NOT), map_signal(sig_a));

		module->remove(cell);
		return;
	}

	if (cell->type.in(ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_), ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_)))
	{
		RTLIL::SigSpec sig_a = cell->getPort(ID::A);
		RTLIL::SigSpec sig_b = cell->getPort(ID::B);
		RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);

		if (cell->type == ID($_AND_))
			map_signal(sig_y, G(AND), mapped_a, mapped_b);
		else if (cell->type == ID($_NAND_))
			map_signal(sig_y, G(NAND), mapped_a, mapped_b);
		else if (cell->type == ID($_OR_))
			map_signal(sig_y, G(OR), mapped_a, mapped_b);
		else if (cell->type == ID($_NOR_))
			map_signal(sig_y, G(NOR), mapped_a, mapped_b);
		else if (cell->type == ID($_XOR_))
			map_signal(sig_y, G(XOR), mapped_a, mapped_b);
		else if (cell->type == ID($_XNOR_))
			map_signal(sig_y, G(XNOR), mapped_a, mapped_b);
		else if (cell->type == ID($_ANDNOT_))
			map_signal(sig_y, G(ANDNOT), mapped_a, mapped_b);
		else if (cell->type == ID($_ORNOT_))
			map_signal(sig_y, G(ORNOT), mapped_a, mapped_b);
		else
			log_abort();

		module->remove(cell);
		return;
	}

	if (cell->type.in(ID($_MUX_), ID($_NMUX_)))
	{
		RTLIL::SigSpec sig_a = cell->getPort(ID::A);
		RTLIL::SigSpec sig_b = cell->getPort(ID::B);
		RTLIL::SigSpec sig_s = cell->getPort(ID::S);
		RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_s);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);
		int mapped_s = map_signal(sig_s);

		map_signal(sig_y, cell->type == ID($_MUX_) ? G(MUX) : G(NMUX), mapped_a, mapped_b, mapped_s);

		module->remove(cell);
		return;
	}

	if (cell->type.in(ID($_AOI3_), ID($_OAI3_)))
	{
		RTLIL::SigSpec sig_a = cell->getPort(ID::A);
		RTLIL::SigSpec sig_b = cell->getPort(ID::B);
		RTLIL::SigSpec sig_c = cell->getPort(ID::C);
		RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_c);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);
		int mapped_c = map_signal(sig_c);

		map_signal(sig_y, cell->type == ID($_AOI3_) ? G(AOI3) : G(OAI3), mapped_a, mapped_b, mapped_c);

		module->remove(cell);
		return;
	}

	if (cell->type.in(ID($_AOI4_), ID($_OAI4_)))
	{
		RTLIL::SigSpec sig_a = cell->getPort(ID::A);
		RTLIL::SigSpec sig_b = cell->getPort(ID::B);
		RTLIL::SigSpec sig_c = cell->getPort(ID::C);
		RTLIL::SigSpec sig_d = cell->getPort(ID::D);
		RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

		assign_map.apply(sig_a);
		assign_map.apply(sig_b);
		assign_map.apply(sig_c);
		assign_map.apply(sig_d);
		assign_map.apply(sig_y);

		int mapped_a = map_signal(sig_a);
		int mapped_b = map_signal(sig_b);
		int mapped_c = map_signal(sig_c);
		int mapped_d = map_signal(sig_d);

		map_signal(sig_y, cell->type == ID($_AOI4_) ? G(AOI4) : G(OAI4), mapped_a, mapped_b, mapped_c, mapped_d);

		module->remove(cell);
		return;
	}
}

std::string remap_name(RTLIL::IdString abc_name, RTLIL::Wire **orig_wire = nullptr)
{
	std::string abc_sname = abc_name.substr(1);
	bool isnew = false;
	if (abc_sname.compare(0, 4, "new_") == 0)
	{
		abc_sname.erase(0, 4);
		isnew = true;
	}
	if (abc_sname.compare(0, 5, "ys__n") == 0)
	{
		abc_sname.erase(0, 5);
		if (std::isdigit(abc_sname.at(0)))
		{
			int sid = std::atoi(abc_sname.c_str());
			size_t postfix_start = abc_sname.find_first_not_of("0123456789");
			std::string postfix = postfix_start != std::string::npos ? abc_sname.substr(postfix_start) : "";

			if (sid < GetSize(signal_list))
			{
				auto sig = signal_list.at(sid);
				if (sig.bit.wire != nullptr)
				{
					std::string s = stringf("$abc$%d$%s", map_autoidx, sig.bit.wire->name.c_str()+1);
					if (sig.bit.wire->width != 1)
						s += stringf("[%d]", sig.bit.offset);
					if (isnew)
						s += "_new";
					s += postfix;
					if (orig_wire != nullptr)
						*orig_wire = sig.bit.wire;
					return s;
				}
			}
		}
	}
	return stringf("$abc$%d$%s", map_autoidx, abc_name.c_str()+1);
}

void dump_loop_graph(FILE *f, int &nr, dict<int, pool<int>> &edges, pool<int> &workpool, std::vector<int> &in_counts)
{
	if (f == nullptr)
		return;

	log("Dumping loop state graph to slide %d.\n", ++nr);

	fprintf(f, "digraph \"slide%d\" {\n", nr);
	fprintf(f, "  label=\"slide%d\";\n", nr);
	fprintf(f, "  rankdir=\"TD\";\n");

	pool<int> nodes;
	for (auto &e : edges) {
		nodes.insert(e.first);
		for (auto n : e.second)
			nodes.insert(n);
	}

	for (auto n : nodes)
		fprintf(f, "  ys__n%d [label=\"%s\\nid=%d, count=%d\"%s];\n", n, log_signal(signal_list[n].bit),
				n, in_counts[n], workpool.count(n) ? ", shape=box" : "");

	for (auto &e : edges)
	for (auto n : e.second)
		fprintf(f, "  ys__n%d -> ys__n%d;\n", e.first, n);

	fprintf(f, "}\n");
}

void handle_loops()
{
	// http://en.wikipedia.org/wiki/Topological_sorting
	// (Kahn, Arthur B. (1962), "Topological sorting of large networks")

	dict<int, pool<int>> edges;
	std::vector<int> in_edges_count(signal_list.size());
	pool<int> workpool;

	FILE *dot_f = nullptr;
	int dot_nr = 0;

	// uncomment for troubleshooting the loop detection code
	// dot_f = fopen("test.dot", "w");

	for (auto &g : signal_list) {
		if (g.type == G(NONE) || g.type == G(FF) || g.type == G(FF0) || g.type == G(FF1)) {
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
				if (w1 == nullptr)
					id1 = id2;
				else if (w2 == nullptr)
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

			log_assert(signal_list[id1].bit.wire != nullptr);

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

	if (dot_f != nullptr)
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
	if (selfdir_name != "/") {
		while (1) {
			size_t pos = text.find(selfdir_name);
			if (pos == std::string::npos)
				break;
			text = text.substr(0, pos) + "<yosys-exe-dir>/" + text.substr(pos + GetSize(selfdir_name));
		}
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
		int pi, po;
		if (sscanf(line.c_str(), "Start-point = pi%d.  End-point = po%d.", &pi, &po) == 2) {
			log("ABC: Start-point = pi%d (%s).  End-point = po%d (%s).\n",
					pi, pi_map.count(pi) ? pi_map.at(pi).c_str() : "???",
					po, po_map.count(po) ? po_map.at(po).c_str() : "???");
			return;
		}

		for (char ch : line)
			next_char(ch);
	}
};

void abc_module(RTLIL::Design *design, RTLIL::Module *current_module, std::string script_file, std::string exe_file,
		std::vector<std::string> &liberty_files, std::vector<std::string> &genlib_files, std::string constr_file,
		bool cleanup, vector<int> lut_costs, bool dff_mode, std::string clk_str, bool keepff, std::string delay_target,
		std::string sop_inputs, std::string sop_products, std::string lutin_shared, bool fast_mode,
		const std::vector<RTLIL::Cell*> &cells, bool show_tempdir, bool sop_mode, bool abc_dress, std::vector<std::string> &dont_use_cells)
{
	module = current_module;
	map_autoidx = autoidx++;

	signal_map.clear();
	signal_list.clear();
	pi_map.clear();
	po_map.clear();

	if (clk_str != "$")
	{
		clk_polarity = true;
		clk_sig = RTLIL::SigSpec();

		en_polarity = true;
		en_sig = RTLIL::SigSpec();

		arst_polarity = true;
		arst_sig = RTLIL::SigSpec();

		srst_polarity = true;
		srst_sig = RTLIL::SigSpec();
	}

	if (!clk_str.empty() && clk_str != "$")
	{
		std::string en_str;
		std::string arst_str;
		std::string srst_str;
		if (clk_str.find(',') != std::string::npos) {
			int pos = clk_str.find(',');
			en_str = clk_str.substr(pos+1);
			clk_str = clk_str.substr(0, pos);
		}
		if (en_str.find(',') != std::string::npos) {
			int pos = en_str.find(',');
			arst_str = en_str.substr(pos+1);
			arst_str = en_str.substr(0, pos);
		}
		if (arst_str.find(',') != std::string::npos) {
			int pos = arst_str.find(',');
			srst_str = arst_str.substr(pos+1);
			srst_str = arst_str.substr(0, pos);
		}
		if (clk_str[0] == '!') {
			clk_polarity = false;
			clk_str = clk_str.substr(1);
		}
		if (module->wire(RTLIL::escape_id(clk_str)) != nullptr)
			clk_sig = assign_map(module->wire(RTLIL::escape_id(clk_str)));
		if (en_str != "") {
			if (en_str[0] == '!') {
				en_polarity = false;
				en_str = en_str.substr(1);
			}
			if (module->wire(RTLIL::escape_id(en_str)) != nullptr)
				en_sig = assign_map(module->wire(RTLIL::escape_id(en_str)));
		}
		if (arst_str != "") {
			if (arst_str[0] == '!') {
				arst_polarity = false;
				arst_str = arst_str.substr(1);
			}
			if (module->wire(RTLIL::escape_id(arst_str)) != nullptr)
				arst_sig = assign_map(module->wire(RTLIL::escape_id(arst_str)));
		}
		if (srst_str != "") {
			if (srst_str[0] == '!') {
				srst_polarity = false;
				srst_str = srst_str.substr(1);
			}
			if (module->wire(RTLIL::escape_id(srst_str)) != nullptr)
				srst_sig = assign_map(module->wire(RTLIL::escape_id(srst_str)));
		}
	}

	if (dff_mode && clk_sig.empty())
		log_cmd_error("Clock domain %s not found.\n", clk_str.c_str());

	std::string tempdir_name;
	if (cleanup) 
		tempdir_name = get_base_tmpdir() + "/";
	else
		tempdir_name = "_tmp_";
	tempdir_name += proc_program_prefix() + "yosys-abc-XXXXXX";
	tempdir_name = make_temp_dir(tempdir_name);
	log_header(design, "Extracting gate netlist of module `%s' to `%s/input.blif'..\n",
			module->name.c_str(), replace_tempdir(tempdir_name, tempdir_name, show_tempdir).c_str());

	std::string abc_script = stringf("read_blif \"%s/input.blif\"; ", tempdir_name.c_str());

	if (!liberty_files.empty() || !genlib_files.empty()) {
		std::string dont_use_args;
		for (std::string dont_use_cell : dont_use_cells) {
			dont_use_args += stringf("-X \"%s\" ", dont_use_cell.c_str());
		}
		bool first_lib = true;
		for (std::string liberty_file : liberty_files) {
			abc_script += stringf("read_lib %s %s -w \"%s\" ; ", dont_use_args.c_str(), first_lib ? "" : "-m", liberty_file.c_str());
			first_lib = false;
		}
		for (std::string liberty_file : genlib_files)
			abc_script += stringf("read_library \"%s\"; ", liberty_file.c_str());
		if (!constr_file.empty())
			abc_script += stringf("read_constr -v \"%s\"; ", constr_file.c_str());
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
			abc_script += "; lutpack {S}";
	} else if (!liberty_files.empty() || !genlib_files.empty())
		abc_script += constr_file.empty() ? (fast_mode ? ABC_FAST_COMMAND_LIB : ABC_COMMAND_LIB) : (fast_mode ? ABC_FAST_COMMAND_CTR : ABC_COMMAND_CTR);
	else if (sop_mode)
		abc_script += fast_mode ? ABC_FAST_COMMAND_SOP : ABC_COMMAND_SOP;
	else
		abc_script += fast_mode ? ABC_FAST_COMMAND_DFL : ABC_COMMAND_DFL;

	if (script_file.empty() && !delay_target.empty())
		for (size_t pos = abc_script.find("dretime;"); pos != std::string::npos; pos = abc_script.find("dretime;", pos+1))
			abc_script = abc_script.substr(0, pos) + "dretime; retime -o {D};" + abc_script.substr(pos+8);

	for (size_t pos = abc_script.find("{D}"); pos != std::string::npos; pos = abc_script.find("{D}", pos))
		abc_script = abc_script.substr(0, pos) + delay_target + abc_script.substr(pos+3);

	for (size_t pos = abc_script.find("{I}"); pos != std::string::npos; pos = abc_script.find("{I}", pos))
		abc_script = abc_script.substr(0, pos) + sop_inputs + abc_script.substr(pos+3);

	for (size_t pos = abc_script.find("{P}"); pos != std::string::npos; pos = abc_script.find("{P}", pos))
		abc_script = abc_script.substr(0, pos) + sop_products + abc_script.substr(pos+3);

	for (size_t pos = abc_script.find("{S}"); pos != std::string::npos; pos = abc_script.find("{S}", pos))
		abc_script = abc_script.substr(0, pos) + lutin_shared + abc_script.substr(pos+3);
	if (abc_dress)
		abc_script += stringf("; dress \"%s/input.blif\"", tempdir_name.c_str());
	abc_script += stringf("; write_blif %s/output.blif", tempdir_name.c_str());
	abc_script = add_echos_to_abc_cmd(abc_script);

	for (size_t i = 0; i+1 < abc_script.size(); i++)
		if (abc_script[i] == ';' && abc_script[i+1] == ' ')
			abc_script[i+1] = '\n';

	std::string buffer = stringf("%s/abc.script", tempdir_name.c_str());
	FILE *f = fopen(buffer.c_str(), "wt");
	if (f == nullptr)
		log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));
	fprintf(f, "%s\n", abc_script.c_str());
	fclose(f);

	if (dff_mode || !clk_str.empty())
	{
		if (clk_sig.size() == 0)
			log("No%s clock domain found. Not extracting any FF cells.\n", clk_str.empty() ? "" : " matching");
		else {
			log("Found%s %s clock domain: %s", clk_str.empty() ? "" : " matching", clk_polarity ? "posedge" : "negedge", log_signal(clk_sig));
			if (en_sig.size() != 0)
				log(", enabled by %s%s", en_polarity ? "" : "!", log_signal(en_sig));
			if (arst_sig.size() != 0)
				log(", asynchronously reset by %s%s", arst_polarity ? "" : "!", log_signal(arst_sig));
			if (srst_sig.size() != 0)
				log(", synchronously reset by %s%s", srst_polarity ? "" : "!", log_signal(srst_sig));
			log("\n");
		}
	}

	undef_bits_lost = 0;

	had_init = false;
	for (auto c : cells)
		extract_cell(c, keepff);

	if (undef_bits_lost)
		log("Replacing %d occurrences of constant undef bits with constant zero bits\n", undef_bits_lost);

	for (auto wire : module->wires()) {
		if (wire->port_id > 0 || wire->get_bool_attribute(ID::keep))
			mark_port(wire);
	}

	for (auto cell : module->cells())
	for (auto &port_it : cell->connections())
		mark_port(port_it.second);

	if (clk_sig.size() != 0)
		mark_port(clk_sig);

	if (en_sig.size() != 0)
		mark_port(en_sig);

	if (arst_sig.size() != 0)
		mark_port(arst_sig);

	if (srst_sig.size() != 0)
		mark_port(srst_sig);

	handle_loops();

	buffer = stringf("%s/input.blif", tempdir_name.c_str());
	f = fopen(buffer.c_str(), "wt");
	if (f == nullptr)
		log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));

	fprintf(f, ".model netlist\n");

	int count_input = 0;
	fprintf(f, ".inputs");
	for (auto &si : signal_list) {
		if (!si.is_port || si.type != G(NONE))
			continue;
		fprintf(f, " ys__n%d", si.id);
		pi_map[count_input++] = log_signal(si.bit);
	}
	if (count_input == 0)
		fprintf(f, " dummy_input\n");
	fprintf(f, "\n");

	int count_output = 0;
	fprintf(f, ".outputs");
	for (auto &si : signal_list) {
		if (!si.is_port || si.type == G(NONE))
			continue;
		fprintf(f, " ys__n%d", si.id);
		po_map[count_output++] = log_signal(si.bit);
	}
	fprintf(f, "\n");

	for (auto &si : signal_list)
		fprintf(f, "# ys__n%-5d %s\n", si.id, log_signal(si.bit));

	for (auto &si : signal_list) {
		if (si.bit.wire == nullptr) {
			fprintf(f, ".names ys__n%d\n", si.id);
			if (si.bit == RTLIL::State::S1)
				fprintf(f, "1\n");
		}
	}

	int count_gates = 0;
	for (auto &si : signal_list) {
		if (si.type == G(BUF)) {
			fprintf(f, ".names ys__n%d ys__n%d\n", si.in1, si.id);
			fprintf(f, "1 1\n");
		} else if (si.type == G(NOT)) {
			fprintf(f, ".names ys__n%d ys__n%d\n", si.in1, si.id);
			fprintf(f, "0 1\n");
		} else if (si.type == G(AND)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "11 1\n");
		} else if (si.type == G(NAND)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "0- 1\n");
			fprintf(f, "-0 1\n");
		} else if (si.type == G(OR)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "-1 1\n");
			fprintf(f, "1- 1\n");
		} else if (si.type == G(NOR)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "00 1\n");
		} else if (si.type == G(XOR)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "01 1\n");
			fprintf(f, "10 1\n");
		} else if (si.type == G(XNOR)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "00 1\n");
			fprintf(f, "11 1\n");
		} else if (si.type == G(ANDNOT)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "10 1\n");
		} else if (si.type == G(ORNOT)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.id);
			fprintf(f, "1- 1\n");
			fprintf(f, "-0 1\n");
		} else if (si.type == G(MUX)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.in3, si.id);
			fprintf(f, "1-0 1\n");
			fprintf(f, "-11 1\n");
		} else if (si.type == G(NMUX)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.in3, si.id);
			fprintf(f, "0-0 1\n");
			fprintf(f, "-01 1\n");
		} else if (si.type == G(AOI3)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.in3, si.id);
			fprintf(f, "-00 1\n");
			fprintf(f, "0-0 1\n");
		} else if (si.type == G(OAI3)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.in3, si.id);
			fprintf(f, "00- 1\n");
			fprintf(f, "--0 1\n");
		} else if (si.type == G(AOI4)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.in3, si.in4, si.id);
			fprintf(f, "-0-0 1\n");
			fprintf(f, "-00- 1\n");
			fprintf(f, "0--0 1\n");
			fprintf(f, "0-0- 1\n");
		} else if (si.type == G(OAI4)) {
			fprintf(f, ".names ys__n%d ys__n%d ys__n%d ys__n%d ys__n%d\n", si.in1, si.in2, si.in3, si.in4, si.id);
			fprintf(f, "00-- 1\n");
			fprintf(f, "--00 1\n");
		} else if (si.type == G(FF)) {
			fprintf(f, ".latch ys__n%d ys__n%d 2\n", si.in1, si.id);
		} else if (si.type == G(FF0)) {
			fprintf(f, ".latch ys__n%d ys__n%d 0\n", si.in1, si.id);
		} else if (si.type == G(FF1)) {
			fprintf(f, ".latch ys__n%d ys__n%d 1\n", si.in1, si.id);
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

		auto &cell_cost = cmos_cost ? CellCosts::cmos_gate_cost() : CellCosts::default_gate_cost();

		buffer = stringf("%s/stdcells.genlib", tempdir_name.c_str());
		f = fopen(buffer.c_str(), "wt");
		if (f == nullptr)
			log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));
		fprintf(f, "GATE ZERO    1 Y=CONST0;\n");
		fprintf(f, "GATE ONE     1 Y=CONST1;\n");
		fprintf(f, "GATE BUF    %d Y=A;                  PIN * NONINV  1 999 1 0 1 0\n", cell_cost.at(ID($_BUF_)));
		fprintf(f, "GATE NOT    %d Y=!A;                 PIN * INV     1 999 1 0 1 0\n", cell_cost.at(ID($_NOT_)));
		if (enabled_gates.count("AND"))
			fprintf(f, "GATE AND    %d Y=A*B;                PIN * NONINV  1 999 1 0 1 0\n", cell_cost.at(ID($_AND_)));
		if (enabled_gates.count("NAND"))
			fprintf(f, "GATE NAND   %d Y=!(A*B);             PIN * INV     1 999 1 0 1 0\n", cell_cost.at(ID($_NAND_)));
		if (enabled_gates.count("OR"))
			fprintf(f, "GATE OR     %d Y=A+B;                PIN * NONINV  1 999 1 0 1 0\n", cell_cost.at(ID($_OR_)));
		if (enabled_gates.count("NOR"))
			fprintf(f, "GATE NOR    %d Y=!(A+B);             PIN * INV     1 999 1 0 1 0\n", cell_cost.at(ID($_NOR_)));
		if (enabled_gates.count("XOR"))
			fprintf(f, "GATE XOR    %d Y=(A*!B)+(!A*B);      PIN * UNKNOWN 1 999 1 0 1 0\n", cell_cost.at(ID($_XOR_)));
		if (enabled_gates.count("XNOR"))
			fprintf(f, "GATE XNOR   %d Y=(A*B)+(!A*!B);      PIN * UNKNOWN 1 999 1 0 1 0\n", cell_cost.at(ID($_XNOR_)));
		if (enabled_gates.count("ANDNOT"))
			fprintf(f, "GATE ANDNOT %d Y=A*!B;               PIN * UNKNOWN 1 999 1 0 1 0\n", cell_cost.at(ID($_ANDNOT_)));
		if (enabled_gates.count("ORNOT"))
			fprintf(f, "GATE ORNOT  %d Y=A+!B;               PIN * UNKNOWN 1 999 1 0 1 0\n", cell_cost.at(ID($_ORNOT_)));
		if (enabled_gates.count("AOI3"))
			fprintf(f, "GATE AOI3   %d Y=!((A*B)+C);         PIN * INV     1 999 1 0 1 0\n", cell_cost.at(ID($_AOI3_)));
		if (enabled_gates.count("OAI3"))
			fprintf(f, "GATE OAI3   %d Y=!((A+B)*C);         PIN * INV     1 999 1 0 1 0\n", cell_cost.at(ID($_OAI3_)));
		if (enabled_gates.count("AOI4"))
			fprintf(f, "GATE AOI4   %d Y=!((A*B)+(C*D));     PIN * INV     1 999 1 0 1 0\n", cell_cost.at(ID($_AOI4_)));
		if (enabled_gates.count("OAI4"))
			fprintf(f, "GATE OAI4   %d Y=!((A+B)*(C+D));     PIN * INV     1 999 1 0 1 0\n", cell_cost.at(ID($_OAI4_)));
		if (enabled_gates.count("MUX"))
			fprintf(f, "GATE MUX    %d Y=(A*B)+(S*B)+(!S*A); PIN * UNKNOWN 1 999 1 0 1 0\n", cell_cost.at(ID($_MUX_)));
		if (enabled_gates.count("NMUX"))
			fprintf(f, "GATE NMUX   %d Y=!((A*B)+(S*B)+(!S*A)); PIN * UNKNOWN 1 999 1 0 1 0\n", cell_cost.at(ID($_NMUX_)));
		if (map_mux4)
			fprintf(f, "GATE MUX4   %d Y=(!S*!T*A)+(S*!T*B)+(!S*T*C)+(S*T*D); PIN * UNKNOWN 1 999 1 0 1 0\n", 2*cell_cost.at(ID($_MUX_)));
		if (map_mux8)
			fprintf(f, "GATE MUX8   %d Y=(!S*!T*!U*A)+(S*!T*!U*B)+(!S*T*!U*C)+(S*T*!U*D)+(!S*!T*U*E)+(S*!T*U*F)+(!S*T*U*G)+(S*T*U*H); PIN * UNKNOWN 1 999 1 0 1 0\n", 4*cell_cost.at(ID($_MUX_)));
		if (map_mux16)
			fprintf(f, "GATE MUX16  %d Y=(!S*!T*!U*!V*A)+(S*!T*!U*!V*B)+(!S*T*!U*!V*C)+(S*T*!U*!V*D)+(!S*!T*U*!V*E)+(S*!T*U*!V*F)+(!S*T*U*!V*G)+(S*T*U*!V*H)+(!S*!T*!U*V*I)+(S*!T*!U*V*J)+(!S*T*!U*V*K)+(S*T*!U*V*L)+(!S*!T*U*V*M)+(S*!T*U*V*N)+(!S*T*U*V*O)+(S*T*U*V*P); PIN * UNKNOWN 1 999 1 0 1 0\n", 8*cell_cost.at(ID($_MUX_)));
		fclose(f);

		if (!lut_costs.empty()) {
			buffer = stringf("%s/lutdefs.txt", tempdir_name.c_str());
			f = fopen(buffer.c_str(), "wt");
			if (f == nullptr)
				log_error("Opening %s for writing failed: %s\n", buffer.c_str(), strerror(errno));
			for (int i = 0; i < GetSize(lut_costs); i++)
				fprintf(f, "%d %d.00 1.00\n", i+1, lut_costs.at(i));
			fclose(f);
		}

		buffer = stringf("\"%s\" -s -f %s/abc.script 2>&1", exe_file.c_str(), tempdir_name.c_str());
		log("Running ABC command: %s\n", replace_tempdir(buffer, tempdir_name, show_tempdir).c_str());

#ifndef YOSYS_LINK_ABC
		abc_output_filter filt(tempdir_name, show_tempdir);
		int ret = run_command(buffer, std::bind(&abc_output_filter::next_line, filt, std::placeholders::_1));
#else
		string temp_stdouterr_name = stringf("%s/stdouterr.txt", tempdir_name.c_str());
		FILE *temp_stdouterr_w = fopen(temp_stdouterr_name.c_str(), "w");
		if (temp_stdouterr_w == NULL)
			log_error("ABC: cannot open a temporary file for output redirection");
		fflush(stdout);
		fflush(stderr);
		FILE *old_stdout = fopen(temp_stdouterr_name.c_str(), "r"); // need any fd for renumbering
		FILE *old_stderr = fopen(temp_stdouterr_name.c_str(), "r"); // need any fd for renumbering
#if defined(__wasm)
#define fd_renumber(from, to) (void)__wasi_fd_renumber(from, to)
#else
#define fd_renumber(from, to) dup2(from, to)
#endif
		fd_renumber(fileno(stdout), fileno(old_stdout));
		fd_renumber(fileno(stderr), fileno(old_stderr));
		fd_renumber(fileno(temp_stdouterr_w), fileno(stdout));
		fd_renumber(fileno(temp_stdouterr_w), fileno(stderr));
		fclose(temp_stdouterr_w);
		// These needs to be mutable, supposedly due to getopt
		char *abc_argv[5];
		string tmp_script_name = stringf("%s/abc.script", tempdir_name.c_str());
		abc_argv[0] = strdup(exe_file.c_str());
		abc_argv[1] = strdup("-s");
		abc_argv[2] = strdup("-f");
		abc_argv[3] = strdup(tmp_script_name.c_str());
		abc_argv[4] = 0;
		int ret = abc::Abc_RealMain(4, abc_argv);
		free(abc_argv[0]);
		free(abc_argv[1]);
		free(abc_argv[2]);
		free(abc_argv[3]);
		fflush(stdout);
		fflush(stderr);
		fd_renumber(fileno(old_stdout), fileno(stdout));
		fd_renumber(fileno(old_stderr), fileno(stderr));
		fclose(old_stdout);
		fclose(old_stderr);
		std::ifstream temp_stdouterr_r(temp_stdouterr_name);
		abc_output_filter filt(tempdir_name, show_tempdir);
		for (std::string line; std::getline(temp_stdouterr_r, line); )
			filt.next_line(line + "\n");
		temp_stdouterr_r.close();
#endif
		if (ret != 0)
			log_error("ABC: execution of command \"%s\" failed: return code %d.\n", buffer.c_str(), ret);

		buffer = stringf("%s/%s", tempdir_name.c_str(), "output.blif");
		std::ifstream ifs;
		ifs.open(buffer);
		if (ifs.fail())
			log_error("Can't open ABC output file `%s'.\n", buffer.c_str());

		bool builtin_lib = liberty_files.empty() && genlib_files.empty();
		RTLIL::Design *mapped_design = new RTLIL::Design;
		parse_blif(mapped_design, ifs, builtin_lib ? ID(DFF) : ID(_dff_), false, sop_mode);

		ifs.close();

		log_header(design, "Re-integrating ABC results.\n");
		RTLIL::Module *mapped_mod = mapped_design->module(ID(netlist));
		if (mapped_mod == nullptr)
			log_error("ABC output file does not contain a module `netlist'.\n");
		for (auto w : mapped_mod->wires()) {
			RTLIL::Wire *orig_wire = nullptr;
			RTLIL::Wire *wire = module->addWire(remap_name(w->name, &orig_wire));
			if (orig_wire != nullptr && orig_wire->attributes.count(ID::src))
				wire->attributes[ID::src] = orig_wire->attributes[ID::src];
			if (markgroups) wire->attributes[ID::abcgroup] = map_autoidx;
			design->select(module, wire);
		}

		SigMap mapped_sigmap(mapped_mod);
		FfInitVals mapped_initvals(&mapped_sigmap, mapped_mod);

		dict<std::string, int> cell_stats;
		for (auto c : mapped_mod->cells())
		{
			if (builtin_lib)
			{
				cell_stats[RTLIL::unescape_id(c->type)]++;
				if (c->type.in(ID(ZERO), ID(ONE))) {
					RTLIL::SigSig conn;
					RTLIL::IdString name_y = remap_name(c->getPort(ID::Y).as_wire()->name);
					conn.first = module->wire(name_y);
					conn.second = RTLIL::SigSpec(c->type == ID(ZERO) ? 0 : 1, 1);
					module->connect(conn);
					continue;
				}
				if (c->type == ID(BUF)) {
					RTLIL::SigSig conn;
					RTLIL::IdString name_y = remap_name(c->getPort(ID::Y).as_wire()->name);
					RTLIL::IdString name_a = remap_name(c->getPort(ID::A).as_wire()->name);
					conn.first = module->wire(name_y);
					conn.second = module->wire(name_a);
					module->connect(conn);
					continue;
				}
				if (c->type == ID(NOT)) {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), ID($_NOT_));
					if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
					for (auto name : {ID::A, ID::Y}) {
						RTLIL::IdString remapped_name = remap_name(c->getPort(name).as_wire()->name);
						cell->setPort(name, module->wire(remapped_name));
					}
					design->select(module, cell);
					continue;
				}
				if (c->type.in(ID(AND), ID(OR), ID(XOR), ID(NAND), ID(NOR), ID(XNOR), ID(ANDNOT), ID(ORNOT))) {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), stringf("$_%s_", c->type.c_str()+1));
					if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
					for (auto name : {ID::A, ID::B, ID::Y}) {
						RTLIL::IdString remapped_name = remap_name(c->getPort(name).as_wire()->name);
						cell->setPort(name, module->wire(remapped_name));
					}
					design->select(module, cell);
					continue;
				}
				if (c->type.in(ID(MUX), ID(NMUX))) {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), stringf("$_%s_", c->type.c_str()+1));
					if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
					for (auto name : {ID::A, ID::B, ID::S, ID::Y}) {
						RTLIL::IdString remapped_name = remap_name(c->getPort(name).as_wire()->name);
						cell->setPort(name, module->wire(remapped_name));
					}
					design->select(module, cell);
					continue;
				}
				if (c->type == ID(MUX4)) {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), ID($_MUX4_));
					if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
					for (auto name : {ID::A, ID::B, ID::C, ID::D, ID::S, ID::T, ID::Y}) {
						RTLIL::IdString remapped_name = remap_name(c->getPort(name).as_wire()->name);
						cell->setPort(name, module->wire(remapped_name));
					}
					design->select(module, cell);
					continue;
				}
				if (c->type == ID(MUX8)) {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), ID($_MUX8_));
					if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
					for (auto name : {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::S, ID::T, ID::U, ID::Y}) {
						RTLIL::IdString remapped_name = remap_name(c->getPort(name).as_wire()->name);
						cell->setPort(name, module->wire(remapped_name));
					}
					design->select(module, cell);
					continue;
				}
				if (c->type == ID(MUX16)) {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), ID($_MUX16_));
					if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
					for (auto name : {ID::A, ID::B, ID::C, ID::D, ID::E, ID::F, ID::G, ID::H, ID::I, ID::J, ID::K,
							ID::L, ID::M, ID::N, ID::O, ID::P, ID::S, ID::T, ID::U, ID::V, ID::Y}) {
						RTLIL::IdString remapped_name = remap_name(c->getPort(name).as_wire()->name);
						cell->setPort(name, module->wire(remapped_name));
					}
					design->select(module, cell);
					continue;
				}
				if (c->type.in(ID(AOI3), ID(OAI3))) {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), stringf("$_%s_", c->type.c_str()+1));
					if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
					for (auto name : {ID::A, ID::B, ID::C, ID::Y}) {
						RTLIL::IdString remapped_name = remap_name(c->getPort(name).as_wire()->name);
						cell->setPort(name, module->wire(remapped_name));
					}
					design->select(module, cell);
					continue;
				}
				if (c->type.in(ID(AOI4), ID(OAI4))) {
					RTLIL::Cell *cell = module->addCell(remap_name(c->name), stringf("$_%s_", c->type.c_str()+1));
					if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
					for (auto name : {ID::A, ID::B, ID::C, ID::D, ID::Y}) {
						RTLIL::IdString remapped_name = remap_name(c->getPort(name).as_wire()->name);
						cell->setPort(name, module->wire(remapped_name));
					}
					design->select(module, cell);
					continue;
				}
				if (c->type == ID(DFF)) {
					log_assert(clk_sig.size() == 1);
					FfData ff(module, &initvals, remap_name(c->name));
					ff.width = 1;
					ff.is_fine = true;
					ff.has_clk = true;
					ff.pol_clk = clk_polarity;
					ff.sig_clk = clk_sig;
					if (en_sig.size() != 0) {
						log_assert(en_sig.size() == 1);
						ff.has_ce = true;
						ff.pol_ce = en_polarity;
						ff.sig_ce = en_sig;
					}
					RTLIL::Const init = mapped_initvals(c->getPort(ID::Q));
					if (had_init)
						ff.val_init = init;
					else
						ff.val_init = State::Sx;
					if (arst_sig.size() != 0) {
						log_assert(arst_sig.size() == 1);
						ff.has_arst = true;
						ff.pol_arst = arst_polarity;
						ff.sig_arst = arst_sig;
						ff.val_arst = init;
					}
					if (srst_sig.size() != 0) {
						log_assert(srst_sig.size() == 1);
						ff.has_srst = true;
						ff.pol_srst = srst_polarity;
						ff.sig_srst = srst_sig;
						ff.val_srst = init;
					}
					ff.sig_d = module->wire(remap_name(c->getPort(ID::D).as_wire()->name));
					ff.sig_q = module->wire(remap_name(c->getPort(ID::Q).as_wire()->name));
					RTLIL::Cell *cell = ff.emit();
					if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
					design->select(module, cell);
					continue;
				}
			}
			else
				cell_stats[RTLIL::unescape_id(c->type)]++;

			if (c->type.in(ID(_const0_), ID(_const1_))) {
				RTLIL::SigSig conn;
				conn.first = module->wire(remap_name(c->connections().begin()->second.as_wire()->name));
				conn.second = RTLIL::SigSpec(c->type == ID(_const0_) ? 0 : 1, 1);
				module->connect(conn);
				continue;
			}

			if (c->type == ID(_dff_)) {
				log_assert(clk_sig.size() == 1);
				FfData ff(module, &initvals, remap_name(c->name));
				ff.width = 1;
				ff.is_fine = true;
				ff.has_clk = true;
				ff.pol_clk = clk_polarity;
				ff.sig_clk = clk_sig;
				if (en_sig.size() != 0) {
					log_assert(en_sig.size() == 1);
					ff.pol_ce = en_polarity;
					ff.sig_ce = en_sig;
				}
				RTLIL::Const init = mapped_initvals(c->getPort(ID::Q));
				if (had_init)
					ff.val_init = init;
				else
					ff.val_init = State::Sx;
				if (arst_sig.size() != 0) {
					log_assert(arst_sig.size() == 1);
					ff.pol_arst = arst_polarity;
					ff.sig_arst = arst_sig;
					ff.val_arst = init;
				}
				if (srst_sig.size() != 0) {
					log_assert(srst_sig.size() == 1);
					ff.pol_srst = srst_polarity;
					ff.sig_srst = srst_sig;
					ff.val_srst = init;
				}
				ff.sig_d = module->wire(remap_name(c->getPort(ID::D).as_wire()->name));
				ff.sig_q = module->wire(remap_name(c->getPort(ID::Q).as_wire()->name));
				RTLIL::Cell *cell = ff.emit();
				if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
				design->select(module, cell);
				continue;
			}

			if (c->type == ID($lut) && GetSize(c->getPort(ID::A)) == 1 && c->getParam(ID::LUT).as_int() == 2) {
				SigSpec my_a = module->wire(remap_name(c->getPort(ID::A).as_wire()->name));
				SigSpec my_y = module->wire(remap_name(c->getPort(ID::Y).as_wire()->name));
				module->connect(my_y, my_a);
				continue;
			}

			RTLIL::Cell *cell = module->addCell(remap_name(c->name), c->type);
			if (markgroups) cell->attributes[ID::abcgroup] = map_autoidx;
			cell->parameters = c->parameters;
			for (auto &conn : c->connections()) {
				RTLIL::SigSpec newsig;
				for (auto &c : conn.second.chunks()) {
					if (c.width == 0)
						continue;
					log_assert(c.width == 1);
					newsig.append(module->wire(remap_name(c.wire->name)));
				}
				cell->setPort(conn.first, newsig);
			}
			design->select(module, cell);
		}

		for (auto conn : mapped_mod->connections()) {
			if (!conn.first.is_fully_const())
				conn.first = module->wire(remap_name(conn.first.as_wire()->name));
			if (!conn.second.is_fully_const())
				conn.second = module->wire(remap_name(conn.second.as_wire()->name));
			module->connect(conn);
		}

		for (auto &it : cell_stats)
			log("ABC RESULTS:   %15s cells: %8d\n", it.first.c_str(), it.second);
		int in_wires = 0, out_wires = 0;
		for (auto &si : signal_list)
			if (si.is_port) {
				char buffer[100];
				snprintf(buffer, 100, "\\ys__n%d", si.id);
				RTLIL::SigSig conn;
				if (si.type != G(NONE)) {
					conn.first = si.bit;
					conn.second = module->wire(remap_name(buffer));
					out_wires++;
				} else {
					conn.first = module->wire(remap_name(buffer));
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
	void help() override
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
		log("        use the specified command instead of \"<yosys-bindir>/%syosys-abc\" to execute ABC.\n", proc_program_prefix().c_str());
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
		log("        for -liberty/-genlib without -constr:\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_LIB).c_str());
		log("\n");
		log("        for -liberty/-genlib with -constr:\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_CTR).c_str());
		log("\n");
		log("        for -lut/-luts (only one LUT size):\n");
		log("%s\n", fold_abc_cmd(ABC_COMMAND_LUT "; lutpack {S}").c_str());
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
		log("        for -liberty/-genlib without -constr:\n");
		log("%s\n", fold_abc_cmd(ABC_FAST_COMMAND_LIB).c_str());
		log("\n");
		log("        for -liberty/-genlib with -constr:\n");
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
		log("    -dont_use <cell_name>\n");
		log("        generate netlists for the specified cell library (using the liberty\n");
		log("        file format).\n");
		log("\n");
		log("    -genlib <file>\n");
		log("        generate netlists for the specified cell library (using the SIS Genlib\n");
		log("        file format).\n");
		log("\n");
		log("    -constr <file>\n");
		log("        pass this file with timing constraints to ABC.\n");
		log("        use with -liberty/-genlib.\n");
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
		log("        this also replaces 'dretime' with 'dretime; retime -o {D}' in the\n");
		log("        default scripts above.\n");
		log("\n");
		log("    -I <num>\n");
		log("        maximum number of SOP inputs.\n");
		log("        (replaces {I} in the default scripts above)\n");
		log("\n");
		log("    -P <num>\n");
		log("        maximum number of SOP products.\n");
		log("        (replaces {P} in the default scripts above)\n");
		log("\n");
		log("    -S <num>\n");
		log("        maximum number of LUT inputs shared.\n");
		log("        (replaces {S} in the default scripts above, default: -S 1)\n");
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
		// log("        (ignored when used with -liberty/-genlib or -lut)\n");
		// log("\n");
		log("    -g type1,type2,...\n");
		log("        Map to the specified list of gate types. Supported gates types are:\n");
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("           AND, NAND, OR, NOR, XOR, XNOR, ANDNOT, ORNOT, MUX,\n");
		log("           NMUX, AOI3, OAI3, AOI4, OAI4.\n");
		log("        (The NOT gate is always added to this list automatically.)\n");
		log("\n");
		log("        The following aliases can be used to reference common sets of gate\n");
		log("        types:\n");
		log("          simple: AND OR XOR MUX\n");
		log("          cmos2:  NAND NOR\n");
		log("          cmos3:  NAND NOR AOI3 OAI3\n");
		log("          cmos4:  NAND NOR AOI3 OAI3 AOI4 OAI4\n");
		log("          cmos:   NAND NOR AOI3 OAI3 AOI4 OAI4 NMUX MUX XOR XNOR\n");
		log("          gates:  AND NAND OR NOR XOR XNOR ANDNOT ORNOT\n");
		log("          aig:    AND NAND OR NOR ANDNOT ORNOT\n");
		log("\n");
		log("        The alias 'all' represent the full set of all gate types.\n");
		log("\n");
		log("        Prefix a gate type with a '-' to remove it from the list. For example\n");
		log("        the arguments 'AND,OR,XOR' and 'simple,-MUX' are equivalent.\n");
		log("\n");
		log("        The default is 'all,-NMUX,-AOI3,-OAI3,-AOI4,-OAI4'.\n");
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
		log("    -dress\n");
		log("        run the 'dress' command after all other ABC commands. This aims to\n");
		log("        preserve naming by an equivalence check between the original and\n");
		log("        post-ABC netlists (experimental).\n");
		log("\n");
		log("When no target cell library is specified the Yosys standard cell library is\n");
		log("loaded into ABC before the ABC script is executed.\n");
		log("\n");
		log("Note that this is a logic optimization pass within Yosys that is calling ABC\n");
		log("internally. This is not going to \"run ABC on your design\". It will instead run\n");
		log("ABC on logic snippets extracted from your design. You will not get any useful\n");
		log("output when passing an ABC script that writes a file. Instead write your full\n");
		log("design as BLIF file with write_blif and then load that into ABC externally if\n");
		log("you want to use ABC to convert your design into another format.\n");
		log("\n");
		log("[1] http://www.eecs.berkeley.edu/~alanmi/abc/\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing ABC pass (technology mapping using ABC).\n");
		log_push();

		assign_map.clear();
		signal_list.clear();
		signal_map.clear();
		initvals.clear();
		pi_map.clear();
		po_map.clear();

		std::string exe_file = yosys_abc_executable;
		std::string script_file, default_liberty_file, constr_file, clk_str;
		std::vector<std::string> liberty_files, genlib_files, dont_use_cells;
		std::string delay_target, sop_inputs, sop_products, lutin_shared = "-S 1";
		bool fast_mode = false, dff_mode = false, keepff = false, cleanup = true;
		bool show_tempdir = false, sop_mode = false;
		bool abc_dress = false;
		vector<int> lut_costs;
		markgroups = false;

		map_mux4 = false;
		map_mux8 = false;
		map_mux16 = false;
		enabled_gates.clear();
		cmos_cost = false;

		// get arguments from scratchpad first, then override by command arguments
		std::string lut_arg, luts_arg, g_arg;
		exe_file = design->scratchpad_get_string("abc.exe", exe_file /* inherit default value if not set */);
		script_file = design->scratchpad_get_string("abc.script", script_file);
		default_liberty_file = design->scratchpad_get_string("abc.liberty", default_liberty_file);
		constr_file = design->scratchpad_get_string("abc.constr", constr_file);
		if (design->scratchpad.count("abc.D")) {
			delay_target = "-D " + design->scratchpad_get_string("abc.D");
		}
		if (design->scratchpad.count("abc.I")) {
			sop_inputs = "-I " + design->scratchpad_get_string("abc.I");
		}
		if (design->scratchpad.count("abc.P")) {
			sop_products = "-P " + design->scratchpad_get_string("abc.P");
		}
		if (design->scratchpad.count("abc.S")) {
			lutin_shared = "-S " + design->scratchpad_get_string("abc.S");
		}
		lut_arg = design->scratchpad_get_string("abc.lut", lut_arg);
		luts_arg = design->scratchpad_get_string("abc.luts", luts_arg);
		sop_mode = design->scratchpad_get_bool("abc.sop", sop_mode);
		map_mux4 = design->scratchpad_get_bool("abc.mux4", map_mux4);
		map_mux8 = design->scratchpad_get_bool("abc.mux8", map_mux8);
		map_mux16 = design->scratchpad_get_bool("abc.mux16", map_mux16);
		abc_dress = design->scratchpad_get_bool("abc.dress", abc_dress);
		g_arg = design->scratchpad_get_string("abc.g", g_arg);

		fast_mode = design->scratchpad_get_bool("abc.fast", fast_mode);
		dff_mode = design->scratchpad_get_bool("abc.dff", dff_mode);
		if (design->scratchpad.count("abc.clk")) {
			clk_str = design->scratchpad_get_string("abc.clk");
			dff_mode = true;
		}
		keepff = design->scratchpad_get_bool("abc.keepff", keepff);
		cleanup = !design->scratchpad_get_bool("abc.nocleanup", !cleanup);
		keepff = design->scratchpad_get_bool("abc.keepff", keepff);
		show_tempdir = design->scratchpad_get_bool("abc.showtmp", show_tempdir);
		markgroups = design->scratchpad_get_bool("abc.markgroups", markgroups);

		if (design->scratchpad_get_bool("abc.debug")) {
			cleanup = false;
			show_tempdir = true;
		}

		size_t argidx, g_argidx;
		bool g_arg_from_cmd = false;
#if defined(__wasm)
		const char *pwd = ".";
#else
		char pwd [PATH_MAX];
		if (!getcwd(pwd, sizeof(pwd))) {
			log_cmd_error("getcwd failed: %s\n", strerror(errno));
			log_abort();
		}
#endif
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-exe" && argidx+1 < args.size()) {
				exe_file = args[++argidx];
				continue;
			}
			if (arg == "-script" && argidx+1 < args.size()) {
				script_file = args[++argidx];
				continue;
			}
			if (arg == "-liberty" && argidx+1 < args.size()) {
				liberty_files.push_back(args[++argidx]);
				continue;
			}
			if (arg == "-dont_use" && argidx+1 < args.size()) {
				dont_use_cells.push_back(args[++argidx]);
				continue;
			}
			if (arg == "-genlib" && argidx+1 < args.size()) {
				genlib_files.push_back(args[++argidx]);
				continue;
			}
			if (arg == "-constr" && argidx+1 < args.size()) {
				constr_file = args[++argidx];
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
			if (arg == "-S" && argidx+1 < args.size()) {
				lutin_shared = "-S " + args[++argidx];
				continue;
			}
			if (arg == "-lut" && argidx+1 < args.size()) {
				lut_arg = args[++argidx];
				continue;
			}
			if (arg == "-luts" && argidx+1 < args.size()) {
				luts_arg = args[++argidx];
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
			if (arg == "-dress") {
				abc_dress = true;
				continue;
			}
			if (arg == "-g" && argidx+1 < args.size()) {
				if (g_arg_from_cmd)
					log_cmd_error("Can only use -g once. Please combine.");
				g_arg = args[++argidx];
				g_argidx = argidx;
				g_arg_from_cmd = true;
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

		if (genlib_files.empty() && liberty_files.empty() && !default_liberty_file.empty())
			liberty_files.push_back(default_liberty_file);

		rewrite_filename(script_file);
		if (!script_file.empty() && !is_absolute_path(script_file) && script_file[0] != '+')
			script_file = std::string(pwd) + "/" + script_file;
		for (int i = 0; i < GetSize(liberty_files); i++) {
			rewrite_filename(liberty_files[i]);
			if (!liberty_files[i].empty() && !is_absolute_path(liberty_files[i]))
				liberty_files[i] = std::string(pwd) + "/" + liberty_files[i];
		}
		for (int i = 0; i < GetSize(genlib_files); i++) {
			rewrite_filename(genlib_files[i]);
			if (!genlib_files[i].empty() && !is_absolute_path(genlib_files[i]))
				genlib_files[i] = std::string(pwd) + "/" + genlib_files[i];
		}
		rewrite_filename(constr_file);
		if (!constr_file.empty() && !is_absolute_path(constr_file))
			constr_file = std::string(pwd) + "/" + constr_file;

		// handle -lut argument
		if (!lut_arg.empty()) {
			size_t pos = lut_arg.find_first_of(':');
			int lut_mode = 0, lut_mode2 = 0;
			if (pos != string::npos) {
				lut_mode = atoi(lut_arg.substr(0, pos).c_str());
				lut_mode2 = atoi(lut_arg.substr(pos+1).c_str());
			} else {
				lut_mode = atoi(lut_arg.c_str());
				lut_mode2 = lut_mode;
			}
			lut_costs.clear();
			for (int i = 0; i < lut_mode; i++)
				lut_costs.push_back(1);
			for (int i = lut_mode; i < lut_mode2; i++)
				lut_costs.push_back(2 << (i - lut_mode));
		}
		//handle -luts argument
		if (!luts_arg.empty()){
			lut_costs.clear();
			for (auto &tok : split_tokens(luts_arg, ",")) {
				auto parts = split_tokens(tok, ":");
				if (GetSize(parts) == 0 && !lut_costs.empty())
					lut_costs.push_back(lut_costs.back());
				else if (GetSize(parts) == 1)
					lut_costs.push_back(atoi(parts.at(0).c_str()));
				else if (GetSize(parts) == 2)
					while (GetSize(lut_costs) < std::atoi(parts.at(0).c_str()))
						lut_costs.push_back(atoi(parts.at(1).c_str()));
				else
					log_cmd_error("Invalid -luts syntax.\n");
			}
		}

		// handle -g argument
		if (!g_arg.empty()){
			for (auto g : split_tokens(g_arg, ",")) {
				vector<string> gate_list;
				bool remove_gates = false;
				if (GetSize(g) > 0 && g[0] == '-') {
					remove_gates = true;
					g = g.substr(1);
				}
				if (g == "AND") goto ok_gate;
				if (g == "NAND") goto ok_gate;
				if (g == "OR") goto ok_gate;
				if (g == "NOR") goto ok_gate;
				if (g == "XOR") goto ok_gate;
				if (g == "XNOR") goto ok_gate;
				if (g == "ANDNOT") goto ok_gate;
				if (g == "ORNOT") goto ok_gate;
				if (g == "MUX") goto ok_gate;
				if (g == "NMUX") goto ok_gate;
				if (g == "AOI3") goto ok_gate;
				if (g == "OAI3") goto ok_gate;
				if (g == "AOI4") goto ok_gate;
				if (g == "OAI4") goto ok_gate;
				if (g == "simple") {
					gate_list.push_back("AND");
					gate_list.push_back("OR");
					gate_list.push_back("XOR");
					gate_list.push_back("MUX");
					goto ok_alias;
				}
				if (g == "cmos2") {
					if (!remove_gates)
						cmos_cost = true;
					gate_list.push_back("NAND");
					gate_list.push_back("NOR");
					goto ok_alias;
				}
				if (g == "cmos3") {
					if (!remove_gates)
						cmos_cost = true;
					gate_list.push_back("NAND");
					gate_list.push_back("NOR");
					gate_list.push_back("AOI3");
					gate_list.push_back("OAI3");
					goto ok_alias;
				}
				if (g == "cmos4") {
					if (!remove_gates)
						cmos_cost = true;
					gate_list.push_back("NAND");
					gate_list.push_back("NOR");
					gate_list.push_back("AOI3");
					gate_list.push_back("OAI3");
					gate_list.push_back("AOI4");
					gate_list.push_back("OAI4");
					goto ok_alias;
				}
				if (g == "cmos") {
					if (!remove_gates)
						cmos_cost = true;
					gate_list.push_back("NAND");
					gate_list.push_back("NOR");
					gate_list.push_back("AOI3");
					gate_list.push_back("OAI3");
					gate_list.push_back("AOI4");
					gate_list.push_back("OAI4");
					gate_list.push_back("NMUX");
					gate_list.push_back("MUX");
					gate_list.push_back("XOR");
					gate_list.push_back("XNOR");
					goto ok_alias;
				}
				if (g == "gates") {
					gate_list.push_back("AND");
					gate_list.push_back("NAND");
					gate_list.push_back("OR");
					gate_list.push_back("NOR");
					gate_list.push_back("XOR");
					gate_list.push_back("XNOR");
					gate_list.push_back("ANDNOT");
					gate_list.push_back("ORNOT");
					goto ok_alias;
				}
				if (g == "aig") {
					gate_list.push_back("AND");
					gate_list.push_back("NAND");
					gate_list.push_back("OR");
					gate_list.push_back("NOR");
					gate_list.push_back("ANDNOT");
					gate_list.push_back("ORNOT");
					goto ok_alias;
				}
				if (g == "all") {
					gate_list.push_back("AND");
					gate_list.push_back("NAND");
					gate_list.push_back("OR");
					gate_list.push_back("NOR");
					gate_list.push_back("XOR");
					gate_list.push_back("XNOR");
					gate_list.push_back("ANDNOT");
					gate_list.push_back("ORNOT");
					gate_list.push_back("AOI3");
					gate_list.push_back("OAI3");
					gate_list.push_back("AOI4");
					gate_list.push_back("OAI4");
					gate_list.push_back("MUX");
					gate_list.push_back("NMUX");
					goto ok_alias;
				}
				if (g_arg_from_cmd)
					cmd_error(args, g_argidx, stringf("Unsupported gate type: %s", g.c_str()));
				else
					log_cmd_error("Unsupported gate type: %s", g.c_str());
			ok_gate:
				gate_list.push_back(g);
			ok_alias:
				for (auto gate : gate_list) {
					if (remove_gates)
						enabled_gates.erase(gate);
					else
						enabled_gates.insert(gate);
				}
			}
		}

		if (!lut_costs.empty() && !(liberty_files.empty() && genlib_files.empty()))
			log_cmd_error("Got -lut and -liberty/-genlib! These two options are exclusive.\n");
		if (!constr_file.empty() && (liberty_files.empty() && genlib_files.empty()))
			log_cmd_error("Got -constr but no -liberty/-genlib!\n");

		if (enabled_gates.empty()) {
			enabled_gates.insert("AND");
			enabled_gates.insert("NAND");
			enabled_gates.insert("OR");
			enabled_gates.insert("NOR");
			enabled_gates.insert("XOR");
			enabled_gates.insert("XNOR");
			enabled_gates.insert("ANDNOT");
			enabled_gates.insert("ORNOT");
			// enabled_gates.insert("AOI3");
			// enabled_gates.insert("OAI3");
			// enabled_gates.insert("AOI4");
			// enabled_gates.insert("OAI4");
			enabled_gates.insert("MUX");
			// enabled_gates.insert("NMUX");
		}

		for (auto mod : design->selected_modules())
		{
			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", log_id(mod));
				continue;
			}

			assign_map.set(mod);
			initvals.set(&assign_map, mod);

			if (!dff_mode || !clk_str.empty()) {
				abc_module(design, mod, script_file, exe_file, liberty_files, genlib_files, constr_file, cleanup, lut_costs, dff_mode, clk_str, keepff,
						delay_target, sop_inputs, sop_products, lutin_shared, fast_mode, mod->selected_cells(), show_tempdir, sop_mode, abc_dress, dont_use_cells);
				continue;
			}

			CellTypes ct(design);

			std::vector<RTLIL::Cell*> all_cells = mod->selected_cells();
			pool<RTLIL::Cell*> unassigned_cells(all_cells.begin(), all_cells.end());

			pool<RTLIL::Cell*> expand_queue, next_expand_queue;
			pool<RTLIL::Cell*> expand_queue_up, next_expand_queue_up;
			pool<RTLIL::Cell*> expand_queue_down, next_expand_queue_down;

			typedef tuple<bool, RTLIL::SigSpec, bool, RTLIL::SigSpec, bool, RTLIL::SigSpec, bool, RTLIL::SigSpec> clkdomain_t;
			dict<clkdomain_t, std::vector<RTLIL::Cell*>> assigned_cells;
			dict<RTLIL::Cell*, clkdomain_t> assigned_cells_reverse;

			dict<RTLIL::Cell*, pool<RTLIL::SigBit>> cell_to_bit, cell_to_bit_up, cell_to_bit_down;
			dict<RTLIL::SigBit, pool<RTLIL::Cell*>> bit_to_cell, bit_to_cell_up, bit_to_cell_down;

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

				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				FfData ff(&initvals, cell);
				if (!ff.has_clk)
					continue;
				if (ff.has_gclk)
					continue;
				if (ff.has_aload)
					continue;
				if (ff.has_sr)
					continue;
				if (!ff.is_fine)
					continue;
				key = clkdomain_t(
					ff.pol_clk,
					ff.sig_clk,
					ff.has_ce ? ff.pol_ce : true,
					ff.has_ce ? assign_map(ff.sig_ce) : RTLIL::SigSpec(),
					ff.has_arst ? ff.pol_arst : true,
					ff.has_arst ? assign_map(ff.sig_arst) : RTLIL::SigSpec(),
					ff.has_srst ? ff.pol_srst : true,
					ff.has_srst ? assign_map(ff.sig_srst) : RTLIL::SigSpec()
				);

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

			clkdomain_t key(true, RTLIL::SigSpec(), true, RTLIL::SigSpec(), true, RTLIL::SigSpec(), true, RTLIL::SigSpec());
			for (auto cell : unassigned_cells) {
				assigned_cells[key].push_back(cell);
				assigned_cells_reverse[cell] = key;
			}

			log_header(design, "Summary of detected clock domains:\n");
			for (auto &it : assigned_cells)
				log("  %d cells in clk=%s%s, en=%s%s, arst=%s%s, srst=%s%s\n", GetSize(it.second),
						std::get<0>(it.first) ? "" : "!", log_signal(std::get<1>(it.first)),
						std::get<2>(it.first) ? "" : "!", log_signal(std::get<3>(it.first)),
						std::get<4>(it.first) ? "" : "!", log_signal(std::get<5>(it.first)),
						std::get<6>(it.first) ? "" : "!", log_signal(std::get<7>(it.first)));

			for (auto &it : assigned_cells) {
				clk_polarity = std::get<0>(it.first);
				clk_sig = assign_map(std::get<1>(it.first));
				en_polarity = std::get<2>(it.first);
				en_sig = assign_map(std::get<3>(it.first));
				arst_polarity = std::get<4>(it.first);
				arst_sig = assign_map(std::get<5>(it.first));
				srst_polarity = std::get<6>(it.first);
				srst_sig = assign_map(std::get<7>(it.first));
				abc_module(design, mod, script_file, exe_file, liberty_files, genlib_files, constr_file, cleanup, lut_costs, !clk_sig.empty(), "$",
						keepff, delay_target, sop_inputs, sop_products, lutin_shared, fast_mode, it.second, show_tempdir, sop_mode, abc_dress, dont_use_cells);
				assign_map.set(mod);
			}
		}

		assign_map.clear();
		signal_list.clear();
		signal_map.clear();
		initvals.clear();
		pi_map.clear();
		po_map.clear();

		log_pop();
	}
} AbcPass;

PRIVATE_NAMESPACE_END
