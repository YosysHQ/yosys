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

// [[CITE]] Berkeley Logic Interchange Format (BLIF)
// University of California. Berkeley. July 28, 1992
// http://www.ece.cmu.edu/~ee760/760docs/blif.pdf

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <string>

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
	G_ANDNOT,
	G_ORNOT,
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
	RTLIL::State init;
};

bool markgroups;
int map_autoidx;
SigMap assign_map;
RTLIL::Module *module;
std::vector<gate_t> signal_list;
std::map<RTLIL::SigBit, int> signal_map;
std::map<RTLIL::SigBit, RTLIL::State> signal_init;
pool<std::string> enabled_gates;
bool recover_init;

bool clk_polarity, en_polarity;
RTLIL::SigSpec clk_sig, en_sig;
dict<int, std::string> pi_map, po_map;

struct BlifDumperConfig
{
	bool icells_mode;
	bool conn_mode;
	bool impltf_mode;
	bool gates_mode;
	bool cname_mode;
	bool iname_mode;
	bool param_mode;
	bool attr_mode;
	bool iattr_mode;
	bool blackbox_mode;
	bool noalias_mode;

	std::string buf_type, buf_in, buf_out;
	std::map<RTLIL::IdString, std::pair<RTLIL::IdString, RTLIL::IdString>> unbuf_types;
	std::string true_type, true_out, false_type, false_out, undef_type, undef_out;

	BlifDumperConfig() : icells_mode(false), conn_mode(false), impltf_mode(false), gates_mode(false),
			cname_mode(false), iname_mode(false), param_mode(false), attr_mode(false), iattr_mode(false),
			blackbox_mode(false), noalias_mode(false) { }
};

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
		if (signal_init.count(bit))
			gate.init = signal_init.at(bit);
		else
			gate.init = State::Sx;
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

void extract_cell(RTLIL::Cell *cell)
{
	if (cell->type.in("$_DFF_N_", "$_DFF_P_", "$dff"))
	{
		std::cout << "Type is DFF_N or DFF_P\n";
		if (GetSize(en_sig) != 0)
			return;
		std::cout << "about to goto\n";
		goto matching_dff;
	}

	if (cell->type.in("$_DFFE_NN_", "$_DFFE_NP_", "$_DFFE_PN_", "$_DFFE_PP_"))
	{
		std::cout << "Type is DFFE_NN or DFFE_NP or DFFE_PN or DFFE_PP\n";
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

	if (cell->type.in("$_AND_", "$_NAND_", "$_OR_", "$_NOR_", "$_XOR_", "$_XNOR_", "$_ANDNOT_", "$_ORNOT_"))
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
		else if (cell->type == "$_ANDNOT_")
			map_signal(sig_y, G(ANDNOT), mapped_a, mapped_b);
		else if (cell->type == "$_ORNOT_")
			map_signal(sig_y, G(ORNOT), mapped_a, mapped_b);
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

void blif_writer_module(std::ostream &f, RTLIL::Module *current_module, RTLIL::Design *design,
		const std::vector<RTLIL::Cell*> &cells)
{
	module = current_module;
	map_autoidx = autoidx++;

	signal_map.clear();
	signal_list.clear();
	pi_map.clear();
	po_map.clear();
	recover_init = false;

	for (auto c : cells)
		extract_cell(c);

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

	dict<int, std::string> node_names;

	f << stringf(".model top\n");

	for (auto &si : signal_list){
		
		std::string name = log_signal(si.bit);
		// Remove beginning slash and any whitespace
		name.erase(0,1);
		name.erase(remove(name.begin(), name.end(), ' '), name.end());
		node_names[si.id] = name;
	}

	int count_input = 0;
	f << stringf(".inputs");
	for (auto &si : signal_list) {
		if (!si.is_port || si.type != G(NONE))
			continue;
		f << stringf(" %s", node_names[si.id].c_str());
		pi_map[count_input++] = log_signal(si.bit);
	}
	if (count_input == 0)
		f << stringf(" dummy_input\n");
	f << stringf("\n");

	int count_output = 0;
	f << stringf(".outputs");
	for (auto &si : signal_list) {
		if (!si.is_port || si.type == G(NONE) || si.type == G(FF))
			continue;
		f << stringf(" %s", node_names[si.id].c_str());
		po_map[count_output++] = log_signal(si.bit);
	}
	f << stringf("\n");

	for (auto &si : signal_list) {
		if (si.bit.wire == NULL) {
			f << stringf(".names %s\n", node_names[si.id].c_str());
			if (si.bit == RTLIL::State::S1)
				f << stringf("1\n");
		}
	}

	int count_gates = 0;
	for (auto &si : signal_list) {
		if (si.type == G(BUF)) {
			f << stringf(".names %s %s\n", node_names[si.in1].c_str(), node_names[si.id].c_str());
			f << stringf("1 1\n");
		} else if (si.type == G(NOT)) {
			f << stringf(".names %s %s\n", node_names[si.in1].c_str(), node_names[si.id].c_str());
			f << stringf("0 1\n");
		} else if (si.type == G(AND)) {
			f << stringf(".names %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.id].c_str());
			f << stringf("11 1\n");
		} else if (si.type == G(NAND)) {
			f << stringf(".names %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.id].c_str());
			f << stringf("0- 1\n");
			f << stringf("-0 1\n");
		} else if (si.type == G(OR)) {
			f << stringf(".names %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.id].c_str());
			f << stringf("-1 1\n");
			f << stringf("1- 1\n");
		} else if (si.type == G(NOR)) {
			f << stringf(".names %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.id].c_str());
			f << stringf("00 1\n");
		} else if (si.type == G(XOR)) {
			f << stringf(".names %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.id].c_str());
			f << stringf("01 1\n");
			f << stringf("10 1\n");
		} else if (si.type == G(XNOR)) {
			f << stringf(".names %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.id].c_str());
			f << stringf("00 1\n");
			f << stringf("11 1\n");
		} else if (si.type == G(ANDNOT)) {
			f << stringf(".names %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.id].c_str());
			f << stringf("10 1\n");
		} else if (si.type == G(ORNOT)) {
			f << stringf(".names %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.id].c_str());
			f << stringf("1- 1\n");
			f << stringf("-0 1\n");
		} else if (si.type == G(MUX)) {
			f << stringf(".names %s %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.in3].c_str(), node_names[si.id].c_str());
			f << stringf("1-0 1\n");
			f << stringf("-11 1\n");
		} else if (si.type == G(AOI3)) {
			f << stringf(".names %s %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.in3].c_str(), node_names[si.id].c_str());
			f << stringf("-00 1\n");
			f << stringf("0-0 1\n");
		} else if (si.type == G(OAI3)) {
			f << stringf(".names %s %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.in3].c_str(), node_names[si.id].c_str());
			f << stringf("00- 1\n");
			f << stringf("--0 1\n");
		} else if (si.type == G(AOI4)) {
			f << stringf(".names %s %s %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.in3].c_str(), node_names[si.in4].c_str(), node_names[si.id].c_str());
			f << stringf("-0-0 1\n");
			f << stringf("-00- 1\n");
			f << stringf("0--0 1\n");
			f << stringf("0-0- 1\n");
		} else if (si.type == G(OAI4)) {
			f << stringf(".names %s %s %s %s %s\n", node_names[si.in1].c_str(), node_names[si.in2].c_str(), node_names[si.in3].c_str(), node_names[si.in4].c_str(), node_names[si.id].c_str());
			f << stringf("00-- 1\n");
			f << stringf("--00 1\n");
		} else if (si.type == G(FF)) {
			if (si.init == State::S0 || si.init == State::S1) {
				f << stringf(".latch %s %s %d\n", node_names[si.in1].c_str(), node_names[si.id].c_str(), si.init == State::S1 ? 1 : 0);
				recover_init = true;
			} else
				f << stringf(".latch %s %s 2\n", node_names[si.in1].c_str(), node_names[si.id].c_str());
		} else if (si.type != G(NONE))
			log_abort();
		if (si.type != G(NONE))
			count_gates++;
	}

	f << stringf(".end\n");
	log_pop();

}

struct BlifDumper
{
	std::ostream &f;
	RTLIL::Module *module;
	RTLIL::Design *design;
	BlifDumperConfig *config;
	CellTypes ct;

	SigMap sigmap;
	dict<SigBit, int> init_bits;

	BlifDumper(std::ostream &f, RTLIL::Module *module, RTLIL::Design *design, BlifDumperConfig *config) :
			f(f), module(module), design(design), config(config), ct(design), sigmap(module)
	{
		for (Wire *wire : module->wires())
			if (wire->attributes.count("\\init")) {
				SigSpec initsig = sigmap(wire);
				Const initval = wire->attributes.at("\\init");
				for (int i = 0; i < GetSize(initsig) && i < GetSize(initval); i++)
					switch (initval[i]) {
						case State::S0:
							init_bits[initsig[i]] = 0;
							break;
						case State::S1:
							init_bits[initsig[i]] = 1;
							break;
						default:
							break;
					}
			}
	}

	vector<shared_str> cstr_buf;
	pool<SigBit> cstr_bits_seen;

	const char *cstr(RTLIL::IdString id)
	{
		std::string str = RTLIL::unescape_id(id);
		for (size_t i = 0; i < str.size(); i++)
			if (str[i] == '#' || str[i] == '=' || str[i] == '<' || str[i] == '>')
				str[i] = '?';
		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	const char *cstr(RTLIL::SigBit sig)
	{
		cstr_bits_seen.insert(sig);

		if (sig.wire == NULL) {
			if (sig == RTLIL::State::S0) return config->false_type == "-" || config->false_type == "+" ? config->false_out.c_str() : "$false";
			if (sig == RTLIL::State::S1) return config->true_type == "-" || config->true_type == "+" ? config->true_out.c_str() : "$true";
			return config->undef_type == "-" || config->undef_type == "+" ? config->undef_out.c_str() : "$undef";
		}

		std::string str = RTLIL::unescape_id(sig.wire->name);
		for (size_t i = 0; i < str.size(); i++)
			if (str[i] == '#' || str[i] == '=' || str[i] == '<' || str[i] == '>')
				str[i] = '?';

		if (sig.wire->width != 1)
			str += stringf("[%d]", sig.wire->upto ? sig.wire->start_offset+sig.wire->width-sig.offset-1 : sig.wire->start_offset+sig.offset);

		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	const char *cstr_init(RTLIL::SigBit sig)
	{
		sigmap.apply(sig);

		if (init_bits.count(sig) == 0)
			return " 2";

		string str = stringf(" %d", init_bits.at(sig));

		cstr_buf.push_back(str);
		return cstr_buf.back().c_str();
	}

	const char *subckt_or_gate(std::string cell_type)
	{
		if (!config->gates_mode)
			return "subckt";
		if (!design->modules_.count(RTLIL::escape_id(cell_type)))
			return "gate";
		if (design->modules_.at(RTLIL::escape_id(cell_type))->get_blackbox_attribute())
			return "gate";
		return "subckt";
	}

	void dump_params(const char *command, dict<IdString, Const> &params)
	{
		for (auto &param : params) {
			f << stringf("%s %s ", command, RTLIL::id2cstr(param.first));
			if (param.second.flags & RTLIL::CONST_FLAG_STRING) {
				std::string str = param.second.decode_string();
				f << stringf("\"");
				for (char ch : str)
					if (ch == '"' || ch == '\\')
						f << stringf("\\%c", ch);
					else if (ch < 32 || ch >= 127)
						f << stringf("\\%03o", ch);
					else
						f << stringf("%c", ch);
				f << stringf("\"\n");
			} else
				f << stringf("%s\n", param.second.as_string().c_str());
		}
	}

	void dump()
	{
		f << stringf("\n");
		f << stringf(".model %s\n", cstr(module->name));

		std::map<int, RTLIL::Wire*> inputs, outputs;

		for (auto &wire_it : module->wires_) {
			RTLIL::Wire *wire = wire_it.second;
			if (wire->port_input)
				inputs[wire->port_id] = wire;
			if (wire->port_output)
				outputs[wire->port_id] = wire;
		}

		f << stringf(".inputs");
		for (auto &it : inputs) {
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				f << stringf(" %s", cstr(RTLIL::SigSpec(wire, i)));
		}
		f << stringf("\n");

		f << stringf(".outputs");
		for (auto &it : outputs) {
			RTLIL::Wire *wire = it.second;
			for (int i = 0; i < wire->width; i++)
				f << stringf(" %s", cstr(RTLIL::SigSpec(wire, i)));
		}
		f << stringf("\n");

		if (module->get_blackbox_attribute()) {
			f << stringf(".blackbox\n");
			f << stringf(".end\n");
			return;
		}

		if (!config->impltf_mode) {
			if (!config->false_type.empty()) {
				if (config->false_type == "+")
					f << stringf(".names %s\n", config->false_out.c_str());
				else if (config->false_type != "-")
					f << stringf(".%s %s %s=$false\n", subckt_or_gate(config->false_type),
							config->false_type.c_str(), config->false_out.c_str());
			} else
				f << stringf(".names $false\n");
			if (!config->true_type.empty()) {
				if (config->true_type == "+")
					f << stringf(".names %s\n1\n", config->true_out.c_str());
				else if (config->true_type != "-")
					f << stringf(".%s %s %s=$true\n", subckt_or_gate(config->true_type),
							config->true_type.c_str(), config->true_out.c_str());
			} else
				f << stringf(".names $true\n1\n");
			if (!config->undef_type.empty()) {
				if (config->undef_type == "+")
					f << stringf(".names %s\n", config->undef_out.c_str());
				else if (config->undef_type != "-")
					f << stringf(".%s %s %s=$undef\n", subckt_or_gate(config->undef_type),
							config->undef_type.c_str(), config->undef_out.c_str());
			} else
				f << stringf(".names $undef\n");
		}

		for (auto &cell_it : module->cells_)
		{
			RTLIL::Cell *cell = cell_it.second;

			if (config->unbuf_types.count(cell->type)) {
				auto portnames = config->unbuf_types.at(cell->type);
				f << stringf(".names %s %s\n1 1\n",
						cstr(cell->getPort(portnames.first)), cstr(cell->getPort(portnames.second)));
				continue;
			}

			if (!config->icells_mode && cell->type == "$_NOT_") {
				f << stringf(".names %s %s\n0 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_AND_") {
				f << stringf(".names %s %s %s\n11 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_OR_") {
				f << stringf(".names %s %s %s\n1- 1\n-1 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_XOR_") {
				f << stringf(".names %s %s %s\n10 1\n01 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_NAND_") {
				f << stringf(".names %s %s %s\n0- 1\n-0 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_NOR_") {
				f << stringf(".names %s %s %s\n00 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_XNOR_") {
				f << stringf(".names %s %s %s\n11 1\n00 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_ANDNOT_") {
				f << stringf(".names %s %s %s\n10 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_ORNOT_") {
				f << stringf(".names %s %s %s\n1- 1\n-0 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_AOI3_") {
				f << stringf(".names %s %s %s %s\n-00 1\n0-0 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\C")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_OAI3_") {
				f << stringf(".names %s %s %s %s\n00- 1\n--0 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")), cstr(cell->getPort("\\C")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_AOI4_") {
				f << stringf(".names %s %s %s %s %s\n-0-0 1\n-00- 1\n0--0 1\n0-0- 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")),
						cstr(cell->getPort("\\C")), cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_OAI4_") {
				f << stringf(".names %s %s %s %s %s\n00-- 1\n--00 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")),
						cstr(cell->getPort("\\C")), cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_MUX_") {
				f << stringf(".names %s %s %s %s\n1-0 1\n-11 1\n",
						cstr(cell->getPort("\\A")), cstr(cell->getPort("\\B")),
						cstr(cell->getPort("\\S")), cstr(cell->getPort("\\Y")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_FF_") {
				f << stringf(".latch %s %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr_init(cell->getPort("\\Q")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_DFF_N_") {
				f << stringf(".latch %s %s fe %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr(cell->getPort("\\C")), cstr_init(cell->getPort("\\Q")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_DFF_P_") {
				f << stringf(".latch %s %s re %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr(cell->getPort("\\C")), cstr_init(cell->getPort("\\Q")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_DLATCH_N_") {
				f << stringf(".latch %s %s al %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr(cell->getPort("\\E")), cstr_init(cell->getPort("\\Q")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$_DLATCH_P_") {
				f << stringf(".latch %s %s ah %s%s\n", cstr(cell->getPort("\\D")), cstr(cell->getPort("\\Q")),
						cstr(cell->getPort("\\E")), cstr_init(cell->getPort("\\Q")));
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$lut") {
				f << stringf(".names");
				auto &inputs = cell->getPort("\\A");
				auto width = cell->parameters.at("\\WIDTH").as_int();
				log_assert(inputs.size() == width);
				for (int i = width-1; i >= 0; i--)
					f << stringf(" %s", cstr(inputs.extract(i, 1)));
				auto &output = cell->getPort("\\Y");
				log_assert(output.size() == 1);
				f << stringf(" %s", cstr(output));
				f << stringf("\n");
				RTLIL::SigSpec mask = cell->parameters.at("\\LUT");
				for (int i = 0; i < (1 << width); i++)
					if (mask[i] == RTLIL::S1) {
						for (int j = width-1; j >= 0; j--) {
							f << ((i>>j)&1 ? '1' : '0');
						}
						f << " 1\n";
					}
				goto internal_cell;
			}

			if (!config->icells_mode && cell->type == "$sop") {
				f << stringf(".names");
				auto &inputs = cell->getPort("\\A");
				auto width = cell->parameters.at("\\WIDTH").as_int();
				auto depth = cell->parameters.at("\\DEPTH").as_int();
				vector<State> table = cell->parameters.at("\\TABLE").bits;
				while (GetSize(table) < 2*width*depth)
					table.push_back(State::S0);
				log_assert(inputs.size() == width);
				for (int i = 0; i < width; i++)
					f << stringf(" %s", cstr(inputs.extract(i, 1)));
				auto &output = cell->getPort("\\Y");
				log_assert(output.size() == 1);
				f << stringf(" %s", cstr(output));
				f << stringf("\n");
				for (int i = 0; i < depth; i++) {
					for (int j = 0; j < width; j++) {
						bool pat0 = table.at(2*width*i + 2*j + 0) == State::S1;
						bool pat1 = table.at(2*width*i + 2*j + 1) == State::S1;
						if (pat0 && !pat1) f << "0";
						else if (!pat0 && pat1) f << "1";
						else f << "-";
					}
					f << " 1\n";
				}
				goto internal_cell;
			}

			f << stringf(".%s %s", subckt_or_gate(cell->type.str()), cstr(cell->type));
			for (auto &conn : cell->connections())
			{
				if (conn.second.size() == 1) {
					f << stringf(" %s=%s", cstr(conn.first), cstr(conn.second[0]));
					continue;
				}

				Module *m = design->module(cell->type);
				Wire *w = m ? m->wire(conn.first) : nullptr;

				if (w == nullptr) {
					for (int i = 0; i < GetSize(conn.second); i++)
						f << stringf(" %s[%d]=%s", cstr(conn.first), i, cstr(conn.second[i]));
				} else {
					for (int i = 0; i < std::min(GetSize(conn.second), GetSize(w)); i++) {
						SigBit sig(w, i);
						f << stringf(" %s[%d]=%s", cstr(conn.first), sig.wire->upto ?
								sig.wire->start_offset+sig.wire->width-sig.offset-1 :
								sig.wire->start_offset+sig.offset, cstr(conn.second[i]));
					}
				}
			}
			f << stringf("\n");

			if (config->cname_mode)
				f << stringf(".cname %s\n", cstr(cell->name));
			if (config->attr_mode)
				dump_params(".attr", cell->attributes);
			if (config->param_mode)
				dump_params(".param", cell->parameters);

			if (0) {
		internal_cell:
				if (config->iname_mode)
					f << stringf(".cname %s\n", cstr(cell->name));
				if (config->iattr_mode)
					dump_params(".attr", cell->attributes);
			}
		}

		for (auto &conn : module->connections())
		for (int i = 0; i < conn.first.size(); i++)
		{
			SigBit lhs_bit = conn.first[i];
			SigBit rhs_bit = conn.second[i];

			if (config->noalias_mode && cstr_bits_seen.count(lhs_bit) == 0)
				continue;

			if (config->conn_mode)
				f << stringf(".conn %s %s\n", cstr(rhs_bit), cstr(lhs_bit));
			else if (!config->buf_type.empty())
				f << stringf(".%s %s %s=%s %s=%s\n", subckt_or_gate(config->buf_type), config->buf_type.c_str(),
						config->buf_in.c_str(), cstr(rhs_bit), config->buf_out.c_str(), cstr(lhs_bit));
			else
				f << stringf(".names %s %s\n1 1\n", cstr(rhs_bit), cstr(lhs_bit));
		}

		f << stringf(".end\n");
	}

	static void dump(std::ostream &f, RTLIL::Module *module, RTLIL::Design *design, BlifDumperConfig &config)
	{
		BlifDumper dumper(f, module, design, &config);
		dumper.dump();
	}
};

struct BlifBackend : public Backend {
	BlifBackend() : Backend("blif", "write design to BLIF file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_blif [options] [filename]\n");
		log("\n");
		log("Write the current design to an BLIF file.\n");
		log("\n");
		log("    -top top_module\n");
		log("        set the specified module as design top module\n");
		log("\n");
		log("    -buf <cell-type> <in-port> <out-port>\n");
		log("        use cells of type <cell-type> with the specified port names for buffers\n");
		log("\n");
		log("    -unbuf <cell-type> <in-port> <out-port>\n");
		log("        replace buffer cells with the specified name and port names with\n");
		log("        a .names statement that models a buffer\n");
		log("\n");
		log("    -true <cell-type> <out-port>\n");
		log("    -false <cell-type> <out-port>\n");
		log("    -undef <cell-type> <out-port>\n");
		log("        use the specified cell types to drive nets that are constant 1, 0, or\n");
		log("        undefined. when '-' is used as <cell-type>, then <out-port> specifies\n");
		log("        the wire name to be used for the constant signal and no cell driving\n");
		log("        that wire is generated. when '+' is used as <cell-type>, then <out-port>\n");
		log("        specifies the wire name to be used for the constant signal and a .names\n");
		log("        statement is generated to drive the wire.\n");
		log("\n");
		log("    -noalias\n");
		log("        if a net name is aliasing another net name, then by default a net\n");
		log("        without fanout is created that is driven by the other net. This option\n");
		log("        suppresses the generation of this nets without fanout.\n");
		log("\n");
		log("The following options can be useful when the generated file is not going to be\n");
		log("read by a BLIF parser but a custom tool. It is recommended to not name the output\n");
		log("file *.blif when any of this options is used.\n");
		log("\n");
		log("    -icells\n");
		log("        do not translate Yosys's internal gates to generic BLIF logic\n");
		log("        functions. Instead create .subckt or .gate lines for all cells.\n");
		log("\n");
		log("    -gates\n");
		log("        print .gate instead of .subckt lines for all cells that are not\n");
		log("        instantiations of other modules from this design.\n");
		log("\n");
		log("    -conn\n");
		log("        do not generate buffers for connected wires. instead use the\n");
		log("        non-standard .conn statement.\n");
		log("\n");
		log("    -attr\n");
		log("        use the non-standard .attr statement to write cell attributes\n");
		log("\n");
		log("    -param\n");
		log("        use the non-standard .param statement to write cell parameters\n");
		log("\n");
		log("    -cname\n");
		log("        use the non-standard .cname statement to write cell names\n");
		log("\n");
		log("    -iname, -iattr\n");
		log("        enable -cname and -attr functionality for .names statements\n");
		log("        (the .cname and .attr statements will be included in the BLIF\n");
		log("        output after the truth table for the .names statement)\n");
		log("\n");
		log("    -blackbox\n");
		log("        write blackbox cells with .blackbox statement.\n");
		log("\n");
		log("    -impltf\n");
		log("        do not write definitions for the $true, $false and $undef wires.\n");
		log("\n");
		log("    -flatten\n");
		log("        write design in BLIF format without the use of the .subckt or .gate functions.\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string top_module_name;
		std::string buf_type, buf_in, buf_out;
		std::string true_type, true_out;
		std::string false_type, false_out;
		BlifDumperConfig config;
		bool flatten = false;

		log_header(design, "Executing BLIF backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module_name = args[++argidx];
				continue;
			}
			if (args[argidx] == "-buf" && argidx+3 < args.size()) {
				config.buf_type = args[++argidx];
				config.buf_in = args[++argidx];
				config.buf_out = args[++argidx];
				continue;
			}
			if (args[argidx] == "-unbuf" && argidx+3 < args.size()) {
				RTLIL::IdString unbuf_type = RTLIL::escape_id(args[++argidx]);
				RTLIL::IdString unbuf_in = RTLIL::escape_id(args[++argidx]);
				RTLIL::IdString unbuf_out = RTLIL::escape_id(args[++argidx]);
				config.unbuf_types[unbuf_type] = std::pair<RTLIL::IdString, RTLIL::IdString>(unbuf_in, unbuf_out);
				continue;
			}
			if (args[argidx] == "-true" && argidx+2 < args.size()) {
				config.true_type = args[++argidx];
				config.true_out = args[++argidx];
				continue;
			}
			if (args[argidx] == "-false" && argidx+2 < args.size()) {
				config.false_type = args[++argidx];
				config.false_out = args[++argidx];
				continue;
			}
			if (args[argidx] == "-undef" && argidx+2 < args.size()) {
				config.undef_type = args[++argidx];
				config.undef_out = args[++argidx];
				continue;
			}
			if (args[argidx] == "-icells") {
				config.icells_mode = true;
				continue;
			}
			if (args[argidx] == "-gates") {
				config.gates_mode = true;
				continue;
			}
			if (args[argidx] == "-conn") {
				config.conn_mode = true;
				continue;
			}
			if (args[argidx] == "-cname") {
				config.cname_mode = true;
				continue;
			}
			if (args[argidx] == "-param") {
				config.param_mode = true;
				continue;
			}
			if (args[argidx] == "-attr") {
				config.attr_mode = true;
				continue;
			}
			if (args[argidx] == "-iname") {
				config.iname_mode = true;
				continue;
			}
			if (args[argidx] == "-iattr") {
				config.iattr_mode = true;
				continue;
			}
			if (args[argidx] == "-blackbox") {
				config.blackbox_mode = true;
				continue;
			}
			if (args[argidx] == "-impltf") {
				config.impltf_mode = true;
				continue;
			}
			if (args[argidx] == "-noalias") {
				config.noalias_mode = true;
				continue;
			}
			if (args[argidx] == "-flatten") {
				flatten = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		if (top_module_name.empty())
			for (auto & mod_it:design->modules_)
				if (mod_it.second->get_bool_attribute("\\top"))
					top_module_name = mod_it.first.str();

		*f << stringf("# Generated by %s\n", yosys_version_str);

		std::vector<RTLIL::Module*> mod_list;

		design->sort();
		for (auto module_it : design->modules_)
		{
			RTLIL::Module *module = module_it.second;
			if (module->get_blackbox_attribute() && !config.blackbox_mode)
				continue;

			if (module->processes.size() != 0)
				log_error("Found unmapped processes in module %s: unmapped processes are not supported in BLIF backend!\n", RTLIL::id2cstr(module->name));
			if (module->memories.size() != 0)
				log_error("Found unmapped memories in module %s: unmapped memories are not supported in BLIF backend!\n", RTLIL::id2cstr(module->name));

			if (module->name == RTLIL::escape_id(top_module_name)) {
				BlifDumper::dump(*f, module, design, config);
				top_module_name.clear();
				continue;
			}

			mod_list.push_back(module);
		}

		if (!top_module_name.empty())
			log_error("Can't find top module `%s'!\n", top_module_name.c_str());

		for (auto module : mod_list){
			if (flatten)
				blif_writer_module(*f, module, design, module->selected_cells());
			else
				BlifDumper::dump(*f, module, design, config);
		}
	}
} BlifBackend;

PRIVATE_NAMESPACE_END
