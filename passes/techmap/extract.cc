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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "libs/subcircuit/subcircuit.h"
#include <algorithm>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using RTLIL::id2cstr;

class SubCircuitSolver : public SubCircuit::Solver
{
public:
	bool ignore_parameters;
	std::set<std::pair<RTLIL::IdString, RTLIL::IdString>> ignored_parameters;
	std::set<RTLIL::IdString> cell_attr, wire_attr;

	SubCircuitSolver() : ignore_parameters(false)
	{
	}

	bool compareAttributes(const std::set<RTLIL::IdString> &attr, const dict<RTLIL::IdString, RTLIL::Const> &needleAttr, const dict<RTLIL::IdString, RTLIL::Const> &haystackAttr)
	{
		for (auto &it : attr) {
			size_t nc = needleAttr.count(it), hc = haystackAttr.count(it);
			if (nc != hc || (nc > 0 && needleAttr.at(it) != haystackAttr.at(it)))
				return false;
		}
		return true;
	}

	RTLIL::Const unified_param(RTLIL::IdString cell_type, RTLIL::IdString param, RTLIL::Const value)
	{
		if (cell_type.substr(0, 1) != "$" || cell_type.substr(0, 2) == "$_")
			return value;

	#define param_bool(_n) if (param == _n) return value.as_bool();
		param_bool("\\ARST_POLARITY");
		param_bool("\\A_SIGNED");
		param_bool("\\B_SIGNED");
		param_bool("\\CLK_ENABLE");
		param_bool("\\CLK_POLARITY");
		param_bool("\\CLR_POLARITY");
		param_bool("\\EN_POLARITY");
		param_bool("\\SET_POLARITY");
		param_bool("\\TRANSPARENT");
	#undef param_bool

	#define param_int(_n) if (param == _n) return value.as_int();
		param_int("\\ABITS")
		param_int("\\A_WIDTH")
		param_int("\\B_WIDTH")
		param_int("\\CTRL_IN_WIDTH")
		param_int("\\CTRL_OUT_WIDTH")
		param_int("\\OFFSET")
		param_int("\\PRIORITY")
		param_int("\\RD_PORTS")
		param_int("\\SIZE")
		param_int("\\STATE_BITS")
		param_int("\\STATE_NUM")
		param_int("\\STATE_NUM_LOG2")
		param_int("\\STATE_RST")
		param_int("\\S_WIDTH")
		param_int("\\TRANS_NUM")
		param_int("\\WIDTH")
		param_int("\\WR_PORTS")
		param_int("\\Y_WIDTH")
	#undef param_int

		return value;
	}

	virtual bool userCompareNodes(const std::string &, const std::string &, void *needleUserData,
			const std::string &, const std::string &, void *haystackUserData, const std::map<std::string, std::string> &portMapping)
	{
		RTLIL::Cell *needleCell = (RTLIL::Cell*) needleUserData;
		RTLIL::Cell *haystackCell = (RTLIL::Cell*) haystackUserData;

		if (!needleCell || !haystackCell) {
			log_assert(!needleCell && !haystackCell);
			return true;
		}

		if (!ignore_parameters) {
			std::map<RTLIL::IdString, RTLIL::Const> needle_param, haystack_param;
			for (auto &it : needleCell->parameters)
				if (!ignored_parameters.count(std::pair<RTLIL::IdString, RTLIL::IdString>(needleCell->type, it.first)))
					needle_param[it.first] = unified_param(needleCell->type, it.first, it.second);
			for (auto &it : haystackCell->parameters)
				if (!ignored_parameters.count(std::pair<RTLIL::IdString, RTLIL::IdString>(haystackCell->type, it.first)))
					haystack_param[it.first] = unified_param(haystackCell->type, it.first, it.second);
			if (needle_param != haystack_param)
				return false;
		}

		if (cell_attr.size() > 0 && !compareAttributes(cell_attr, needleCell->attributes, haystackCell->attributes))
			return false;

		if (wire_attr.size() > 0)
		{
			RTLIL::Wire *lastNeedleWire = NULL;
			RTLIL::Wire *lastHaystackWire = NULL;
			dict<RTLIL::IdString, RTLIL::Const> emptyAttr;

			for (auto &conn : needleCell->connections())
			{
				RTLIL::SigSpec needleSig = conn.second;
				RTLIL::SigSpec haystackSig = haystackCell->getPort(portMapping.at(conn.first.str()));

				for (int i = 0; i < min(needleSig.size(), haystackSig.size()); i++) {
					RTLIL::Wire *needleWire = needleSig[i].wire, *haystackWire = haystackSig[i].wire;
					if (needleWire != lastNeedleWire || haystackWire != lastHaystackWire)
						if (!compareAttributes(wire_attr, needleWire ? needleWire->attributes : emptyAttr, haystackWire ? haystackWire->attributes : emptyAttr))
							return false;
					lastNeedleWire = needleWire, lastHaystackWire = haystackWire;
				}
			}
		}

		return true;
	}
};

struct bit_ref_t {
	std::string cell, port;
	int bit;
};

bool module2graph(SubCircuit::Graph &graph, RTLIL::Module *mod, bool constports, RTLIL::Design *sel = NULL,
		int max_fanout = -1, std::set<std::pair<RTLIL::IdString, RTLIL::IdString>> *split = NULL)
{
	SigMap sigmap(mod);
	std::map<RTLIL::SigBit, bit_ref_t> sig_bit_ref;

	if (sel && !sel->selected(mod)) {
		log("  Skipping module %s as it is not selected.\n", id2cstr(mod->name));
		return false;
	}

	if (mod->processes.size() > 0) {
		log("  Skipping module %s as it contains unprocessed processes.\n", id2cstr(mod->name));
		return false;
	}

	if (constports) {
		graph.createNode("$const$0", "$const$0", NULL, true);
		graph.createNode("$const$1", "$const$1", NULL, true);
		graph.createNode("$const$x", "$const$x", NULL, true);
		graph.createNode("$const$z", "$const$z", NULL, true);
		graph.createPort("$const$0", "\\Y", 1);
		graph.createPort("$const$1", "\\Y", 1);
		graph.createPort("$const$x", "\\Y", 1);
		graph.createPort("$const$z", "\\Y", 1);
		graph.markExtern("$const$0", "\\Y", 0);
		graph.markExtern("$const$1", "\\Y", 0);
		graph.markExtern("$const$x", "\\Y", 0);
		graph.markExtern("$const$z", "\\Y", 0);
	}

	std::map<std::pair<RTLIL::Wire*, int>, int> sig_use_count;
	if (max_fanout > 0)
		for (auto &cell_it : mod->cells_)
		{
			RTLIL::Cell *cell = cell_it.second;
			if (!sel || sel->selected(mod, cell))
				for (auto &conn : cell->connections()) {
					RTLIL::SigSpec conn_sig = conn.second;
					sigmap.apply(conn_sig);
					for (auto &bit : conn_sig)
						if (bit.wire != NULL)
							sig_use_count[std::pair<RTLIL::Wire*, int>(bit.wire, bit.offset)]++;
				}
		}

	// create graph nodes from cells
	for (auto &cell_it : mod->cells_)
	{
		RTLIL::Cell *cell = cell_it.second;
		if (sel && !sel->selected(mod, cell))
			continue;

		std::string type = cell->type.str();
		if (sel == NULL && type.substr(0, 2) == "\\$")
			type = type.substr(1);
		graph.createNode(cell->name.str(), type, (void*)cell);

		for (auto &conn : cell->connections())
		{
			graph.createPort(cell->name.str(), conn.first.str(), conn.second.size());

			if (split && split->count(std::pair<RTLIL::IdString, RTLIL::IdString>(cell->type, conn.first)) > 0)
				continue;

			RTLIL::SigSpec conn_sig = conn.second;
			sigmap.apply(conn_sig);

			for (int i = 0; i < conn_sig.size(); i++)
			{
				auto &bit = conn_sig[i];

				if (bit.wire == NULL) {
					if (constports) {
						std::string node = "$const$x";
						if (bit == RTLIL::State::S0) node = "$const$0";
						if (bit == RTLIL::State::S1) node = "$const$1";
						if (bit == RTLIL::State::Sz) node = "$const$z";
						graph.createConnection(cell->name.str(), conn.first.str(), i, node, "\\Y", 0);
					} else
						graph.createConstant(cell->name.str(), conn.first.str(), i, int(bit.data));
					continue;
				}

				if (max_fanout > 0 && sig_use_count[std::pair<RTLIL::Wire*, int>(bit.wire, bit.offset)] > max_fanout)
					continue;

				if (sel && !sel->selected(mod, bit.wire))
					continue;

				if (sig_bit_ref.count(bit) == 0) {
					bit_ref_t &bit_ref = sig_bit_ref[bit];
					bit_ref.cell = cell->name.str();
					bit_ref.port = conn.first.str();
					bit_ref.bit = i;
				}

				bit_ref_t &bit_ref = sig_bit_ref[bit];
				graph.createConnection(bit_ref.cell, bit_ref.port, bit_ref.bit, cell->name.str(), conn.first.str(), i);
			}
		}
	}

	// mark external signals (used in non-selected cells)
	for (auto &cell_it : mod->cells_)
	{
		RTLIL::Cell *cell = cell_it.second;
		if (sel && !sel->selected(mod, cell))
			for (auto &conn : cell->connections())
			{
				RTLIL::SigSpec conn_sig = conn.second;
				sigmap.apply(conn_sig);

				for (auto &bit : conn_sig)
					if (sig_bit_ref.count(bit) != 0) {
						bit_ref_t &bit_ref = sig_bit_ref[bit];
						graph.markExtern(bit_ref.cell, bit_ref.port, bit_ref.bit);
					}
			}
	}

	// mark external signals (used in module ports)
	for (auto &wire_it : mod->wires_)
	{
		RTLIL::Wire *wire = wire_it.second;
		if (wire->port_id > 0)
		{
			RTLIL::SigSpec conn_sig(wire);
			sigmap.apply(conn_sig);

			for (auto &bit : conn_sig)
				if (sig_bit_ref.count(bit) != 0) {
					bit_ref_t &bit_ref = sig_bit_ref[bit];
					graph.markExtern(bit_ref.cell, bit_ref.port, bit_ref.bit);
				}
		}
	}

	// graph.print();
	return true;
}

RTLIL::Cell *replace(RTLIL::Module *needle, RTLIL::Module *haystack, SubCircuit::Solver::Result &match)
{
	SigMap sigmap(needle);
	SigSet<std::pair<RTLIL::IdString, int>> sig2port;

	// create new cell
	RTLIL::Cell *cell = haystack->addCell(stringf("$extract$%s$%d", needle->name.c_str(), autoidx++), needle->name);

	// create cell ports
	for (auto &it : needle->wires_) {
		RTLIL::Wire *wire = it.second;
		if (wire->port_id > 0) {
			for (int i = 0; i < wire->width; i++)
				sig2port.insert(sigmap(RTLIL::SigSpec(wire, i)), std::pair<RTLIL::IdString, int>(wire->name, i));
			cell->setPort(wire->name, RTLIL::SigSpec(RTLIL::State::Sz, wire->width));
		}
	}

	// delete replaced cells and connect new ports
	for (auto &it : match.mappings)
	{
		auto &mapping = it.second;
		RTLIL::Cell *needle_cell = (RTLIL::Cell*)mapping.needleUserData;
		RTLIL::Cell *haystack_cell = (RTLIL::Cell*)mapping.haystackUserData;

		if (needle_cell == NULL)
			continue;

		for (auto &conn : needle_cell->connections()) {
			RTLIL::SigSpec sig = sigmap(conn.second);
			if (mapping.portMapping.count(conn.first.str()) > 0 && sig2port.has(sigmap(sig))) {
				for (int i = 0; i < sig.size(); i++)
				for (auto &port : sig2port.find(sig[i])) {
					RTLIL::SigSpec bitsig = haystack_cell->getPort(mapping.portMapping[conn.first.str()]).extract(i, 1);
					RTLIL::SigSpec new_sig = cell->getPort(port.first);
					new_sig.replace(port.second, bitsig);
					cell->setPort(port.first, new_sig);
				}
			}
		}

		haystack->remove(haystack_cell);
	}

	return cell;
}

bool compareSortNeedleList(RTLIL::Module *left, RTLIL::Module *right)
{
	int left_idx = 0, right_idx = 0;
	if (left->attributes.count("\\extract_order") > 0)
		left_idx = left->attributes.at("\\extract_order").as_int();
	if (right->attributes.count("\\extract_order") > 0)
		right_idx = right->attributes.at("\\extract_order").as_int();
	if (left_idx != right_idx)
		return left_idx < right_idx;
	return left->name < right->name;
}

struct ExtractPass : public Pass {
	ExtractPass() : Pass("extract", "find subcircuits and replace them with cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    extract -map <map_file> [options] [selection]\n");
		log("    extract -mine <out_file> [options] [selection]\n");
		log("\n");
		log("This pass looks for subcircuits that are isomorphic to any of the modules\n");
		log("in the given map file and replaces them with instances of this modules. The\n");
		log("map file can be a Verilog source file (*.v) or an ilang file (*.il).\n");
		log("\n");
		log("    -map <map_file>\n");
		log("        use the modules in this file as reference. This option can be used\n");
		log("        multiple times.\n");
		log("\n");
		log("    -map %%<design-name>\n");
		log("        use the modules in this in-memory design as reference. This option can\n");
		log("        be used multiple times.\n");
		log("\n");
		log("    -verbose\n");
		log("        print debug output while analyzing\n");
		log("\n");
		log("    -constports\n");
		log("        also find instances with constant drivers. this may be much\n");
		log("        slower than the normal operation.\n");
		log("\n");
		log("    -nodefaultswaps\n");
		log("        normally builtin port swapping rules for internal cells are used per\n");
		log("        default. This turns that off, so e.g. 'a^b' does not match 'b^a'\n");
		log("        when this option is used.\n");
		log("\n");
		log("    -compat <needle_type> <haystack_type>\n");
		log("        Per default, the cells in the map file (needle) must have the\n");
		log("        type as the cells in the active design (haystack). This option\n");
		log("        can be used to register additional pairs of types that should\n");
		log("        match. This option can be used multiple times.\n");
		log("\n");
		log("    -swap <needle_type> <port1>,<port2>[,...]\n");
		log("        Register a set of swappable ports for a needle cell type.\n");
		log("        This option can be used multiple times.\n");
		log("\n");
		log("    -perm <needle_type> <port1>,<port2>[,...] <portA>,<portB>[,...]\n");
		log("        Register a valid permutation of swappable ports for a needle\n");
		log("        cell type. This option can be used multiple times.\n");
		log("\n");
		log("    -cell_attr <attribute_name>\n");
		log("        Attributes on cells with the given name must match.\n");
		log("\n");
		log("    -wire_attr <attribute_name>\n");
		log("        Attributes on wires with the given name must match.\n");
		log("\n");
		log("    -ignore_parameters\n");
		log("        Do not use parameters when matching cells.\n");
		log("\n");
		log("    -ignore_param <cell_type> <parameter_name>\n");
		log("        Do not use this parameter when matching cells.\n");
		log("\n");
		log("This pass does not operate on modules with unprocessed processes in it.\n");
		log("(I.e. the 'proc' pass should be used first to convert processes to netlists.)\n");
		log("\n");
		log("This pass can also be used for mining for frequent subcircuits. In this mode\n");
		log("the following options are to be used instead of the -map option.\n");
		log("\n");
		log("    -mine <out_file>\n");
		log("        mine for frequent subcircuits and write them to the given ilang file\n");
		log("\n");
		log("    -mine_cells_span <min> <max>\n");
		log("        only mine for subcircuits with the specified number of cells\n");
		log("        default value: 3 5\n");
		log("\n");
		log("    -mine_min_freq <num>\n");
		log("        only mine for subcircuits with at least the specified number of matches\n");
		log("        default value: 10\n");
		log("\n");
		log("    -mine_limit_matches_per_module <num>\n");
		log("        when calculating the number of matches for a subcircuit, don't count\n");
		log("        more than the specified number of matches per module\n");
		log("\n");
		log("    -mine_max_fanout <num>\n");
		log("        don't consider internal signals with more than <num> connections\n");
		log("\n");
		log("The modules in the map file may have the attribute 'extract_order' set to an\n");
		log("integer value. Then this value is used to determine the order in which the pass\n");
		log("tries to map the modules to the design (ascending, default value is 0).\n");
		log("\n");
		log("See 'help techmap' for a pass that does the opposite thing.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing EXTRACT pass (map subcircuits to cells).\n");
		log_push();

		SubCircuitSolver solver;

		std::vector<std::string> map_filenames;
		std::string mine_outfile;
		bool constports = false;
		bool nodefaultswaps = false;

		bool mine_mode = false;
		int mine_cells_min = 3;
		int mine_cells_max = 5;
		int mine_min_freq = 10;
		int mine_limit_mod = -1;
		int mine_max_fanout = -1;
		std::set<std::pair<RTLIL::IdString, RTLIL::IdString>> mine_split;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				if (mine_mode)
					log_cmd_error("You cannot mix -map and -mine.\n");
				map_filenames.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-mine" && argidx+1 < args.size()) {
				if (!map_filenames.empty())
					log_cmd_error("You cannot mix -map and -mine.\n");
				mine_outfile = args[++argidx];
				mine_mode = true;
				continue;
			}
			if (args[argidx] == "-mine_cells_span" && argidx+2 < args.size()) {
				mine_cells_min = atoi(args[++argidx].c_str());
				mine_cells_max = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-mine_min_freq" && argidx+1 < args.size()) {
				mine_min_freq = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-mine_limit_matches_per_module" && argidx+1 < args.size()) {
				mine_limit_mod = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-mine_split" && argidx+2 < args.size()) {
				mine_split.insert(std::pair<RTLIL::IdString, RTLIL::IdString>(RTLIL::escape_id(args[argidx+1]), RTLIL::escape_id(args[argidx+2])));
				argidx += 2;
				continue;
			}
			if (args[argidx] == "-mine_max_fanout" && argidx+1 < args.size()) {
				mine_max_fanout = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-verbose") {
				solver.setVerbose();
				continue;
			}
			if (args[argidx] == "-constports") {
				constports = true;
				continue;
			}
			if (args[argidx] == "-nodefaultswaps") {
				nodefaultswaps = true;
				continue;
			}
			if (args[argidx] == "-compat" && argidx+2 < args.size()) {
				std::string needle_type = RTLIL::escape_id(args[++argidx]);
				std::string haystack_type = RTLIL::escape_id(args[++argidx]);
				solver.addCompatibleTypes(needle_type, haystack_type);
				continue;
			}
			if (args[argidx] == "-swap" && argidx+2 < args.size()) {
				std::string type = RTLIL::escape_id(args[++argidx]);
				std::set<std::string> ports;
				std::string ports_str = args[++argidx], p;
				while (!(p = next_token(ports_str, ",\t\r\n ")).empty())
					ports.insert(RTLIL::escape_id(p));
				solver.addSwappablePorts(type, ports);
				continue;
			}
			if (args[argidx] == "-perm" && argidx+3 < args.size()) {
				std::string type = RTLIL::escape_id(args[++argidx]);
				std::vector<std::string> map_left, map_right;
				std::string left_str = args[++argidx];
				std::string right_str = args[++argidx], p;
				while (!(p = next_token(left_str, ",\t\r\n ")).empty())
					map_left.push_back(RTLIL::escape_id(p));
				while (!(p = next_token(right_str, ",\t\r\n ")).empty())
					map_right.push_back(RTLIL::escape_id(p));
				if (map_left.size() != map_right.size())
					log_cmd_error("Arguments to -perm are not a valid permutation!\n");
				std::map<std::string, std::string> map;
				for (size_t i = 0; i < map_left.size(); i++)
					map[map_left[i]] = map_right[i];
				std::sort(map_left.begin(), map_left.end());
				std::sort(map_right.begin(), map_right.end());
				if (map_left != map_right)
					log_cmd_error("Arguments to -perm are not a valid permutation!\n");
				solver.addSwappablePortsPermutation(type, map);
				continue;
			}
			if (args[argidx] == "-cell_attr" && argidx+1 < args.size()) {
				solver.cell_attr.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-wire_attr" && argidx+1 < args.size()) {
				solver.wire_attr.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-ignore_parameters") {
				solver.ignore_parameters = true;
				continue;
			}
			if (args[argidx] == "-ignore_param" && argidx+2 < args.size()) {
				solver.ignored_parameters.insert(std::pair<RTLIL::IdString, RTLIL::IdString>(RTLIL::escape_id(args[argidx+1]), RTLIL::escape_id(args[argidx+2])));
				argidx += 2;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!nodefaultswaps) {
			solver.addSwappablePorts("$and",       "\\A", "\\B");
			solver.addSwappablePorts("$or",        "\\A", "\\B");
			solver.addSwappablePorts("$xor",       "\\A", "\\B");
			solver.addSwappablePorts("$xnor",      "\\A", "\\B");
			solver.addSwappablePorts("$eq",        "\\A", "\\B");
			solver.addSwappablePorts("$ne",        "\\A", "\\B");
			solver.addSwappablePorts("$eqx",       "\\A", "\\B");
			solver.addSwappablePorts("$nex",       "\\A", "\\B");
			solver.addSwappablePorts("$add",       "\\A", "\\B");
			solver.addSwappablePorts("$mul",       "\\A", "\\B");
			solver.addSwappablePorts("$logic_and", "\\A", "\\B");
			solver.addSwappablePorts("$logic_or",  "\\A", "\\B");
			solver.addSwappablePorts("$_AND_",     "\\A", "\\B");
			solver.addSwappablePorts("$_OR_",      "\\A", "\\B");
			solver.addSwappablePorts("$_XOR_",     "\\A", "\\B");
		}

		if (map_filenames.empty() && mine_outfile.empty())
			log_cmd_error("Missing option -map <verilog_or_ilang_file> or -mine <output_ilang_file>.\n");

		RTLIL::Design *map = NULL;

		if (!mine_mode)
		{
			map = new RTLIL::Design;
			for (auto &filename : map_filenames)
			{
				if (filename.substr(0, 1) == "%")
				{
					if (!saved_designs.count(filename.substr(1))) {
						delete map;
						log_cmd_error("Can't saved design `%s'.\n", filename.c_str()+1);
					}
					for (auto mod : saved_designs.at(filename.substr(1))->modules())
						if (!map->has(mod->name))
							map->add(mod->clone());
				}
				else
				{
					std::ifstream f;
					rewrite_filename(filename);
					f.open(filename.c_str());
					if (f.fail()) {
						delete map;
						log_cmd_error("Can't open map file `%s'.\n", filename.c_str());
					}
					Frontend::frontend_call(map, &f, filename, (filename.size() > 3 && filename.substr(filename.size()-3) == ".il") ? "ilang" : "verilog");
					f.close();

					if (filename.size() <= 3 || filename.substr(filename.size()-3) != ".il") {
						Pass::call(map, "proc");
						Pass::call(map, "opt_clean");
					}
				}
			}
		}

		std::map<std::string, RTLIL::Module*> needle_map, haystack_map;
		std::vector<RTLIL::Module*> needle_list;

		log_header(design, "Creating graphs for SubCircuit library.\n");

		if (!mine_mode)
			for (auto &mod_it : map->modules_) {
				SubCircuit::Graph mod_graph;
				std::string graph_name = "needle_" + RTLIL::unescape_id(mod_it.first);
				log("Creating needle graph %s.\n", graph_name.c_str());
				if (module2graph(mod_graph, mod_it.second, constports)) {
					solver.addGraph(graph_name, mod_graph);
					needle_map[graph_name] = mod_it.second;
					needle_list.push_back(mod_it.second);
				}
			}

		for (auto &mod_it : design->modules_) {
			SubCircuit::Graph mod_graph;
			std::string graph_name = "haystack_" + RTLIL::unescape_id(mod_it.first);
			log("Creating haystack graph %s.\n", graph_name.c_str());
			if (module2graph(mod_graph, mod_it.second, constports, design, mine_mode ? mine_max_fanout : -1, mine_mode ? &mine_split : NULL)) {
				solver.addGraph(graph_name, mod_graph);
				haystack_map[graph_name] = mod_it.second;
			}
		}

		if (!mine_mode)
		{
			std::vector<SubCircuit::Solver::Result> results;
			log_header(design, "Running solver from SubCircuit library.\n");

			std::sort(needle_list.begin(), needle_list.end(), compareSortNeedleList);

			for (auto needle : needle_list)
			for (auto &haystack_it : haystack_map) {
				log("Solving for %s in %s.\n", ("needle_" + RTLIL::unescape_id(needle->name)).c_str(), haystack_it.first.c_str());
				solver.solve(results, "needle_" + RTLIL::unescape_id(needle->name), haystack_it.first, false);
			}
			log("Found %d matches.\n", GetSize(results));

			if (results.size() > 0)
			{
				log_header(design, "Substitute SubCircuits with cells.\n");

				for (int i = 0; i < int(results.size()); i++) {
					auto &result = results[i];
					log("\nMatch #%d: (%s in %s)\n", i, result.needleGraphId.c_str(), result.haystackGraphId.c_str());
					for (const auto &it : result.mappings) {
						log("  %s -> %s", it.first.c_str(), it.second.haystackNodeId.c_str());
						for (const auto & it2 : it.second.portMapping)
							log(" %s:%s", it2.first.c_str(), it2.second.c_str());
						log("\n");
					}
					RTLIL::Cell *new_cell = replace(needle_map.at(result.needleGraphId), haystack_map.at(result.haystackGraphId), result);
					design->select(haystack_map.at(result.haystackGraphId), new_cell);
					log("  new cell: %s\n", id2cstr(new_cell->name));
				}
			}
		}
		else
		{
			std::vector<SubCircuit::Solver::MineResult> results;

			log_header(design, "Running miner from SubCircuit library.\n");
			solver.mine(results, mine_cells_min, mine_cells_max, mine_min_freq, mine_limit_mod);

			map = new RTLIL::Design;

			int needleCounter = 0;
			for (auto &result: results)
			{
				log("\nFrequent SubCircuit with %d nodes and %d matches:\n", int(result.nodes.size()), result.totalMatchesAfterLimits);
				log("  primary match in %s:", id2cstr(haystack_map.at(result.graphId)->name));
				for (auto &node : result.nodes)
					log(" %s", RTLIL::unescape_id(node.nodeId).c_str());
				log("\n");
				for (auto &it : result.matchesPerGraph)
					log("  matches in %s: %d\n", id2cstr(haystack_map.at(it.first)->name), it.second);

				RTLIL::Module *mod = haystack_map.at(result.graphId);
				std::set<RTLIL::Cell*> cells;
				std::set<RTLIL::Wire*> wires;

				SigMap sigmap(mod);

				for (auto &node : result.nodes)
					cells.insert((RTLIL::Cell*)node.userData);

				for (auto cell : cells)
				for (auto &conn : cell->connections()) {
					RTLIL::SigSpec sig = sigmap(conn.second);
					for (auto &chunk : sig.chunks())
						if (chunk.wire != NULL)
							wires.insert(chunk.wire);
				}

				RTLIL::Module *newMod = new RTLIL::Module;
				newMod->name = stringf("\\needle%05d_%s_%dx", needleCounter++, id2cstr(haystack_map.at(result.graphId)->name), result.totalMatchesAfterLimits);
				map->add(newMod);

				for (auto wire : wires) {
					RTLIL::Wire *newWire = newMod->addWire(wire->name, wire->width);
					newWire->port_input = true;
					newWire->port_output = true;
				}

				newMod->fixup_ports();

				for (auto cell : cells) {
					RTLIL::Cell *newCell = newMod->addCell(cell->name, cell->type);
					newCell->parameters = cell->parameters;
					for (auto &conn : cell->connections()) {
						std::vector<SigChunk> chunks = sigmap(conn.second);
						for (auto &chunk : chunks)
							if (chunk.wire != NULL)
								chunk.wire = newMod->wires_.at(chunk.wire->name);
						newCell->setPort(conn.first, chunks);
					}
				}
			}

			std::ofstream f;
			rewrite_filename(mine_outfile);
			f.open(mine_outfile.c_str(), std::ofstream::trunc);
			if (f.fail())
				log_error("Can't open output file `%s'.\n", mine_outfile.c_str());
			Backend::backend_call(map, &f, mine_outfile, "ilang");
			f.close();
		}

		delete map;
		log_pop();
	}
} ExtractPass;

PRIVATE_NAMESPACE_END
