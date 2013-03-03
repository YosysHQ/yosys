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
#include <assert.h>
#include <stdio.h>
#include <string.h>

using RTLIL::id2cstr;

namespace
{
	struct bit_ref_t {
		std::string cell, port;
		int bit;
	};

	bool module2graph(SubCircuit::Graph &graph, RTLIL::Module *mod, bool constports, RTLIL::Design *sel = NULL, int max_fanout = -1)
	{
		SigMap sigmap(mod);
		std::map<RTLIL::SigChunk, bit_ref_t> sig_bit_ref;

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
			for (auto &cell_it : mod->cells)
			{
				RTLIL::Cell *cell = cell_it.second;
				if (!sel || sel->selected(mod, cell))
					for (auto &conn : cell->connections) {
						RTLIL::SigSpec conn_sig = conn.second;
						sigmap.apply(conn_sig);
						conn_sig.expand();
						for (auto &chunk : conn_sig.chunks)
							if (chunk.wire != NULL)
								sig_use_count[std::pair<RTLIL::Wire*, int>(chunk.wire, chunk.offset)]++;
					}
			}

		// create graph nodes from cells
		for (auto &cell_it : mod->cells)
		{
			RTLIL::Cell *cell = cell_it.second;
			if (sel && !sel->selected(mod, cell))
				continue;

			std::string type = cell->type;
			if (sel == NULL && type.substr(0, 2) == "\\$")
				type = type.substr(1);
			graph.createNode(cell->name, type, (void*)cell);

			for (auto &conn : cell->connections)
			{
				RTLIL::SigSpec conn_sig = conn.second;
				sigmap.apply(conn_sig);
				conn_sig.expand();

				graph.createPort(cell->name, conn.first, conn.second.width);
				for (size_t i = 0; i < conn_sig.chunks.size(); i++)
				{
					auto &chunk = conn_sig.chunks[i];
					assert(chunk.width == 1);

					if (chunk.wire == NULL) {
						if (constports) {
							std::string node = "$const$x";
							if (chunk.data.bits[0] == RTLIL::State::S0) node = "$const$0";
							if (chunk.data.bits[0] == RTLIL::State::S1) node = "$const$1";
							if (chunk.data.bits[0] == RTLIL::State::Sz) node = "$const$z";
							graph.createConnection(cell->name, conn.first, i, node, "\\Y", 0);
						} else
							graph.createConstant(cell->name, conn.first, i, int(chunk.data.bits[0]));
						continue;
					}

					if (max_fanout > 0 && sig_use_count[std::pair<RTLIL::Wire*, int>(chunk.wire, chunk.offset)] > max_fanout)
						continue;

					if (sig_bit_ref.count(chunk) == 0) {
						bit_ref_t &bit_ref = sig_bit_ref[chunk];
						bit_ref.cell = cell->name;
						bit_ref.port = conn.first;
						bit_ref.bit = i;
					}

					bit_ref_t &bit_ref = sig_bit_ref[chunk];
					graph.createConnection(bit_ref.cell, bit_ref.port, bit_ref.bit, cell->name, conn.first, i);
				}
			}
		}

		// mark external signals (used in non-selected cells)
		for (auto &cell_it : mod->cells)
		{
			RTLIL::Cell *cell = cell_it.second;
			if (sel && !sel->selected(mod, cell))
				for (auto &conn : cell->connections)
				{
					RTLIL::SigSpec conn_sig = conn.second;
					sigmap.apply(conn_sig);
					conn_sig.expand();

					for (auto &chunk : conn_sig.chunks)
						if (sig_bit_ref.count(chunk) != 0) {
							bit_ref_t &bit_ref = sig_bit_ref[chunk];
							graph.markExtern(bit_ref.cell, bit_ref.port, bit_ref.bit);
						}
				}
		}

		// mark external signals (used in module ports)
		for (auto &wire_it : mod->wires)
		{
			RTLIL::Wire *wire = wire_it.second;
			if (wire->port_id > 0)
			{
				RTLIL::SigSpec conn_sig(wire);
				sigmap.apply(conn_sig);
				conn_sig.expand();

				for (auto &chunk : conn_sig.chunks)
					if (sig_bit_ref.count(chunk) != 0) {
						bit_ref_t &bit_ref = sig_bit_ref[chunk];
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
		SigSet<std::pair<std::string, int>> sig2port;

		// create new cell
		RTLIL::Cell *cell = new RTLIL::Cell;
		cell->name = stringf("$extract$%s$%d", needle->name.c_str(), RTLIL::autoidx++);
		cell->type = needle->name;
		haystack->add(cell);

		// create cell ports
		for (auto &it : needle->wires) {
			RTLIL::Wire *wire = it.second;
			if (wire->port_id > 0) {
				for (int i = 0; i < wire->width; i++)
					sig2port.insert(sigmap(RTLIL::SigSpec(wire, 1, i)), std::pair<std::string, int>(wire->name, i));
				cell->connections[wire->name] = RTLIL::SigSpec(RTLIL::State::Sz, wire->width);
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

			for (auto &conn : needle_cell->connections) {
				RTLIL::SigSpec sig = sigmap(conn.second);
				if (mapping.portMapping.count(conn.first) > 0 && sig2port.has(sigmap(sig))) {
					sig.expand();
					for (int i = 0; i < sig.width; i++)
					for (auto &port : sig2port.find(sig.chunks[i])) {
						RTLIL::SigSpec bitsig = haystack_cell->connections.at(mapping.portMapping[conn.first]).extract(i, 1);
						cell->connections.at(port.first).replace(port.second, bitsig);
					}
				}
			}

			haystack->cells.erase(haystack_cell->name);
			delete haystack_cell;
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
		log("map file can be a verilog source file (*.v) or an ilang file (*.il).\n");
		log("\n");
		log("    -map <map_file>\n");
		log("        use the modules in this file as reference\n");
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
		log("        Register a set of swapable ports for a needle cell type.\n");
		log("        This option can be used multiple times.\n");
		log("\n");
		log("    -perm <needle_type> <port1>,<port2>[,...] <portA>,<portB>[,...]\n");
		log("        Register a valid permutation of swapable ports for a needle\n");
		log("        cell type. This option can be used multiple times.\n");
		log("\n");
		log("This pass does not operate on modules with uprocessed processes in it.\n");
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
		log("        default value: 3 10\n");
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
		log("This pass operates on whole modules or selected cells from modules. Other\n");
		log("selected entities (wires, etc.) are ignored.\n");
		log("\n");
		log("See 'help techmap' for a pass that does the opposite thing.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing EXTRACT pass (map subcircuits to cells).\n");
		log_push();

		SubCircuit::Solver solver;

		std::string filename;
		bool constports = false;
		bool nodefaultswaps = false;

		bool mine_mode = false;
		int mine_cells_min = 3;
		int mine_cells_max = 10;
		int mine_min_freq = 10;
		int mine_limit_mod = -1;
		int mine_max_fanout = -1;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-mine" && argidx+1 < args.size()) {
				filename = args[++argidx];
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
				char *ports_str = strdup(args[++argidx].c_str());
				for (char *sptr, *p = strtok_r(ports_str, ",\t\r\n ", &sptr); p != NULL; p = strtok_r(NULL, ",\t\r\n ", &sptr))
					ports.insert(RTLIL::escape_id(p));
				free(ports_str);
				solver.addSwappablePorts(type, ports);
				continue;
			}
			if (args[argidx] == "-perm" && argidx+3 < args.size()) {
				std::string type = RTLIL::escape_id(args[++argidx]);
				std::vector<std::string> map_left, map_right;
				char *left_str = strdup(args[++argidx].c_str());
				char *right_str = strdup(args[++argidx].c_str());
				for (char *sptr, *p = strtok_r(left_str, ",\t\r\n ", &sptr); p != NULL; p = strtok_r(NULL, ",\t\r\n ", &sptr))
					map_left.push_back(RTLIL::escape_id(p));
				for (char *sptr, *p = strtok_r(right_str, ",\t\r\n ", &sptr); p != NULL; p = strtok_r(NULL, ",\t\r\n ", &sptr))
					map_right.push_back(RTLIL::escape_id(p));
				free(left_str);
				free(right_str);
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
			solver.addSwappablePorts("$add",       "\\A", "\\B");
			solver.addSwappablePorts("$mul",       "\\A", "\\B");
			solver.addSwappablePorts("$logic_and", "\\A", "\\B");
			solver.addSwappablePorts("$logic_or",  "\\A", "\\B");
			solver.addSwappablePorts("$_AND_",     "\\A", "\\B");
			solver.addSwappablePorts("$_OR_",      "\\A", "\\B");
			solver.addSwappablePorts("$_XOR_",     "\\A", "\\B");
		}

		if (filename.empty())
			log_cmd_error("Missing option -map <verilog_or_ilang_file> or -mine <output_ilang_file>.\n");

		RTLIL::Design *map = NULL;

		if (!mine_mode)
		{
			FILE *f = fopen(filename.c_str(), "rt");
			if (f == NULL)
				log_cmd_error("Can't open map file `%s'.\n", filename.c_str());
			map = new RTLIL::Design;
			Frontend::frontend_call(map, f, filename, (filename.size() > 3 && filename.substr(filename.size()-3) == ".il") ? "ilang" : "verilog");
			fclose(f);
		}

		std::map<std::string, RTLIL::Module*> needle_map, haystack_map;
		std::vector<RTLIL::Module*> needle_list;

		log_header("Creating graphs for SubCircuit library.\n");

		if (!mine_mode)
			for (auto &mod_it : map->modules) {
				SubCircuit::Graph mod_graph;
				std::string graph_name = "needle_" + RTLIL::unescape_id(mod_it.first);
				log("Creating needle graph %s.\n", graph_name.c_str());
				if (module2graph(mod_graph, mod_it.second, constports)) {
					solver.addGraph(graph_name, mod_graph);
					needle_map[graph_name] = mod_it.second;
					needle_list.push_back(mod_it.second);
				}
			}

		for (auto &mod_it : design->modules) {
			SubCircuit::Graph mod_graph;
			std::string graph_name = "haystack_" + RTLIL::unescape_id(mod_it.first);
			log("Creating haystack graph %s.\n", graph_name.c_str());
			if (module2graph(mod_graph, mod_it.second, constports, design, mine_mode ? mine_max_fanout : -1)) {
				solver.addGraph(graph_name, mod_graph);
				haystack_map[graph_name] = mod_it.second;
			}
		}
		
		if (!mine_mode)
		{
			std::vector<SubCircuit::Solver::Result> results;
			log_header("Running solver from SubCircuit library.\n");

			std::sort(needle_list.begin(), needle_list.end(), compareSortNeedleList);

			for (auto needle : needle_list)
			for (auto &haystack_it : haystack_map) {
				log("Solving for %s in %s.\n", ("needle_" + RTLIL::unescape_id(needle->name)).c_str(), haystack_it.first.c_str());
				solver.solve(results, "needle_" + RTLIL::unescape_id(needle->name), haystack_it.first, false);
			}
			log("Found %zd matches.\n", results.size());

			if (results.size() > 0)
			{
				log_header("Substitute SubCircuits with cells.\n");

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

			log_header("Running miner from SubCircuit library.\n");
			solver.mine(results, mine_cells_min, mine_cells_max, mine_min_freq, mine_limit_mod);

			map = new RTLIL::Design;

			int needleCounter = 0;
			for (auto &result: results)
			{
				log("\nFrequent SubCircuit with %d nodes and %d matches:\n", int(result.nodes.size()), result.totalMatchesAfterLimits);
				log("  primary match in %s:", id2cstr(haystack_map.at(result.graphId)->name));
				for (auto &node : result.nodes)
					log(" %s", id2cstr(node.nodeId));
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
				for (auto &conn : cell->connections) {
					RTLIL::SigSpec sig = sigmap(conn.second);
					for (auto &chunk : sig.chunks)
						if (chunk.wire != NULL)
							wires.insert(chunk.wire);
				}

				RTLIL::Module *newMod = new RTLIL::Module;
				newMod->name = stringf("\\needle%05d_%s_%dx", needleCounter++, id2cstr(haystack_map.at(result.graphId)->name), result.totalMatchesAfterLimits);
				map->modules[newMod->name] = newMod;

				int portCounter = 1;
				for (auto wire : wires) {
					RTLIL::Wire *newWire = new RTLIL::Wire;
					newWire->name = wire->name;
					newWire->width = wire->width;
					newWire->port_id = portCounter++;
					newWire->port_input = true;
					newWire->port_output = true;
					newMod->add(newWire);
				}

				for (auto cell : cells) {
					RTLIL::Cell *newCell = new RTLIL::Cell;
					newCell->name = cell->name;
					newCell->type = cell->type;
					newCell->parameters = cell->parameters;
					for (auto &conn : cell->connections) {
						RTLIL::SigSpec sig = sigmap(conn.second);
						for (auto &chunk : sig.chunks)
							if (chunk.wire != NULL)
								chunk.wire = newMod->wires.at(chunk.wire->name);
						newCell->connections[conn.first] = sig;
					}
					newMod->add(newCell);
				}
			}

			FILE *f = fopen(filename.c_str(), "wt");
			if (f == NULL)
				log_error("Can't open output file `%s'.\n", filename.c_str());
			Backend::backend_call(map, f, filename, "ilang");
			fclose(f);
		}

		delete map;
		log_pop();
	}
} ExtractPass;
 
