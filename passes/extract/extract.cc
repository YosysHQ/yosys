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

namespace
{
	struct bit_ref_t {
		std::string cell, port;
		int bit;
	};

	bool module2graph(SubCircuit::Graph &graph, RTLIL::Module *mod, bool constports, RTLIL::Design *sel = NULL)
	{
		SigMap sigmap(mod);
		std::map<RTLIL::SigChunk, bit_ref_t> sig_bit_ref;

		if (sel && !sel->selected(mod)) {
			log("  Skipping module %s as it is not selected.\n", mod->name.c_str());
			return false;
		}

		if (mod->processes.size() > 0) {
			log("  Skipping module %s as it contains unprocessed processes.\n", mod->name.c_str());
			return false;
		}

		if (constports) {
			graph.createNode("$const$0", "$const$0");
			graph.createNode("$const$1", "$const$1");
			graph.createNode("$const$x", "$const$x");
			graph.createNode("$const$z", "$const$z");
			graph.createPort("$const$0", "\\Y", 1);
			graph.createPort("$const$1", "\\Y", 1);
			graph.createPort("$const$x", "\\Y", 1);
			graph.createPort("$const$z", "\\Y", 1);
			graph.markExtern("$const$0", "\\Y", 0);
			graph.markExtern("$const$1", "\\Y", 0);
			graph.markExtern("$const$x", "\\Y", 0);
			graph.markExtern("$const$z", "\\Y", 0);
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

		return true;
	}

	void replace(RTLIL::Module *needle, RTLIL::Module *haystack, SubCircuit::Solver::Result &match)
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
	}
}

struct ExtractPass : public Pass {
	ExtractPass() : Pass("extract", "find subcircuits and replace them with cells") { }
	virtual void help()
	{
		log("\n");
		log("    extract -map <map_file> [options] [selection]\n");
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
		std::vector<SubCircuit::Solver::Result> results;

		std::string filename;
		bool constports = false;
		bool nodefaultswaps = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				filename = args[++argidx];
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
			log_cmd_error("Missing option -map <verilog_or_ilang_file>.\n");

		FILE *f = fopen(filename.c_str(), "rt");
		if (f == NULL)
			log_cmd_error("Can't open map file `%s'.\n", filename.c_str());

		RTLIL::Design *map = new RTLIL::Design;
		Frontend::frontend_call(map, f, filename, (filename.size() > 3 && filename.substr(filename.size()-3) == ".il") ? "ilang" : "verilog");

		fclose(f);

		std::map<std::string, RTLIL::Module*> needle_map, haystack_map;

		log_header("Creating graphs for SubCircuit library.\n");

		for (auto &mod_it : map->modules) {
			SubCircuit::Graph mod_graph;
			std::string graph_name = "needle_" + RTLIL::unescape_id(mod_it.first);
			log("Creating needle graph %s.\n", graph_name.c_str());
			if (module2graph(mod_graph, mod_it.second, constports)) {
				solver.addGraph(graph_name, mod_graph);
				needle_map[graph_name] = mod_it.second;
			}
		}

		for (auto &mod_it : design->modules) {
			SubCircuit::Graph mod_graph;
			std::string graph_name = "haystack_" + RTLIL::unescape_id(mod_it.first);
			log("Creating haystack graph %s.\n", graph_name.c_str());
			if (module2graph(mod_graph, mod_it.second, constports, design)) {
				solver.addGraph(graph_name, mod_graph);
				haystack_map[graph_name] = mod_it.second;
			}
		}
		
		log_header("Running solver from SubCircuit library.\n");

		for (auto &needle_it : needle_map)
		for (auto &haystack_it : haystack_map) {
			log("Solving for %s in %s.\n", needle_it.first.c_str(), haystack_it.first.c_str());
			solver.solve(results, needle_it.first, haystack_it.first, false);
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
				replace(needle_map.at(result.needleGraphId), haystack_map.at(result.haystackGraphId), result);
			}
		}

		delete map;
		log_pop();
	}
} ExtractPass;
 
