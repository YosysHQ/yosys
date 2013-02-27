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

	bool module2graph(SubCircuit::Graph &graph, RTLIL::Module *mod, RTLIL::Design *sel = NULL)
	{
		SigMap sigmap(mod);
		std::map<RTLIL::SigChunk, bit_ref_t> sig_bit_ref;

		if (sel && !sel->selected(mod)) {
			log("  Skipping module %s as it is not selected.\n", mod->name.c_str());
			return false;
		}

		if (mod->memories.size() > 0 || mod->processes.size() > 0) {
			log("  Skipping module %s as it contains unprocessed memories or processes.\n", mod->name.c_str());
			return false;
		}

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
}

struct ExtractPass : public Pass {
	ExtractPass() : Pass("extract") { }
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing EXTRACT pass (map subcircuits to cells).\n");
		log_push();

		std::string filename;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				filename = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (filename.empty())
			log_cmd_error("Missing option -map <verilog_file>.\n");

		RTLIL::Design *map = new RTLIL::Design;
		FILE *f = fopen(filename.c_str(), "rt");
		if (f == NULL)
			log_error("Can't open map file `%s'\n", filename.c_str());
		Frontend::frontend_call(map, f, filename, "verilog");
		fclose(f);

		SubCircuit::Solver solver;
		std::map<std::string, RTLIL::Module*> needle_map, haystack_map;

		log_header("Creating graphs for SubCircuit library.\n");

		for (auto &mod_it : map->modules) {
			SubCircuit::Graph mod_graph;
			std::string graph_name = "needle_" + mod_it.first.substr(mod_it.first[0] == '\\' ? 1 : 0);
			log("Creating needle graph %s.\n", graph_name.c_str());
			if (module2graph(mod_graph, mod_it.second)) {
				solver.addGraph(graph_name, mod_graph);
				needle_map[graph_name] = mod_it.second;
			}
		}

		for (auto &mod_it : design->modules) {
			SubCircuit::Graph mod_graph;
			std::string graph_name = "haystack_" + mod_it.first.substr(mod_it.first[0] == '\\' ? 1 : 0);
			log("Creating haystack graph %s.\n", graph_name.c_str());
			if (module2graph(mod_graph, mod_it.second, design)) {
				solver.addGraph(graph_name, mod_graph);
				haystack_map[graph_name] = mod_it.second;
			}
		}
		
		log_header("Running solver from SubCircuit library.\n");

		solver.setVerbose();
		std::vector<SubCircuit::Solver::Result> results;

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
				log("\nMatch #%d: (%s in %s)\n", i, results[i].needleGraphId.c_str(), results[i].haystackGraphId.c_str());
				for (const auto & it : results[i].mappings) {
					log("  %s -> %s", it.first.c_str(), it.second.haystackNodeId.c_str());
					for (const auto & it2 : it.second.portMapping)
						log(" %s:%s", it2.first.c_str(), it2.second.c_str());
					log("\n");
				}
			}
		}

		delete map;
		log_pop();

		log("\n** UNFINISHED IMPLEMENTATION **\n");
		log_cmd_error("TBD: Replace found subcircuits with cells.\n");
	}
} ExtractPass;
 
