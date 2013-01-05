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

#include "opt_status.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/sha1.h"
#include "kernel/celltypes.h"
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <set>

#define USE_CELL_HASH_CACHE

struct OptShareWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap assign_map;

	CellTypes ct;
	int total_count;
#ifdef USE_CELL_HASH_CACHE
	std::map<const RTLIL::Cell*, std::string> cell_hash_cache;
#endif

#ifdef USE_CELL_HASH_CACHE
	std::string int_to_hash_string(unsigned int v)
	{
		if (v == 0)
			return "0";
		std::string str = "";
		while (v > 0) {
			str += 'a' + (v & 15);
			v = v >> 4;
		}
		return str;
	}

	std::string hash_cell_parameters_and_connections(const RTLIL::Cell *cell)
	{
		if (cell_hash_cache.count(cell) > 0)
			return cell_hash_cache[cell];

		std::string hash_string = cell->type + "\n";

		for (auto &it : cell->parameters)
			hash_string += "P " + it.first + "=" + it.second.as_string() + "\n";

		for (auto &it : cell->connections) {
			if (ct.cell_output(cell->type, it.first))
				continue;
			RTLIL::SigSpec sig = it.second;
			assign_map.apply(sig);
			hash_string += "C " + it.first + "=";
			for (auto &chunk : sig.chunks) {
				if (chunk.wire)
					hash_string += "{" + chunk.wire->name + " " +
							int_to_hash_string(chunk.offset) + " " +
							int_to_hash_string(chunk.width) + "}";
				else
					hash_string += chunk.data.as_string();
			}
			hash_string += "\n";
		}

		unsigned char hash[20];
		char hash_hex_string[41];
		sha1::calc(hash_string.c_str(), hash_string.size(), hash);
		sha1::toHexString(hash, hash_hex_string);
		cell_hash_cache[cell] = hash_hex_string;

		return cell_hash_cache[cell];
	}
#endif

	bool compare_cell_parameters_and_connections(const RTLIL::Cell *cell1, const RTLIL::Cell *cell2, bool &lt)
	{
#ifdef USE_CELL_HASH_CACHE
		std::string hash1 = hash_cell_parameters_and_connections(cell1);
		std::string hash2 = hash_cell_parameters_and_connections(cell2);

		if (hash1 != hash2) {
			lt = hash1 < hash2;
			return true;
		}
#endif

		if (cell1->parameters != cell2->parameters) {
			lt = cell1->parameters < cell2->parameters;
			return true;
		}

		std::map<RTLIL::IdString, RTLIL::SigSpec> conn1 = cell1->connections;
		std::map<RTLIL::IdString, RTLIL::SigSpec> conn2 = cell2->connections;

		for (auto &it : conn1) {
			if (ct.cell_output(cell1->type, it.first))
				it.second = RTLIL::SigSpec();
			else
				assign_map.apply(it.second);
		}

		for (auto &it : conn2) {
			if (ct.cell_output(cell2->type, it.first))
				it.second = RTLIL::SigSpec();
			else
				assign_map.apply(it.second);
		}

		if (conn1 != conn2) {
			lt = conn1 < conn2;
			return true;
		}

		return false;
	}

	bool compare_cells(const RTLIL::Cell *cell1, const RTLIL::Cell *cell2)
	{
		if (cell1->type != cell2->type)
			return cell1->type < cell2->type;

		if (!ct.cell_known(cell1->type))
			return cell1 < cell2;

		bool lt;
		if (compare_cell_parameters_and_connections(cell1, cell2, lt))
			return lt;

		return false;
	}

	struct CompareCells {
		OptShareWorker *that;
		CompareCells(OptShareWorker *that) : that(that) {}
		bool operator()(const RTLIL::Cell *cell1, const RTLIL::Cell *cell2) const {
			return that->compare_cells(cell1, cell2);
		}
	};

	OptShareWorker(RTLIL::Design *design, RTLIL::Module *module, bool mode_nomux) :
		design(design), module(module), assign_map(module)
	{
		total_count = 0;
		ct.setup_internals();
		ct.setup_internals_mem();
		ct.setup_stdcells();
		ct.setup_stdcells_mem();

		if (mode_nomux) {
			ct.cell_types.erase("$mux");
			ct.cell_types.erase("$pmux");
			ct.cell_types.erase("$safe_pmux");
		}

		log("Finding identical cells in module `%s'.\n", module->name.c_str());
		assign_map.set(module);

		bool did_something = true;
		while (did_something)
		{
#ifdef USE_CELL_HASH_CACHE
			cell_hash_cache.clear();
#endif
			std::vector<RTLIL::Cell*> cells;
			cells.reserve(module->cells.size());
			for (auto &it : module->cells) {
				if (ct.cell_known(it.second->type) && design->selected(module, it.second))
					cells.push_back(it.second);
			}

			did_something = false;
			std::map<RTLIL::Cell*, RTLIL::Cell*, CompareCells> sharemap(CompareCells(this));
			for (auto cell : cells)
			{
				if (sharemap.count(cell) > 0) {
					did_something = true;
					log("  Cell `%s' is identical to cell `%s'.\n", cell->name.c_str(), sharemap[cell]->name.c_str());
					for (auto &it : cell->connections) {
						if (ct.cell_output(cell->type, it.first)) {
							RTLIL::SigSpec other_sig = sharemap[cell]->connections[it.first];
							log("    Redirecting output %s: %s = %s\n", it.first.c_str(),
									log_signal(it.second), log_signal(other_sig));
							module->connections.push_back(RTLIL::SigSig(it.second, other_sig));
							assign_map.add(it.second, other_sig);
						}
					}
					log("    Removing %s cell `%s' from module `%s'.\n", cell->type.c_str(), cell->name.c_str(), module->name.c_str());
					module->cells.erase(cell->name);
					OPT_DID_SOMETHING = true;
					total_count++;
					delete cell;
				} else {
					sharemap[cell] = cell;
				}
			}
		}
	}
};

struct OptSharePass : public Pass {
	OptSharePass() : Pass("opt_share") { }
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing OPT_SHARE pass (detect identical cells).\n");

		bool mode_nomux = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-nomux") {
				mode_nomux = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto &mod_it : design->modules) {
			if (!design->selected(mod_it.second))
				continue;
			OptShareWorker worker(design, mod_it.second, mode_nomux);
			total_count += worker.total_count;
		}

		log("Removed a total of %d cells.\n", total_count);
	}
} OptSharePass;
 
