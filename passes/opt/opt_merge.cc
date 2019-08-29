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
#include "kernel/celltypes.h"
#include "libs/sha1/sha1.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

#define USE_CELL_HASH_CACHE

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptMergeWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap assign_map;
	SigMap dff_init_map;
	bool mode_share_all;

	CellTypes ct;
	int total_count;
#ifdef USE_CELL_HASH_CACHE
	dict<const RTLIL::Cell*, std::string> cell_hash_cache;
#endif

	static void sort_pmux_conn(dict<RTLIL::IdString, RTLIL::SigSpec> &conn)
	{
		SigSpec sig_s = conn.at(ID(S));
		SigSpec sig_b = conn.at(ID::B);

		int s_width = GetSize(sig_s);
		int width = GetSize(sig_b) / s_width;

		vector<pair<SigBit, SigSpec>> sb_pairs;
		for (int i = 0; i < s_width; i++)
			sb_pairs.push_back(pair<SigBit, SigSpec>(sig_s[i], sig_b.extract(i*width, width)));

		std::sort(sb_pairs.begin(), sb_pairs.end());

		conn[ID(S)] = SigSpec();
		conn[ID::B] = SigSpec();

		for (auto &it : sb_pairs) {
			conn[ID(S)].append(it.first);
			conn[ID::B].append(it.second);
		}
	}

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

		std::string hash_string = cell->type.str() + "\n";

		for (auto &it : cell->parameters)
			hash_string += "P " + it.first.str() + "=" + it.second.as_string() + "\n";

		const dict<RTLIL::IdString, RTLIL::SigSpec> *conn = &cell->connections();
		dict<RTLIL::IdString, RTLIL::SigSpec> alt_conn;

		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($add), ID($mul),
				ID($logic_and), ID($logic_or), ID($_AND_), ID($_OR_), ID($_XOR_))) {
			alt_conn = *conn;
			if (assign_map(alt_conn.at(ID::A)) < assign_map(alt_conn.at(ID::B))) {
				alt_conn[ID::A] = conn->at(ID::B);
				alt_conn[ID::B] = conn->at(ID::A);
			}
			conn = &alt_conn;
		} else
		if (cell->type.in(ID($reduce_xor), ID($reduce_xnor))) {
			alt_conn = *conn;
			assign_map.apply(alt_conn.at(ID::A));
			alt_conn.at(ID::A).sort();
			conn = &alt_conn;
		} else
		if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool))) {
			alt_conn = *conn;
			assign_map.apply(alt_conn.at(ID::A));
			alt_conn.at(ID::A).sort_and_unify();
			conn = &alt_conn;
		} else
		if (cell->type == ID($pmux)) {
			alt_conn = *conn;
			assign_map.apply(alt_conn.at(ID::A));
			assign_map.apply(alt_conn.at(ID::B));
			assign_map.apply(alt_conn.at(ID(S)));
			sort_pmux_conn(alt_conn);
			conn = &alt_conn;
		}

		vector<string> hash_conn_strings;

		for (auto &it : *conn) {
			if (cell->output(it.first))
				continue;
			RTLIL::SigSpec sig = it.second;
			assign_map.apply(sig);
			string s = "C " + it.first.str() + "=";
			for (auto &chunk : sig.chunks()) {
				if (chunk.wire)
					s += "{" + chunk.wire->name.str() + " " +
							int_to_hash_string(chunk.offset) + " " +
							int_to_hash_string(chunk.width) + "}";
				else
					s += RTLIL::Const(chunk.data).as_string();
			}
			hash_conn_strings.push_back(s + "\n");
		}

		std::sort(hash_conn_strings.begin(), hash_conn_strings.end());

		for (auto it : hash_conn_strings)
			hash_string += it;

		cell_hash_cache[cell] = sha1(hash_string);
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
			std::map<RTLIL::IdString, RTLIL::Const> p1(cell1->parameters.begin(), cell1->parameters.end());
			std::map<RTLIL::IdString, RTLIL::Const> p2(cell2->parameters.begin(), cell2->parameters.end());
			lt = p1 < p2;
			return true;
		}

		dict<RTLIL::IdString, RTLIL::SigSpec> conn1 = cell1->connections();
		dict<RTLIL::IdString, RTLIL::SigSpec> conn2 = cell2->connections();

		for (auto &it : conn1) {
			if (cell1->output(it.first))
				it.second = RTLIL::SigSpec();
			else
				assign_map.apply(it.second);
		}

		for (auto &it : conn2) {
			if (cell2->output(it.first))
				it.second = RTLIL::SigSpec();
			else
				assign_map.apply(it.second);
		}

		if (cell1->type == ID($and) || cell1->type == ID($or) || cell1->type == ID($xor) || cell1->type == ID($xnor) || cell1->type == ID($add) || cell1->type == ID($mul) ||
				cell1->type == ID($logic_and) || cell1->type == ID($logic_or) || cell1->type == ID($_AND_) || cell1->type == ID($_OR_) || cell1->type == ID($_XOR_)) {
			if (conn1.at(ID::A) < conn1.at(ID::B)) {
				RTLIL::SigSpec tmp = conn1[ID::A];
				conn1[ID::A] = conn1[ID::B];
				conn1[ID::B] = tmp;
			}
			if (conn2.at(ID::A) < conn2.at(ID::B)) {
				RTLIL::SigSpec tmp = conn2[ID::A];
				conn2[ID::A] = conn2[ID::B];
				conn2[ID::B] = tmp;
			}
		} else
		if (cell1->type == ID($reduce_xor) || cell1->type == ID($reduce_xnor)) {
			conn1[ID::A].sort();
			conn2[ID::A].sort();
		} else
		if (cell1->type == ID($reduce_and) || cell1->type == ID($reduce_or) || cell1->type == ID($reduce_bool)) {
			conn1[ID::A].sort_and_unify();
			conn2[ID::A].sort_and_unify();
		} else
		if (cell1->type == ID($pmux)) {
			sort_pmux_conn(conn1);
			sort_pmux_conn(conn2);
		}

		if (conn1 != conn2) {
			std::map<RTLIL::IdString, RTLIL::SigSpec> c1(conn1.begin(), conn1.end());
			std::map<RTLIL::IdString, RTLIL::SigSpec> c2(conn2.begin(), conn2.end());
			lt = c1 < c2;
			return true;
		}

		if (cell1->type.begins_with("$") && conn1.count(ID(Q)) != 0) {
			std::vector<RTLIL::SigBit> q1 = dff_init_map(cell1->getPort(ID(Q))).to_sigbit_vector();
			std::vector<RTLIL::SigBit> q2 = dff_init_map(cell2->getPort(ID(Q))).to_sigbit_vector();
			for (size_t i = 0; i < q1.size(); i++)
				if ((q1.at(i).wire == NULL || q2.at(i).wire == NULL) && q1.at(i) != q2.at(i)) {
					lt = q1.at(i) < q2.at(i);
					return true;
				}
		}

		return false;
	}

	bool compare_cells(const RTLIL::Cell *cell1, const RTLIL::Cell *cell2)
	{
		if (cell1->type != cell2->type)
			return cell1->type < cell2->type;

		if ((!mode_share_all && !ct.cell_known(cell1->type)) || !cell1->known())
			return cell1 < cell2;

		if (cell1->has_keep_attr() || cell2->has_keep_attr())
			return cell1 < cell2;

		bool lt;
		if (compare_cell_parameters_and_connections(cell1, cell2, lt))
			return lt;

		return false;
	}

	struct CompareCells {
		OptMergeWorker *that;
		CompareCells(OptMergeWorker *that) : that(that) {}
		bool operator()(const RTLIL::Cell *cell1, const RTLIL::Cell *cell2) const {
			return that->compare_cells(cell1, cell2);
		}
	};

	OptMergeWorker(RTLIL::Design *design, RTLIL::Module *module, bool mode_nomux, bool mode_share_all) :
		design(design), module(module), assign_map(module), mode_share_all(mode_share_all)
	{
		total_count = 0;
		ct.setup_internals();
		ct.setup_internals_mem();
		ct.setup_stdcells();
		ct.setup_stdcells_mem();

		if (mode_nomux) {
			ct.cell_types.erase(ID($mux));
			ct.cell_types.erase(ID($pmux));
		}

		ct.cell_types.erase(ID($tribuf));
		ct.cell_types.erase(ID($_TBUF_));
		ct.cell_types.erase(ID($anyseq));
		ct.cell_types.erase(ID($anyconst));
		ct.cell_types.erase(ID($allseq));
		ct.cell_types.erase(ID($allconst));

		log("Finding identical cells in module `%s'.\n", module->name.c_str());
		assign_map.set(module);

		dff_init_map.set(module);
		for (auto &it : module->wires_)
			if (it.second->attributes.count(ID(init)) != 0) {
				Const initval = it.second->attributes.at(ID(init));
				for (int i = 0; i < GetSize(initval) && i < GetSize(it.second); i++)
					if (initval[i] == State::S0 || initval[i] == State::S1)
						dff_init_map.add(SigBit(it.second, i), initval[i]);
			}

		bool did_something = true;
		while (did_something)
		{
#ifdef USE_CELL_HASH_CACHE
			cell_hash_cache.clear();
#endif
			std::vector<RTLIL::Cell*> cells;
			cells.reserve(module->cells_.size());
			for (auto &it : module->cells_) {
				if (!design->selected(module, it.second))
					continue;
				if (ct.cell_known(it.second->type) || (mode_share_all && it.second->known()))
					cells.push_back(it.second);
			}

			did_something = false;
			std::map<RTLIL::Cell*, RTLIL::Cell*, CompareCells> sharemap(CompareCells(this));
			for (auto cell : cells)
			{
				if (sharemap.count(cell) > 0) {
					did_something = true;
					log_debug("  Cell `%s' is identical to cell `%s'.\n", cell->name.c_str(), sharemap[cell]->name.c_str());
					for (auto &it : cell->connections()) {
						if (cell->output(it.first)) {
							RTLIL::SigSpec other_sig = sharemap[cell]->getPort(it.first);
							log_debug("    Redirecting output %s: %s = %s\n", it.first.c_str(),
									log_signal(it.second), log_signal(other_sig));
							module->connect(RTLIL::SigSig(it.second, other_sig));
							assign_map.add(it.second, other_sig);
						}
					}
					log_debug("    Removing %s cell `%s' from module `%s'.\n", cell->type.c_str(), cell->name.c_str(), module->name.c_str());
#ifdef USE_CELL_HASH_CACHE
					cell_hash_cache.erase(cell);
#endif
					module->remove(cell);
					total_count++;
				} else {
					sharemap[cell] = cell;
				}
			}
		}

		log_suppressed();
	}
};

struct OptMergePass : public Pass {
	OptMergePass() : Pass("opt_merge", "consolidate identical cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_merge [options] [selection]\n");
		log("\n");
		log("This pass identifies cells with identical type and input signals. Such cells\n");
		log("are then merged to one cell.\n");
		log("\n");
		log("    -nomux\n");
		log("        Do not merge MUX cells.\n");
		log("\n");
		log("    -share_all\n");
		log("        Operate on all cell types, not just built-in types.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing OPT_MERGE pass (detect identical cells).\n");

		bool mode_nomux = false;
		bool mode_share_all = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-nomux") {
				mode_nomux = true;
				continue;
			}
			if (arg == "-share_all") {
				mode_share_all = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto module : design->selected_modules()) {
			OptMergeWorker worker(design, module, mode_nomux, mode_share_all);
			total_count += worker.total_count;
		}

		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Removed a total of %d cells.\n", total_count);
	}
} OptMergePass;

PRIVATE_NAMESPACE_END
