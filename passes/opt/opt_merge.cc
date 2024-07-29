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

#include "kernel/register.h"
#include "kernel/ffinit.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
#include "libs/sha1/sha1.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptMergeWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap assign_map;
	FfInitVals initvals;
	bool mode_share_all;

	CellTypes ct;
	int total_count;

	static void sort_pmux_conn(dict<RTLIL::IdString, RTLIL::SigSpec> &conn)
	{
		SigSpec sig_s = conn.at(ID::S);
		SigSpec sig_b = conn.at(ID::B);

		int s_width = GetSize(sig_s);
		int width = GetSize(sig_b) / s_width;

		vector<pair<SigBit, SigSpec>> sb_pairs;
		for (int i = 0; i < s_width; i++)
			sb_pairs.push_back(pair<SigBit, SigSpec>(sig_s[i], sig_b.extract(i*width, width)));

		std::sort(sb_pairs.begin(), sb_pairs.end());

		conn[ID::S] = SigSpec();
		conn[ID::B] = SigSpec();

		for (auto &it : sb_pairs) {
			conn[ID::S].append(it.first);
			conn[ID::B].append(it.second);
		}
	}

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

	uint64_t hash_cell_parameters_and_connections(const RTLIL::Cell *cell)
	{
		uint64_t conn_hash = 0;

		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($add), ID($mul),
				ID($logic_and), ID($logic_or), ID($_AND_), ID($_OR_), ID($_XOR_))) {
			conn_hash = hashlib::mkhash_xorshift64(assign_map(cell->getPort(ID::A)).hash()) \
							+ hashlib::mkhash_xorshift64(assign_map(cell->getPort(ID::B)).hash());
		} else if (cell->type.in(ID($reduce_xor), ID($reduce_xnor))) {
			SigSpec a = assign_map(cell->getPort(ID::A));
			a.sort();
			conn_hash = a.hash();
		} else if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool))) {
			SigSpec a = assign_map(cell->getPort(ID::A));
			a.sort_and_unify();
			conn_hash = a.hash();
		} else if (cell->type == ID($pmux)) {
			uint64_t acc = 0;
			int width = cell->getParam(ID::WIDTH).as_int();
			SigSpec a = assign_map(cell->getPort(ID::A));
			SigSpec b = assign_map(cell->getPort(ID::B));
			SigSpec s = assign_map(cell->getPort(ID::S));
			for (int i = 0; i < cell->getParam(ID::S_WIDTH).as_int(); i++) {
				SigSpec b_window = b.extract(i * width, width);
				acc += mkhash_xorshift64(mkhash(s[i].hash(), b_window.hash()));
			}
			conn_hash = mkhash_xorshift64(a.hash()) + acc;
		} else {
			for (auto conn : cell->connections())
			if (!cell->output(conn.first))
				conn_hash += mkhash_xorshift64(mkhash(conn.first.hash(), assign_map(conn.second).hash()));

			if (RTLIL::builtin_ff_cell_types().count(cell->type))
				conn_hash += initvals(cell->getPort(ID::Q)).hash();
		}

		uint64_t param_hash = 0;
		for (auto &it : cell->parameters)
			param_hash += mkhash_xorshift64(mkhash(it.first.hash(), it.second.hash()));

		return conn_hash + mkhash_xorshift64(param_hash + cell->type.hash());
	}

	bool compare_cell_parameters_and_connections(const RTLIL::Cell *cell1, const RTLIL::Cell *cell2)
	{
		log_assert(cell1 != cell2);
		if (cell1->type != cell2->type) return false;

		if (cell1->parameters != cell2->parameters)
			return false;

		if (cell1->connections_.size() != cell2->connections_.size())
			return false;
		for (const auto &it : cell1->connections_)
			if (!cell2->connections_.count(it.first))
				return false;

		decltype(Cell::connections_) conn1, conn2;
		conn1.reserve(cell1->connections_.size());
		conn2.reserve(cell1->connections_.size());

		for (const auto &it : cell1->connections_) {
			if (cell1->output(it.first)) {
				if (it.first == ID::Q && RTLIL::builtin_ff_cell_types().count(cell1->type)) {
					// For the 'Q' output of state elements,
					//   use the (* init *) attribute value
					conn1[it.first] = initvals(it.second);
					conn2[it.first] = initvals(cell2->getPort(it.first));
				}
				else {
					conn1[it.first] = RTLIL::SigSpec();
					conn2[it.first] = RTLIL::SigSpec();
				}
			}
			else {
				conn1[it.first] = assign_map(it.second);
				conn2[it.first] = assign_map(cell2->getPort(it.first));
			}
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

		return conn1 == conn2;
	}

	bool has_dont_care_initval(const RTLIL::Cell *cell)
	{
		if (!RTLIL::builtin_ff_cell_types().count(cell->type))
			return false;

		return !initvals(cell->getPort(ID::Q)).is_fully_def();
	}

	OptMergeWorker(RTLIL::Design *design, RTLIL::Module *module, bool mode_nomux, bool mode_share_all, bool mode_keepdc) :
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

		initvals.set(&assign_map, module);

		bool did_something = true;
		while (did_something)
		{
			std::vector<RTLIL::Cell*> cells;
			cells.reserve(module->cells().size());
			for (auto cell : module->cells()) {
				if (!design->selected(module, cell))
					continue;
				if (cell->type.in(ID($meminit), ID($meminit_v2), ID($mem), ID($mem_v2))) {
					// Ignore those for performance: meminit can have an excessively large port,
					// mem can have an excessively large parameter holding the init data
					continue;
				}
				if (mode_keepdc && has_dont_care_initval(cell))
					continue;
				if (ct.cell_known(cell->type) || (mode_share_all && cell->known()))
					cells.push_back(cell);
			}

			did_something = false;
                        dict<uint64_t, RTLIL::Cell*> sharemap;
			for (auto cell : cells)
			{
				if ((!mode_share_all && !ct.cell_known(cell->type)) || !cell->known())
					continue;

				if (cell->type == ID($scopeinfo))
					continue;

				uint64_t hash = hash_cell_parameters_and_connections(cell);
				auto r = sharemap.insert(std::make_pair(hash, cell));
				if (!r.second) {
					if (compare_cell_parameters_and_connections(cell, r.first->second)) {
						if (cell->has_keep_attr()) {
							if (r.first->second->has_keep_attr())
								continue;
							std::swap(r.first->second, cell);
						}


						did_something = true;
						log_debug("  Cell `%s' is identical to cell `%s'.\n", cell->name.c_str(), r.first->second->name.c_str());
						for (auto &it : cell->connections()) {
							if (cell->output(it.first)) {
								RTLIL::SigSpec other_sig = r.first->second->getPort(it.first);
								log_debug("    Redirecting output %s: %s = %s\n", it.first.c_str(),
										log_signal(it.second), log_signal(other_sig));
								Const init = initvals(other_sig);
								initvals.remove_init(it.second);
								initvals.remove_init(other_sig);
								module->connect(RTLIL::SigSig(it.second, other_sig));
								assign_map.add(it.second, other_sig);
								initvals.set_init(other_sig, init);
							}
						}
						log_debug("    Removing %s cell `%s' from module `%s'.\n", cell->type.c_str(), cell->name.c_str(), module->name.c_str());
						module->remove(cell);
						total_count++;
					}
				}
			}
		}

		log_suppressed();
	}
};

struct OptMergePass : public Pass {
	OptMergePass() : Pass("opt_merge", "consolidate identical cells") { }
	void help() override
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
		log("    -keepdc\n");
		log("        Do not merge flipflops with don't-care bits in their initial value.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MERGE pass (detect identical cells).\n");

		bool mode_nomux = false;
		bool mode_share_all = false;
		bool mode_keepdc = false;

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
			if (arg == "-keepdc") {
				mode_keepdc = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto module : design->selected_modules()) {
			OptMergeWorker worker(design, module, mode_nomux, mode_share_all, mode_keepdc);
			total_count += worker.total_count;
		}

		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Removed a total of %d cells.\n", total_count);
	}
} OptMergePass;

PRIVATE_NAMESPACE_END
