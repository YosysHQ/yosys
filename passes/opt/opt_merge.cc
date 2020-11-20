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
	SHA1 checksum;

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

	std::string hash_cell_parameters_and_connections(const RTLIL::Cell *cell)
	{
		vector<string> hash_conn_strings;
		std::string hash_string = cell->type.str() + "\n";

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
			assign_map.apply(alt_conn.at(ID::S));
			sort_pmux_conn(alt_conn);
			conn = &alt_conn;
		}

		for (auto &it : *conn) {
			RTLIL::SigSpec sig;
			if (cell->output(it.first)) {
				if (it.first == ID::Q && RTLIL::builtin_ff_cell_types().count(cell->type)) {
					// For the 'Q' output of state elements,
					//   use its (* init *) attribute value
					for (const auto &b : dff_init_map(it.second))
						sig.append(b.wire ? State::Sx : b);
				}
				else
					continue;
			}
			else
				sig = assign_map(it.second);
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

		for (auto &it : cell->parameters)
			hash_conn_strings.push_back("P " + it.first.str() + "=" + it.second.as_string() + "\n");

		std::sort(hash_conn_strings.begin(), hash_conn_strings.end());

		for (auto it : hash_conn_strings)
			hash_string += it;

		checksum.update(hash_string);
		return checksum.final();
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
					auto &sig1 = conn1[it.first];
					for (const auto &b : dff_init_map(it.second))
						sig1.append(b.wire ? State::Sx : b);
					auto &sig2 = conn2[it.first];
					for (const auto &b : dff_init_map(cell2->getPort(it.first)))
						sig2.append(b.wire ? State::Sx : b);
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
			if (it.second->attributes.count(ID::init) != 0) {
				Const initval = it.second->attributes.at(ID::init);
				for (int i = 0; i < GetSize(initval) && i < GetSize(it.second); i++)
					if (initval[i] == State::S0 || initval[i] == State::S1)
						dff_init_map.add(SigBit(it.second, i), initval[i]);
			}

		bool did_something = true;
		while (did_something)
		{
			std::vector<RTLIL::Cell*> cells;
			cells.reserve(module->cells_.size());
			for (auto &it : module->cells_) {
				if (!design->selected(module, it.second))
					continue;
				if (ct.cell_known(it.second->type) || (mode_share_all && it.second->known()))
					cells.push_back(it.second);
			}

			did_something = false;
			dict<std::string, RTLIL::Cell*> sharemap;
			for (auto cell : cells)
			{
				if ((!mode_share_all && !ct.cell_known(cell->type)) || !cell->known())
					continue;

				auto hash = hash_cell_parameters_and_connections(cell);
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
								module->connect(RTLIL::SigSig(it.second, other_sig));
								assign_map.add(it.second, other_sig);

								if (it.first == ID::Q && RTLIL::builtin_ff_cell_types().count(cell->type)) {
									for (auto c : it.second.chunks()) {
										auto jt = c.wire->attributes.find(ID::init);
										if (jt == c.wire->attributes.end())
											continue;
										for (int i = c.offset; i < c.offset + c.width; i++)
											jt->second[i] = State::Sx;
									}
									dff_init_map.add(it.second, Const(State::Sx, GetSize(it.second)));
								}
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
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
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
