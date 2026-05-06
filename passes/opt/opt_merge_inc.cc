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
#include "kernel/newcelltypes.h"
#include "libs/sha1/sha1.h"
#include "passes/opt/opt_merge_common.h"
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>
#include <set>
#include <unordered_map>
#include <array>


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using OptMergeCommon::CellHasher;
using MergeableTypes = StaticCellTypes::Categories::Category;

// setup_internals + setup_internals_mem + setup_stdcells + setup_stdcells_mem,
// minus a fixed set of cells we never want to merge. setup_internals_anyinit
// is intentionally not included, so $anyinit stays excluded
static constexpr MergeableTypes build_mergeable_types(bool nomux) {
	auto c = StaticCellTypes::categories.is_known;
	c.set_id(ID($anyinit), false);
	c.set_id(ID($tribuf), false);
	c.set_id(ID($_TBUF_), false);
	c.set_id(ID($anyseq), false);
	c.set_id(ID($anyconst), false);
	c.set_id(ID($allseq), false);
	c.set_id(ID($allconst), false);
	c.set_id(ID($connect), false);
	c.set_id(ID($input_port), false);
	if (nomux) {
		c.set_id(ID($mux), false);
		c.set_id(ID($pmux), false);
	}
	return c;
}

static constexpr MergeableTypes mergeable_with_mux = build_mergeable_types(false);
static constexpr MergeableTypes mergeable_without_mux = build_mergeable_types(true);

struct OptMergeIncWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap assign_map;
	FfInitVals initvals;
	bool mode_share_all;

	const MergeableTypes &ct;
	int total_count;
	CellHasher hasher;

	OptMergeIncWorker(RTLIL::Design *design, RTLIL::Module *module, const MergeableTypes &ct, bool mode_share_all, bool mode_keepdc) :
		design(design), module(module), mode_share_all(mode_share_all), ct(ct),
		hasher(assign_map, initvals, /*apply_sigmap=*/false)
	{
		total_count = 0;

		log("Finding identical cells in module `%s'.\n", module->name);
		assign_map.set(module);

		initvals.set(&assign_map, module);


		dict<Cell *, uint32_t> hashes;
		dict<uint32_t, Cell *> first_with_hash;
		dict<uint32_t, pool<Cell *>> more_with_hash;

		auto forget_cell = [&](Cell * cell) {
			auto found = hashes.find(cell);
			if (found != hashes.end()) {
				auto found_first = first_with_hash.find(found->second);
				log_assert(found_first != first_with_hash.end());
				auto found_more = more_with_hash.find(found->second);
				if (found_more != more_with_hash.end()) {
					found_more->second.erase(cell);
					found_first->second = *found_more->second.begin();
					if (found_more->second.size() < 2)
						more_with_hash.erase(found_more);
				}

				// auto found_first = first_with_hash.find(found->second);
				// log_assert(found_first != first_with_hash.end());
				// if (found_first->second == cell) {
				// 	auto found_more = more_with_hash.find(found->second);
				// 	if (found_more != more_with_hash.end()) {
				// 		log_assert(!found_more->second.empty());
				// 		found_first->second = found_more->second.pop();
				// 		if (found_more->second.empty())
				// 			more_with_hash.erase(found_more);

				// 	} else {
				// 		first_with_hash.erase(found_first);
				// 	}

				// } else {
				// 	auto found_more = more_with_hash.find(found->second);
				// 	if (found_more != more_with_hash.end()) {
				// 		found_more->second.erase(cell);
				// 		if (found_more->second.empty())
				// 			more_with_hash.erase(found_more);
				// 	}
				// }
			}
		};

		auto remember_cell = [&](Cell * cell, uint32_t hash) -> bool {
			hashes[cell] = hash;
			auto [it, inserted] = first_with_hash.emplace(hash, cell);
			if (!inserted) {
				auto &more = more_with_hash[hash];
				if (more.empty())
					more.emplace(it->second);
				more.emplace(cell);
			}
			return !inserted;
		};

		int timestamp = INT_MIN;

		bool did_something = true;
		// A cell may have to go through a lot of collisions if the hash
		// function is performing poorly, but it's a symptom of something bad
		// beyond the user's control.

		bool first = true;
		while (did_something)
		{
			std::vector<RTLIL::Cell*> cells;

			if (timestamp == INT_MIN) {
				timestamp = module->next_timestamp();
				cells.reserve(module->cells().size());
				for (auto cell : module->cells()) {
					if (!design->selected(module, cell))
						continue;
					if (cell->type.in(ID($meminit), ID($meminit_v2), ID($mem), ID($mem_v2))) {
						// Ignore those for performance: meminit can have an excessively large port,
						// mem can have an excessively large parameter holding the init data
						continue;
					}
					if (cell->type == ID($scopeinfo))
						continue;
					if (mode_keepdc && hasher.has_dont_care_initval(cell))
						continue;
					if (!cell->known())
						continue;
					if (!mode_share_all && !ct(cell->type))
						continue;

					cells.push_back(cell);
				}
			} else {
				int next = module->next_timestamp();
				// idict<Cell *> pending;
				// for (auto cell : module->dirty_cells(timestamp))
				//     pending(cell);
				// std::vector<const pool<RTLIL::PortBit> *> fanouts;
				// int i = 0;
				// while (i < GetSize(pending)) {
				//     Cell * cell = pending[i];
				pool<Cell *> pending;
				for (auto cell : module->dirty_cells(timestamp)) {
					if (!design->selected(module, cell))
						continue;
					if (cell->type.in(ID($meminit), ID($meminit_v2), ID($mem), ID($mem_v2))) {
						// Ignore those for performance: meminit can have an excessively large port,
						// mem can have an excessively large parameter holding the init data
						continue;
					}
					if (cell->type == ID($scopeinfo))
						continue;
					if (mode_keepdc && hasher.has_dont_care_initval(cell))
						continue;
					if (!cell->known())
						continue;
					if (!mode_share_all && !ct(cell->type))
						continue;


					cells.push_back(cell);
				}
				timestamp = next;
			}
			log("scanning %d cells\n", GetSize(cells));

			did_something = false;

			if (!first)
				for (auto cell : cells)
					forget_cell(cell);
			first = false;


			pool<int32_t> buckets;

			for (auto cell : cells) {
				uint32_t hash = hasher.hash_cell_function(cell, Hasher()).yield();
				if (remember_cell(cell, hash))
					buckets.emplace(hash);
			}

			std::vector<std::pair<Cell *, Cell*>> pairs;
			pool<Cell *> removed;

			log("scanning %d/%d/%d buckets\n", GetSize(buckets), GetSize(more_with_hash), GetSize(first_with_hash));
			for (auto hash : buckets) {
				auto more = more_with_hash.at(hash);

				for (int i = 0; i < GetSize(more); ++i) {
					for (int j = i + 1; j < GetSize(more); ++j) {
						Cell *other_cell = *more.element(j);
						if (removed.count(other_cell))
							continue;
						Cell *cell = *more.element(i);
						if (removed.count(cell))
							break;

						if (!hasher.compare_cell_parameters_and_connections(cell, other_cell))
							continue;

						if (cell->has_keep_attr()) {
							if (other_cell->has_keep_attr())
								continue;
							std::swap(cell, other_cell);
						}

						removed.insert(cell);
						pairs.emplace_back(other_cell, cell);
					}

				}
			}

			for (auto cell : removed)
				forget_cell(cell);

			int iter_count = 0;

			for (auto [other_cell, cell] : pairs) {
				did_something = true;
				log_debug("  Cell `%s' is identical to cell `%s'.\n", cell->name, other_cell->name);

				for (auto &[port, sig] : cell->connections()) {
					if (cell->output(port)) {
						// TODO why was this removed before?
						RTLIL::SigSpec other_sig = other_cell->getPort(port);
						Const init = initvals(other_sig);
						initvals.remove_init(sig);
						initvals.remove_init(other_sig);
						module->connect(sig, other_cell->getPort(port));
						assign_map.add(sig, other_sig);
						initvals.set_init(other_sig, init);
					}
				}

				log_debug("    Removing %s cell `%s' from module `%s'.\n", cell->type, cell->name, module->name);
				module->remove(cell);
				total_count++;
				iter_count++;
			}
			log("removed %d cells\n", iter_count);


				// hashes[cell] = hash;

				// auto [found, inserted] = first_with_hash.emplace(hash, cell);

				// if (inserted) {
				// 	hashes.emplace(cell, hash);
				// 	continue;
				// }


				// // if (check_candidate(found->second))
				// // 	continue;

				// auto found_more = more_with_hash[hash];

				// // for (auto other_cell : found_more) {
				// // 	if (check_candidate(other_cell))
				// // 		continue;
				// // }

				// found_more.emplace(cell);
				// hashes.emplace(cell, hash);

				// // if (compare_cell_parameters_and_connections(found->second, cell)) {

				// // }


				// auto check_candidate = [&](Cell *other_cell) -> bool {
				// 	if (!compare_cell_parameters_and_connections(other_cell, cell))
				// 		return false;

				// 	if (cell->has_keep_attr())
				// 		if (other_cell->has_keep_attr())
				// 			return false;

				// 	forget_cell(cell);



				// 	return true;

				// };

				// if (!check_candidate(found->second)) {
				// }


			// for ()


				// auto [cell_in_map, inserted] = known_cells.insert(cell);
				// if (!inserted) {
				// 	// We've failed to insert since we already have an equivalent cell
				// 	Cell* other_cell = *cell_in_map;
				// 	if (cell->has_keep_attr()) {
				// 		if (other_cell->has_keep_attr())
				// 			continue;
				// 		known_cells.erase(other_cell);
				// 		known_cells.insert(cell);
				// 		std::swap(other_cell, cell);
				// 	}

				// 	did_something = true;
				// 	log_debug("  Cell `%s' is identical to cell `%s'.\n", cell->name, other_cell->name);
				// 	for (auto &it : cell->connections()) {
				// 		if (cell->output(it.first)) {
				// 			RTLIL::SigSpec other_sig = other_cell->getPort(it.first);
				// 			log_debug("    Redirecting output %s: %s = %s\n", it.first,
				// 					log_signal(it.second), log_signal(other_sig));
				// 			Const init = initvals(other_sig);
				// 			initvals.remove_init(it.second);
				// 			initvals.remove_init(other_sig);
				// 			module->connect(RTLIL::SigSig(it.second, other_sig));
				// 			assign_map.add(it.second, other_sig);
				// 			initvals.set_init(other_sig, init);
				// 		}
				// 	}
				// 	log_debug("    Removing %s cell `%s' from module `%s'.\n", cell->type, cell->name, module->name);
				// 	module->remove(cell);
				// 	total_count++;
				// }

		}

		log_suppressed();
	}
};

struct OptMergeIncPass : public Pass {
	OptMergeIncPass() : Pass("opt_merge", "consolidate identical cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_merge_inc [options] [selection]\n");
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
		log_header(design, "Executing OPT_MERGE_INC pass (detect identical cells).\n");

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

		design->sigNormalize(true);

		const MergeableTypes &ct = mode_nomux ? mergeable_without_mux : mergeable_with_mux;

		int total_count = 0;
		for (auto module : design->selected_modules()) {
			OptMergeIncWorker worker(design, module, ct, mode_share_all, mode_keepdc);
			total_count += worker.total_count;
		}


		// design->sigNormalize(false);

		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Removed a total of %d cells.\n", total_count);
	}
} OptMergeIncPass;

PRIVATE_NAMESPACE_END
