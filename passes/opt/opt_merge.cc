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
#include "kernel/threading.h"
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

// Some cell and its hash value.
struct CellHash
{
	// Index of a cell in the module
	int cell_index;
	Hasher::hash_t hash_value;
};

// The algorithm:
// 1) Compute and store the hashes of all relevant cells, in parallel.
// 2) Given N = the number of threads, partition the cells into N buckets by hash value:
// bucket k contains the cells whose hash value mod N = k.
// 3) For each bucket in parallel, build a hashtable of that bucket’s cells (using the
// precomputed hashes) and record the duplicates found.
// 4) On the main thread, process the list of duplicates to remove cells.
// For efficiency we fuse the second step into the first step by having the parallel
// threads write the cells into buckets directly.
// To avoid synchronization overhead, we divide each bucket into N shards. Each
// thread j adds a cell to bucket k by writing to shard j of bucket k —
// no synchronization required. In the next phase, thread k builds the hashtable for
// bucket k by iterating over all shards of the bucket.

// The input to each thread in the "compute cell hashes" phase.
struct CellRange
{
	int begin;
	int end;
};

// The output from each thread in the "compute cell hashes" phase.
struct CellHashes
{
	// Entry i contains the hashes where hash_value % bucketed_cell_hashes.size() == i
	std::vector<std::vector<CellHash>> bucketed_cell_hashes;
};

// A duplicate cell that has been found.
struct DuplicateCell
{
	// Remove this cell from the design
	int remove_cell;
	// ... and use this cell instead.
	int keep_cell;
};

// The input to each thread in the "find duplicate cells" phase.
// Shards of buckets of cell hashes
struct Shards
{
	std::vector<std::vector<std::vector<CellHash>>> &bucketed_cell_hashes;
};

// The output from each thread in the "find duplicate cells" phase.
struct FoundDuplicates
{
	std::vector<DuplicateCell> duplicates;
};

struct OptMergeThreadWorker : public CellHasher
{
	const RTLIL::Module *module;
	const CellTypes &ct;
	int workers;
	bool mode_share_all;
	bool mode_keepdc;

	OptMergeThreadWorker(const RTLIL::Module *module, const FfInitVals &initvals,
			const SigMap &assign_map, const CellTypes &ct, int workers,
			bool mode_share_all, bool mode_keepdc) :
		CellHasher(assign_map, initvals, /*apply_sigmap=*/true),
		module(module), ct(ct),
		workers(workers), mode_share_all(mode_share_all), mode_keepdc(mode_keepdc)
	{
	}

	CellHashes compute_cell_hashes(const CellRange &cell_range) const
	{
		std::vector<std::vector<CellHash>> bucketed_cell_hashes(workers);
		for (int cell_index = cell_range.begin; cell_index < cell_range.end; ++cell_index) {
			const RTLIL::Cell *cell = module->cell_at(cell_index);
			if (!module->selected(cell))
				continue;
			if (cell->type.in(ID($meminit), ID($meminit_v2), ID($mem), ID($mem_v2))) {
				// Ignore those for performance: meminit can have an excessively large port,
				// mem can have an excessively large parameter holding the init data
				continue;
			}
			if (cell->type == ID($scopeinfo))
				continue;
			if (mode_keepdc && has_dont_care_initval(cell))
				continue;
			if (!cell->known())
				continue;
			if (!mode_share_all && !ct.cell_known(cell->type))
				continue;

			Hasher::hash_t h = hash_cell_function(cell, Hasher()).yield();
			int bucket_index = h % workers;
			bucketed_cell_hashes[bucket_index].push_back({cell_index, h});
		}
		return {std::move(bucketed_cell_hashes)};
	}

	FoundDuplicates find_duplicate_cells(int index, const Shards &in) const
	{
		// We keep a set of known cells. They're hashed with our hash_cell_function
		// and compared with our compare_cell_parameters_and_connections.
		struct CellHashOp {
			std::size_t operator()(const CellHash &c) const {
				return (std::size_t)c.hash_value;
			}
		};
		struct CellEqualOp {
			const OptMergeThreadWorker& worker;
			CellEqualOp(const OptMergeThreadWorker& w) : worker(w) {}
			bool operator()(const CellHash &lhs, const CellHash &rhs) const {
				return worker.compare_cell_parameters_and_connections(
						worker.module->cell_at(lhs.cell_index),
						worker.module->cell_at(rhs.cell_index));
			}
		};
		std::unordered_set<
			CellHash,
			CellHashOp,
			CellEqualOp> known_cells(0, CellHashOp(), CellEqualOp(*this));

		std::vector<DuplicateCell> duplicates;
		for (const std::vector<std::vector<CellHash>> &buckets : in.bucketed_cell_hashes) {
			// Clear out our buckets as we go. This keeps the work of deallocation
			// off the main thread.
			std::vector<CellHash> bucket = std::move(buckets[index]);
			for (CellHash c : bucket) {
				auto [cell_in_map, inserted] = known_cells.insert(c);
				if (inserted)
					continue;
				CellHash map_c = *cell_in_map;
				if (module->cell_at(c.cell_index)->has_keep_attr()) {
					if (module->cell_at(map_c.cell_index)->has_keep_attr())
						continue;
					known_cells.erase(map_c);
					known_cells.insert(c);
					std::swap(c, map_c);
				}
				duplicates.push_back({c.cell_index, map_c.cell_index});
			}
		}
		return {duplicates};
	}
};

template <typename T>
void initialize_queues(std::vector<ConcurrentQueue<T>> &queues, int size) {
	queues.reserve(size);
	for (int i = 0; i < size; ++i)
		queues.emplace_back(1);
}

struct OptMergeWorker
{
	int total_count;

	OptMergeWorker(RTLIL::Module *module, const CellTypes &ct, bool mode_share_all, bool mode_keepdc) :
		total_count(0)
	{
		SigMap assign_map(module);
		FfInitVals initvals;
		initvals.set(&assign_map, module);

		log("Finding identical cells in module `%s'.\n", module->name);

		// Use no more than one worker per thousand cells, rounded down, so
		// we only start multithreading with at least 2000 cells.
		int num_worker_threads = ThreadPool::pool_size(0, module->cells_size()/1000);
		int workers = std::max(1, num_worker_threads);

		// The main thread doesn't do any work, so if there is only one worker thread,
		// just run everything on the main thread instead.
		// This avoids creating and waiting on a thread, which is pretty high overhead
		// for very small modules.
		if (num_worker_threads == 1)
			num_worker_threads = 0;
		OptMergeThreadWorker thread_worker(module, initvals, assign_map, ct, workers, mode_share_all, mode_keepdc);

		std::vector<ConcurrentQueue<CellRange>> cell_ranges_queues(num_worker_threads);
		std::vector<ConcurrentQueue<CellHashes>> cell_hashes_queues(num_worker_threads);
		std::vector<ConcurrentQueue<Shards>> shards_queues(num_worker_threads);
		std::vector<ConcurrentQueue<FoundDuplicates>> duplicates_queues(num_worker_threads);

		ThreadPool thread_pool(num_worker_threads, [&](int i) {
			while (std::optional<CellRange> c = cell_ranges_queues[i].pop_front()) {
				cell_hashes_queues[i].push_back(thread_worker.compute_cell_hashes(*c));
				std::optional<Shards> shards = shards_queues[i].pop_front();
				duplicates_queues[i].push_back(thread_worker.find_duplicate_cells(i, *shards));
			}
		});

		bool did_something = true;
		// A cell may have to go through a lot of collisions if the hash
		// function is performing poorly, but it's a symptom of something bad
		// beyond the user's control.
		while (did_something)
		{
			int cells_size = module->cells_size();
			log("Computing hashes of %d cells of `%s'.\n", cells_size, module->name);
			std::vector<std::vector<std::vector<CellHash>>> sharded_bucketed_cell_hashes(workers);

			int cell_index = 0;
			int cells_size_mod_workers = cells_size % workers;
			{
				Multithreading multithreading;
				for (int i = 0; i < workers; ++i) {
					int num_cells = cells_size/workers + ((i < cells_size_mod_workers) ? 1 : 0);
					CellRange c = { cell_index, cell_index + num_cells };
					cell_index += num_cells;
					if (num_worker_threads > 0)
						cell_ranges_queues[i].push_back(c);
					else
						sharded_bucketed_cell_hashes[i] = std::move(thread_worker.compute_cell_hashes(c).bucketed_cell_hashes);
				}
				log_assert(cell_index == cells_size);
				if (num_worker_threads > 0)
					for (int i = 0; i < workers; ++i)
						sharded_bucketed_cell_hashes[i] = std::move(cell_hashes_queues[i].pop_front()->bucketed_cell_hashes);
			}

			log("Finding duplicate cells in `%s'.\n", module->name);
			std::vector<DuplicateCell> merged_duplicates;
			{
				Multithreading multithreading;
				for (int i = 0; i < workers; ++i) {
					Shards thread_shards = { sharded_bucketed_cell_hashes };
					if (num_worker_threads > 0)
						shards_queues[i].push_back(thread_shards);
					else {
						std::vector<DuplicateCell> d = std::move(thread_worker.find_duplicate_cells(i, thread_shards).duplicates);
						merged_duplicates.insert(merged_duplicates.end(), d.begin(), d.end());
					}
				}
				if (num_worker_threads > 0)
					for (int i = 0; i < workers; ++i) {
						std::vector<DuplicateCell> d = std::move(duplicates_queues[i].pop_front()->duplicates);
						merged_duplicates.insert(merged_duplicates.end(), d.begin(), d.end());
					}
			}
			std::sort(merged_duplicates.begin(), merged_duplicates.end(), [](const DuplicateCell &lhs, const DuplicateCell &rhs) {
				// Sort them by the order in which duplicates would have been detected in a single-threaded
				// run. The cell at which the duplicate would have been detected is the latter of the two
				// cells involved.
				return std::max(lhs.remove_cell, lhs.keep_cell) < std::max(rhs.remove_cell, rhs.keep_cell);
			});

			// Convert to cell pointers because removing cells will invalidate the indices.
			std::vector<std::pair<RTLIL::Cell*, RTLIL::Cell*>> cell_ptrs;
			for (DuplicateCell dup : merged_duplicates)
				cell_ptrs.push_back({module->cell_at(dup.remove_cell), module->cell_at(dup.keep_cell)});

			for (auto [remove_cell, keep_cell] : cell_ptrs)
			{
				log_debug("  Cell `%s' is identical to cell `%s'.\n", remove_cell->name, keep_cell->name);
				for (auto &it : remove_cell->connections()) {
					if (remove_cell->output(it.first)) {
						RTLIL::SigSpec keep_sig = keep_cell->getPort(it.first);
						log_debug("    Redirecting output %s: %s = %s\n", it.first,
								log_signal(it.second), log_signal(keep_sig));
						Const init = initvals(keep_sig);
						initvals.remove_init(it.second);
						initvals.remove_init(keep_sig);
						module->connect(RTLIL::SigSig(it.second, keep_sig));
						auto keep_sig_it = keep_sig.begin();
						for (SigBit remove_sig_bit : it.second) {
							assign_map.add(remove_sig_bit, *keep_sig_it);
							++keep_sig_it;
						}
						initvals.set_init(keep_sig, init);
					}
				}
				log_debug("    Removing %s cell `%s' from module `%s'.\n", remove_cell->type, remove_cell->name, module->name);
				module->remove(remove_cell);
				total_count++;
			}
			did_something = !merged_duplicates.empty();
		}

		for (ConcurrentQueue<CellRange> &q : cell_ranges_queues)
			q.close();

		for (ConcurrentQueue<Shards> &q : shards_queues)
			q.close();

		for (ConcurrentQueue<CellRange> &q : cell_ranges_queues)
			q.close();

		for (ConcurrentQueue<Shards> &q : shards_queues)
			q.close();

		log_suppressed();
	}
};

struct OptMergePass : public Pass {
	OptMergePass() : Pass("opt_merge_old", "consolidate identical cells") { }
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

		CellTypes ct;
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

		int total_count = 0;
		for (auto module : design->selected_modules()) {
			OptMergeWorker worker(module, ct, mode_share_all, mode_keepdc);
			total_count += worker.total_count;
		}

		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Removed a total of %d cells.\n", total_count);
	}
} OptMergePass;

PRIVATE_NAMESPACE_END
