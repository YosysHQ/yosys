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

#include "kernel/ffinit.h"
#include "kernel/yosys_common.h"
#include "passes/opt/opt_clean/opt_clean.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

unsigned int hash_bit(const SigBit &bit) {
	return static_cast<unsigned int>(hash_ops<SigBit>::hash(bit).yield());
}

SigMap wire_sigmap(const RTLIL::Module* mod) {
	SigMap map;
	for (auto &it : mod->connections_) {
		for (int i = 0; i < GetSize(it.second); i++) {
			if (it.second[i].wire != nullptr)
				map.add(it.first[i], it.second[i]);
		}
	}
	return map;
}

struct WireDrivers;
// Maps from a SigBit to a unique driver cell.
struct WireDriver {
	using Accumulated = WireDrivers;
	SigBit bit;
	int driver_cell;
};
// Maps from a SigBit to one or more driver cells.
struct WireDrivers {
	WireDrivers() : driver_cell(0) {}
	WireDrivers(WireDriver driver) : bit(driver.bit), driver_cell(driver.driver_cell) {}
	WireDrivers(SigBit bit) : bit(bit), driver_cell(0) {}
	WireDrivers(WireDrivers &&other) = default;

	class const_iterator {
	public:
		const_iterator(const WireDrivers &drivers, bool end)
				: driver_cell(drivers.driver_cell), in_extra_cells(end) {
			if (drivers.extra_driver_cells) {
				if (end) {
					extra_it = drivers.extra_driver_cells->end();
				} else {
					extra_it = drivers.extra_driver_cells->begin();
				}
			}
		}
		int operator*() const {
			if (in_extra_cells)
				return **extra_it;
			return driver_cell;
		}
		const_iterator& operator++() {
			if (in_extra_cells)
				++*extra_it;
			else
				in_extra_cells = true;
			return *this;
		}
		bool operator!=(const const_iterator &other) const {
			return !(*this == other);
		}
		bool operator==(const const_iterator &other) const {
			return in_extra_cells == other.in_extra_cells &&
				extra_it == other.extra_it;
		}
	private:
		std::optional<pool<int>::iterator> extra_it;
		int driver_cell;
		bool in_extra_cells;
	};

	const_iterator begin() const { return const_iterator(*this, false); }
	const_iterator end() const { return const_iterator(*this, true); }

	SigBit bit;
	int driver_cell;
	std::unique_ptr<pool<int>> extra_driver_cells;
};
struct WireDriversKeyEquality {
	bool operator()(const WireDrivers &a, const WireDrivers &b) const {
		return a.bit == b.bit;
	}
};
struct WireDriversCollisionHandler {
	void operator()(WireDrivers &incumbent, WireDrivers &new_value) const {
		log_assert(new_value.extra_driver_cells == nullptr);
		if (!incumbent.extra_driver_cells)
			incumbent.extra_driver_cells.reset(new pool<int>());
		incumbent.extra_driver_cells->insert(new_value.driver_cell);
	}
};
using Wire2Drivers = ShardedHashtable<WireDriver, WireDriversKeyEquality, WireDriversCollisionHandler>;

// TODO difference from DeferredLogs ?
struct ConflictLogs {
	ShardedVector<std::pair<SigBit, std::string>> logs;
	ConflictLogs(ParallelDispatchThreadPool::Subpool &subpool) : logs(subpool) {}
	void print_warnings(pool<SigBit>& used_raw_bits, const SigMap& wire_map, const RTLIL::Module* mod, CleanRunContext &clean_ctx) {
		if (!logs.empty()) {
			// We could do this in parallel but hopefully this is rare.
			for (auto [_, cell] : mod->cells_) {
				for (auto &[port, sig] : cell->connections()) {
					if (clean_ctx.ct_all.cell_known(cell->type) && !clean_ctx.ct_all.cell_input(cell->type, port))
						continue;
					for (auto raw_bit : wire_map(sig))
						used_raw_bits.insert(raw_bit);
				}
			}
			for (std::pair<SigBit, std::string> &it : logs) {
				if (used_raw_bits.count(it.first))
					log_warning("%s\n", it.second);
			}
		}
	}
};

struct CellTraversal {
	ConcurrentWorkQueue<int> queue;
	Wire2Drivers wire2driver;
	dict<std::string, pool<int>> mem2cells;
	CellTraversal(int num_threads) : queue(num_threads), wire2driver(), mem2cells() {}
};

struct CellAnalysis {
	ShardedVector<Wire*> keep_wires;
	std::vector<std::atomic<bool>> unused;

	CellAnalysis(AnalysisContext& actx)
	: keep_wires(actx.subpool), unused(actx.mod->cells_size()) {}

	pool<SigBit> analyze_kept_wires(CellTraversal& traversal, const SigMap& sigmap, const SigMap& wire_map, int num_threads) {
		// Also enqueue cells that drive kept wires into cell_queue
		// and mark those cells as used
		// and mark all bits of those wires as used
		pool<SigBit> used_raw_bits;
		int i = 0;
		for (Wire *wire : keep_wires) {
			for (auto bit : sigmap(wire)) {
				const WireDrivers *drivers = traversal.wire2driver.find({{bit}, hash_bit(bit)});
				if (drivers != nullptr)
					for (int cell_index : *drivers)
						if (unused[cell_index].exchange(false, std::memory_order_relaxed)) {
							ThreadIndex fake_thread_index = {i++ % num_threads};
							traversal.queue.push(fake_thread_index, cell_index);
						}
			}
			for (auto raw_bit : SigSpec(wire))
				used_raw_bits.insert(wire_map(raw_bit));
		}
		return used_raw_bits;
	}

	void mark_used_and_enqueue(int cell_idx, ConcurrentWorkQueue<int>& queue, const ParallelDispatchThreadPool::RunCtx &ctx) {
		if (unused[cell_idx].exchange(false, std::memory_order_relaxed))
			queue.push(ctx, cell_idx);
	}
};



// TODO name
ConflictLogs explore(CellAnalysis& analysis, CellTraversal& traversal, const SigMap& wire_map, AnalysisContext& actx, CleanRunContext &clean_ctx) {
	ConflictLogs logs(actx.subpool);
	Wire2Drivers::Builder wire2driver_builder(actx.subpool);
	ShardedVector<std::pair<std::string, int>> mem2cells_vector(actx.subpool);

	// Enqueue kept cells into traversal.queue
	// Prepare input cone traversal into traversal.wire2driver
	// Prepare "input cone" traversal from memory to write port or meminit as analysis.mem2cells
	// Also check driver conflicts
	// Also mark cells unused to true unless keep (we override this later)
	actx.subpool.run([&analysis, &traversal, &logs, &wire_map, &mem2cells_vector, &wire2driver_builder, &actx, &clean_ctx](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(actx.mod->cells_size())) {
			Cell *cell = actx.mod->cell_at(i);
			if (cell->type.in(ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2)))
				mem2cells_vector.insert(ctx, {cell->getParam(ID::MEMID).decode_string(), i});

			for (auto &it2 : cell->connections()) {
				if (clean_ctx.ct_all.cell_known(cell->type) && !clean_ctx.ct_all.cell_output(cell->type, it2.first))
					continue;
				for (auto raw_bit : it2.second) {
					if (raw_bit.wire == nullptr)
						continue;
					auto bit = actx.assign_map(raw_bit);
					if (bit.wire == nullptr && clean_ctx.ct_all.cell_known(cell->type)) {
						std::string msg = stringf("Driver-driver conflict "
							"for %s between cell %s.%s and constant %s in %s: Resolved using constant.",
							log_signal(raw_bit), cell->name.unescape(), it2.first.unescape(), log_signal(bit), actx.mod->name.unescape());
							logs.logs.insert(ctx, {wire_map(raw_bit), msg});
						}
						if (bit.wire != nullptr)
							wire2driver_builder.insert(ctx, {{bit, i}, hash_bit(bit)});
					}
			}
			bool keep = clean_ctx.keep_cache.query(cell);
			analysis.unused[i].store(!keep, std::memory_order_relaxed);
			if (keep)
				traversal.queue.push(ctx, i);
		}
		for (int i : ctx.item_range(actx.mod->wires_size())) {
			Wire *wire = actx.mod->wire_at(i);
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				analysis.keep_wires.insert(ctx, wire);
		}
	});
	// Finish by merging per-thread collected data
	actx.subpool.run([&wire2driver_builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		wire2driver_builder.process(ctx);
	});
	traversal.wire2driver = wire2driver_builder;

	for (std::pair<std::string, int> &mem2cell : mem2cells_vector)
		traversal.mem2cells[mem2cell.first].insert(mem2cell.second);

	return logs;
}

struct MemAnalysis {
	std::vector<std::atomic<bool>> unused;
	dict<std::string, int> indices;
	MemAnalysis(const RTLIL::Module* mod) : unused(mod->memories.size()), indices() {
		for (int i = 0; i < GetSize(mod->memories); ++i) {
			indices[mod->memories.element(i)->first.str()] = i;
			unused[i].store(true, std::memory_order_relaxed);
		}
	}
};

void fixup_unused_cells_and_mems(CellAnalysis& analysis, MemAnalysis& mem_analysis, CellTraversal& traversal, AnalysisContext& actx, CleanRunContext &clean_ctx) {
	// Processes the cell queue in batches, traversing input cones by enqueuing more cells
	// Discover and mark used memories and cells
	actx.subpool.run([&analysis, &mem_analysis, &traversal, &actx, &clean_ctx](const ParallelDispatchThreadPool::RunCtx &ctx) {
		pool<SigBit> bits;
		pool<std::string> mems;
		while (true) {
			std::vector<int> cell_indices = traversal.queue.pop_batch(ctx);
			if (cell_indices.empty())
				return;
			for (auto cell_index : cell_indices) {
				Cell *cell = actx.mod->cell_at(cell_index);
				for (auto &it : cell->connections())
					if (!clean_ctx.ct_all.cell_known(cell->type) || clean_ctx.ct_all.cell_input(cell->type, it.first))
						for (auto bit : actx.assign_map(it.second))
							bits.insert(bit);

				if (cell->type.in(ID($memrd), ID($memrd_v2))) {
					std::string mem_id = cell->getParam(ID::MEMID).decode_string();
					if (mem_analysis.indices.count(mem_id)) {
						int mem_index = mem_analysis.indices[mem_id];
						// Memory fixup
						if (mem_analysis.unused[mem_index].exchange(false, std::memory_order_relaxed))
							mems.insert(mem_id);
					}
				}
			}

			for (auto bit : bits) {
				// Cells fixup
				const WireDrivers *drivers = traversal.wire2driver.find({{bit}, hash_bit(bit)});
				if (drivers != nullptr)
					for (int cell_idx : *drivers)
						analysis.mark_used_and_enqueue(cell_idx, traversal.queue, ctx);
			}
			bits.clear();

			for (auto mem : mems) {
				if (traversal.mem2cells.count(mem) == 0)
					continue;
				// Cells fixup
				for (int cell_idx : traversal.mem2cells.at(mem))
					analysis.mark_used_and_enqueue(cell_idx, traversal.queue, ctx);
			}
			mems.clear();
		}
	});
}

pool<Cell*> all_unused_cells(const Module *mod, const CellAnalysis& analysis, Wire2Drivers& wire2driver, ParallelDispatchThreadPool::Subpool &subpool) {
	pool<Cell*> unused_cells;
	ShardedVector<int> sharded_unused_cells(subpool);
	subpool.run([mod, &analysis, &wire2driver, &sharded_unused_cells](const ParallelDispatchThreadPool::RunCtx &ctx) {
		// Parallel destruction of `wire2driver`
		wire2driver.clear(ctx);
		for (int i : ctx.item_range(mod->cells_size()))
			if (analysis.unused[i].load(std::memory_order_relaxed))
				sharded_unused_cells.insert(ctx, i);
	});
	for (int cell_index : sharded_unused_cells)
		unused_cells.insert(mod->cell_at(cell_index));
	unused_cells.sort(RTLIL::sort_by_name_id<RTLIL::Cell>());
	return unused_cells;
}

void remove_cells(RTLIL::Module* mod, FfInitVals& ffinit, const pool<Cell*>& cells, bool verbose, RmStats& stats) {
	for (auto cell : cells) {
		if (verbose)
			log_debug("  removing unused `%s' cell `%s'.\n", cell->type, cell->name);
		mod->design->scratchpad_set_bool("opt.did_something", true);
		if (cell->is_builtin_ff())
			ffinit.remove_init(cell->getPort(ID::Q));
		mod->remove(cell);
		stats.count_rm_cells++;
	}
}

void remove_mems(RTLIL::Module* mod, const MemAnalysis& mem_analysis, bool verbose) {
	for (const auto &it : mem_analysis.indices) {
		if (!mem_analysis.unused[it.second].load(std::memory_order_relaxed))
			continue;
		RTLIL::IdString id(it.first);
		if (verbose)
			log_debug("  removing unused memory `%s'.\n", id.unescape());
		delete mod->memories.at(id);
		mod->memories.erase(id);
	}
}

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN

void rmunused_module_cells(Module *module, ParallelDispatchThreadPool::Subpool &subpool, CleanRunContext &clean_ctx)
{
	AnalysisContext actx(module, subpool);
	SigMap sigmap(module);
	FfInitVals ffinit;
	ffinit.set_parallel(&sigmap, subpool.thread_pool(), module);

	// Used for logging warnings only
	SigMap wire_map = wire_sigmap(module);

	CellAnalysis analysis(actx);
	CellTraversal traversal(subpool.num_threads());
	// Mark all unkept cells as unused initially
	// and queue up cell traversal from those cells
	auto logs = explore(analysis, traversal, wire_map, actx, clean_ctx);
	// Mark cells that drive kept wires into cell_queue and those bits as used
	// and queue up cell traversal from those cells
	pool<SigBit> used_raw_bits = analysis.analyze_kept_wires(traversal, sigmap, wire_map, subpool.num_threads());

	// Mark all memories as unused initially
	MemAnalysis mem_analysis(module);
	// Marked all used cells and mems as used by traversing with cell queue
	fixup_unused_cells_and_mems(analysis, mem_analysis, traversal, actx, clean_ctx);
	// Analyses are now fully correct

	// unused_cells.contains(foo) iff analysis.used[foo] == true
	// wire2driver is passed in only to destroy it
	pool<Cell*> unused_cells = all_unused_cells(module, analysis, traversal.wire2driver, subpool);

	// Now we know what to kill
	remove_cells(module, ffinit, unused_cells, clean_ctx.flags.verbose, clean_ctx.stats);
	remove_mems(module, mem_analysis, clean_ctx.flags.verbose);
	logs.print_warnings(used_raw_bits, wire_map, module, clean_ctx);
}

YOSYS_NAMESPACE_END
