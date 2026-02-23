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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
#include "kernel/ffinit.h"
#include "kernel/threading.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using RTLIL::id2cstr;

struct keep_cache_t
{
	dict<Module*, bool> keep_modules;
	bool purge_mode;

	keep_cache_t(bool purge_mode, ParallelDispatchThreadPool &thread_pool, const std::vector<RTLIL::Module *> &selected_modules)
			: purge_mode(purge_mode) {

		std::vector<RTLIL::Module *> scan_modules_worklist;
		dict<RTLIL::Module *, std::vector<RTLIL::Module*>> dependents;
		std::vector<RTLIL::Module *> propagate_kept_modules_worklist;
		for (RTLIL::Module *module : selected_modules) {
			if (keep_modules.count(module))
				continue;
			bool keep = scan_module(module, thread_pool, dependents, ALL_CELLS, scan_modules_worklist);
			keep_modules[module] = keep;
			if (keep)
				propagate_kept_modules_worklist.push_back(module);
		}

		while (!scan_modules_worklist.empty()) {
			RTLIL::Module *module = scan_modules_worklist.back();
			scan_modules_worklist.pop_back();
			if (keep_modules.count(module))
				continue;
			bool keep = scan_module(module, thread_pool, dependents, MINIMUM_CELLS, scan_modules_worklist);
			keep_modules[module] = keep;
			if (keep)
				propagate_kept_modules_worklist.push_back(module);
		}

		while (!propagate_kept_modules_worklist.empty()) {
			RTLIL::Module *module = propagate_kept_modules_worklist.back();
			propagate_kept_modules_worklist.pop_back();
			for (RTLIL::Module *dependent : dependents[module]) {
				if (keep_modules[dependent])
					continue;
				keep_modules[dependent] = true;
				propagate_kept_modules_worklist.push_back(dependent);
			}
		}
	}

	bool query(Cell *cell) const
	{
		if (keep_cell(cell, purge_mode))
			return true;
		if (cell->type.in(ID($specify2), ID($specify3), ID($specrule)))
			return true;
		if (cell->module && cell->module->design) {
			RTLIL::Module *cell_module = cell->module->design->module(cell->type);
			return cell_module != nullptr && keep_modules.at(cell_module);
		}
		return false;
	}

private:
	enum ScanCells {
		// Scan every cell to see if it uses a module that is kept.
		ALL_CELLS,
		// Stop scanning cells if we determine early that this module is kept.
		MINIMUM_CELLS,
	};
	bool scan_module(Module *module, ParallelDispatchThreadPool &thread_pool, dict<RTLIL::Module *, std::vector<RTLIL::Module*>> &dependents,
			ScanCells scan_cells, std::vector<Module*> &worklist) const
	{
		MonotonicFlag keep_module;
		if (module->get_bool_attribute(ID::keep)) {
			if (scan_cells == MINIMUM_CELLS)
				return true;
			keep_module.set();
		}

		ParallelDispatchThreadPool::Subpool subpool(thread_pool, ThreadPool::work_pool_size(0, module->cells_size(), 1000));
		ShardedVector<Module*> deps(subpool);
		const RTLIL::Module *const_module = module;
		bool purge_mode = this->purge_mode;
		subpool.run([purge_mode, const_module, scan_cells, &deps, &keep_module](const ParallelDispatchThreadPool::RunCtx &ctx) {
			bool keep = false;
			for (int i : ctx.item_range(const_module->cells_size())) {
				Cell *cell = const_module->cell_at(i);
				if (keep_cell(cell, purge_mode)) {
					if (scan_cells == MINIMUM_CELLS) {
						keep_module.set();
						return;
					}
					keep = true;
				}
				if (const_module->design) {
					RTLIL::Module *cell_module = const_module->design->module(cell->type);
					if (cell_module != nullptr)
						deps.insert(ctx, cell_module);
				}
			}
			if (keep) {
				keep_module.set();
				return;
			}
			for (int i : ctx.item_range(const_module->wires_size())) {
				Wire *wire = const_module->wire_at(i);
				if (wire->get_bool_attribute(ID::keep)) {
					keep_module.set();
					return;
				}
			}
		});
		if (scan_cells == MINIMUM_CELLS && keep_module.load())
			return true;
		for (Module *dep : deps) {
			dependents[dep].push_back(module);
			worklist.push_back(dep);
		}
		return keep_module.load();
	}

	static bool keep_cell(Cell *cell, bool purge_mode)
	{
		if (cell->type.in(ID($assert), ID($assume), ID($live), ID($fair), ID($cover)))
			return true;

		if (cell->type.in(ID($overwrite_tag)))
			return true;

		if (cell->type == ID($print) || cell->type == ID($check))
			return true;

		if (cell->has_keep_attr())
			return true;

		if (!purge_mode && cell->type == ID($scopeinfo))
			return true;
		return false;
	}
};

CellTypes ct_reg, ct_all;

struct RmStats {
	int count_rm_cells = 0;
	int count_rm_wires = 0;

	void log()
	{
		if (count_rm_cells > 0 || count_rm_wires > 0)
			YOSYS_NAMESPACE_PREFIX log("Removed %d unused cells and %d unused wires.\n", count_rm_cells, count_rm_wires);
	}
};

unsigned int hash_bit(const SigBit &bit) {
	return static_cast<unsigned int>(hash_ops<SigBit>::hash(bit).yield());
}

void rmunused_module_cells(Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose, RmStats &stats, keep_cache_t &keep_cache)
{
	SigMap sigmap(module);
	FfInitVals ffinit;
	ffinit.set_parallel(&sigmap, subpool.thread_pool(), module);

	SigMap raw_sigmap;
	for (auto &it : module->connections_) {
		for (int i = 0; i < GetSize(it.second); i++) {
			if (it.second[i].wire != nullptr)
				raw_sigmap.add(it.first[i], it.second[i]);
		}
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

	Wire2Drivers::Builder wire2driver_builder(subpool);
	ShardedVector<std::pair<std::string, int>> mem2cells_vector(subpool);
	ShardedVector<std::pair<SigBit, std::string>> driver_driver_logs(subpool);
	ShardedVector<Wire*> keep_wires(subpool);
	const RTLIL::Module *const_module = module;
	int num_threads = subpool.num_threads();
	ConcurrentWorkQueue<int> cell_queue(num_threads);
	std::vector<std::atomic<bool>> unused(const_module->cells_size());

	// Enqueue kept cells into cell_queue
	// Prepare input cone traversal from wire to driver cell as wire2driver
	// Prepare "input cone" traversal from memory to write port or meminit as mem2cells
	// Also check driver conflicts
	// Also mark cells unused to true unless keep (we override this later)
	subpool.run([&sigmap, &raw_sigmap, &keep_cache, const_module, &mem2cells_vector, &driver_driver_logs, &keep_wires, &cell_queue, &wire2driver_builder, &unused](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(const_module->cells_size())) {
			Cell *cell = const_module->cell_at(i);
			if (cell->type.in(ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2)))
				mem2cells_vector.insert(ctx, {cell->getParam(ID::MEMID).decode_string(), i});

			for (auto &it2 : cell->connections()) {
				if (ct_all.cell_known(cell->type) && !ct_all.cell_output(cell->type, it2.first))
					continue;
				for (auto raw_bit : it2.second) {
					if (raw_bit.wire == nullptr)
						continue;
					auto bit = sigmap(raw_bit);
					if (bit.wire == nullptr && ct_all.cell_known(cell->type)) {
						std::string msg = stringf("Driver-driver conflict "
								"for %s between cell %s.%s and constant %s in %s: Resolved using constant.",
								log_signal(raw_bit), cell->name.unescape(), it2.first.unescape(), log_signal(bit), const_module->name.unescape());
						driver_driver_logs.insert(ctx, {raw_sigmap(raw_bit), msg});
					}
					if (bit.wire != nullptr)
						wire2driver_builder.insert(ctx, {{bit, i}, hash_bit(bit)});
				}
			}
			bool keep = keep_cache.query(cell);
			unused[i].store(!keep, std::memory_order_relaxed);
			if (keep)
				cell_queue.push(ctx, i);
		}
		for (int i : ctx.item_range(const_module->wires_size())) {
			Wire *wire = const_module->wire_at(i);
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				keep_wires.insert(ctx, wire);
		}
	});
	// Finish by merging per-thread collected data
	subpool.run([&wire2driver_builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		wire2driver_builder.process(ctx);
	});
	Wire2Drivers wire2driver(wire2driver_builder);
	dict<std::string, pool<int>> mem2cells;
	for (std::pair<std::string, int> &mem2cell : mem2cells_vector)
		mem2cells[mem2cell.first].insert(mem2cell.second);

	// Also enqueue cells that drive kept wires into cell_queue
	// and mark those cells as used
	// and mark all bits of those wires as used
	pool<SigBit> used_raw_bits;
	int i = 0;
	for (Wire *wire : keep_wires) {
		for (auto bit : sigmap(wire)) {
			const WireDrivers *drivers = wire2driver.find({{bit}, hash_bit(bit)});
			if (drivers != nullptr)
				for (int cell_index : *drivers)
					if (unused[cell_index].exchange(false, std::memory_order_relaxed)) {
						ThreadIndex fake_thread_index = {i++ % num_threads};
						cell_queue.push(fake_thread_index, cell_index);
					}
		}
		for (auto raw_bit : SigSpec(wire))
			used_raw_bits.insert(raw_sigmap(raw_bit));
	}

	// Mark all memories as unused (we override this later)
	std::vector<std::atomic<bool>> mem_unused(module->memories.size());
	dict<std::string, int> mem_indices;
	for (int i = 0; i < GetSize(module->memories); ++i) {
		mem_indices[module->memories.element(i)->first.str()] = i;
		mem_unused[i].store(true, std::memory_order_relaxed);
	}

	// Discover and mark used memories and cells
	// Processes the cell queue in batches, traversing input cones by enqueuing more cells
	subpool.run([const_module, &sigmap, &wire2driver, &mem2cells, &unused, &cell_queue, &mem_indices, &mem_unused](const ParallelDispatchThreadPool::RunCtx &ctx) {
		pool<SigBit> bits;
		pool<std::string> mems;
		while (true) {
			std::vector<int> cell_indices = cell_queue.pop_batch(ctx);
			if (cell_indices.empty())
				return;
			for (auto cell_index : cell_indices) {
				Cell *cell = const_module->cell_at(cell_index);
				for (auto &it : cell->connections())
					if (!ct_all.cell_known(cell->type) || ct_all.cell_input(cell->type, it.first))
						for (auto bit : sigmap(it.second))
							bits.insert(bit);

				if (cell->type.in(ID($memrd), ID($memrd_v2))) {
					std::string mem_id = cell->getParam(ID::MEMID).decode_string();
					if (mem_indices.count(mem_id)) {
						int mem_index = mem_indices[mem_id];
						if (mem_unused[mem_index].exchange(false, std::memory_order_relaxed))
							mems.insert(mem_id);
					}
				}
			}

			for (auto bit : bits) {
				const WireDrivers *drivers = wire2driver.find({{bit}, hash_bit(bit)});
				if (drivers != nullptr)
					for (int cell_index : *drivers)
						if (unused[cell_index].exchange(false, std::memory_order_relaxed))
							cell_queue.push(ctx, cell_index);
			}
			bits.clear();

			for (auto mem : mems) {
				if (mem2cells.count(mem) == 0)
					continue;
				for (int cell_index : mem2cells.at(mem))
					if (unused[cell_index].exchange(false, std::memory_order_relaxed))
						cell_queue.push(ctx, cell_index);
			}
			mems.clear();
		}
	});

	// Set of all unused cells, built in parallel from unused by filtering for unused[i]==true
	pool<Cell*> unused_cells;
	{
		ShardedVector<int> sharded_unused_cells(subpool);
		subpool.run([const_module, &unused, &sharded_unused_cells, &wire2driver](const ParallelDispatchThreadPool::RunCtx &ctx) {
			// Parallel destruction of `wire2driver`
			wire2driver.clear(ctx);
			for (int i : ctx.item_range(const_module->cells_size()))
				if (unused[i].load(std::memory_order_relaxed))
					sharded_unused_cells.insert(ctx, i);
		});
		for (int cell_index : sharded_unused_cells)
			unused_cells.insert(const_module->cell_at(cell_index));
		unused_cells.sort(RTLIL::sort_by_name_id<RTLIL::Cell>());
	}

	for (auto cell : unused_cells) {
		if (verbose)
			log_debug("  removing unused `%s' cell `%s'.\n", cell->type, cell->name);
		module->design->scratchpad_set_bool("opt.did_something", true);
		if (cell->is_builtin_ff())
			ffinit.remove_init(cell->getPort(ID::Q));
		module->remove(cell);
		stats.count_rm_cells++;
	}

	for (const auto &it : mem_indices) {
		if (!mem_unused[it.second].load(std::memory_order_relaxed))
			continue;
		RTLIL::IdString id(it.first);
		if (verbose)
			log_debug("  removing unused memory `%s'.\n", id.unescape());
		delete module->memories.at(id);
		module->memories.erase(id);
	}

	if (!driver_driver_logs.empty()) {
		// We could do this in parallel but hopefully this is rare.
		for (auto [_, cell] : module->cells_) {
			for (auto &[port, sig] : cell->connections()) {
				if (ct_all.cell_known(cell->type) && !ct_all.cell_input(cell->type, port))
					continue;
				for (auto raw_bit : raw_sigmap(sig))
					used_raw_bits.insert(raw_bit);
			}
		}
		for (std::pair<SigBit, std::string> &it : driver_driver_logs) {
			if (used_raw_bits.count(it.first))
				log_warning("%s\n", it.second);
		}
	}
}

int count_nontrivial_wire_attrs(RTLIL::Wire *w)
{
	int count = w->attributes.size();
	count -= w->attributes.count(ID::src);
	count -= w->attributes.count(ID::hdlname);
	count -= w->attributes.count(ID::scopename);
	count -= w->attributes.count(ID::unused_bits);
	return count;
}

// No collision handler for these, since we will use them such that collisions don't happen
struct ShardedSigBit {
	using Accumulated = ShardedSigBit;
	RTLIL::SigBit bit;
	ShardedSigBit() = default;
	ShardedSigBit(const RTLIL::SigBit &bit) : bit(bit) {}
};
struct ShardedSigBitEquality {
	bool operator()(const ShardedSigBit &b1, const ShardedSigBit &b2) const {
		return b1.bit == b2.bit;
	}
};
using ShardedSigPool = ShardedHashtable<ShardedSigBit, ShardedSigBitEquality>;

struct ShardedSigSpec {
	using Accumulated = ShardedSigSpec;
	RTLIL::SigSpec spec;
	ShardedSigSpec() = default;
	ShardedSigSpec(RTLIL::SigSpec spec) : spec(std::move(spec)) {}
	ShardedSigSpec(ShardedSigSpec &&) = default;
};
struct ShardedSigSpecEquality {
	bool operator()(const ShardedSigSpec &s1, const ShardedSigSpec &s2) const {
		return s1.spec == s2.spec;
	}
};
using ShardedSigSpecPool = ShardedHashtable<ShardedSigSpec, ShardedSigSpecEquality>;

struct DirectWires {
	const SigMap &assign_map;
	const ShardedSigSpecPool &direct_sigs;
	dict<RTLIL::Wire *, bool> cache;

	DirectWires(const SigMap &assign_map, const ShardedSigSpecPool &direct_sigs) : assign_map(assign_map), direct_sigs(direct_sigs) {}
	void cache_result_for_bit(const SigBit &bit) {
		if (bit.wire != nullptr)
			(void)is_direct(bit.wire);
	}
	bool is_direct(RTLIL::Wire *wire) {
		if (wire->port_input)
			return true;
		auto it = cache.find(wire);
		if (it != cache.end())
			return it->second;
		SigSpec direct_sig = assign_map(wire);
		bool direct = direct_sigs.find({direct_sig, direct_sig.hash_into(Hasher()).yield()}) != nullptr;
		cache.insert({wire, direct});
		return direct;
	}
};

// Should we pick `s2` over `s1` to represent a signal?
bool compare_signals(const RTLIL::SigBit &s1, const RTLIL::SigBit &s2, const ShardedSigPool &regs, const ShardedSigPool &conns, DirectWires &direct_wires)
{
	if (s1 == s2)
		return false;

	RTLIL::Wire *w1 = s1.wire;
	RTLIL::Wire *w2 = s2.wire;

	if (w1 == NULL || w2 == NULL)
		return w2 == NULL;

	if (w1->port_input != w2->port_input)
		return w2->port_input;

	if ((w1->port_input && w1->port_output) != (w2->port_input && w2->port_output))
		return !(w2->port_input && w2->port_output);

	if (w1->name.isPublic() && w2->name.isPublic()) {
		ShardedSigPool::AccumulatedValue s1_val = {s1, s1.hash_top().yield()};
		ShardedSigPool::AccumulatedValue s2_val = {s2, s2.hash_top().yield()};
		bool regs1 = regs.find(s1_val) != nullptr;
		bool regs2 = regs.find(s2_val) != nullptr;
		if (regs1 != regs2)
			return regs2;
		bool w1_direct = direct_wires.is_direct(w1);
		bool w2_direct = direct_wires.is_direct(w2);
		if (w1_direct != w2_direct)
			return w2_direct;
		bool conns1 = conns.find(s1_val) != nullptr;
		bool conns2 = conns.find(s2_val) != nullptr;
		if (conns1 != conns2)
			return conns2;
	}

	if (w1 == w2)
		return s2.offset < s1.offset;

	if (w1->port_output != w2->port_output)
		return w2->port_output;

	if (w1->name[0] != w2->name[0])
		return w2->name.isPublic();

	int attrs1 = count_nontrivial_wire_attrs(w1);
	int attrs2 = count_nontrivial_wire_attrs(w2);

	if (attrs1 != attrs2)
		return attrs2 > attrs1;

	return w2->name.lt_by_name(w1->name);
}

bool check_public_name(RTLIL::IdString id)
{
	if (id.begins_with("$"))
		return false;
	const std::string &id_str = id.str();
	if (id.begins_with("\\_") && (id.ends_with("_") || id_str.find("_[") != std::string::npos))
		return false;
	if (id_str.find(".$") != std::string::npos)
		return false;
	return true;
}

void add_spec(ShardedSigPool::Builder &builder, const ThreadIndex &thread, const RTLIL::SigSpec &spec) {
	for (SigBit bit : spec)
		if (bit.wire != nullptr)
			builder.insert(thread, {bit, bit.hash_top().yield()});
}

bool check_any(const ShardedSigPool &sigs, const RTLIL::SigSpec &spec) {
	for (SigBit b : spec)
		if (sigs.find({b, b.hash_top().yield()}) != nullptr)
			return true;
	return false;
}

bool check_all(const ShardedSigPool &sigs, const RTLIL::SigSpec &spec) {
	for (SigBit b : spec)
		if (sigs.find({b, b.hash_top().yield()}) == nullptr)
			return false;
	return true;
}

bool rmunused_module_signals(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool purge_mode, bool verbose, RmStats &stats)
{
	SigMap assign_map(module);

	const RTLIL::Module *const_module = module;
	// `register_signals` and `connected_signals` will help us decide later on
	// on picking representatives out of groups of connected signals
	// Wire bits driven by registers (with clk2fflogic exception)
	ShardedSigPool::Builder register_signals_builder(subpool);
	// Wire bits connected to any cell port
	ShardedSigPool::Builder connected_signals_builder(subpool);
	// construct a pool of wires which are directly driven by a known celltype,
	// this will influence our choice of representatives
	ShardedSigSpecPool::Builder direct_sigs_builder(subpool);
	subpool.run([const_module, purge_mode, &assign_map, &direct_sigs_builder, &register_signals_builder, &connected_signals_builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(const_module->cells_size())) {
			RTLIL::Cell *cell = const_module->cell_at(i);
			if (!purge_mode) {
				if (ct_reg.cell_known(cell->type)) {
					// Improve witness signal naming when clk2fflogic used
					// see commit message e36c71b5
					bool clk2fflogic = cell->get_bool_attribute(ID::clk2fflogic);
					for (auto &[port, sig] : cell->connections())
						if (clk2fflogic ? port == ID::D : ct_reg.cell_output(cell->type, port))
							add_spec(register_signals_builder, ctx, sig);
				}
				// TODO optimize for direct wire connections?
				for (auto &[_, sig] : cell->connections())
					add_spec(connected_signals_builder, ctx, sig);
			}
			if (ct_all.cell_known(cell->type))
				for (auto &[port, sig] : cell->connections())
					if (ct_all.cell_output(cell->type, port)) {
						RTLIL::SigSpec spec = assign_map(sig);
						unsigned int hash = spec.hash_into(Hasher()).yield();
						direct_sigs_builder.insert(ctx, {std::move(spec), hash});
					}
		}
	});
	subpool.run([&register_signals_builder, &connected_signals_builder, &direct_sigs_builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		register_signals_builder.process(ctx);
		connected_signals_builder.process(ctx);
		direct_sigs_builder.process(ctx);
	});
	ShardedSigPool register_signals(register_signals_builder);
	ShardedSigPool connected_signals(connected_signals_builder);
	ShardedSigSpecPool direct_sigs(direct_sigs_builder);

	// First thread's cached direct wires are retained and used later:
	DirectWires direct_wires(assign_map, direct_sigs);
	// Other threads' caches get discarded when threads finish
	// but the per-thread results are collected into sigmap_canonical_candidates
	ShardedVector<RTLIL::SigBit> sigmap_canonical_candidates(subpool);
	subpool.run([const_module, &assign_map, &register_signals, &connected_signals, &sigmap_canonical_candidates, &direct_sigs, &direct_wires](const ParallelDispatchThreadPool::RunCtx &ctx) {
		std::optional<DirectWires> local_direct_wires;
		DirectWires *this_thread_direct_wires = &direct_wires;
		if (ctx.thread_num > 0) {
			// Rebuild a thread-local direct_wires from scratch
			// but from the same inputs
			local_direct_wires.emplace(assign_map, direct_sigs);
			this_thread_direct_wires = &local_direct_wires.value();
		}
		for (int i : ctx.item_range(const_module->wires_size())) {
			RTLIL::Wire *wire = const_module->wire_at(i);
			for (int j = 0; j < wire->width; ++j) {
				RTLIL::SigBit s1(wire, j);
				RTLIL::SigBit s2 = assign_map(s1);
				if (compare_signals(s2, s1, register_signals, connected_signals, *this_thread_direct_wires))
					sigmap_canonical_candidates.insert(ctx, s1);
			}
		}
	});
	// Cache all the direct_wires results that we might possible need. This avoids the results
	// changing when we update `assign_map` below.
	for (RTLIL::SigBit candidate : sigmap_canonical_candidates) {
		direct_wires.cache_result_for_bit(candidate);
		direct_wires.cache_result_for_bit(assign_map(candidate));
	}
	// Modify assign_map to reflect the connectivity we want, not the one we have
	for (RTLIL::SigBit candidate : sigmap_canonical_candidates) {
		RTLIL::SigBit current_canonical = assign_map(candidate);
		if (compare_signals(current_canonical, candidate, register_signals, connected_signals, direct_wires))
			assign_map.add(candidate);
	}

	// we are removing all connections
	module->connections_.clear();

	// here, "used" means "driven or driving something"
	// meanwhile, "unused" means "driving nothing"
	// TODO ...
	// used signals sigmapped
	ShardedSigPool::Builder used_signals_builder(subpool);
	// used signals pre-sigmapped
	ShardedSigPool::Builder raw_used_signals_builder(subpool);
	// used signals sigmapped, ignoring drivers (we keep track of this to set `unused_bits`)
	ShardedSigPool::Builder used_signals_nodrivers_builder(subpool);
	struct UpdateConnection {
		RTLIL::Cell *cell;
		RTLIL::IdString port;
		RTLIL::SigSpec spec;
	};
	// Deferred updates to the assign_map
	ShardedVector<UpdateConnection> update_connections(subpool);
	ShardedVector<RTLIL::Wire*> initialized_wires(subpool);
	// gather the usage information for cells and update cell connections with the altered sigmap
	// also gather the usage information for ports, wires with `keep`
	// also gather init bits
	subpool.run([const_module, &register_signals, &connected_signals, &direct_sigs, &assign_map, &used_signals_builder, &raw_used_signals_builder, &used_signals_nodrivers_builder, &update_connections, &initialized_wires](const ParallelDispatchThreadPool::RunCtx &ctx) {
		// Parallel destruction of these sharded structures
		register_signals.clear(ctx);
		connected_signals.clear(ctx);
		direct_sigs.clear(ctx);

		for (int i : ctx.item_range(const_module->cells_size())) {
			RTLIL::Cell *cell = const_module->cell_at(i);
			for (const auto &[port, sig] : cell->connections_) {
				SigSpec spec = assign_map(sig);
				if (spec != sig)
					update_connections.insert(ctx, {cell, port, spec});
				add_spec(raw_used_signals_builder, ctx, spec);
				add_spec(used_signals_builder, ctx, spec);
				if (!ct_all.cell_output(cell->type, port))
					add_spec(used_signals_nodrivers_builder, ctx, spec);
			}
		}
		for (int i : ctx.item_range(const_module->wires_size())) {
			RTLIL::Wire *wire = const_module->wire_at(i);
			if (wire->port_id > 0) {
				RTLIL::SigSpec sig = RTLIL::SigSpec(wire);
				add_spec(raw_used_signals_builder, ctx, sig);
				assign_map.apply(sig);
				add_spec(used_signals_builder, ctx, sig);
				if (!wire->port_input)
					add_spec(used_signals_nodrivers_builder, ctx, sig);
			}
			if (wire->get_bool_attribute(ID::keep)) {
				RTLIL::SigSpec sig = RTLIL::SigSpec(wire);
				assign_map.apply(sig);
				add_spec(used_signals_builder, ctx, sig);
			}
			auto it = wire->attributes.find(ID::init);
			if (it != wire->attributes.end())
				initialized_wires.insert(ctx, wire);
		}
	});
	subpool.run([&used_signals_builder, &raw_used_signals_builder, &used_signals_nodrivers_builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		used_signals_builder.process(ctx);
		raw_used_signals_builder.process(ctx);
		used_signals_nodrivers_builder.process(ctx);
	});
	ShardedSigPool used_signals(used_signals_builder);
	ShardedSigPool raw_used_signals(raw_used_signals_builder);
	ShardedSigPool used_signals_nodrivers(used_signals_nodrivers_builder);

	dict<RTLIL::SigBit, RTLIL::State> init_bits;
	// The wires that appear in the keys of `init_bits`
	pool<Wire*> init_bits_wires;
	for (const UpdateConnection &update : update_connections)
		update.cell->connections_.at(update.port) = std::move(update.spec);
	for (RTLIL::Wire *intialized_wire : initialized_wires) {
		auto it = intialized_wire->attributes.find(ID::init);
		RTLIL::Const &val = it->second;
		SigSpec sig = assign_map(intialized_wire);
		for (int i = 0; i < GetSize(val) && i < GetSize(sig); i++)
			if (val[i] != State::Sx && sig[i].wire != nullptr) {
				init_bits[sig[i]] = val[i];
				init_bits_wires.insert(sig[i].wire);
			}
		intialized_wire->attributes.erase(it);
	}

	// set init attributes on all wires of a connected group
	for (RTLIL::Wire *wire : init_bits_wires) {
		bool found = false;
		Const val(State::Sx, wire->width);
		for (int i = 0; i < wire->width; i++) {
			auto it = init_bits.find(RTLIL::SigBit(wire, i));
			if (it != init_bits.end()) {
				val.set(i, it->second);
				found = true;
			}
		}
		if (found)
			wire->attributes[ID::init] = val;
	}

	// now decide for each wire if we should be deleting it
	ShardedVector<RTLIL::Wire*> del_wires(subpool);
	ShardedVector<RTLIL::Wire*> remove_init(subpool);
	ShardedVector<std::pair<RTLIL::Wire*, RTLIL::Const>> set_init(subpool);
	ShardedVector<RTLIL::SigSig> connections(subpool);
	ShardedVector<RTLIL::Wire*> remove_unused_bits(subpool);
	ShardedVector<std::pair<RTLIL::Wire*, RTLIL::Const>> set_unused_bits(subpool);
	subpool.run([const_module, purge_mode, &assign_map, &used_signals, &raw_used_signals, &used_signals_nodrivers, &del_wires, &remove_init, &set_init, &connections, &remove_unused_bits, &set_unused_bits](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(const_module->wires_size())) {
			RTLIL::Wire *wire = const_module->wire_at(i);
			SigSpec s1 = SigSpec(wire), s2 = assign_map(s1);
			log_assert(GetSize(s1) == GetSize(s2));

			Const initval;
			bool has_init_attribute = wire->attributes.count(ID::init);
			bool init_changed = false;
			if (has_init_attribute)
				initval = wire->attributes.at(ID::init);
			if (GetSize(initval) != GetSize(wire)) {
				initval.resize(GetSize(wire), State::Sx);
				init_changed = true;
			}

			if (GetSize(wire) == 0) {
				// delete zero-width wires, unless they are module ports
				if (wire->port_id == 0)
					goto delete_this_wire;
			} else
			if (wire->port_id != 0 || wire->get_bool_attribute(ID::keep) || !initval.is_fully_undef()) {
				// do not delete anything with "keep" or module ports or initialized wires
			} else
			if (!purge_mode && check_public_name(wire->name) && (check_any(raw_used_signals, s1) || check_any(used_signals, s2) || s1 != s2)) {
				// do not get rid of public names unless in purge mode or if the wire is entirely unused, not even aliased
			} else
			if (!check_any(raw_used_signals, s1)) {
				// delete wires that aren't used by anything directly
				goto delete_this_wire;
			}

			if (0)
			{
		delete_this_wire:
				del_wires.insert(ctx, wire);
			}
			else
			{
				RTLIL::SigSig new_conn;
				for (int i = 0; i < GetSize(s1); i++)
					if (s1[i] != s2[i]) {
						if (s2[i] == State::Sx && (initval[i] == State::S0 || initval[i] == State::S1)) {
							s2[i] = initval[i];
							initval.set(i, State::Sx);
							init_changed = true;
						}
						new_conn.first.append(s1[i]);
						new_conn.second.append(s2[i]);
					}
				if (new_conn.first.size() > 0)
					connections.insert(ctx, std::move(new_conn));
				if (initval.is_fully_undef()) {
					if (has_init_attribute)
						remove_init.insert(ctx, wire);
				} else
					if (init_changed)
						set_init.insert(ctx, {wire, std::move(initval)});

				std::string unused_bits;
				if (!check_all(used_signals_nodrivers, s2)) {
					for (int i = 0; i < GetSize(s2); i++) {
						if (s2[i].wire == NULL)
							continue;
						SigBit b = s2[i];
						if (used_signals_nodrivers.find({b, b.hash_top().yield()}) == nullptr) {
							if (!unused_bits.empty())
								unused_bits += " ";
							unused_bits += stringf("%d", i);
						}
					}
				}
				if (unused_bits.empty() || wire->port_id != 0) {
					if (wire->attributes.count(ID::unused_bits))
						remove_unused_bits.insert(ctx, wire);
				} else {
					RTLIL::Const unused_bits_const(std::move(unused_bits));
					if (wire->attributes.count(ID::unused_bits)) {
						RTLIL::Const &unused_bits_attr = wire->attributes.at(ID::unused_bits);
						if (unused_bits_attr != unused_bits_const)
							set_unused_bits.insert(ctx, {wire, std::move(unused_bits_const)});
					} else
						set_unused_bits.insert(ctx, {wire, std::move(unused_bits_const)});
				}
			}
		}
	});
	pool<RTLIL::Wire*> del_wires_queue;
	del_wires_queue.insert(del_wires.begin(), del_wires.end());
	for (RTLIL::Wire *wire : remove_init)
		wire->attributes.erase(ID::init);
	for (auto &p : set_init)
		p.first->attributes[ID::init] = std::move(p.second);
	for (auto &conn : connections)
		module->connect(std::move(conn));
	for (RTLIL::Wire *wire : remove_unused_bits)
		wire->attributes.erase(ID::unused_bits);
	for (auto &p : set_unused_bits)
		p.first->attributes[ID::unused_bits] = std::move(p.second);

	subpool.run([&used_signals, &raw_used_signals, &used_signals_nodrivers](const ParallelDispatchThreadPool::RunCtx &ctx) {
		used_signals.clear(ctx);
		raw_used_signals.clear(ctx);
		used_signals_nodrivers.clear(ctx);
	});

	int del_temp_wires_count = 0;
	for (auto wire : del_wires_queue) {
		if (ys_debug() || (check_public_name(wire->name) && verbose))
			log_debug("  removing unused non-port wire %s.\n", wire->name);
		else
			del_temp_wires_count++;
	}

	module->remove(del_wires_queue);
	stats.count_rm_wires += GetSize(del_wires_queue);

	if (verbose && del_temp_wires_count)
		log_debug("  removed %d unused temporary wires.\n", del_temp_wires_count);

	if (!del_wires_queue.empty())
		module->design->scratchpad_set_bool("opt.did_something", true);

	return !del_wires_queue.empty();
}

bool rmunused_module_init(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose)
{
	CellTypes fftypes;
	fftypes.setup_internals_mem();

	SigMap sigmap(module);

	const Module *const_module = module;
	ShardedVector<std::pair<SigBit, State>> results(subpool);
	subpool.run([const_module, &fftypes, &results](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(const_module->cells_size())) {
			RTLIL::Cell *cell = const_module->cell_at(i);
			if (fftypes.cell_known(cell->type) && cell->hasPort(ID::Q))
			{
				SigSpec sig = cell->getPort(ID::Q);

				for (int i = 0; i < GetSize(sig); i++)
				{
					SigBit bit = sig[i];

					if (bit.wire == nullptr || bit.wire->attributes.count(ID::init) == 0)
						continue;

					Const init = bit.wire->attributes.at(ID::init);

					if (i >= GetSize(init) || init[i] == State::Sx || init[i] == State::Sz)
						continue;

					results.insert(ctx, {bit, init[i]});
				}
			}
		}
	});
	dict<SigBit, State> qbits;
	for (std::pair<SigBit, State> &p : results) {
		sigmap.add(p.first);
		qbits[p.first] = p.second;
	}

	ShardedVector<RTLIL::Wire*> wire_results(subpool);
	subpool.run([const_module, &sigmap, &qbits, &wire_results](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int j : ctx.item_range(const_module->wires_size())) {
			RTLIL::Wire *wire = const_module->wire_at(j);
			if (wire->attributes.count(ID::init) == 0)
				continue;
			Const init = wire->attributes.at(ID::init);

			for (int i = 0; i < GetSize(wire) && i < GetSize(init); i++)
			{
				if (init[i] == State::Sx || init[i] == State::Sz)
					continue;

				SigBit wire_bit = SigBit(wire, i);
				SigBit mapped_wire_bit = sigmap(wire_bit);

				if (wire_bit == mapped_wire_bit)
					goto next_wire;

				if (mapped_wire_bit.wire) {
					if (qbits.count(mapped_wire_bit) == 0)
						goto next_wire;

					if (qbits.at(mapped_wire_bit) != init[i])
						goto next_wire;
				}
				else {
					if (mapped_wire_bit == State::Sx || mapped_wire_bit == State::Sz)
						goto next_wire;

					if (mapped_wire_bit != init[i]) {
						log_warning("Initial value conflict for %s resolving to %s but with init %s.\n", log_signal(wire_bit), log_signal(mapped_wire_bit), log_signal(init[i]));
						goto next_wire;
					}
				}
			}
			wire_results.insert(ctx, wire);

			next_wire:;
		}
	});

	bool did_something = false;
	for (RTLIL::Wire *wire : wire_results) {
		if (verbose)
			log_debug("  removing redundant init attribute on %s.\n", log_id(wire));
		wire->attributes.erase(ID::init);
		did_something = true;
	}

	if (did_something)
		module->design->scratchpad_set_bool("opt.did_something", true);

	return did_something;
}

void remove_temporary_cells(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose)
{
	ShardedVector<RTLIL::Cell*> delcells(subpool);
	ShardedVector<RTLIL::SigSig> new_connections(subpool);
	const RTLIL::Module *const_module = module;
	subpool.run([const_module, &delcells, &new_connections](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(const_module->cells_size())) {
			RTLIL::Cell *cell = const_module->cell_at(i);
			if (cell->type.in(ID($pos), ID($_BUF_), ID($buf)) && !cell->has_keep_attr()) {
				bool is_signed = cell->type == ID($pos) && cell->getParam(ID::A_SIGNED).as_bool();
				RTLIL::SigSpec a = cell->getPort(ID::A);
				RTLIL::SigSpec y = cell->getPort(ID::Y);
				a.extend_u0(GetSize(y), is_signed);

				if (a.has_const(State::Sz)) {
					RTLIL::SigSpec new_a;
					RTLIL::SigSpec new_y;
					for (int i = 0; i < GetSize(a); ++i) {
						RTLIL::SigBit b = a[i];
						if (b == State::Sz)
							continue;
						new_a.append(b);
						new_y.append(y[i]);
					}
					a = std::move(new_a);
					y = std::move(new_y);
				}
				if (!y.empty())
					new_connections.insert(ctx, {y, a});
				delcells.insert(ctx, cell);
			} else if (cell->type.in(ID($connect)) && !cell->has_keep_attr()) {
				RTLIL::SigSpec a = cell->getPort(ID::A);
				RTLIL::SigSpec b = cell->getPort(ID::B);
				if (a.has_const() && !b.has_const())
					std::swap(a, b);
				new_connections.insert(ctx, {a, b});
				delcells.insert(ctx, cell);
			} else if (cell->type.in(ID($input_port)) && !cell->has_keep_attr()) {
				delcells.insert(ctx, cell);
			}
		}
	});
	bool did_something = false;
	for (RTLIL::SigSig &connection : new_connections) {
		module->connect(connection);
	}
	for (RTLIL::Cell *cell : delcells) {
		if (verbose) {
			if (cell->type == ID($connect))
				log_debug("  removing connect cell `%s': %s <-> %s\n", cell->name,
						log_signal(cell->getPort(ID::A)), log_signal(cell->getPort(ID::B)));
			else if (cell->type == ID($input_port))
				log_debug("  removing input port marker cell `%s': %s\n", cell->name,
						log_signal(cell->getPort(ID::Y)));
			else
				log_debug("  removing buffer cell `%s': %s = %s\n", cell->name,
						log_signal(cell->getPort(ID::Y)), log_signal(cell->getPort(ID::A)));
		}
		module->remove(cell);
		did_something = true;
	}
	if (did_something)
		module->design->scratchpad_set_bool("opt.did_something", true);
}

void rmunused_module(RTLIL::Module *module, ParallelDispatchThreadPool &thread_pool, bool purge_mode, bool verbose, bool rminit, RmStats &stats, keep_cache_t &keep_cache)
{
	if (verbose)
		log("Finding unused cells or wires in module %s..\n", module->name);

	// Use no more than one worker per thousand cells, rounded down, so
	// we only start multithreading with at least 2000 cells.
	int num_worker_threads = ThreadPool::work_pool_size(0, module->cells_size(), 1000);
	ParallelDispatchThreadPool::Subpool subpool(thread_pool, num_worker_threads);
	remove_temporary_cells(module, subpool, verbose);
	rmunused_module_cells(module, subpool, verbose, stats, keep_cache);
	while (rmunused_module_signals(module, subpool, purge_mode, verbose, stats)) { }

	if (rminit && rmunused_module_init(module, subpool, verbose))
		while (rmunused_module_signals(module, subpool, purge_mode, verbose, stats)) { }
}
struct OptCleanPass : public Pass {
	OptCleanPass() : Pass("opt_clean", "remove unused cells and wires") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_clean [options] [selection]\n");
		log("\n");
		log("This pass identifies wires and cells that are unused and removes them. Other\n");
		log("passes often remove cells but leave the wires in the design or reconnect the\n");
		log("wires but leave the old cells in the design. This pass can be used to clean up\n");
		log("after the passes that do the actual work.\n");
		log("\n");
		log("This pass only operates on completely selected modules without processes.\n");
		log("\n");
		log("    -purge\n");
		log("        also remove internal nets if they have a public name\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool purge_mode = false;

		log_header(design, "Executing OPT_CLEAN pass (remove unused cells and wires).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge") {
				purge_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::vector<RTLIL::Module*> selected_modules;
		for (auto module : design->selected_whole_modules_warn())
			if (!module->has_processes_warn())
				selected_modules.push_back(module);
		int thread_pool_size = 0;
		for (RTLIL::Module *m : selected_modules)
			thread_pool_size = std::max(thread_pool_size, ThreadPool::work_pool_size(0, m->cells_size(), 1000));
		ParallelDispatchThreadPool thread_pool(thread_pool_size);
		keep_cache_t keep_cache(purge_mode, thread_pool, selected_modules);

		ct_reg.setup_internals_mem();
		ct_reg.setup_internals_anyinit();
		ct_reg.setup_stdcells_mem();

		ct_all.setup(design);

		RmStats stats;
		for (auto module : selected_modules)
			rmunused_module(module, thread_pool, purge_mode, true, true, stats, keep_cache);
		stats.log();

		design->optimize();
		design->check();

		ct_reg.clear();
		ct_all.clear();
		log_pop();

		request_garbage_collection();
	}
} OptCleanPass;

struct CleanPass : public Pass {
	CleanPass() : Pass("clean", "remove unused cells and wires") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    clean [options] [selection]\n");
		log("\n");
		log("This is identical to 'opt_clean', but less verbose.\n");
		log("\n");
		log("When commands are separated using the ';;' token, this command will be executed\n");
		log("between the commands.\n");
		log("\n");
		log("When commands are separated using the ';;;' token, this command will be executed\n");
		log("in -purge mode between the commands.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool purge_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge") {
				purge_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::vector<RTLIL::Module*> selected_modules;
		for (auto module : design->selected_unboxed_whole_modules())
			if (!module->has_processes())
				selected_modules.push_back(module);
		int thread_pool_size = 0;
		for (RTLIL::Module *m : selected_modules)
			thread_pool_size = std::max(thread_pool_size, ThreadPool::work_pool_size(0, m->cells_size(), 1000));
		ParallelDispatchThreadPool thread_pool(thread_pool_size);
		keep_cache_t keep_cache(purge_mode, thread_pool, selected_modules);

		ct_reg.setup_internals_mem();
		ct_reg.setup_internals_anyinit();
		ct_reg.setup_stdcells_mem();

		ct_all.setup(design);

		RmStats stats;
		for (auto module : selected_modules)
			rmunused_module(module, thread_pool, purge_mode, ys_debug(), true, stats, keep_cache);

		log_suppressed();
		stats.log();

		design->optimize();
		design->check();

		ct_reg.clear();
		ct_all.clear();

		request_garbage_collection();
	}
} CleanPass;

PRIVATE_NAMESPACE_END
