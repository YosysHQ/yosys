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
#include "passes/opt/opt_clean/opt_clean.h"

YOSYS_NAMESPACE_BEGIN

unsigned int hash_bit(const SigBit &bit) {
	return static_cast<unsigned int>(hash_ops<SigBit>::hash(bit).yield());
}

void rmunused_module_cells(Module *module, ParallelDispatchThreadPool::Subpool &subpool, CleanRunContext &clean_ctx)
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
	subpool.run([&sigmap, &raw_sigmap, const_module, &mem2cells_vector, &driver_driver_logs, &keep_wires, &cell_queue, &wire2driver_builder, &clean_ctx, &unused](const ParallelDispatchThreadPool::RunCtx &ctx) {
		for (int i : ctx.item_range(const_module->cells_size())) {
			Cell *cell = const_module->cell_at(i);
			if (cell->type.in(ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2)))
				mem2cells_vector.insert(ctx, {cell->getParam(ID::MEMID).decode_string(), i});

			for (auto &it2 : cell->connections()) {
				if (clean_ctx.ct_all.cell_known(cell->type) && !clean_ctx.ct_all.cell_output(cell->type, it2.first))
					continue;
				for (auto raw_bit : it2.second) {
					if (raw_bit.wire == nullptr)
						continue;
					auto bit = sigmap(raw_bit);
					if (bit.wire == nullptr && clean_ctx.ct_all.cell_known(cell->type)) {
						std::string msg = stringf("Driver-driver conflict "
								"for %s between cell %s.%s and constant %s in %s: Resolved using constant.",
								log_signal(raw_bit), cell->name.unescape(), it2.first.unescape(), log_signal(bit), const_module->name.unescape());
						driver_driver_logs.insert(ctx, {raw_sigmap(raw_bit), msg});
					}
					if (bit.wire != nullptr)
						wire2driver_builder.insert(ctx, {{bit, i}, hash_bit(bit)});
				}
			}
			bool keep = clean_ctx.keep_cache.query(cell);
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
	subpool.run([const_module, &sigmap, &wire2driver, &mem2cells, &unused, &cell_queue, &mem_indices, &mem_unused, &clean_ctx](const ParallelDispatchThreadPool::RunCtx &ctx) {
		pool<SigBit> bits;
		pool<std::string> mems;
		while (true) {
			std::vector<int> cell_indices = cell_queue.pop_batch(ctx);
			if (cell_indices.empty())
				return;
			for (auto cell_index : cell_indices) {
				Cell *cell = const_module->cell_at(cell_index);
				for (auto &it : cell->connections())
					if (!clean_ctx.ct_all.cell_known(cell->type) || clean_ctx.ct_all.cell_input(cell->type, it.first))
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
		if (clean_ctx.flags.verbose)
			log_debug("  removing unused `%s' cell `%s'.\n", cell->type, cell->name);
		module->design->scratchpad_set_bool("opt.did_something", true);
		if (cell->is_builtin_ff())
			ffinit.remove_init(cell->getPort(ID::Q));
		module->remove(cell);
		clean_ctx.stats.count_rm_cells++;
	}

	for (const auto &it : mem_indices) {
		if (!mem_unused[it.second].load(std::memory_order_relaxed))
			continue;
		RTLIL::IdString id(it.first);
		if (clean_ctx.flags.verbose)
			log_debug("  removing unused memory `%s'.\n", id.unescape());
		delete module->memories.at(id);
		module->memories.erase(id);
	}

	if (!driver_driver_logs.empty()) {
		// We could do this in parallel but hopefully this is rare.
		for (auto [_, cell] : module->cells_) {
			for (auto &[port, sig] : cell->connections()) {
				if (clean_ctx.ct_all.cell_known(cell->type) && !clean_ctx.ct_all.cell_input(cell->type, port))
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

YOSYS_NAMESPACE_END
