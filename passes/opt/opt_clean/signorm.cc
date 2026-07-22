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

// Everything here follows the same shape: the scans that touch every cell,
// every wire, every wire bit or every sigmap entry run on all worker threads
// and write their findings into a `ShardedVector`, and the mutations of the
// module that follow are replayed from those vectors on one thread. Because
// `ctx.item_range()` hands each thread a contiguous block of indices, a
// `ShardedVector` reads back in exactly the order a plain sequential loop
// would have produced, so the replay is order-for-order what the single
// threaded code did.
using Subpool = ParallelDispatchThreadPool::Subpool;
using RunCtx = ParallelDispatchThreadPool::RunCtx;

bool is_signed_pos(RTLIL::Cell *cell) {
	return cell->type == TW($pos) && cell->getParam(ID::A_SIGNED).as_bool();
}

bool remove_buffer_cells(RTLIL::Module *module, Subpool &subpool, bool verbose)
{
	const RTLIL::Module *scan = module;
	ShardedVector<RTLIL::Cell *> buffers(subpool);
	subpool.run([scan, &buffers](const RunCtx &ctx) {
		for (int i : ctx.item_range(scan->cells_size())) {
			RTLIL::Cell *cell = scan->cell_at(i);
			if (cell->type.in(TW($pos), TW($_BUF_), TW($buf)) && !cell->has_keep_attr())
				buffers.insert(ctx, cell);
		}
	});

	bool did_something = false;
	for (RTLIL::Cell *cell : buffers) {
		RTLIL::SigSpec a = cell->getPort(TW::A);
		RTLIL::SigSpec y = cell->getPort(TW::Y);
		a.extend_u0(GetSize(y), is_signed_pos(cell));

		if (a.has_const(State::Sz))
			continue;

		if (verbose)
			log_debug("  removing buffer cell `%s': %s = %s\n", cell->name,
					log_signal(y), log_signal(a));

		module->remove(cell);
		if (!y.empty())
			module->connect_incremental(y, a);
		did_something = true;
	}
	return did_something;
}

struct LiveSet {
	pool<RTLIL::Cell *> cells;
	std::vector<RTLIL::Cell *> worklist;

	void mark(RTLIL::Cell *cell) {
		if (cell != nullptr && cells.insert(cell).second)
			worklist.push_back(cell);
	}
};

// What a single parallel walk over the cells collects for `trace_live()`.
struct CellScan {
	// The $connect cells, which are edges of the liveness graph rather than
	// logic, in module order.
	ShardedVector<RTLIL::Cell *> connects;
	// (memory id, writer) for every $memwr/$meminit.
	ShardedVector<std::pair<std::string, RTLIL::Cell *>> mem_writers;
	// Cells that are live no matter what reads them.
	ShardedVector<RTLIL::Cell *> roots;

	CellScan(Subpool &subpool) : connects(subpool), mem_writers(subpool), roots(subpool) {}
};

void mark_bit(RTLIL::SigBit bit, LiveSet &live,
		const dict<RTLIL::SigBit, std::vector<RTLIL::Cell *>> &connect_cells)
{
	if (!bit.is_wire())
		return;
	live.mark(bit.wire->driverCell_);
	if (connect_cells.empty())
		return;
	auto found = connect_cells.find(bit);
	if (found != connect_cells.end())
		for (RTLIL::Cell *connect : found->second)
			live.mark(connect);
}

void trace_live(RTLIL::Module *module, Subpool &subpool, LiveSet &live, pool<std::string> &live_mems,
		const SigMap &sigmap, CleanRunContext &clean_ctx)
{
	const RTLIL::Module *scan = module;

	CellScan cell_scan(subpool);
	ShardedVector<RTLIL::SigBit> root_bits(subpool);
	subpool.run([scan, &cell_scan, &root_bits, &sigmap, &clean_ctx](const RunCtx &ctx) {
		for (int i : ctx.item_range(scan->cells_size())) {
			RTLIL::Cell *cell = scan->cell_at(i);
			if (cell->type == TW($connect))
				cell_scan.connects.insert(ctx, cell);
			if (cell->type.in(TW($memwr), TW($memwr_v2), TW($meminit), TW($meminit_v2)))
				cell_scan.mem_writers.insert(ctx, {cell->getParam(ID::MEMID).decode_string(), cell});
			if (cell->type == TW($input_port) || clean_ctx.keep_cache.query(cell))
				cell_scan.roots.insert(ctx, cell);
		}
		for (int i : ctx.item_range(scan->wires_size())) {
			RTLIL::Wire *wire = scan->wire_at(i);
			if (!wire->port_output && !wire->get_bool_attribute(ID::keep))
				continue;
			for (auto bit : sigmap(RTLIL::SigSpec(wire)))
				root_bits.insert(ctx, bit);
		}
	});

	// A bit that a $connect touches keeps that $connect alive, and through it
	// whatever sits on the other side.
	dict<RTLIL::SigBit, std::vector<RTLIL::Cell *>> connect_cells;
	for (RTLIL::Cell *cell : cell_scan.connects)
		for (auto &[port, sig] : cell->connections())
			for (auto bit : sig)
				if (bit.is_wire())
					connect_cells[bit].push_back(cell);

	dict<std::string, std::vector<RTLIL::Cell *>> mem_writers;
	for (auto &[memid, cell] : cell_scan.mem_writers)
		mem_writers[memid].push_back(cell);

	for (RTLIL::Cell *cell : cell_scan.roots)
		live.mark(cell);
	for (RTLIL::SigBit bit : root_bits)
		mark_bit(bit, live, connect_cells);

	while (!live.worklist.empty()) {
		RTLIL::Cell *cell = live.worklist.back();
		live.worklist.pop_back();

		for (auto &[port, sig] : cell->connections_) {
			if (clean_ctx.ct_all.cell_known(cell->type_impl) &&
					!clean_ctx.ct_all.cell_input(cell->type_impl, port))
				continue;
			for (auto bit : sig)
				mark_bit(bit, live, connect_cells);
		}

		if (cell->type.in(TW($memrd), TW($memrd_v2))) {
			std::string memid = cell->getParam(ID::MEMID).decode_string();
			if (live_mems.insert(memid).second) {
				auto found = mem_writers.find(memid);
				if (found != mem_writers.end())
					for (RTLIL::Cell *writer : found->second)
						live.mark(writer);
			}
		}
	}
}

bool sweep_cells(RTLIL::Module *module, Subpool &subpool, const LiveSet &live, FfInitVals &ffinit,
		CleanRunContext &clean_ctx)
{
	const RTLIL::Module *scan = module;
	ShardedVector<RTLIL::Cell *> dead_cells(subpool);
	subpool.run([scan, &live, &dead_cells](const RunCtx &ctx) {
		for (int i : ctx.item_range(scan->cells_size())) {
			RTLIL::Cell *cell = scan->cell_at(i);
			if (!live.cells.count(cell))
				dead_cells.insert(ctx, cell);
		}
	});

	pool<RTLIL::Cell *> dead(dead_cells.begin(), dead_cells.end());
	if (dead.empty())
		return false;

	dead.sort(RTLIL::sort_by_name<RTLIL::Cell>());
	for (RTLIL::Cell *cell : dead) {
		if (clean_ctx.flags.verbose)
			log_debug("  removing unused `%s' cell `%s'.\n", cell->type, cell->name);
		if (cell->is_builtin_ff())
			ffinit.remove_init(cell->getPort(TW::Q));
		module->remove(cell);
		clean_ctx.stats.count_rm_cells++;
	}
	module->design->scratchpad_set_bool("opt.did_something", true);
	return true;
}

void sweep_mems(RTLIL::Module *module, const pool<std::string> &live_mems, bool verbose)
{
	std::vector<TwineRef> dead;
	for (auto &it : module->memories)
		if (!live_mems.count(module->design->twines.str(it.first)))
			dead.push_back(it.first);

	for (TwineRef id : dead) {
		if (verbose)
			log_debug("  removing unused memory `%s'.\n", module->design->twines.str(id).c_str());
		delete module->memories.at(id);
		module->memories.erase(id);
	}
}

// Wires that something reads or something drives. Filled on one thread and
// then only read: a `ShardedHashtable` would build in parallel but is
// node-based, and for a set of pointers the flat table wins back more on the
// queries than the parallel build saves. `count()` is const the whole way
// down, so every worker can query this at once.
pool<RTLIL::Wire *> referenced_wires(const RTLIL::Module *module)
{
	pool<RTLIL::Wire *> referenced;
	for (auto &[bit, portbits] : module->signorm_fanout())
		if (bit.is_wire() && !portbits.empty())
			referenced.insert(bit.wire);
	for (int i = 0; i < module->wires_size(); i++) {
		RTLIL::Wire *wire = module->wire_at(i);
		if (wire->driverCell_ != nullptr)
			referenced.insert(wire);
	}
	return referenced;
}

// "Something reads this bit". The fanout index is already a hash table over
// exactly that question, so this asks it directly instead of copying it into a
// `pool` of its own first; only the output port bits, which the index does not
// count as readers, need a set. Const lookups in both, so the query is safe to
// run on every worker.
struct UsedBits {
	const dict<RTLIL::SigBit, pool<RTLIL::PortBit>> &fanout;
	pool<RTLIL::SigBit> output_port_bits;

	UsedBits(const RTLIL::Module *module, const SigMap &sigmap) : fanout(module->signorm_fanout())
	{
		for (int i = 0; i < module->wires_size(); i++) {
			RTLIL::Wire *wire = module->wire_at(i);
			if (wire->port_id > 0 && !wire->port_input)
				for (auto bit : sigmap(RTLIL::SigSpec(wire)))
					output_port_bits.insert(bit);
		}
	}

	bool count(const RTLIL::SigBit &bit) const
	{
		auto found = fanout.find(bit);
		if (found != fanout.end() && !found->second.empty())
			return true;
		return output_port_bits.count(bit) != 0;
	}
};

void update_unused_bits(RTLIL::Module *module, Subpool &subpool, const SigMap &sigmap)
{
	const RTLIL::Module *scan = module;
	const UsedBits used(scan, sigmap);

	// Each thread only ever looks at the wires in its own index range, so the
	// attribute reads below are unshared; the writes are still deferred, since
	// mutating two neighbouring wires at once is not.
	ShardedVector<RTLIL::Wire *> clear_attr(subpool);
	ShardedVector<std::pair<RTLIL::Wire *, RTLIL::Const>> set_attr(subpool);
	subpool.run([scan, &sigmap, &used, &clear_attr, &set_attr](const RunCtx &ctx) {
		for (int i : ctx.item_range(scan->wires_size())) {
			RTLIL::Wire *wire = scan->wire_at(i);

			std::string unused;
			if (wire->port_id == 0)
				for (int j = 0; j < GetSize(wire); j++) {
					RTLIL::SigBit bit = sigmap(RTLIL::SigBit(wire, j));
					if (!bit.is_wire() || used.count(bit))
						continue;
					if (!unused.empty())
						unused += " ";
					unused += stringf("%d", j);
				}

			if (unused.empty()) {
				if (wire->attributes.count(ID::unused_bits))
					clear_attr.insert(ctx, wire);
			} else {
				RTLIL::Const value(std::move(unused));
				auto it = wire->attributes.find(ID::unused_bits);
				if (it == wire->attributes.end() || it->second != value)
					set_attr.insert(ctx, {wire, std::move(value)});
			}
		}
	});

	for (RTLIL::Wire *wire : clear_attr)
		wire->attributes.erase(ID::unused_bits);
	for (auto &[wire, value] : set_attr)
		wire->attributes[ID::unused_bits] = std::move(value);
}

void normalize_inits(RTLIL::Module *module, Subpool &subpool, const SigMap &sigmap)
{
	const RTLIL::Module *scan = module;

	ShardedVector<RTLIL::Wire *> init_wires(subpool);
	ShardedVector<std::pair<RTLIL::SigBit, RTLIL::State>> init_bits(subpool);
	subpool.run([scan, &sigmap, &init_wires, &init_bits](const RunCtx &ctx) {
		for (int i : ctx.item_range(scan->wires_size())) {
			RTLIL::Wire *wire = scan->wire_at(i);
			auto it = wire->attributes.find(ID::init);
			if (it == wire->attributes.end())
				continue;

			const RTLIL::Const &val = it->second;
			RTLIL::SigSpec sig = sigmap(RTLIL::SigSpec(wire));
			for (int j = 0; j < GetSize(val) && j < GetSize(sig); j++)
				if (val[j] != State::Sx && sig[j].is_wire())
					init_bits.insert(ctx, {sig[j], val[j]});
			init_wires.insert(ctx, wire);
		}
	});

	dict<RTLIL::SigBit, RTLIL::State> values;
	std::vector<RTLIL::Wire *> representatives;
	{
		pool<RTLIL::Wire *> seen;
		for (auto &[bit, state] : init_bits) {
			values[bit] = state;
			if (seen.insert(bit.wire).second)
				representatives.push_back(bit.wire);
		}
	}
	for (RTLIL::Wire *wire : init_wires)
		wire->attributes.erase(ID::init);

	// Re-hang the surviving init bits off the representatives, x-filling the
	// bits of the group nobody had an init for.
	const dict<RTLIL::SigBit, RTLIL::State> &lookup = values;
	ShardedVector<std::pair<RTLIL::Wire *, RTLIL::Const>> set_init(subpool);
	subpool.run([&representatives, &lookup, &set_init](const RunCtx &ctx) {
		for (int i : ctx.item_range(GetSize(representatives))) {
			RTLIL::Wire *wire = representatives[i];
			bool found = false;
			RTLIL::Const val(State::Sx, wire->width);
			for (int j = 0; j < wire->width; j++) {
				auto it = lookup.find(RTLIL::SigBit(wire, j));
				if (it != lookup.end()) {
					val.set(j, it->second);
					found = true;
				}
			}
			if (found)
				set_init.insert(ctx, {wire, std::move(val)});
		}
	});
	for (auto &[wire, val] : set_init)
		wire->attributes[ID::init] = std::move(val);
}

// Taken by const pointer on purpose: the wire sweep asks this about the
// representative of an aliased bit, which can belong to another thread's slice
// of the wires. Only the const attribute lookups are safe to share, since the
// mutable ones rehash.
bool wire_is_pinned(const RTLIL::Wire *wire)
{
	if (wire->port_id != 0)
		return true;
	if (wire->get_bool_attribute(ID::keep))
		return true;
	auto init = wire->attributes.find(ID::init);
	if (init != wire->attributes.end() && !init->second.is_fully_undef())
		return true;
	return false;
}

bool wire_is_live(RTLIL::Wire *wire, const pool<RTLIL::Wire *> &referenced)
{
	return wire_is_pinned(wire) || referenced.count(wire) != 0;
}

int sweep_wires(RTLIL::Module *module, Subpool &subpool, CleanRunContext &clean_ctx)
{
	const SigMap *sigmap = module->signorm_sigmap();
	log_assert(sigmap != nullptr);
	const RTLIL::Module *scan = module;
	const pool<RTLIL::Wire *> referenced = referenced_wires(scan);

	bool purge = clean_ctx.flags.purge;
	ShardedVector<RTLIL::Wire *> dead_wires(subpool);
	subpool.run([scan, sigmap, purge, &referenced, &dead_wires](const RunCtx &ctx) {
		for (int i : ctx.item_range(scan->wires_size())) {
			RTLIL::Wire *wire = scan->wire_at(i);
			if (wire_is_live(wire, referenced))
				continue;

			if (GetSize(wire) != 0 && !purge &&
					check_public_name(wire->name.escaped())) {
				bool aliases_live_net = false;
				for (int j = 0; j < GetSize(wire); j++) {
					RTLIL::SigBit bit(wire, j), rep = (*sigmap)(bit);
					if (rep == bit)
						continue;
					if (!rep.is_wire() || wire_is_live(rep.wire, referenced)) {
						aliases_live_net = true;
						break;
					}
				}
				if (aliases_live_net)
					continue;
			}

			dead_wires.insert(ctx, wire);
		}
	});

	pool<RTLIL::Wire *> dead(dead_wires.begin(), dead_wires.end());
	// Nothing left for the sigmap walk below to rescue.
	if (dead.empty())
		return 0;

	// A wire that represents a bit of a wire we are keeping has to stay. Only
	// an entry whose representative is a removal candidate can change that
	// verdict, so the parallel pass drops the rest and the sequential replay
	// stays as short as the number of candidates.
	const pool<RTLIL::Wire *> &candidates = dead;
	ShardedVector<std::pair<RTLIL::Wire *, RTLIL::Wire *>> rescues(subpool);
	subpool.run([sigmap, &candidates, &rescues](const RunCtx &ctx) {
		for (int i : ctx.item_range(GetSize(sigmap->database))) {
			const RTLIL::SigBit &bit = sigmap->database[i];
			if (!bit.is_wire())
				continue;
			RTLIL::SigBit rep = (*sigmap)(bit);
			if (!rep.is_wire() || !candidates.count(rep.wire))
				continue;
			rescues.insert(ctx, {bit.wire, rep.wire});
		}
	});
	for (auto &[wire, rep] : rescues) {
		if (dead.count(wire))
			continue;
		dead.erase(rep);
	}

	if (dead.empty())
		return 0;

	int unreported = 0;
	for (RTLIL::Wire *wire : dead) {
		if (ys_debug() || (check_public_name(wire->name.escaped()) && clean_ctx.flags.verbose))
			log_debug("  removing unused non-port wire %s.\n", wire->name);
		else
			unreported++;
	}

	module->signorm_compact(dead);
	module->remove(dead);

	clean_ctx.stats.count_rm_wires += GetSize(dead);
	if (clean_ctx.flags.verbose && unreported)
		log_debug("  removed %d unused temporary wires.\n", unreported);
	return GetSize(dead);
}

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN

void rmunused_module_signorm(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool,
		CleanRunContext &clean_ctx)
{
	if (remove_buffer_cells(module, subpool, clean_ctx.flags.verbose))
		module->design->scratchpad_set_bool("opt.did_something", true);

	const SigMap *sigmap = module->signorm_sigmap();
	log_assert(sigmap != nullptr);
	FfInitVals ffinit;
	ffinit.set_parallel(sigmap, subpool.thread_pool(), module);

	LiveSet live;
	pool<std::string> live_mems;
	trace_live(module, subpool, live, live_mems, *sigmap, clean_ctx);

	sweep_cells(module, subpool, live, ffinit, clean_ctx);
	sweep_mems(module, live_mems, clean_ctx.flags.verbose);

	normalize_inits(module, subpool, *sigmap);
	sweep_wires(module, subpool, clean_ctx);

	if (rmunused_module_init(module, subpool, clean_ctx.flags.verbose))
		sweep_wires(module, subpool, clean_ctx);

	// sweep_wires() compacted signorm, invalidating the sigmap
	const SigMap *swept = module->signorm_sigmap();
	log_assert(swept != nullptr);
	update_unused_bits(module, subpool, *swept);
}

YOSYS_NAMESPACE_END
