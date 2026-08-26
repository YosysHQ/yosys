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
#include "passes/opt/clean/opt_clean.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using Subpool = ParallelDispatchThreadPool::Subpool;
using RunCtx = ParallelDispatchThreadPool::RunCtx;

bool is_signed_pos(RTLIL::Cell *cell) {
	return cell->type == ID($pos) && cell->getParam(ID::A_SIGNED).as_bool();
}

bool remove_buffer_cells(RTLIL::Module *module, Subpool &subpool, bool verbose)
{
	const RTLIL::Module *scan = module;
	ShardedVector<RTLIL::Cell *> buffers(subpool);
	subpool.run([scan, &buffers](const RunCtx &ctx) {
		for (int i : ctx.item_range(scan->cells_size())) {
			RTLIL::Cell *cell = scan->cell_at(i);
			if (cell->type.in(ID($pos), ID($_BUF_), ID($buf)) && !cell->has_keep_attr())
				buffers.insert(ctx, cell);
		}
	});

	bool did_something = false;
	for (RTLIL::Cell *cell : buffers) {
		RTLIL::SigSpec a = cell->getPort(ID::A);
		RTLIL::SigSpec y = cell->getPort(ID::Y);
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

struct CellScan {
	ShardedVector<RTLIL::Cell *> connects;
	ShardedVector<std::pair<std::string, RTLIL::Cell *>> mem_writers;
	ShardedVector<RTLIL::Cell *> roots;

	CellScan(Subpool &subpool) : connects(subpool), mem_writers(subpool), roots(subpool) {}
};

void mark_bit(RTLIL::SigBit bit, LiveSet &live,
		const dict<RTLIL::SigBit, std::vector<RTLIL::Cell *>> &connect_cells)
{
	if (!bit.is_wire())
		return;
	if (bit.wire->known_driver())
		live.mark(bit.wire->driverCell());
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
			if (cell->type == ID($connect))
				cell_scan.connects.insert(ctx, cell);
			if (cell->type.in(ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2)))
				cell_scan.mem_writers.insert(ctx, {cell->getParam(ID::MEMID).decode_string(), cell});
			if (cell->type == ID($input_port) || clean_ctx.keep_cache.query(cell))
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
			if (clean_ctx.ct_all.cell_known(cell->type) &&
					!clean_ctx.ct_all.cell_input(cell->type, port))
				continue;
			for (auto bit : sig)
				mark_bit(bit, live, connect_cells);
		}

		if (cell->type.in(ID($memrd), ID($memrd_v2))) {
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

	dead.sort(RTLIL::sort_by_name_id<RTLIL::Cell>());
	for (RTLIL::Cell *cell : dead) {
		if (clean_ctx.flags.verbose)
			log_debug("  removing unused `%s' cell `%s'.\n", cell->type, cell->name);
		if (cell->is_builtin_ff())
			ffinit.remove_init(cell->getPort(ID::Q));
		module->remove(cell);
		clean_ctx.stats.count_rm_cells++;
	}
	module->design->scratchpad_set_bool("opt.did_something", true);
	return true;
}

void sweep_mems(RTLIL::Module *module, const pool<std::string> &live_mems, bool verbose)
{
	std::vector<RTLIL::IdString> dead;
	for (auto &it : module->memories)
		if (!live_mems.count(it.first.str()))
			dead.push_back(it.first);

	for (RTLIL::IdString id : dead) {
		if (verbose)
			log_debug("  removing unused memory `%s'.\n", log_id(id));
		delete module->memories.at(id);
		module->memories.erase(id);
	}
}

pool<RTLIL::Wire *> referenced_wires(const RTLIL::Module *module)
{
	pool<RTLIL::Wire *> referenced;
	for (auto &[bit, portbits] : module->signorm_fanout())
		if (bit.is_wire() && !portbits.empty())
			referenced.insert(bit.wire);
	for (int i = 0; i < module->wires_size(); i++) {
		RTLIL::Wire *wire = module->wire_at(i);
		if (wire->known_driver())
			referenced.insert(wire);
	}
	return referenced;
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
					check_public_name(wire->name)) {
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
	if (dead.empty())
		return 0;

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
		if (ys_debug() || (check_public_name(wire->name) && clean_ctx.flags.verbose))
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
}

YOSYS_NAMESPACE_END
