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

// opt_clean for designs that are in signorm mode.
//
// The denormalized pass has to build its own view of the netlist first: a
// SigMap over the module connections, a hashtable mapping every output bit to
// its driver cells, and sharded pools recording which bits are connected or
// used. In signorm mode the module already carries all of that, maintained
// incrementally by Cell::setPort/unsetPort:
//
//   * every wire has at most one driver, `wire->driverCell_`, and that port
//     holds exactly SigSpec(wire) -- so a driver lookup is a dereference;
//   * every cell port sigspec is sigmap-canonical, so no assign_map is needed
//     to compare or traverse;
//   * `fanout[bit]` is the exact set of input port bits equal to it, so "is
//     this wire read by anything" is a lookup rather than a scan;
//   * multi-driver nets are $connect cells and module inputs are $input_port
//     cells, both of which are structure here rather than temporaries.
//
// So this is a plain tracing GC: mark from the roots through driver edges,
// sweep the cells and wires that were not reached. What it deliberately does
// *not* do is the denormalized pass's re-canonicalization: there,
// compare_signals picks the nicest bit of each net as the representative and
// every cell port is rewritten to it. Under the index the representative is
// forced to be the driver's wire, and re-pointing readers at some other wire
// would leave the driving port non-canonical. Alias wires are simply left
// alone, which is fine to traverse -- that is what the sigmap is for.

#include "kernel/ffinit.h"
#include "kernel/yosys_common.h"
#include "passes/opt/opt_clean/opt_clean.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool is_signed_pos(RTLIL::Cell *cell) {
	return cell->type == TW($pos) && cell->getParam(ID::A_SIGNED).as_bool();
}

// $buf/$pos/$_BUF_ are identity cells with no reason to exist. Dropping one
// merges its output net into its input net, which the index handles as an
// ordinary connection. The cell has to go first: while it still drives Y both
// sides are driven, and connecting two driven nets produces a $connect cell
// instead of a merge.
bool remove_buffer_cells(RTLIL::Module *module, bool verbose)
{
	std::vector<RTLIL::Cell *> buffers;
	for (int i = 0; i < module->cells_size(); i++) {
		RTLIL::Cell *cell = module->cell_at(i);
		if (cell->type.in(TW($pos), TW($_BUF_), TW($buf)) && !cell->has_keep_attr())
			buffers.push_back(cell);
	}

	bool did_something = false;
	for (RTLIL::Cell *cell : buffers) {
		RTLIL::SigSpec a = cell->getPort(TW::A);
		RTLIL::SigSpec y = cell->getPort(TW::Y);
		a.extend_u0(GetSize(y), is_signed_pos(cell));

		if (a.has_const(State::Sz)) {
			RTLIL::SigSpec new_a, new_y;
			bool bail = false;
			for (int i = 0; i < GetSize(a); ++i) {
				if (a[i] == State::Sz) {
					bail = true;
					break;
				}
				new_a.append(a[i]);
				new_y.append(y[i]);
			}
			if (bail)
				continue;
			a = std::move(new_a);
			y = std::move(new_y);
		}

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

// $connect cells record that two already-driven nets are the same net. They
// are the one place where liveness flows backwards through a cell input, so
// they need an index from bit to cell. There are normally none at all, so this
// stays empty and the traversal skips the lookup entirely.
dict<RTLIL::SigBit, std::vector<RTLIL::Cell *>> index_connect_cells(RTLIL::Module *module)
{
	dict<RTLIL::SigBit, std::vector<RTLIL::Cell *>> result;
	for (int i = 0; i < module->cells_size(); i++) {
		RTLIL::Cell *cell = module->cell_at(i);
		if (cell->type != TW($connect))
			continue;
		for (auto &[port, sig] : cell->connections())
			for (auto bit : sig)
				if (bit.is_wire())
					result[bit].push_back(cell);
	}
	return result;
}

void trace_live(RTLIL::Module *module, LiveSet &live, pool<std::string> &live_mems,
		const SigMap &sigmap, CleanRunContext &clean_ctx)
{
	dict<RTLIL::SigBit, std::vector<RTLIL::Cell *>> connect_cells = index_connect_cells(module);
	dict<std::string, std::vector<RTLIL::Cell *>> mem_writers;

	// Everything that reaches a net reaches it the same way: through the one
	// cell driving it, and through any $connect tying it to another net that
	// may hold the driver instead.
	auto mark_bit = [&](RTLIL::SigBit bit) {
		if (!bit.is_wire())
			return;
		live.mark(bit.wire->driverCell_);
		if (connect_cells.empty())
			return;
		auto found = connect_cells.find(bit);
		if (found != connect_cells.end())
			for (RTLIL::Cell *connect : found->second)
				live.mark(connect);
	};

	for (int i = 0; i < module->cells_size(); i++) {
		RTLIL::Cell *cell = module->cell_at(i);
		if (cell->type.in(TW($memwr), TW($memwr_v2), TW($meminit), TW($meminit_v2)))
			mem_writers[cell->getParam(ID::MEMID).decode_string()].push_back(cell);
		// An $input_port cell is what makes a module input a driven net, so
		// it lives exactly as long as its wire does.
		if (cell->type == TW($input_port) || clean_ctx.keep_cache.query(cell))
			live.mark(cell);
	}

	for (int i = 0; i < module->wires_size(); i++) {
		RTLIL::Wire *wire = module->wire_at(i);
		if (!wire->port_output && !wire->get_bool_attribute(ID::keep))
			continue;
		for (auto bit : sigmap(RTLIL::SigSpec(wire)))
			mark_bit(bit);
	}

	while (!live.worklist.empty()) {
		RTLIL::Cell *cell = live.worklist.back();
		live.worklist.pop_back();

		for (auto &[port, sig] : cell->connections_) {
			if (clean_ctx.ct_all.cell_known(cell->type_impl) &&
					!clean_ctx.ct_all.cell_input(cell->type_impl, port))
				continue;
			// Ports hold canonical bits, so the driver is one hop away.
			for (auto bit : sig)
				mark_bit(bit);
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

bool sweep_cells(RTLIL::Module *module, const LiveSet &live, FfInitVals &ffinit,
		CleanRunContext &clean_ctx)
{
	pool<RTLIL::Cell *> dead;
	for (int i = 0; i < module->cells_size(); i++) {
		RTLIL::Cell *cell = module->cell_at(i);
		if (!live.cells.count(cell))
			dead.insert(cell);
	}
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

// A wire is referenced iff a cell port names it: as an output (it has a
// driver) or as an input (it has fanout entries). Aliases are named by
// nothing -- readers hold the canonical bits -- which is what makes them
// collectable.
pool<RTLIL::Wire *> referenced_wires(RTLIL::Module *module)
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

// A bit is used if some cell input port reads it or it leaves the module. The
// fanout index answers the first directly; only the module's own output ports
// have to be collected.
pool<RTLIL::SigBit> used_bits(RTLIL::Module *module, const SigMap &sigmap)
{
	pool<RTLIL::SigBit> used;
	for (auto &[bit, portbits] : module->signorm_fanout())
		if (!portbits.empty())
			used.insert(bit);
	for (int i = 0; i < module->wires_size(); i++) {
		RTLIL::Wire *wire = module->wire_at(i);
		if (wire->port_id > 0 && !wire->port_input)
			for (auto bit : sigmap(RTLIL::SigSpec(wire)))
				used.insert(bit);
	}
	return used;
}

void update_unused_bits(RTLIL::Module *module, const SigMap &sigmap)
{
	pool<RTLIL::SigBit> used = used_bits(module, sigmap);

	for (int i = 0; i < module->wires_size(); i++) {
		RTLIL::Wire *wire = module->wire_at(i);

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
			wire->attributes.erase(ID::unused_bits);
		} else {
			RTLIL::Const value(std::move(unused));
			auto it = wire->attributes.find(ID::unused_bits);
			if (it == wire->attributes.end() || it->second != value)
				wire->attributes[ID::unused_bits] = std::move(value);
		}
	}
}

// An init value on an alias only means anything through the net it aliases,
// and that alias may be about to be collected, so move init onto the
// representative wires first. This also narrows an init to the bits that
// actually survived: a 2-bit register with one bit left keeps a 1-bit init
// rather than the original 2-bit one.
void normalize_inits(RTLIL::Module *module, const SigMap &sigmap)
{
	dict<RTLIL::SigBit, RTLIL::State> values;
	pool<RTLIL::Wire *> representatives;

	for (int i = 0; i < module->wires_size(); i++) {
		RTLIL::Wire *wire = module->wire_at(i);
		auto it = wire->attributes.find(ID::init);
		if (it == wire->attributes.end())
			continue;

		RTLIL::Const val = it->second;
		RTLIL::SigSpec sig = sigmap(RTLIL::SigSpec(wire));
		for (int j = 0; j < GetSize(val) && j < GetSize(sig); j++)
			if (val[j] != State::Sx && sig[j].is_wire()) {
				values[sig[j]] = val[j];
				representatives.insert(sig[j].wire);
			}
		wire->attributes.erase(it);
	}

	for (RTLIL::Wire *wire : representatives) {
		bool found = false;
		RTLIL::Const val(State::Sx, wire->width);
		for (int j = 0; j < wire->width; j++) {
			auto it = values.find(RTLIL::SigBit(wire, j));
			if (it != values.end()) {
				val.set(j, it->second);
				found = true;
			}
		}
		if (found)
			wire->attributes[ID::init] = val;
	}
}

bool wire_is_pinned(RTLIL::Wire *wire)
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

int sweep_wires(RTLIL::Module *module, CleanRunContext &clean_ctx)
{
	const SigMap *sigmap = module->signorm_sigmap();
	log_assert(sigmap != nullptr);
	pool<RTLIL::Wire *> referenced = referenced_wires(module);

	auto is_live = [&](RTLIL::Wire *wire) {
		return wire_is_pinned(wire) || referenced.count(wire) != 0;
	};

	pool<RTLIL::Wire *> dead;

	for (int i = 0; i < module->wires_size(); i++) {
		RTLIL::Wire *wire = module->wire_at(i);
		if (is_live(wire))
			continue;

		if (GetSize(wire) != 0 && !clean_ctx.flags.purge &&
				check_public_name(wire->name.escaped())) {
			// A public name aliasing a live net is the only record of that
			// name, so keep it and leave the alias in the sigmap. Aliasing a
			// net that is itself dead saves nothing -- the whole net goes,
			// which is also what the denormalized pass does once it has
			// collected the driver.
			bool aliases_live_net = false;
			for (int j = 0; j < GetSize(wire); j++) {
				RTLIL::SigBit bit(wire, j), rep = (*sigmap)(bit);
				if (rep == bit)
					continue;
				// A constant representative still gives the name a value.
				if (!rep.is_wire() || is_live(rep.wire)) {
					aliases_live_net = true;
					break;
				}
			}
			if (aliases_live_net)
				continue;
		}

		dead.insert(wire);
	}

	// Whatever survives keeps its representative reachable through the sigmap,
	// so the representative has to survive too -- otherwise the map is left
	// pointing at freed memory. This catches the wires kept for reasons other
	// than aliasing something live: a port, `keep`, or an init value sitting
	// on an alias of a net whose driver was just collected. Representatives
	// are canonical, so rescuing one cannot strand a further wire.
	for (auto const &bit : sigmap->database) {
		if (!bit.is_wire() || dead.count(bit.wire))
			continue;
		RTLIL::SigBit rep = (*sigmap)(bit);
		if (rep.is_wire())
			dead.erase(rep.wire);
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
	if (remove_buffer_cells(module, clean_ctx.flags.verbose))
		module->design->scratchpad_set_bool("opt.did_something", true);

	SigMap sigmap(module);
	FfInitVals ffinit;
	ffinit.set_parallel(&sigmap, subpool.thread_pool(), module);

	LiveSet live;
	pool<std::string> live_mems;
	trace_live(module, live, live_mems, sigmap, clean_ctx);

	sweep_cells(module, live, ffinit, clean_ctx);
	sweep_mems(module, live_mems, clean_ctx.flags.verbose);

	normalize_inits(module, sigmap);
	sweep_wires(module, clean_ctx);

	// Reads and erases wire attributes and works off its own copy of the
	// sigmap, so it needs no adaptation to run under the index. Dropping a
	// redundant init unpins its wire, so sweep once more when it fires.
	if (rmunused_module_init(module, subpool, clean_ctx.flags.verbose))
		sweep_wires(module, clean_ctx);

	// Sweeping is what makes bits unused, so the annotation comes last, over
	// a sigmap refreshed past the compaction in sweep_wires.
	SigMap swept(module);
	update_unused_bits(module, swept);
}

YOSYS_NAMESPACE_END
