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

bool is_signed_pos(RTLIL::Cell *cell) {
	return cell->type == TW($pos) && cell->getParam(ID::A_SIGNED).as_bool();
}

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

	for (int i = 0; i < module->cells_size(); i++) {
		RTLIL::Cell *cell = module->cell_at(i);
		if (cell->type.in(TW($memwr), TW($memwr_v2), TW($meminit), TW($meminit_v2)))
			mem_writers[cell->getParam(ID::MEMID).decode_string()].push_back(cell);
		if (cell->type == TW($input_port) || clean_ctx.keep_cache.query(cell))
			live.mark(cell);
	}

	for (int i = 0; i < module->wires_size(); i++) {
		RTLIL::Wire *wire = module->wire_at(i);
		if (!wire->port_output && !wire->get_bool_attribute(ID::keep))
			continue;
		for (auto bit : sigmap(RTLIL::SigSpec(wire)))
			if (bit.is_wire())
				live.mark(bit.wire->driverCell_);
	}

	while (!live.worklist.empty()) {
		RTLIL::Cell *cell = live.worklist.back();
		live.worklist.pop_back();

		for (auto &[port, sig] : cell->connections_) {
			if (clean_ctx.ct_all.cell_known(cell->type_impl) &&
					!clean_ctx.ct_all.cell_input(cell->type_impl, port))
				continue;
			for (auto bit : sig) {
				if (!bit.is_wire())
					continue;
				live.mark(bit.wire->driverCell_);
				if (!connect_cells.empty()) {
					auto found = connect_cells.find(bit);
					if (found != connect_cells.end())
						for (RTLIL::Cell *connect : found->second)
							live.mark(connect);
				}
			}
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

bool wire_is_live(RTLIL::Wire *wire, const pool<RTLIL::Wire *> &referenced)
{
	return wire_is_pinned(wire) || referenced.count(wire) != 0;
}

int sweep_wires(RTLIL::Module *module, CleanRunContext &clean_ctx)
{
	const SigMap *sigmap = module->signorm_sigmap();
	log_assert(sigmap != nullptr);
	pool<RTLIL::Wire *> referenced = referenced_wires(module);

	pool<RTLIL::Wire *> dead;

	for (int i = 0; i < module->wires_size(); i++) {
		RTLIL::Wire *wire = module->wire_at(i);
		if (wire_is_live(wire, referenced))
			continue;

		if (GetSize(wire) != 0 && !clean_ctx.flags.purge &&
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

		dead.insert(wire);
	}

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

	if (rmunused_module_init(module, subpool, clean_ctx.flags.verbose))
		sweep_wires(module, clean_ctx);

	SigMap swept(module);
	update_unused_bits(module, swept);
}

YOSYS_NAMESPACE_END
