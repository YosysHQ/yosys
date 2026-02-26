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

#include "passes/opt/opt_clean/opt_clean.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

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
	const ShardedSigSpecPool &direct_sigs;
	const SigMap &assign_map;
	dict<RTLIL::Wire *, bool> cache;

	DirectWires(const ShardedSigSpecPool &direct_sigs, const SigMap &assign_map) : direct_sigs(direct_sigs), assign_map(assign_map) {}
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
	void cache_all(ShardedVector<RTLIL::SigBit> &bits) {
		for (RTLIL::SigBit candidate : bits) {
			cache_result_for_bit(candidate);
			cache_result_for_bit(assign_map(candidate));
		}

	}
};

int count_nontrivial_wire_attrs(RTLIL::Wire *w)
{
	int count = w->attributes.size();
	count -= w->attributes.count(ID::src);
	count -= w->attributes.count(ID::hdlname);
	count -= w->attributes.count(ID::scopename);
	count -= w->attributes.count(ID::unused_bits);
	return count;
}

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

struct UpdateConnection {
	RTLIL::Cell *cell;
	RTLIL::IdString port;
	RTLIL::SigSpec spec;
};
void fixup_update_ports(ShardedVector<UpdateConnection> &update_connections)
{
	for (UpdateConnection &update : update_connections)
		update.cell->connections_.at(update.port) = std::move(update.spec);
}

struct InitBits {
	dict<SigBit, RTLIL::State> values;
	// Wires that appear in the keys of the `values` dict
	pool<Wire*> wires;

	// Set init attributes on all wires of a connected group
	void apply_normalised_inits() {
		for (RTLIL::Wire *wire : wires) {
			bool found = false;
			Const val(State::Sx, wire->width);
			for (int i = 0; i < wire->width; i++) {
				auto it = values.find(RTLIL::SigBit(wire, i));
				if (it != values.end()) {
					val.set(i, it->second);
					found = true;
				}
			}
			if (found)
				wire->attributes[ID::init] = val;
		}
	}
};
static InitBits consume_inits(ShardedVector<RTLIL::Wire*> &initialized_wires, const SigMap &assign_map)
{
	InitBits init_bits;
	for (RTLIL::Wire *initialized_wire : initialized_wires) {
		auto it = initialized_wire->attributes.find(ID::init);
		RTLIL::Const &val = it->second;
		SigSpec sig = assign_map(initialized_wire);
		for (int i = 0; i < GetSize(val) && i < GetSize(sig); i++)
			if (val[i] != State::Sx && sig[i].wire != nullptr) {
				init_bits.values[sig[i]] = val[i];
				init_bits.wires.insert(sig[i].wire);
			}
		initialized_wire->attributes.erase(it);
	}
	return init_bits;
}

/**
 * What kinds of things are signals connected to?
 * Helps pick representatives out of groups of connected signals */
struct SigConnKinds {
	// Wire bits driven by registers (with clk2fflogic exception)
	ShardedSigPool registers;
	// Wire bits connected to any cell port
	ShardedSigPool cells;
	// construct a pool of wires which are directly driven by a known celltype,
	// this will influence our choice of representatives
	ShardedSigSpecPool direct;
	SigConnKinds(bool purge_mode, const AnalysisContext& actx, CleanRunContext& clean_ctx) {
		ShardedSigPool::Builder register_signals_builder(actx.subpool);
		ShardedSigPool::Builder connected_signals_builder(actx.subpool);
		ShardedSigSpecPool::Builder direct_sigs_builder(actx.subpool);
		actx.subpool.run([&direct_sigs_builder, &register_signals_builder, &connected_signals_builder, purge_mode, &actx, &clean_ctx](const ParallelDispatchThreadPool::RunCtx &ctx) {

			for (int i : ctx.item_range(actx.mod->cells_size())) {
				RTLIL::Cell *cell = actx.mod->cell_at(i);
				if (!purge_mode) {
					if (clean_ctx.ct_reg.cell_known(cell->type)) {
						// Improve witness signal naming when clk2fflogic used
						// see commit message e36c71b5
						bool clk2fflogic = cell->get_bool_attribute(ID::clk2fflogic);
						for (auto &[port, sig] : cell->connections())
							if (clk2fflogic ? port == ID::D : clean_ctx.ct_reg.cell_output(cell->type, port))
								add_spec(register_signals_builder, ctx, sig);
					}
					// TODO optimize for direct wire connections?
					for (auto &[_, sig] : cell->connections())
						add_spec(connected_signals_builder, ctx, sig);
				}
				if (clean_ctx.ct_all.cell_known(cell->type))
					for (auto &[port, sig] : cell->connections())
						if (clean_ctx.ct_all.cell_output(cell->type, port)) {
							RTLIL::SigSpec spec = actx.assign_map(sig);
							unsigned int hash = spec.hash_into(Hasher()).yield();
							direct_sigs_builder.insert(ctx, {std::move(spec), hash});
						}
			}
		});
		actx.subpool.run([&register_signals_builder, &connected_signals_builder, &direct_sigs_builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
			register_signals_builder.process(ctx);
			connected_signals_builder.process(ctx);
			direct_sigs_builder.process(ctx);
		});
		registers = register_signals_builder;
		cells = connected_signals_builder;
		direct = direct_sigs_builder;
	}
	void clear(const ParallelDispatchThreadPool::RunCtx &ctx) {
		registers.clear(ctx);
		cells.clear(ctx);
		direct.clear(ctx);
	}
};

ShardedVector<RTLIL::SigBit> build_candidates(DirectWires& direct_wires, const SigConnKinds& sig_analysis, const AnalysisContext& actx) {
	ShardedVector<RTLIL::SigBit> sigmap_canonical_candidates(actx.subpool);
	actx.subpool.run([&actx, &sig_analysis, &sigmap_canonical_candidates, &direct_wires](const ParallelDispatchThreadPool::RunCtx &ctx) {
		std::optional<DirectWires> local_direct_wires;
		DirectWires *this_thread_direct_wires = &direct_wires;
		if (ctx.thread_num > 0) {
			// Rebuild a thread-local direct_wires from scratch
			// but from the same inputs
			local_direct_wires.emplace(sig_analysis.direct, actx.assign_map);
			this_thread_direct_wires = &local_direct_wires.value();
		}
		for (int i : ctx.item_range(actx.mod->wires_size())) {
			RTLIL::Wire *wire = actx.mod->wire_at(i);
			for (int j = 0; j < wire->width; ++j) {
				RTLIL::SigBit s1(wire, j);
				RTLIL::SigBit s2 = actx.assign_map(s1);
				if (compare_signals(s2, s1, sig_analysis.registers, sig_analysis.cells, *this_thread_direct_wires))
					sigmap_canonical_candidates.insert(ctx, s1);
			}
		}
	});
	return sigmap_canonical_candidates;
}

void update_assign_map(ShardedVector<RTLIL::SigBit>& sigmap_canonical_candidates, DirectWires& direct_wires, const SigConnKinds& sig_analysis, SigMap& assign_map) {
	for (RTLIL::SigBit candidate : sigmap_canonical_candidates) {
		RTLIL::SigBit current_canonical = assign_map(candidate);
		if (compare_signals(current_canonical, candidate, sig_analysis.registers, sig_analysis.cells, direct_wires))
			assign_map.add(candidate);
	}
}

struct DeferredUpdates {
	// Deferred updates to the assign_map
	ShardedVector<UpdateConnection> update_connections;
	// Wires we should remove init from
	ShardedVector<RTLIL::Wire*> initialized_wires;
	DeferredUpdates(ParallelDispatchThreadPool::Subpool &subpool) : update_connections(subpool), initialized_wires(subpool) {}
};
struct UsedSignals {
	// here, "connected" means "driven or driving something"
	// meanwhile, "used" means "driving something"
	// sigmapped
	ShardedSigPool connected;
	// pre-sigmapped
	ShardedSigPool raw_connected;
	// sigmapped
	ShardedSigPool used;

	void clear(ParallelDispatchThreadPool::Subpool &subpool) {
		subpool.run([this](const ParallelDispatchThreadPool::RunCtx &ctx) {
			connected.clear(ctx);
			raw_connected.clear(ctx);
			used.clear(ctx);
		});
	}
};

std::tuple<DeferredUpdates, UsedSignals> analyse_connectivity(SigConnKinds& sig_analysis, const AnalysisContext& actx, CleanRunContext &clean_ctx) {
	DeferredUpdates deferred(actx.subpool);
	ShardedSigPool::Builder conn_builder(actx.subpool);
	ShardedSigPool::Builder raw_conn_builder(actx.subpool);
	ShardedSigPool::Builder used_builder(actx.subpool);

	// gather the usage information for cells and update cell connections with the altered sigmap
	// also gather the usage information for ports, wires with `keep`
	// also gather init bits
	actx.subpool.run([&deferred, &conn_builder, &raw_conn_builder, &used_builder, &sig_analysis, &actx, &clean_ctx](const ParallelDispatchThreadPool::RunCtx &ctx) {
		// Parallel destruction of these sharded structures
		sig_analysis.clear(ctx);

		for (int i : ctx.item_range(actx.mod->cells_size())) {
			RTLIL::Cell *cell = actx.mod->cell_at(i);
			for (const auto &[port, sig] : cell->connections_) {
				SigSpec spec = actx.assign_map(sig);
				if (spec != sig)
					deferred.update_connections.insert(ctx, {cell, port, spec});
				add_spec(raw_conn_builder, ctx, spec);
				add_spec(conn_builder, ctx, spec);
				if (!clean_ctx.ct_all.cell_output(cell->type, port))
					add_spec(used_builder, ctx, spec);
			}
		}
		for (int i : ctx.item_range(actx.mod->wires_size())) {
			RTLIL::Wire *wire = actx.mod->wire_at(i);
			if (wire->port_id > 0) {
				RTLIL::SigSpec sig = RTLIL::SigSpec(wire);
				add_spec(raw_conn_builder, ctx, sig);
				actx.assign_map.apply(sig);
				add_spec(conn_builder, ctx, sig);
				if (!wire->port_input)
					add_spec(used_builder, ctx, sig);
			}
			if (wire->get_bool_attribute(ID::keep)) {
				RTLIL::SigSpec sig = RTLIL::SigSpec(wire);
				actx.assign_map.apply(sig);
				add_spec(conn_builder, ctx, sig);
			}
			auto it = wire->attributes.find(ID::init);
			if (it != wire->attributes.end())
				deferred.initialized_wires.insert(ctx, wire);
		}
	});
	actx.subpool.run([&conn_builder, &raw_conn_builder, &used_builder](const ParallelDispatchThreadPool::RunCtx &ctx) {
		conn_builder.process(ctx);
		raw_conn_builder.process(ctx);
		used_builder.process(ctx);
	});
	UsedSignals used {conn_builder, raw_conn_builder, used_builder};
	return {std::move(deferred), std::move(used)};
}

struct WireDeleter {
	pool<RTLIL::Wire*> del_wires_queue;
	ShardedVector<RTLIL::Wire*> remove_init;
	ShardedVector<std::pair<RTLIL::Wire*, RTLIL::Const>> set_init;
	ShardedVector<RTLIL::SigSig> new_connections;
	ShardedVector<RTLIL::Wire*> remove_unused_bits;
	ShardedVector<std::pair<RTLIL::Wire*, RTLIL::Const>> set_unused_bits;
	WireDeleter(UsedSignals& used_sig_analysis, bool purge_mode, const AnalysisContext& actx) :
		remove_init(actx.subpool),
		set_init(actx.subpool),
		new_connections(actx.subpool),
		remove_unused_bits(actx.subpool),
		set_unused_bits(actx.subpool) {
		ShardedVector<RTLIL::Wire*> del_wires(actx.subpool);
		actx.subpool.run([&actx, purge_mode, &del_wires, &used_sig_analysis, this](const ParallelDispatchThreadPool::RunCtx &ctx) {
			for (int i : ctx.item_range(actx.mod->wires_size())) {
				RTLIL::Wire *wire = actx.mod->wire_at(i);
				SigSpec s1 = SigSpec(wire), s2 = actx.assign_map(s1);
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
				if (!purge_mode && check_public_name(wire->name) && (check_any(used_sig_analysis.raw_connected, s1) || check_any(used_sig_analysis.connected, s2) || s1 != s2)) {
					// do not get rid of public names unless in purge mode or if the wire is entirely unused, not even aliased
				} else
				if (!check_any(used_sig_analysis.raw_connected, s1)) {
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
						new_connections.insert(ctx, std::move(new_conn));
					if (initval.is_fully_undef()) {
						if (has_init_attribute)
							remove_init.insert(ctx, wire);
					} else
						if (init_changed)
							set_init.insert(ctx, {wire, std::move(initval)});

					std::string unused_bits;
					if (!check_all(used_sig_analysis.used, s2)) {
						for (int i = 0; i < GetSize(s2); i++) {
							if (s2[i].wire == NULL)
								continue;
							SigBit b = s2[i];
							if (used_sig_analysis.used.find({b, b.hash_top().yield()}) == nullptr) {
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
		del_wires_queue.insert(del_wires.begin(), del_wires.end());
	}
	// Decide for each wire if we should be deleting it
	// and fix up attributes
	void commit_changes(RTLIL::Module* mod) {
		for (RTLIL::Wire *wire : remove_init)
			wire->attributes.erase(ID::init);
		for (auto &p : set_init)
			p.first->attributes[ID::init] = std::move(p.second);
		for (auto &conn : new_connections)
			mod->connect(std::move(conn));
		for (RTLIL::Wire *wire : remove_unused_bits)
			wire->attributes.erase(ID::unused_bits);
		for (auto &p : set_unused_bits)
			p.first->attributes[ID::unused_bits] = std::move(p.second);
	}
	int delete_wires(RTLIL::Module* mod, bool verbose) {
		int deleted_and_unreported = 0;
		for (auto wire : del_wires_queue) {
			if (ys_debug() || (check_public_name(wire->name) && verbose))
				log_debug("  removing unused non-port wire %s.\n", wire->name);
			else
				deleted_and_unreported++;
		}
		mod->remove(del_wires_queue);
		return deleted_and_unreported;
	}
};

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN

bool rmunused_module_signals(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, CleanRunContext &clean_ctx)
{
	// Passing actx to function == function does parallel work
	// Not passing module as function argument == function does not modify module
	// TODO the above sentence is false due to constness laundering in wire_at / cell_at
	AnalysisContext actx(module, subpool);
	SigConnKinds conn_kinds(clean_ctx.flags.purge, actx, clean_ctx);

	// Main thread's cached direct wires are retained and used later:
	DirectWires direct_wires(conn_kinds.direct, actx.assign_map);
	// Other threads' caches get discarded when threads finish in build_candidates
	// but the per-thread results are collected into sigmap_canonical_candidates
	ShardedVector<RTLIL::SigBit> sigmap_canonical_candidates = build_candidates(direct_wires, conn_kinds, actx);

	// Cache all the direct_wires results that we might possible need. This avoids the results
	// changing when we update `assign_map` below.
	direct_wires.cache_all(sigmap_canonical_candidates);
	// Modify assign_map to reflect the connectivity we want, not the one we have
	update_assign_map(sigmap_canonical_candidates, direct_wires, conn_kinds, actx.assign_map);

	// Remove all wire-wire connections
	module->connections_.clear();

	// UsedSigConnKinds used_sig_analysis(sig_analysis, actx);
	auto [deferred, used] = analyse_connectivity(conn_kinds, actx, clean_ctx);
	fixup_update_ports(deferred.update_connections);
	consume_inits(deferred.initialized_wires, actx.assign_map).apply_normalised_inits();

	WireDeleter deleter(used, clean_ctx.flags.purge, actx);

	used.clear(subpool);

	deleter.commit_changes(module);
	int deleted_and_unreported = deleter.delete_wires(module, clean_ctx.flags.verbose);
	int deleted_total = GetSize(deleter.del_wires_queue);

	clean_ctx.stats.count_rm_wires += deleted_total;

	if (clean_ctx.flags.verbose && deleted_and_unreported)
		log_debug("  removed %d unused temporary wires.\n", deleted_and_unreported);

	if (deleted_total)
		module->design->scratchpad_set_bool("opt.did_something", true);

	return deleted_total != 0;
}

YOSYS_NAMESPACE_END
