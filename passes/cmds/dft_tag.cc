/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

#include "kernel/celltypes.h"
#include "kernel/ff.h"
#include "kernel/modtools.h"
#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <deque>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct DftTagOptions {
	bool tag_public = false;
	bool overwrite_only = false;
};

struct DftTagWorker {
	Module *module;
	DftTagOptions options;
	ModWalker modwalker;
	SigMap &sigmap;
	FfInitVals initvals;

	struct tag_set {
		int index = 0;

		tag_set(int index = 0) : index(index) {}

		bool operator<(const tag_set &other) const { return index < other.index; }
		bool operator==(const tag_set &other) const { return index == other.index; }

		unsigned int hash() const { return hash_ops<int>::hash(index); }

		bool empty() const { return index == 0; }
	};

	idict<pool<IdString>> tag_sets;

	pool<IdString> tmp_tag_set;
	dict<std::pair<tag_set, tag_set>, tag_set> tag_set_union_cache;

	dict<SigBit, tag_set> tagged_signals;

	dict<IdString, pool<IdString>> tag_groups;
	dict<IdString, IdString> group_of_tag;
	pool<IdString> all_tags;

	pool<Cell *> pending_cells;
	std::deque<Cell *> pending_cell_queue;

	dict<std::pair<IdString, SigBit>, SigBit> tag_signals;

	// Uses SigSpec instead of SigBit so we can use coarse grained cells to combine the individual tags
	dict<std::pair<IdString, SigSpec>, SigSpec> tag_group_signals;

	pool<Cell *> warned_cells;

	DftTagWorker(Module *module, DftTagOptions options) :
		module(module), options(options), modwalker(module->design), sigmap(modwalker.sigmap)
	{
		modwalker.setup(module);
		initvals.set(&modwalker.sigmap, module);
		tag_sets(tmp_tag_set);
	}

	void resolve_overwrites()
	{
		std::vector<Cell *> overwrite_cells;
		std::vector<Cell *> original_cells;

		bool design_changed = false;

		for (auto cell : module->cells()) {
			if (cell->type == ID($overwrite_tag))
				overwrite_cells.push_back(cell);

			if (cell->type == ID($original_tag))
				original_cells.push_back(cell);
		}

		for (auto cell : overwrite_cells) {
			log_debug("Applying $overwrite_tag %s for signal %s\n", log_id(cell->name), log_signal(cell->getPort(ID::A)));
			SigSpec orig_signal = cell->getPort(ID::A);
			SigSpec interposed_signal = divert_users(orig_signal);
			auto *set_tag_cell = module->addSetTag(NEW_ID, cell->getParam(ID::TAG).decode_string(), orig_signal, cell->getPort(ID::SET), cell->getPort(ID::CLR), interposed_signal);
			modwalker.add_cell(set_tag_cell); // Make sure the next $overwrite_tag sees the new connections
			design_changed = true;
		}

		for (auto cell : overwrite_cells) {
			module->remove(cell);
		}
		for (auto cell : original_cells) {
			cell->type = ID($get_tag);
		}

		if (design_changed)
			modwalker.setup(module);
	}

	SigSpec divert_users(SigSpec signal)
	{
		SigSpec signal_mapped = sigmap(signal);
		signal_mapped.sort_and_unify();
		if (GetSize(signal_mapped) < GetSize(signal))
			log_warning("Detected $overwrite_tag on signal %s which contains repeated bits, this can result in unexpected behavior.\n", log_signal(signal));
		SigSpec new_wire = module->addWire(NEW_ID, GetSize(signal));
		for (int i = 0; i < GetSize(new_wire); ++i)
			divert_users(signal[i], new_wire[i]);
		return new_wire;
	}

	void divert_users(SigBit driver_bit, SigBit interposed_bit)
	{
		dict<std::pair<Cell *, IdString>, SigSpec> updated_ports;
		// TODO also check module outputs
		auto found = modwalker.signal_consumers.find(driver_bit);
		if (found == modwalker.signal_consumers.end())
			return;
		for (auto &consumer : found->second) {
			if (consumer.cell->type.in(ID($original_tag)))
				continue;
			if (sigmap(consumer.cell->getPort(consumer.port)[consumer.offset]) != driver_bit)
				continue;
			std::pair<Cell *, IdString> key = {consumer.cell, consumer.port};
			auto found_port = updated_ports.find(key);
			if (found_port == updated_ports.end()) {
				updated_ports.emplace(key, consumer.cell->getPort(consumer.port));
			}
			updated_ports[key][consumer.offset] = interposed_bit;
		}
		for (auto &update : updated_ports) {
			update.first.first->setPort(update.first.second, update.second);
			modwalker.add_cell(update.first.first); // Make sure the next $overwrite_tag sees the new connections
		}
	}

	const pool<IdString> &tag_pool(tag_set set) { return tag_sets[set.index]; }

	tag_set singleton(IdString tag)
	{
		tmp_tag_set.clear();
		tmp_tag_set.emplace(tag);
		return tag_sets(tmp_tag_set);
	}

	tag_set merge(tag_set a, tag_set b)
	{
		if (b < a)
			std::swap(a, b);
		if (a.empty() || a == b)
			return b;
		auto found = tag_set_union_cache.find(std::make_pair(a, b));
		if (found == tag_set_union_cache.end()) {
			tmp_tag_set.clear();
			auto &a_tags = tag_pool(a);
			auto &b_tags = tag_pool(b);
			tmp_tag_set.insert(a_tags.begin(), a_tags.end());
			tmp_tag_set.insert(b_tags.begin(), b_tags.end());
			tag_set result = tag_sets(tmp_tag_set);
			tag_set_union_cache.emplace(std::make_pair(a, b), result);
			return result;
		}
		return found->second;
	}

	tag_set tags(SigBit bit)
	{
		sigmap.apply(bit);
		auto found = tagged_signals.find(bit);
		if (found != tagged_signals.end())
			return found->second;
		return tag_set();
	}

	tag_set tags(SigSpec sig)
	{
		tag_set result;
		for (auto bit : sig)
			result = merge(result, tags(bit));
		return result;
	}

	tag_set tags(Cell *cell)
	{
		tag_set result;
		for (auto &conn : cell->connections()) {
			if (cell->input(conn.first))
				result = merge(result, tags(conn.second));
		}
		return result;
	}

	void add_tags(SigBit bit, tag_set new_tags)
	{
		sigmap.apply(bit);
		auto &tags = tagged_signals[bit];
		tag_set merged_tags = merge(tags, new_tags);
		if (merged_tags == tags)
			return;
		tags = merged_tags;
		auto it = modwalker.signal_consumers.find(bit);
		if (it == modwalker.signal_consumers.end())
			return;
		for (auto &consumer : it->second)
			if (pending_cells.insert(consumer.cell).second)
				pending_cell_queue.push_back(consumer.cell);
	}

	void add_tags(SigSpec sig, tag_set new_tags)
	{
		for (auto bit : sigmap(sig))
			add_tags(bit, new_tags);
	}

	void add_tags(Cell *cell, tag_set new_tags)
	{
		for (auto &conn : cell->connections())
			if (cell->output(conn.first))
				add_tags(conn.second, new_tags);
	}

	void forward_tags(SigSpec dst, SigSpec src)
	{
		log_assert(GetSize(dst) == GetSize(src));
		for (int i = 0; i < GetSize(dst); i++)
			add_tags(dst[i], tags(src[i]));
	}

	void propagate_tags()
	{
		for (auto cell : module->cells()) {
			if (cell->type == ID($set_tag)) {
				pending_cells.insert(cell);
				pending_cell_queue.push_back(cell);
			}
		}

		while (!pending_cell_queue.empty()) {
			Cell *cell = pending_cell_queue.front();
			pending_cell_queue.pop_front();
			pending_cells.erase(cell);

			propagate_tags(cell);
		}
	}

	SigBit tag_signal(IdString tag, SigBit bit)
	{
		sigmap.apply(bit);
		if (!bit.is_wire())
			return State::S0; // Constant value - no tags

		auto found = tag_signals.find(std::make_pair(tag, bit));
		if (found != tag_signals.end())
			return found->second;

		if (!tag_pool(tags(bit)).count(tag))
			return State::S0; // Statically known to not have this tag

		// TODO handle module inputs
		auto drivers = modwalker.signal_drivers.find(bit);
		if (drivers == modwalker.signal_drivers.end() || drivers->second.empty())
			return State::S0; // No driver - no tags

		log_assert(drivers->second.size() == 1);
		auto driver = *drivers->second.begin();

		emit_tag_signals(tag, driver.cell);

		found = tag_signals.find(std::make_pair(tag, bit));
		log_assert(found != tag_signals.end());
		return found->second;
	}

	SigSpec tag_signal(IdString tag, SigSpec sig)
	{
		SigSpec result;
		for (auto bit : sig)
			result.append(tag_signal(tag, bit));
		return result;
	}

	SigSpec tag_group_signal(IdString tag_group, SigSpec sig)
	{
		sigmap.apply(sig);
		if (sig.is_fully_const() || tag_groups.count(tag_group) == 0)
			return Const(0, GetSize(sig));

		auto found = tag_group_signals.find(std::make_pair(tag_group, sig));
		if (found != tag_group_signals.end())
			return found->second;

		SigSpec combined;

		for (auto &tag : tag_groups[tag_group]) {
			auto tag_sig = tag_signal(tag, sig);

			if (!GetSize(combined))
				combined = tag_sig;
			else
				combined = autoOr(NEW_ID, combined, tag_sig);
		}

		if (!GetSize(combined))
			combined = Const(0, GetSize(sig));

		tag_group_signals.emplace(std::make_pair(tag_group, sig), combined);
		return combined;
	}

	void emit_tag_signal(IdString tag, SigBit bit, SigBit tag_bit)
	{
		sigmap.apply(bit);
		sigmap.apply(tag_bit);

		if (!tag_pool(tags(bit)).count(tag))
			return;

		auto key = std::make_pair(tag, bit);
		auto found = tag_signals.find(key);
		if (found != tag_signals.end()) {
			module->connect(found->second, tag_bit);
			return;
		}
		tag_signals.emplace(key, tag_bit);
	}

	void emit_tag_signal(IdString tag, SigSpec sig, SigSpec tag_sig)
	{
		log_assert(GetSize(sig) == GetSize(tag_sig));
		for (int i = 0; i < GetSize(sig); i++)
			emit_tag_signal(tag, sig[i], tag_sig[i]);
	}

	void emit_tag_signals(IdString tag, Cell *cell)
	{
		if (!pending_cells.insert(cell).second) {
			// We have a cycle, emit placeholder wires which will be connected
			// when the outer call for this tag/cell returns
			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					emit_tag_signal(tag, conn.second, module->addWire(NEW_ID, GetSize(conn.second)));

			return;
		}

		process_cell(tag, cell);

		pending_cells.erase(cell);
	}

	void propagate_tags(Cell *cell)
	{
		if (cell->type == ID($set_tag)) {
			IdString tag = stringf("\\%s", cell->getParam(ID::TAG).decode_string().c_str());
			if (all_tags.insert(tag).second) {
				auto group_sep = tag.str().find(':');
				IdString tag_group = group_sep != std::string::npos ? tag.str().substr(0, group_sep) : tag;
				tag_groups[tag_group].insert(tag);
				group_of_tag[tag] = tag_group;
			}

			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			// TODO handle constant set/clr masks
			add_tags(sig_y, singleton(tag));
			forward_tags(sig_y, sig_a);
			return;
		}

		if (cell->type == ID($get_tag)) {
			return;
		}

		if (cell->type.in(ID($not), ID($pos))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			if (cell->type.in(ID($not), ID($or))) {
				sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
			}
			forward_tags(sig_y, sig_a);
			return;
		}

		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($bweqx))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			auto sig_b = cell->getPort(ID::B);
			if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
				sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
				sig_b.extend_u0(GetSize(sig_y), cell->getParam(ID::B_SIGNED).as_bool());
			}
			forward_tags(sig_y, sig_a);
			forward_tags(sig_y, sig_b);
			return;
		}

		if (cell->type.in(ID($mux), ID($bwmux))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);
			auto sig_s = cell->getPort(ID::S);

			if (cell->type == ID($mux))
				sig_s = SigSpec(sig_s[0], GetSize(sig_y));

			forward_tags(sig_y, sig_a);
			forward_tags(sig_y, sig_b);
			forward_tags(sig_y, sig_s);
			return;
		}

		if (RTLIL::builtin_ff_cell_types().count(cell->type) || cell->type == ID($anyinit)) {
			FfData ff(&initvals, cell);

			if (ff.has_clk || ff.has_gclk)
				forward_tags(ff.sig_q, ff.sig_d);
			return;
		}

		// Single output but, sensitive to all inputs
		if (cell->type.in(
			ID($le), ID($lt), ID($ge), ID($gt),
			ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor),
			ID($reduce_bool), ID($logic_not), ID($logic_or), ID($logic_and),
			ID($eq), ID($ne)
		)) {
			auto &sig_y = cell->getPort(ID::Y);

			add_tags(sig_y[0], tags(cell));
			return;
		}


		// Fallback, propagate tags from all inputs to all outputs
		add_tags(cell, tags(cell));

		if (cell->type.in(
			ID($_AND_), ID($_OR_), ID($_NAND_), ID($_NOR_), ID($_ANDNOT_), ID($_ORNOT_),
			ID($_XOR_), ID($_XNOR_), ID($_NOT_), ID($_BUF_), ID($_MUX_),

			ID($assert), ID($assume)
		)) {
			return;
		}

		// This isn't a correctness concern (unless cell is a module generating
		// tags), but we may end up generating a lot of extra logic when
		// reaching this
		if (!warned_cells.insert(cell).second)
			return;
		if (cell->type.isPublic())
			log_warning("Unhandled cell %s (%s) during tag propagation\n", log_id(cell), log_id(cell->type));
		else
			log_debug("Unhandled cell %s (%s) during tag propagation\n", log_id(cell), log_id(cell->type));
	}

	void process_cell(IdString tag, Cell *cell)
	{
		if (cell->type == ID($set_tag)) {
			IdString cell_tag = stringf("\\%s", cell->getParam(ID::TAG).decode_string().c_str());

			auto tag_sig_a = tag_signal(tag, cell->getPort(ID::A));
			auto &sig_y = cell->getPort(ID::Y);

			if (cell_tag == tag) {
				auto &sig_set = cell->getPort(ID::SET);
				auto &sig_clr = cell->getPort(ID::CLR);
				tag_sig_a = autoAnd(NEW_ID, tag_sig_a, autoNot(NEW_ID, sig_clr));
				tag_sig_a = autoOr(NEW_ID, tag_sig_a, sig_set);
			}

			emit_tag_signal(tag, sig_y, tag_sig_a);
			return;
		}

		if (cell->type == ID($get_tag)) {
			log_assert(false);
		}

		if (cell->type.in(ID($not), ID($pos), ID($_NOT_), ID($_BUF_))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			if (cell->type.in(ID($not), ID($or))) {
				sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
			}
			emit_tag_signal(tag, sig_y, tag_signal(tag, sig_a));
			return;
		}

		if (cell->type.in(
			ID($and), ID($or),
			ID($_AND_), ID($_OR_), ID($_NAND_), ID($_NOR_), ID($_ANDNOT_), ID($_ORNOT_)
		)) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			auto sig_b = cell->getPort(ID::B);
			if (cell->type.in(ID($and), ID($or))) {
				sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
				sig_b.extend_u0(GetSize(sig_y), cell->getParam(ID::B_SIGNED).as_bool());
			}

			bool inv_a = false;
			bool inv_b = false;

			if (cell->type.in(ID($or), ID($_OR_), ID($_NOR_), ID($_ORNOT_)))
				inv_a ^= true, inv_b ^= true;
			if (cell->type.in(ID($_ANDNOT_), ID($_ORNOT_)))
				inv_b ^= true;

			if (inv_a)
				sig_a = autoNot(NEW_ID, sig_a);
			if (inv_b)
				sig_b = autoNot(NEW_ID, sig_b);

			auto group_sig_a = tag_group_signal(tag, sig_a);
			auto group_sig_b = tag_group_signal(tag, sig_b);

			auto tag_sig_a = tag_signal(tag, sig_a);
			auto tag_sig_b = tag_signal(tag, sig_b);


			// Does this input allow propagating (doesn't fix output or same tag group)
			sig_a = autoOr(NEW_ID, sig_a, group_sig_a);
			sig_b = autoOr(NEW_ID, sig_b, group_sig_b);

			// Mask input tags by whether the other side allows propagation
			tag_sig_a = autoAnd(NEW_ID, tag_sig_a, sig_b);
			tag_sig_b = autoAnd(NEW_ID, tag_sig_b, sig_a);


			auto tag_sig = autoOr(NEW_ID, tag_sig_a, tag_sig_b);
			emit_tag_signal(tag, sig_y, tag_sig);
			return;
		}

		if (cell->type.in(ID($xor), ID($xnor), ID($bweqx), ID($_XOR_), ID($_XNOR_))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			auto sig_b = cell->getPort(ID::B);
			if (cell->type.in(ID($xor), ID($xnor))) {
				sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
				sig_b.extend_u0(GetSize(sig_y), cell->getParam(ID::B_SIGNED).as_bool());
			}

			auto tag_sig_a = tag_signal(tag, sig_a);
			auto tag_sig_b = tag_signal(tag, sig_b);

			auto tag_sig = autoOr(NEW_ID, tag_sig_a, tag_sig_b);
			emit_tag_signal(tag, sig_y, tag_sig);
			return;
		}


		if (cell->type.in(ID($_MUX_), ID($mux), ID($bwmux))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);
			auto sig_s = cell->getPort(ID::S);

			if (cell->type == ID($mux))
				sig_s = SigSpec(sig_s[0], GetSize(sig_y));

			auto group_sig_a = tag_group_signal(tag, sig_a);
			auto group_sig_b = tag_group_signal(tag, sig_b);
			auto group_sig_s = tag_group_signal(tag, sig_s);

			auto prop_s = autoOr(NEW_ID,
					autoXor(NEW_ID, sig_a, sig_b),
					autoOr(NEW_ID, group_sig_a, group_sig_b));

			auto prop_a = autoOr(NEW_ID, autoNot(NEW_ID, sig_s), group_sig_s);
			auto prop_b = autoOr(NEW_ID, sig_s, group_sig_s);

			auto tag_sig_a = tag_signal(tag, sig_a);
			auto tag_sig_b = tag_signal(tag, sig_b);
			auto tag_sig_s = tag_signal(tag, sig_s);

			tag_sig_a = autoAnd(NEW_ID, tag_sig_a, prop_a);
			tag_sig_b = autoAnd(NEW_ID, tag_sig_b, prop_b);
			tag_sig_s = autoAnd(NEW_ID, tag_sig_s, prop_s);

			auto tag_sig = autoOr(NEW_ID, tag_sig_s,
					autoOr(NEW_ID, tag_sig_a, tag_sig_b));
			emit_tag_signal(tag, sig_y, tag_sig);
			return;
		}

		if (cell->type.in(ID($eq), ID($ne), ID($eqx), ID($nex))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			auto sig_b = cell->getPort(ID::B);
			int width = std::max(GetSize(sig_a), GetSize(sig_b));
			sig_a.extend_u0(width, cell->getParam(ID::A_SIGNED).as_bool());
			sig_b.extend_u0(width, cell->getParam(ID::B_SIGNED).as_bool());

			auto group_sig_a = tag_group_signal(tag, sig_a);
			auto group_sig_b = tag_group_signal(tag, sig_b);

			auto tag_sig_a = tag_signal(tag, sig_a);
			auto tag_sig_b = tag_signal(tag, sig_b);

			auto group_sig = autoOr(NEW_ID, group_sig_a, group_sig_b);
			// The output can only be affected by the tagged inputs if all group-untagged bits are equal

			auto masked_a = autoOr(NEW_ID, sig_a, group_sig);
			auto masked_b = autoOr(NEW_ID, sig_b, group_sig);

			auto prop = autoEq(NEW_ID, masked_a, masked_b);

			auto tag_sig = autoAnd(NEW_ID, prop, autoReduceOr(NEW_ID, {tag_sig_a, tag_sig_b}));
			tag_sig.extend_u0(GetSize(sig_y), false);
			emit_tag_signal(tag, sig_y, tag_sig);
			return;
		}


		if (cell->type.in(ID($lt), ID($gt), ID($le), ID($ge))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);
			auto sig_b = cell->getPort(ID::B);
			int width = std::max(GetSize(sig_a), GetSize(sig_b));
			sig_a.extend_u0(width, cell->getParam(ID::A_SIGNED).as_bool());
			sig_b.extend_u0(width, cell->getParam(ID::B_SIGNED).as_bool());

			if (cell->type.in(ID($gt), ID($le)))
				std::swap(sig_a, sig_b);

			auto group_sig_a = tag_group_signal(tag, sig_a);
			auto group_sig_b = tag_group_signal(tag, sig_b);

			auto tag_sig_a = tag_signal(tag, sig_a);
			auto tag_sig_b = tag_signal(tag, sig_b);

			auto group_sig = autoOr(NEW_ID, group_sig_a, group_sig_b);
			// The output can only be affected by the tagged inputs if the greatest possible sig_a is
			// greater or equal to the least possible sig_b
			auto masked_a = autoOr(NEW_ID, sig_a, group_sig);
			auto masked_b = autoAnd(NEW_ID, sig_b, autoNot(NEW_ID, group_sig));

			auto prop = autoGe(NEW_ID, masked_a, masked_b);

			auto tag_sig = autoAnd(NEW_ID, prop, autoReduceOr(NEW_ID, {tag_sig_a, tag_sig_b}));
			tag_sig.extend_u0(GetSize(sig_y), false);
			emit_tag_signal(tag, sig_y, tag_sig);
			return;
		}

		if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($logic_not))) {
			auto &sig_y = cell->getPort(ID::Y);
			auto sig_a = cell->getPort(ID::A);

			auto group_sig_a = tag_group_signal(tag, sig_a);
			auto tag_sig_a = tag_signal(tag, sig_a);

			if (cell->type.in(ID($reduce_or), ID($reduce_bool), ID($logic_not)))
				sig_a = autoNot(NEW_ID, sig_a);

			auto filled = autoOr(NEW_ID, sig_a, group_sig_a);

			auto prop = autoReduceAnd(NEW_ID, filled);
			auto tagged = autoReduceOr(NEW_ID, tag_sig_a);
			auto tag_sig = autoAnd(NEW_ID, prop, tagged);
			tag_sig.extend_u0(GetSize(sig_y), false);
			emit_tag_signal(tag, sig_y, tag_sig);
			return;
		}

		if (RTLIL::builtin_ff_cell_types().count(cell->type) || cell->type == ID($anyinit)) {
			FfData ff(&initvals, cell);
			// TODO handle some more variants
			if ((ff.has_clk || ff.has_gclk) && !ff.has_ce && !ff.has_aload && !ff.has_srst && !ff.has_arst && !ff.has_sr) {
				if (ff.has_clk && !tags(ff.sig_clk).empty())
					log_warning("Tags on CLK input ignored for %s (%s)\n", log_id(cell), log_id(cell->type));

				int width = ff.width;

				auto sig_q = ff.sig_q;
				auto sig_d = ff.sig_d;

				ff.name = NEW_ID;
				ff.cell = nullptr;
				ff.sig_d = tag_signal(tag, ff.sig_d);
				ff.sig_q = module->addWire(NEW_ID, width);
				ff.is_anyinit = false;
				ff.val_init = Const(0, width);
				ff.emit();

				emit_tag_signal(tag, sig_q, ff.sig_q);
				return;
			} else {
				log_warning("Unhandled FF-cell %s (%s), consider running clk2fflogic, async2sync and/or dffunmap\n", log_id(cell), log_id(cell->type));

				// For unhandled FFs, the default propagation would cause combinational loops
				emit_tag_signal(tag, ff.sig_q, Const(0, ff.width));
				return;
			}
		}

		// Fallback
		SigSpec tag_input;

		for (auto &conn : cell->connections()) {
			if (cell->input(conn.first)) {
				auto tag_sig = tag_signal(tag, conn.second);
				tag_input.append(tag_sig);
			}
		}

		SigBit any_tagged = autoReduceOr(NEW_ID, tag_input);

		for (auto &conn : cell->connections()) {
			if (cell->output(conn.first)) {
				emit_tag_signal(tag, conn.second, SigSpec(any_tagged, GetSize(conn.second)));
			}
		}

		// As fallback we propagate all tags from all inputs to all outputs,
		// which is an over-approximation (unless the cell is a module that
		// generates tags itself in which case it could be arbitrary).
		if (warned_cells.insert(cell).second)
			log_warning("Unhandled cell %s (%s) while emitting tag signals\n", log_id(cell), log_id(cell->type));
	}

	void emit_tags()
	{
		warned_cells.clear();
		std::vector<Cell *> get_tag_cells;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($get_tag))
				get_tag_cells.push_back(cell);

		for (auto cell : get_tag_cells) {
			auto &sig_a = cell->getPort(ID::A);
			IdString tag = stringf("\\%s", cell->getParam(ID::TAG).decode_string().c_str());

			tag_signal(tag, sig_a);
		}

		if (options.tag_public)
		{
			std::vector<Wire *> public_wires;

			for (auto wire : module->selected_wires())
				if (wire->name.isPublic())
					public_wires.push_back(wire);

			for (auto wire : public_wires) {
				for (auto tag : tag_pool(tags(SigSpec(wire)))) {
					auto tag_sig = tag_signal(tag, SigSpec(wire));
					if (tag_sig.is_fully_zero())
						continue;

					int index = 0;
					auto name = module->uniquify(stringf("%s:%s", wire->name.c_str(), tag.c_str() + 1), index);
					auto hdlname = wire->get_hdlname_attribute();

					if (!hdlname.empty())
						hdlname.back() += index ?
								stringf(":%s_%d", tag.c_str() + 1, index) :
								stringf(":%s", tag.c_str() + 1);

					auto tag_wire = module->addWire(name, wire->width);

					tag_wire->set_bool_attribute(ID::keep);
					tag_wire->set_bool_attribute(ID(dft_tag));
					if (!hdlname.empty())
						tag_wire->set_hdlname_attribute(hdlname);

					module->connect(tag_wire, tag_sig);
				}
			}
		}
	}

	void replace_dft_cells()
	{
		std::vector<Cell *> get_tag_cells;
		std::vector<Cell *> set_tag_cells;
		for (auto cell : module->cells()) {
			if (cell->type == ID($get_tag))
				get_tag_cells.push_back(cell);

			if (cell->type == ID($set_tag))
				set_tag_cells.push_back(cell);

			log_assert(!cell->type.in(ID($overwrite_tag), ID($original_tag)));
		}

		for (auto cell : set_tag_cells) {
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_y = cell->getPort(ID::Y);
			module->connect(sig_y, sig_a);
			module->remove(cell);
		}

		for (auto cell : get_tag_cells) {
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_y = cell->getPort(ID::Y);
			IdString tag = stringf("\\%s", cell->getParam(ID::TAG).decode_string().c_str());

			auto tag_sig = tag_signal(tag, sig_a);
			module->connect(sig_y, tag_sig);
			module->remove(cell);
		}
	}


	SigSpec autoAnd(IdString name, const SigSpec &sig_a, const SigSpec &sig_b)
	{
		log_assert(GetSize(sig_a) == GetSize(sig_b));
		if (sig_a.is_fully_zero() || sig_b.is_fully_ones() || sig_a == sig_b)
			return sig_a;
		if (sig_a.is_fully_ones() || sig_b.is_fully_zero())
			return sig_b;

		return module->And(name, sig_a, sig_b);
	}

	SigSpec autoOr(IdString name, const SigSpec &sig_a, const SigSpec &sig_b)
	{
		log_assert(GetSize(sig_a) == GetSize(sig_b));
		if (sig_a.is_fully_ones() || sig_b.is_fully_zero() || sig_a == sig_b)
			return sig_a;
		if (sig_a.is_fully_zero() || sig_b.is_fully_ones())
			return sig_b;

		return module->Or(name, sig_a, sig_b);
	}

	SigSpec autoXor(IdString name, const SigSpec &sig_a, const SigSpec &sig_b)
	{
		log_assert(GetSize(sig_a) == GetSize(sig_b));
		if (sig_a == sig_b)
			return Const(State::S0, GetSize(sig_a));
		if (sig_a.is_fully_zero())
			return sig_b;
		if (sig_b.is_fully_zero())
			return sig_a;
		if (sig_a.is_fully_ones())
			return autoNot(name, sig_b);
		if (sig_b.is_fully_ones())
			return autoNot(name, sig_a);
		return module->Xor(name, sig_a, sig_b);
	}

	SigSpec autoXnor(IdString name, const SigSpec &sig_a, const SigSpec &sig_b)
	{
		log_assert(GetSize(sig_a) == GetSize(sig_b));
		if (sig_a == sig_b)
			return Const(State::S1, GetSize(sig_a));
		if (sig_a.is_fully_ones())
			return sig_b;
		if (sig_b.is_fully_ones())
			return sig_a;
		if (sig_a.is_fully_zero())
			return autoNot(name, sig_b);
		if (sig_b.is_fully_zero())
			return autoNot(name, sig_a);
		return module->Xnor(name, sig_a, sig_b);
	}

	SigSpec autoNot(IdString name, const SigSpec &sig_a)
	{
		if (sig_a.is_fully_const()) {
			auto const_val = sig_a.as_const();
			for (auto bit : const_val)
				bit = bit == State::S0 ? State::S1 : bit == State::S1 ? State::S0 : bit;
			return const_val;
		}
		return module->Not(name, sig_a);
	}

	SigSpec autoEq(IdString name, const SigSpec &sig_a, const SigSpec &sig_b)
	{
		log_assert(GetSize(sig_a) == GetSize(sig_b));
		if (sig_a == sig_b)
			return State::S1;
		for (int i = 0; i < GetSize(sig_a); i++) {
			auto bit_a = sig_a[i];
			auto bit_b = sig_b[i];
			if (bit_a.is_wire() || bit_b.is_wire())
				continue;
			if ((bit_a.data == State::S0 && bit_b.data == State::S1) ||
					(bit_a.data == State::S1 && bit_b.data == State::S0))
				return State::S0;
		}

		return module->Eq(name, sig_a, sig_b);
	}

	SigSpec autoGe(IdString name, const SigSpec &sig_a, const SigSpec &sig_b)
	{
		log_assert(GetSize(sig_a) == GetSize(sig_b));
		if (sig_a == sig_b || sig_a.is_fully_ones())
			return State::S1;
		if (sig_b.is_fully_zero())
			return State::S1;

		return module->Ge(name, sig_a, sig_b);
	}

	SigSpec autoReduceAnd(IdString name, const SigSpec &sig_a)
	{
		if (GetSize(sig_a) == 0)
			return State::S1;

		if (GetSize(sig_a) == 1 || sig_a == SigSpec(sig_a[0], GetSize(sig_a)))
			return sig_a[0];
		for (auto bit : sig_a)
			if (!bit.is_wire() && bit.data == State::S0)
				return State::S0;
		if (sig_a.is_fully_ones())
			return State::S1;
		return module->ReduceAnd(name, sig_a);
	}

	SigSpec autoReduceOr(IdString name, const SigSpec &sig_a)
	{
		if (GetSize(sig_a) == 0)
			return State::S0;

		if (GetSize(sig_a) == 1 || sig_a == SigSpec(sig_a[0], GetSize(sig_a)))
			return sig_a[0];
		for (auto bit : sig_a)
			if (!bit.is_wire() && bit.data == State::S1)
				return State::S1;
		if (sig_a.is_fully_zero())
			return State::S0;
		return module->ReduceOr(name, sig_a);
	}
};

struct DftTagPass : public Pass {
	DftTagPass() : Pass("dft_tag", "create tagging logic for data flow tracking") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dft_tag [options] [selection]\n");
		log("\n");
		log("This pass... TODO\n");
		log("\n");
		log("    -overwrite-only\n");
		log("        Only process $overwrite_tag and $original_tag cells.\n");
		log("    -tag-public\n");
		log("        For each public wire that may carry tagged data, create a new public\n");
		log("        wire (named <wirename>:<tagname>) that carries the tag bits. Note\n");
		log("        that without this, tagging logic will only be emitted as required\n");
		log("        for uses of $get_tag.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		DftTagOptions options;

		log_header(design, "Executing DFT_TAG pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-tag-public") {
				options.tag_public = true;
				continue;
			}
			if (args[argidx] == "-overwrite-only") {
				options.overwrite_only = true;
				continue;
			}
			break;
		}

		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			DftTagWorker worker(module, options);

			log_debug("Resolve overwrite_tag and original_tag.\n");
			worker.resolve_overwrites();

			if (options.overwrite_only)
				continue;

			log_debug("Propagate tagged signals.\n");
			worker.propagate_tags();

			log_debug("Emit tag signals and logic.\n");
			worker.emit_tags();

			log_debug("Replace dft cells.\n");
			worker.replace_dft_cells();
		}
	}
} DftTagPass;

PRIVATE_NAMESPACE_END
