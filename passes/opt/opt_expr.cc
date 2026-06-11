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
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/newcelltypes.h"
#include "kernel/utils.h"
#include "kernel/log.h"
#include "kernel/unstable/patch.h"
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool did_something;

void replace_undriven(RTLIL::Module *module, const NewCellTypes &ct)
{
	SigMap sigmap(module);
	SigPool driven_signals;
	SigPool used_signals;
	SigPool all_signals;

	dict<SigBit, pair<Wire*, State>> initbits;
	pool<Wire*> revisit_initwires;

	for (auto cell : module->cells())
	for (auto &conn : cell->connections()) {
		if (!ct.cell_known(cell->type_impl) || ct.cell_output(cell->type_impl, conn.first))
			driven_signals.add(sigmap(conn.second));
		if (!ct.cell_known(cell->type_impl) || ct.cell_input(cell->type_impl, conn.first))
			used_signals.add(sigmap(conn.second));
	}

	for (auto wire : module->wires()) {
		if (wire->attributes.count(ID::init)) {
			SigSpec sig = sigmap(wire);
			Const initval = wire->attributes.at(ID::init);
			for (int i = 0; i < GetSize(initval) && i < GetSize(wire); i++) {
				if (initval[i] == State::S0 || initval[i] == State::S1)
					initbits[sig[i]] = make_pair(wire, initval[i]);
			}
		}
		if (wire->port_input)
			driven_signals.add(sigmap(wire));
		if (wire->port_output || wire->get_bool_attribute(ID::keep))
			used_signals.add(sigmap(wire));
		all_signals.add(sigmap(wire));
	}

	all_signals.del(driven_signals);
	RTLIL::SigSpec undriven_signals = all_signals.export_all();

	for (auto &c : undriven_signals.chunks())
	{
		RTLIL::SigSpec sig = c;

		if (c.wire->name[0] == '$')
			sig = used_signals.extract(sig);
		if (sig.size() == 0)
			continue;

		Const val(RTLIL::State::Sx, GetSize(sig));
		for (int i = 0; i < GetSize(sig); i++) {
			SigBit bit = sigmap(sig[i]);
			auto cursor = initbits.find(bit);
			if (cursor != initbits.end()) {
				revisit_initwires.insert(cursor->second.first);
				val.set(i, cursor->second.second);
			}
		}

		log_debug("Setting undriven signal in %s to constant: %s = %s\n", module, log_signal(sig), log_signal(val));
		module->connect(sig, val);
		did_something = true;
	}

	if (!revisit_initwires.empty())
	{
		SigMap sm2(module);

		for (auto wire : revisit_initwires) {
			SigSpec sig = sm2(wire);
			Const initval = wire->attributes.at(ID::init);
			for (int i = 0; i < GetSize(initval) && i < GetSize(wire); i++) {
				if (SigBit(initval[i]) == sig[i])
					initval.set(i, State::Sx);
			}
			if (initval.is_fully_undef()) {
				log_debug("Removing init attribute from %s/%s.\n", module, wire);
				wire->attributes.erase(ID::init);
				did_something = true;
			} else if (initval != wire->attributes.at(ID::init)) {
				log_debug("Updating init attribute on %s/%s: %s\n", module, wire, log_signal(initval));
				wire->attributes[ID::init] = initval;
				did_something = true;
			}
		}
	}
}

void log_replace_sig(RTLIL::Module *module, RTLIL::Cell *cell,
		const std::string &info, RTLIL::SigSpec old_sig, RTLIL::SigSpec new_sig)
{
	log_debug("Replacing %s cell `%s' (%s) in module `%s' with constant driver `%s = %s'.\n",
			cell->type.c_str(), cell->name.c_str(), info.c_str(),
			module->design->twines.str(module->meta_->name).c_str(), log_signal(old_sig), log_signal(new_sig));
}

void log_replace_port(RTLIL::Module *module, RTLIL::Cell *cell,
		const std::string &info, TwineRef port, RTLIL::SigSpec new_sig)
{
	log_replace_sig(module, cell, info, cell->getPort(port), new_sig);
}

struct OptExprPatcher : public RTLIL::Patch {
	OptExprPatcher(Module *mod, SigMap *map) : RTLIL::Patch(mod, map) {}
	// Single-output rewrite via the compatible Patch::patch interface.
	void patch(Cell *old_cell, TwineRef old_port, SigSpec new_sig, const std::string &info) {
		new_sig.extend_u0(old_cell->getPort(old_port).size(), false);
		log_replace_port(mod, old_cell, info, old_port, new_sig);
		RTLIL::Patch::patch(old_cell, old_port, new_sig);
		did_something = true;
	}
	// Multi-output rewrite via Patch::patch_ports. Used for cell types
	// with more than one output port (e.g. $alu). patch_ports asserts
	// `ports` covers every output of `old_cell` and removes the cell.
	void patch_multi(Cell *old_cell, std::vector<std::pair<TwineRef, SigSpec>> ports, const std::string &info) {
		for (auto &[port, new_sig] : ports) {
			new_sig.extend_u0(old_cell->getPort(port).size(), false);
			log_replace_port(mod, old_cell, info, port, new_sig);
		}
		RTLIL::Patch::patch_ports(old_cell, ports);
		did_something = true;
	}
};

bool group_cell_inputs(RTLIL::Module *module, RTLIL::Cell *cell, bool commutative, SigMap &sigmap, bool keepdc)
{
	TwineRef b_name = cell->hasPort(TW::B) ? TW::B : TW::A;

	bool a_signed = cell->parameters.at(ID::A_SIGNED).as_bool();
	bool b_signed = cell->parameters.at(b_name == TW::B ? ID::B_SIGNED : ID::A_SIGNED).as_bool();

	RTLIL::SigSpec sig_a = sigmap(cell->getPort(TW::A));
	RTLIL::SigSpec sig_b = sigmap(cell->getPort(b_name));
	RTLIL::SigSpec sig_y = sigmap(cell->getPort(TW::Y));

	sig_a.extend_u0(sig_y.size(), a_signed);
	sig_b.extend_u0(sig_y.size(), b_signed);

	std::vector<RTLIL::SigBit> bits_a = sig_a, bits_b = sig_b, bits_y = sig_y;

	enum { GRP_DYN, GRP_CONST_A, GRP_CONST_B, GRP_CONST_AB, GRP_N };
	// Two-level partition: outer key is the rewrite kind (GRP_*), inner key
	// is the (a, b) pair that selects this bit's slot inside the new cell.
	// Two original bits sharing (kind, a, b) collapse to the same output bit.
	using Key = std::tuple<int, RTLIL::SigBit, RTLIL::SigBit>;
	BitGrouper<Key> grouper(GetSize(bits_y), [&](int i) -> std::optional<Key> {
		int group_idx = GRP_DYN;
		RTLIL::SigBit bit_a = bits_a[i], bit_b = bits_b[i];

		if (cell->type == TW($or)) {
			if (bit_a == RTLIL::State::S1 || bit_b == RTLIL::State::S1)
				bit_a = bit_b = RTLIL::State::S1;
		}
		else if (cell->type == TW($and)) {
			if (bit_a == RTLIL::State::S0 || bit_b == RTLIL::State::S0)
				bit_a = bit_b = RTLIL::State::S0;
		}
		else if (!keepdc) {
			if (cell->type == TW($xor)) {
				if (bit_a == bit_b)
					bit_a = bit_b = RTLIL::State::S0;
			}
			else if (cell->type == TW($xnor)) {
				if (bit_a == bit_b)
					bit_a = bit_b = RTLIL::State::S1; // For consistency with gate-level which does $xnor -> $_XOR_ + $_NOT_
			}
		}

		bool def = (bit_a != State::Sx && bit_a != State::Sz && bit_b != State::Sx && bit_b != State::Sz);
		if (def || !keepdc) {
			if (bit_a.wire == NULL && bit_b.wire == NULL)
				group_idx = GRP_CONST_AB;
			else if (bit_a.wire == NULL)
				group_idx = GRP_CONST_A;
			else if (bit_b.wire == NULL && commutative)
				group_idx = GRP_CONST_A, std::swap(bit_a, bit_b);
			else if (bit_b.wire == NULL)
				group_idx = GRP_CONST_B;
		}

		return std::make_tuple(group_idx, bit_a, bit_b);
	});

	// If every original bit ended up with its own unique (a, b) slot within
	// some single kind, splitting would just rename without shrinking.
	int slots_per_kind[GRP_N] = {};
	for (auto &g : grouper.groups())
		slots_per_kind[std::get<0>(g.key)]++;
	for (int kind = 0; kind < GRP_N; kind++)
		if (slots_per_kind[kind] == GetSize(bits_y))
			return false;

	log_debug("Replacing %s cell `%s' in module `%s' with cells using grouped bits:\n",
			cell->type.unescape(), cell, module);

	OptExprPatcher patcher(module, &sigmap);

	// Replacement bit for each original sig_y bit.
	dict<SigBit, SigBit> bit_map;

	// Pre-collect groups per kind, preserving BitGrouper's insertion order
	// within each kind.
	std::vector<const BitGrouper<Key>::Group*> per_kind[GRP_N];
	for (auto &g : grouper.groups())
		per_kind[std::get<0>(g.key)].push_back(&g);

	for (int kind = 0; kind < GRP_N; kind++)
	{
		if (per_kind[kind].empty())
			continue;

		int group_size = GetSize(per_kind[kind]);
		RTLIL::SigSpec new_y = patcher.addWire(NEW_TWINE, group_size);
		RTLIL::SigSpec new_a, new_b;

		int slot = 0;
		for (auto *g : per_kind[kind]) {
			SigBit bit_a = std::get<1>(g->key);
			SigBit bit_b = std::get<2>(g->key);
			new_a.append(bit_a);
			new_b.append(bit_b);
			for (int i : g->indices)
				bit_map[bits_y[i]] = new_y[slot];
			slot++;
		}

		if (cell->type.in(TW($and), TW($or)) && kind == GRP_CONST_A) {
			if (!keepdc) {
				if (cell->type == TW($and))
					new_a.replace(dict<SigBit,SigBit>{{State::Sx, State::S0}, {State::Sz, State::S0}}, &new_b);
				else if (cell->type == TW($or))
					new_a.replace(dict<SigBit,SigBit>{{State::Sx, State::S1}, {State::Sz, State::S1}}, &new_b);
				else log_abort();
			}
			log_debug("  Direct Connection: %s (%s with %s)\n", log_signal(new_b), cell->type.unescaped(), log_signal(new_a));
			// new_y becomes new_b directly: rewrite any bit_map entries pointing at new_y bits.
			dict<SigBit, SigBit> remap;
			for (int j = 0; j < group_size; j++)
				remap[new_y[j]] = new_b[j];
			for (auto &entry : bit_map) {
				auto it = remap.find(entry.second);
				if (it != remap.end()) entry.second = it->second;
			}
			continue;
		}

		if (cell->type.in(TW($xor), TW($xnor)) && kind == GRP_CONST_A) {
			SigSpec undef_a, undef_y, undef_b;
			SigSpec def_y, def_a, def_b;
			for (int j = 0; j < GetSize(new_y); j++) {
				bool undef = new_a[j] == State::Sx || new_a[j] == State::Sz;
				if (!keepdc && (undef || new_a[j] == new_b[j])) {
					undef_a.append(new_a[j]);
					if (cell->type == TW($xor))
						undef_b.append(State::S0);
					// For consistency since simplemap does $xnor -> $_XOR_ + $_NOT_
					else if (cell->type == TW($xnor))
						undef_b.append(State::S1);
					else log_abort();
					undef_y.append(new_y[j]);
				}
				else if (new_a[j] == State::S0 || new_a[j] == State::S1) {
					undef_a.append(new_a[j]);
					if (cell->type == TW($xor))
						undef_b.append(new_a[j] == State::S1 ? patcher.Not(NEW_TWINE, new_b[j]).as_bit() : new_b[j]);
					else if (cell->type == TW($xnor))
						undef_b.append(new_a[j] == State::S1 ? new_b[j] : patcher.Not(NEW_TWINE, new_b[j]).as_bit());
					else log_abort();
					undef_y.append(new_y[j]);
				}
				else {
					def_a.append(new_a[j]);
					def_b.append(new_b[j]);
					def_y.append(new_y[j]);
				}
			}
			if (!undef_y.empty()) {
				log_debug("  Direct Connection: %s (%s with %s)\n", log_signal(undef_b), cell->type.unescaped(), log_signal(undef_a));
				dict<SigBit, SigBit> remap;
				for (int j = 0; j < GetSize(undef_y); j++)
					remap[undef_y[j]] = undef_b[j];
				for (auto &entry : bit_map) {
					auto it = remap.find(entry.second);
					if (it != remap.end()) entry.second = it->second;
				}
				if (def_y.empty())
					continue;
			}
			new_a = std::move(def_a);
			new_b = std::move(def_b);
			new_y = std::move(def_y);
		}

		RTLIL::Cell *c = patcher.addCell(NEW_TWINE, cell->type_impl);

		c->setPort(TW::A, new_a);
		c->parameters[ID::A_WIDTH] = new_a.size();
		c->parameters[ID::A_SIGNED] = false;

		if (b_name == TW::B) {
			c->setPort(TW::B, new_b);
			c->parameters[ID::B_WIDTH] = new_b.size();
			c->parameters[ID::B_SIGNED] = false;
		}

		c->setPort(TW::Y, new_y);
		c->parameters[ID::Y_WIDTH] = GetSize(new_y);

		log_debug("  New cell `%s': A=%s", c, log_signal(new_a));
		if (b_name == TW::B)
			log_debug(", B=%s", log_signal(new_b));
		log_debug("\n");
	}

	// Build replacement SigSpec for cell's Y port.
	SigSpec orig_y = cell->getPort(TW::Y);
	SigSpec new_sig_y;
	for (auto bit : orig_y) {
		SigBit canon = sigmap(bit);
		auto it = bit_map.find(canon);
		new_sig_y.append(it != bit_map.end() ? it->second : bit);
	}
	patcher.patch(cell, TW::Y, new_sig_y, "group_cell_inputs");
	return true;
}

std::optional<SigBit> get_inverted_raw(SigBit s)
{
	if (!s.is_wire() || !s.wire->known_driver())
		return std::nullopt;
	Cell* cell = s.wire->driverCell();
	if (!cell->type.in(TW($_NOT_), TW($not), TW($logic_not)))
		return std::nullopt;
	if (GetSize(cell->getPort(TW::A)) != 1 || GetSize(cell->getPort(TW::Y)) != 1)
		return std::nullopt;
	return cell->getPort(TW::A);
}

std::optional<SigBit> get_inverted(SigBit s, const SigMap &assign_map)
{
	if (auto inv_a = get_inverted_raw(assign_map(s)))
		return assign_map(*inv_a);
	else
		return std::nullopt;
}

void handle_polarity_inv(Cell *cell, TwineRef port, IdString param, const SigMap &assign_map)
{
	SigSpec raw = cell->getPort(port);
	if (raw.size() != 1)
		return;
	SigBit sig = assign_map(raw);
	if (auto inv_a = get_inverted_raw(sig)) {
		SigBit new_sig = assign_map(*inv_a);
		auto twines = cell->module->design->twines;
		log_debug("Inverting %s of %s cell `%s' in module `%s': %s -> %s\n",
				twines.unescaped_str(port), cell->type.unescaped(), cell, cell->module,
				log_signal(sig), log_signal(new_sig));
		cell->setPort(port, new_sig);
		cell->setParam(param, !cell->getParam(param).as_bool());
	}
}

void handle_clkpol_celltype_swap(Cell *cell, string type1, string type2, TwineRef port, const SigMap &assign_map)
{
	log_assert(GetSize(type1) == GetSize(type2));
	string cell_type = cell->type.str();

	if (GetSize(type1) != GetSize(cell_type))
		return;

	for (int i = 0; i < GetSize(type1); i++) {
		log_assert((type1[i] == '?') == (type2[i] == '?'));
		if (type1[i] == '?') {
			if (cell_type[i] != '0' && cell_type[i] != '1' && cell_type[i] != 'N' && cell_type[i] != 'P')
				return;
			type1[i] = cell_type[i];
			type2[i] = cell_type[i];
		}
	}

	if (cell->type.in(type1, type2)) {
		SigSpec sig = assign_map(cell->getPort(port));
		auto twines = cell->module->design->twines;
		if (auto inv_a = get_inverted_raw(sig)) {
			SigSpec new_sig = assign_map(*inv_a);
			log_debug("Inverting %s of %s cell `%s' in module `%s': %s -> %s\n",
					twines.unescaped_str(port), cell->type.unescaped(), cell, cell->module,
					log_signal(sig), log_signal(new_sig));
			cell->setPort(port, new_sig);
			cell->type_impl = cell->module->design->twines.add(Twine{cell->type == type1 ? type2 : type1});
		}
	}
}

bool is_one_or_minus_one(const Const &value, bool is_signed, bool &is_negative)
{
	bool all_bits_one = true;
	bool last_bit_one = true;

	if (GetSize(value) < 1)
		return false;

	if (GetSize(value) == 1) {
		if (value[0] != State::S1)
			return false;
		if (is_signed)
			is_negative = true;
		return true;
	}

	for (int i = 0; i < GetSize(value); i++) {
		if (value[i] != State::S1)
			all_bits_one = false;
		if (value[i] != (i ? State::S0 : State::S1))
			last_bit_one = false;
	}

	if (all_bits_one && is_signed) {
		is_negative = true;
		return true;
	}

	return last_bit_one;
}

int get_highest_hot_index(RTLIL::SigSpec signal)
{
	for (int i = GetSize(signal) - 1; i >= 0; i--)
	{
		if (signal[i] == RTLIL::State::S0)
			continue;

		if (signal[i] == RTLIL::State::S1)
			return i;

		break;
	}

	return -1;
}

void replace_const_cells(RTLIL::Design *design, RTLIL::Module *module, bool consume_x, bool mux_undef, bool mux_bool, bool do_fine, bool keepdc, bool noclkinv, int timestamp=INT_MIN)
{
	SigMap assign_map; //(module);

	auto dirty_cells = module->dirty_cells(timestamp);

	if (!noclkinv)
	for (auto cell : dirty_cells)
	if (design->selected(module, cell)) {
		if (cell->type.in(TW($dff), TW($dffe), TW($dffsr), TW($dffsre), TW($adff), TW($adffe), TW($aldff), TW($aldffe), TW($sdff), TW($sdffe), TW($sdffce), TW($fsm), TW($memrd), TW($memrd_v2), TW($memwr), TW($memwr_v2)))
			handle_polarity_inv(cell, TW::CLK, ID::CLK_POLARITY, assign_map);

		if (cell->type.in(TW($sr), TW($dffsr), TW($dffsre), TW($dlatchsr))) {
			handle_polarity_inv(cell, TW::SET, ID::SET_POLARITY, assign_map);
			handle_polarity_inv(cell, TW::CLR, ID::CLR_POLARITY, assign_map);
		}

		if (cell->type.in(TW($adff), TW($adffe), TW($adlatch)))
			handle_polarity_inv(cell, TW::ARST, ID::ARST_POLARITY, assign_map);

		if (cell->type.in(TW($aldff), TW($aldffe)))
			handle_polarity_inv(cell, TW::ALOAD, ID::ALOAD_POLARITY, assign_map);

		if (cell->type.in(TW($sdff), TW($sdffe), TW($sdffce)))
			handle_polarity_inv(cell, TW::SRST, ID::SRST_POLARITY, assign_map);

		if (cell->type.in(TW($dffe), TW($adffe), TW($aldffe), TW($sdffe), TW($sdffce), TW($dffsre), TW($dlatch), TW($adlatch), TW($dlatchsr)))
			handle_polarity_inv(cell, TW::EN, ID::EN_POLARITY, assign_map);

		if (!StaticCellTypes::Compat::stdcells_mem(cell->type_impl))
			continue;

		handle_clkpol_celltype_swap(cell, "$_SR_N?_", "$_SR_P?_", TW::S, assign_map);
		handle_clkpol_celltype_swap(cell, "$_SR_?N_", "$_SR_?P_", TW::R, assign_map);

		handle_clkpol_celltype_swap(cell, "$_DFF_N_", "$_DFF_P_", TW::C, assign_map);

		handle_clkpol_celltype_swap(cell, "$_DFFE_N?_", "$_DFFE_P?_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DFFE_?N_", "$_DFFE_?P_", TW::E, assign_map);

		handle_clkpol_celltype_swap(cell, "$_DFF_N??_", "$_DFF_P??_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DFF_?N?_", "$_DFF_?P?_", TW::R, assign_map);

		handle_clkpol_celltype_swap(cell, "$_DFFE_N???_", "$_DFFE_P???_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DFFE_?N??_", "$_DFFE_?P??_", TW::R, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DFFE_???N_", "$_DFFE_???P_", TW::E, assign_map);

		handle_clkpol_celltype_swap(cell, "$_SDFF_N??_", "$_SDFF_P??_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_SDFF_?N?_", "$_SDFF_?P?_", TW::R, assign_map);

		handle_clkpol_celltype_swap(cell, "$_SDFFE_N???_", "$_SDFFE_P???_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_SDFFE_?N??_", "$_SDFFE_?P??_", TW::R, assign_map);
		handle_clkpol_celltype_swap(cell, "$_SDFFE_???N_", "$_SDFFE_???P_", TW::E, assign_map);

		handle_clkpol_celltype_swap(cell, "$_SDFFCE_N???_", "$_SDFFCE_P???_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_SDFFCE_?N??_", "$_SDFFCE_?P??_", TW::R, assign_map);
		handle_clkpol_celltype_swap(cell, "$_SDFFCE_???N_", "$_SDFFCE_???P_", TW::E, assign_map);

		handle_clkpol_celltype_swap(cell, "$_ALDFF_N?_", "$_ALDFF_P?_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_ALDFF_?N_", "$_ALDFF_?P_", TW::L, assign_map);

		handle_clkpol_celltype_swap(cell, "$_ALDFFE_N??_", "$_ALDFFE_P??_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_ALDFFE_?N?_", "$_ALDFFE_?P?_", TW::L, assign_map);
		handle_clkpol_celltype_swap(cell, "$_ALDFFE_??N_", "$_ALDFFE_??P_", TW::E, assign_map);

		handle_clkpol_celltype_swap(cell, "$_DFFSR_N??_", "$_DFFSR_P??_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DFFSR_?N?_", "$_DFFSR_?P?_", TW::S, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DFFSR_??N_", "$_DFFSR_??P_", TW::R, assign_map);

		handle_clkpol_celltype_swap(cell, "$_DFFSRE_N???_", "$_DFFSRE_P???_", TW::C, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DFFSRE_?N??_", "$_DFFSRE_?P??_", TW::S, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DFFSRE_??N?_", "$_DFFSRE_??P?_", TW::R, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DFFSRE_???N_", "$_DFFSRE_???P_", TW::E, assign_map);

		handle_clkpol_celltype_swap(cell, "$_DLATCH_N_", "$_DLATCH_P_", TW::E, assign_map);

		handle_clkpol_celltype_swap(cell, "$_DLATCH_N??_", "$_DLATCH_P??_", TW::E, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DLATCH_?N?_", "$_DLATCH_?P?_", TW::R, assign_map);

		handle_clkpol_celltype_swap(cell, "$_DLATCHSR_N??_", "$_DLATCHSR_P??_", TW::E, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DLATCHSR_?N?_", "$_DLATCHSR_?P?_", TW::S, assign_map);
		handle_clkpol_celltype_swap(cell, "$_DLATCHSR_??N_", "$_DLATCHSR_??P_", TW::R, assign_map);
	}

	TopoSort<RTLIL::Cell*, RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell>> cells;

	dict<RTLIL::SigBit, Cell*> outbit_to_cell;

	for (auto cell : dirty_cells)
	if (design->selected(module, cell) && yosys_celltypes.cell_evaluable(cell->type_impl)) {
		for (auto &conn : cell->connections())
		if (yosys_celltypes.cell_output(cell->type_impl, conn.first))
		for (auto bit : assign_map(conn.second))
			outbit_to_cell[bit] = cell;
		cells.node(cell);
	}

	for (auto cell : dirty_cells)
	if (design->selected(module, cell) && yosys_celltypes.cell_evaluable(cell->type_impl)) {
		const int r_index = cells.node(cell);
		for (auto &conn : cell->connections())
		if (yosys_celltypes.cell_input(cell->type_impl, conn.first))
		for (auto bit : assign_map(conn.second))
		if (outbit_to_cell.count(bit))
			cells.edge(cells.node(outbit_to_cell.at(bit)), r_index);
	}

	if (!cells.sort()) {
		// There might be a combinational loop, or there might be constants on the output of cells. 'check' may find out more.
		// ...unless this is a coarse-grained cell loop, but not a bit loop, in which case it won't, and all is good.
		log("Couldn't topologically sort cells, optimizing module %s may take a longer time.\n", module);
	}

	log("iterating over %d cells\n", GetSize(cells.sorted));

	for (auto cell : cells.sorted)
	{
#define ACTION_DO(_p_, _s_) do { OptExprPatcher patcher(module, &assign_map); patcher.patch(cell, _p_, _s_, input.as_string()); goto next_cell; } while (0)
#define ACTION_DO_Y(_v_) ACTION_DO(TW::Y, RTLIL::SigSpec(RTLIL::State::S ## _v_))

		bool detect_const_and = false;
		bool detect_const_or = false;

		if (cell->type.in(TW($reduce_and), TW($_AND_)))
			detect_const_and = true;

		if (cell->type.in(TW($and), TW($logic_and)) && GetSize(cell->getPort(TW::A)) == 1 && GetSize(cell->getPort(TW::B)) == 1 && !cell->getParam(ID::A_SIGNED).as_bool())
			detect_const_and = true;

		if (cell->type.in(TW($reduce_or), TW($reduce_bool), TW($_OR_)))
			detect_const_or = true;

		if (cell->type.in(TW($or), TW($logic_or)) && GetSize(cell->getPort(TW::A)) == 1 && GetSize(cell->getPort(TW::B)) == 1 && !cell->getParam(ID::A_SIGNED).as_bool())
			detect_const_or = true;

		if (detect_const_and || detect_const_or)
		{
			pool<SigBit> input_bits = assign_map(cell->getPort(TW::A)).to_sigbit_pool();
			bool found_zero = false, found_one = false, found_undef = false, found_inv = false, many_conconst = false;
			SigBit non_const_input = State::Sm;

			if (cell->hasPort(TW::B)) {
				vector<SigBit> more_bits = assign_map(cell->getPort(TW::B)).to_sigbit_vector();
				input_bits.insert(more_bits.begin(), more_bits.end());
			}

			for (auto bit : input_bits) {
				if (bit.wire) {
					if (auto inv_a = get_inverted(bit, assign_map)) {
						if (input_bits.count(*inv_a)) {
							found_inv = true;
						}
					}
					if (non_const_input != State::Sm)
						many_conconst = true;
					non_const_input = many_conconst ? State::Sm : bit;
				} else {
					if (bit == State::S0)
						found_zero = true;
					else if (bit == State::S1)
						found_one = true;
					else
						found_undef = true;
				}
			}

			if (detect_const_and && (found_zero || found_inv || (found_undef && consume_x))) {
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, RTLIL::State::S0, "const_and");
				goto next_cell;
			}

			if (detect_const_or && (found_one || found_inv || (found_undef && consume_x))) {
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, RTLIL::State::S1, "const_or");
				goto next_cell;
			}

			if (non_const_input != State::Sm && !found_undef) {
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, non_const_input, "and_or_buffer");
				goto next_cell;
			}
		}

		if (cell->type.in(TW($_XOR_), TW($_XNOR_)) || (cell->type.in(TW($xor), TW($xnor)) && GetSize(cell->getPort(TW::A)) == 1 && GetSize(cell->getPort(TW::B)) == 1 && !cell->getParam(ID::A_SIGNED).as_bool()))
		{
			SigBit sig_a = assign_map(cell->getPort(TW::A));
			SigBit sig_b = assign_map(cell->getPort(TW::B));
			if (!keepdc && (sig_a == sig_b || sig_a == State::Sx || sig_a == State::Sz || sig_b == State::Sx || sig_b == State::Sz)) {
				OptExprPatcher patcher(module, &assign_map);
				if (cell->type.in(TW($xor), TW($_XOR_))) {
					patcher.patch(cell, TW::Y, RTLIL::State::S0, "const_xor");
					goto next_cell;
				}
				if (cell->type.in(TW($xnor), TW($_XNOR_))) {
					// For consistency since simplemap does $xnor -> $_XOR_ + $_NOT_
					int width = GetSize(cell->getPort(TW::Y));
					patcher.patch(cell, TW::Y, SigSpec(RTLIL::State::S1, width), "const_xnor");
					goto next_cell;
				}
				log_abort();
			}

			if (!sig_a.wire)
				std::swap(sig_a, sig_b);
			if (sig_b == State::S0 || sig_b == State::S1) {
				OptExprPatcher patcher(module, &assign_map);
				bool is_gate = cell->type.in(TW($_XOR_), TW($_XNOR_));
				int width = is_gate ? 1 : cell->getParam(ID::Y_WIDTH).as_int();
				if (cell->type.in(TW($xor), TW($_XOR_))) {
					if (sig_b == State::S0) {
						SigSpec sig_y = sig_a;
						sig_y.append(RTLIL::Const(State::S0, width-1));
						patcher.patch(cell, TW::Y, sig_y, "xor_buffer");
					} else {
						SigSpec sig_y = is_gate ? (SigSpec)patcher.NotGate(NEW_TWINE, sig_a) : patcher.Not(NEW_TWINE, sig_a);
						sig_y.append(RTLIL::Const(State::S0, width-1));
						patcher.patch(cell, TW::Y, sig_y, "xor_buffer");
					}
					goto next_cell;
				}
				if (cell->type.in(TW($xnor), TW($_XNOR_))) {
					if (sig_b == State::S1) {
						SigSpec sig_y = sig_a;
						sig_y.append(RTLIL::Const(State::S1, width-1));
						patcher.patch(cell, TW::Y, sig_y, "xnor_buffer");
					} else {
						SigSpec sig_y = is_gate ? (SigSpec)patcher.NotGate(NEW_TWINE, sig_a) : patcher.Not(NEW_TWINE, sig_a);
						sig_y.append(RTLIL::Const(State::S1, width-1));
						patcher.patch(cell, TW::Y, sig_y, "xnor_buffer");
					}
					goto next_cell;
				}
				log_abort();
			}
		}

		if (cell->type.in(TW($reduce_and), TW($reduce_or), TW($reduce_bool), TW($reduce_xor), TW($reduce_xnor), TW($neg)) &&
				GetSize(cell->getPort(TW::A)) == 1 && GetSize(cell->getPort(TW::Y)) == 1)
		{
			if (cell->type == TW($reduce_xnor)) {
				log_debug("Replacing %s cell `%s' in module `%s' with $not cell.\n",
						cell->type.unescape(), cell->module->design->twines.str(cell->meta_->name), module);
				cell->type_impl = TW::$not;
				did_something = true;
			} else {
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, cell->getPort(TW::A), "unary_buffer");
			}
			goto next_cell;
		}

		if (cell->type.in(TW($and), TW($or), TW($xor), TW($xnor)))
		{
			RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));
			RTLIL::SigSpec sig_b = assign_map(cell->getPort(TW::B));

			bool a_fully_const = (sig_a.is_fully_const() && (!keepdc || !sig_a.is_fully_undef()));
			bool b_fully_const = (sig_b.is_fully_const() && (!keepdc || !sig_b.is_fully_undef()));

			if (a_fully_const != b_fully_const)
			{
				log_debug("Replacing %s cell `%s' in module `%s' having one fully constant input\n",
						cell->type.unescape(), cell->module->design->twines.str(cell->meta_->name), module);
				RTLIL::SigSpec sig_y = assign_map(cell->getPort(TW::Y));

				int width = GetSize(cell->getPort(TW::Y));

				sig_a.extend_u0(width, cell->getParam(ID::A_SIGNED).as_bool());
				sig_b.extend_u0(width, cell->getParam(ID::B_SIGNED).as_bool());

				if (!a_fully_const)
					std::swap(sig_a, sig_b);

				RTLIL::SigSpec b_group_0, b_group_1, b_group_x;
				// Per-i (group, position_in_group); group = -1 means leave as Sx
				std::vector<std::pair<int, int>> origin(width, {-1, 0});

				auto group_0 = cell->type == TW($xnor) ? 1 : 0;
				auto group_1 = cell->type == TW($xnor) ? 0 : 1;

				for (int i = 0; i < width; i++) {
					auto bit_a = sig_a[i].data;
					if (bit_a == State::S0) origin[i] = {group_0, b_group_0.size()}, b_group_0.append(sig_b[i]);
					else if (bit_a == State::S1) origin[i] = {group_1, b_group_1.size()}, b_group_1.append(sig_b[i]);
					else if (bit_a == State::Sx) origin[i] = {2, b_group_x.size()}, b_group_x.append(sig_b[i]);
				}

				if (cell->type == TW($xnor))
					std::swap(b_group_0, b_group_1);

				OptExprPatcher patcher(module, &assign_map);
				RTLIL::SigSpec y_new_0, y_new_1, y_new_x;

				if (cell->type == TW($and)) {
					if (!b_group_0.empty()) y_new_0 = Const(State::S0, GetSize(b_group_0));
					if (!b_group_1.empty()) y_new_1 = b_group_1;
					if (!b_group_x.empty()) {
						if (keepdc)
							y_new_x = patcher.And(NEW_TWINE, Const(State::Sx, GetSize(b_group_x)), b_group_x);
						else
							y_new_x = Const(State::S0, GetSize(b_group_x));
					}
				} else if (cell->type == TW($or)) {
					if (!b_group_0.empty()) y_new_0 = b_group_0;
					if (!b_group_1.empty()) y_new_1 = Const(State::S1, GetSize(b_group_1));
					if (!b_group_x.empty()) {
						if (keepdc)
							y_new_x = patcher.Or(NEW_TWINE, Const(State::Sx, GetSize(b_group_x)), b_group_x);
						else
							y_new_x = Const(State::S1, GetSize(b_group_x));
					}
				} else if (cell->type.in(TW($xor), TW($xnor))) {
					if (!b_group_0.empty()) y_new_0 = b_group_0;
					if (!b_group_1.empty()) y_new_1 = patcher.Not(NEW_TWINE, b_group_1);
					if (!b_group_x.empty()) {
						if (keepdc)
							y_new_x = patcher.Xor(NEW_TWINE, Const(State::Sx, GetSize(b_group_x)), b_group_x);
						else // This should be fine even with keepdc, but opt_expr_xor.ys wants to keep the xor
							y_new_x = Const(State::Sx, GetSize(b_group_x));
					}
				} else {
					log_abort();
				}

				RTLIL::SigSpec new_sig_y(State::Sx, width);
				for (int i = 0; i < width; i++) {
					if (origin[i].first == 0) new_sig_y[i] = y_new_0[origin[i].second];
					else if (origin[i].first == 1) new_sig_y[i] = y_new_1[origin[i].second];
					else if (origin[i].first == 2) new_sig_y[i] = y_new_x[origin[i].second];
					// else: bit_a was Sz / Sa / etc.; leave as Sx
				}
				patcher.patch(cell, TW::Y, new_sig_y, "bit_partition");
				goto next_cell;
			}
		}

		if (cell->type == TW($bwmux))
		{
			RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));
			RTLIL::SigSpec sig_b = assign_map(cell->getPort(TW::B));
			RTLIL::SigSpec sig_s = assign_map(cell->getPort(TW::S));
			RTLIL::SigSpec sig_y = assign_map(cell->getPort(TW::Y));
			int width = GetSize(cell->getPort(TW::Y));

			if (sig_s.is_fully_def())
			{
				RTLIL::SigSpec new_sig_y(width);
				for (int i = 0; i < width; i++)
					new_sig_y[i] = sig_s[i].data == State::S1 ? sig_b[i] : sig_a[i];
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, new_sig_y, "bwmux_const_s");
				goto next_cell;
			}
			else if (sig_a.is_fully_def() || sig_b.is_fully_def())
			{
				bool flip = !sig_a.is_fully_def();
				if (flip)
					std::swap(sig_a, sig_b);

				RTLIL::SigSpec b_group_0, b_group_1;
				RTLIL::SigSpec s_group_0, s_group_1;
				std::vector<std::pair<int, int>> origin(width);
				for (int i = 0; i < width; i++) {
					if (sig_a[i].data == State::S1) {
						origin[i] = {1, b_group_1.size()};
						b_group_1.append(sig_b[i]), s_group_1.append(sig_s[i]);
					} else {
						origin[i] = {0, b_group_0.size()};
						b_group_0.append(sig_b[i]), s_group_0.append(sig_s[i]);
					}
				}

				OptExprPatcher patcher(module, &assign_map);
				RTLIL::SigSpec y_new_0, y_new_1;

				if (flip) {
					if (!b_group_0.empty()) y_new_0 = patcher.And(NEW_TWINE, b_group_0, patcher.Not(NEW_TWINE, s_group_0));
					if (!b_group_1.empty()) y_new_1 = patcher.Or(NEW_TWINE, b_group_1, s_group_1);
				} else {
					if (!b_group_0.empty()) y_new_0 = patcher.And(NEW_TWINE, b_group_0, s_group_0);
					if (!b_group_1.empty()) y_new_1 = patcher.Or(NEW_TWINE, b_group_1, patcher.Not(NEW_TWINE, s_group_1));
				}

				RTLIL::SigSpec new_sig_y(width);
				for (int i = 0; i < width; i++)
					new_sig_y[i] = origin[i].first == 1 ? y_new_1[origin[i].second] : y_new_0[origin[i].second];
				patcher.patch(cell, TW::Y, new_sig_y, "bwmux_const_ab");
				goto next_cell;
			}
		}

		if (do_fine)
		{
			if (cell->type.in(TW($not), TW($pos), TW($and), TW($or), TW($xor), TW($xnor)))
				if (group_cell_inputs(module, cell, true, assign_map, keepdc))
					goto next_cell;

			if (cell->type.in(TW($logic_not), TW($logic_and), TW($logic_or), TW($reduce_or), TW($reduce_and), TW($reduce_bool)))
			{
				SigBit neutral_bit = cell->type == TW($reduce_and) ? State::S1 : State::S0;

				RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));
				RTLIL::SigSpec new_sig_a;

				for (auto bit : sig_a)
					if (bit != neutral_bit) new_sig_a.append(bit);

				if (GetSize(new_sig_a) == 0)
					new_sig_a.append(neutral_bit);

				if (GetSize(new_sig_a) < GetSize(sig_a)) {
					log_debug("Replacing port A of %s cell `%s' in module `%s' with shorter expression: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str(), log_signal(sig_a), log_signal(new_sig_a));
					cell->setPort(TW::A, new_sig_a);
					cell->parameters.at(ID::A_WIDTH) = GetSize(new_sig_a);
					did_something = true;
				}
			}

			if (cell->type.in(TW($logic_and), TW($logic_or)))
			{
				SigBit neutral_bit = State::S0;

				RTLIL::SigSpec sig_b = assign_map(cell->getPort(TW::B));
				RTLIL::SigSpec new_sig_b;

				for (auto bit : sig_b)
					if (bit != neutral_bit) new_sig_b.append(bit);

				if (GetSize(new_sig_b) == 0)
					new_sig_b.append(neutral_bit);

				if (GetSize(new_sig_b) < GetSize(sig_b)) {
					log_debug("Replacing port B of %s cell `%s' in module `%s' with shorter expression: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str(), log_signal(sig_b), log_signal(new_sig_b));
					cell->setPort(TW::B, new_sig_b);
					cell->parameters.at(ID::B_WIDTH) = GetSize(new_sig_b);
					did_something = true;
				}
			}

			if (cell->type == TW($reduce_and))
			{
				RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));

				RTLIL::State new_a = RTLIL::State::S1;
				for (auto &bit : sig_a.to_sigbit_vector())
					if (bit == RTLIL::State::Sx) {
						if (new_a == RTLIL::State::S1)
							new_a = RTLIL::State::Sx;
					} else if (bit == RTLIL::State::S0) {
						new_a = RTLIL::State::S0;
						break;
					} else if (bit.wire != NULL) {
						new_a = RTLIL::State::Sm;
					}

				if (new_a != RTLIL::State::Sm && RTLIL::SigSpec(new_a) != sig_a) {
					log_debug("Replacing port A of %s cell `%s' in module `%s' with constant driver: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str(), log_signal(sig_a), log_signal(new_a));
					cell->setPort(TW::A, sig_a = new_a);
					cell->parameters.at(ID::A_WIDTH) = 1;
					did_something = true;
				}
			}

			if (cell->type.in(TW($logic_not), TW($logic_and), TW($logic_or), TW($reduce_or), TW($reduce_bool)))
			{
				RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));

				RTLIL::State new_a = RTLIL::State::S0;
				for (auto &bit : sig_a.to_sigbit_vector())
					if (bit == RTLIL::State::Sx) {
						if (new_a == RTLIL::State::S0)
							new_a = RTLIL::State::Sx;
					} else if (bit == RTLIL::State::S1) {
						new_a = RTLIL::State::S1;
						break;
					} else if (bit.wire != NULL) {
						new_a = RTLIL::State::Sm;
					}

				if (new_a != RTLIL::State::Sm && RTLIL::SigSpec(new_a) != sig_a) {
					log_debug("Replacing port A of %s cell `%s' in module `%s' with constant driver: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str(), log_signal(sig_a), log_signal(new_a));
					cell->setPort(TW::A, sig_a = new_a);
					cell->parameters.at(ID::A_WIDTH) = 1;
					did_something = true;
				}
			}

			if (cell->type.in(TW($logic_and), TW($logic_or)))
			{
				RTLIL::SigSpec sig_b = assign_map(cell->getPort(TW::B));

				RTLIL::State new_b = RTLIL::State::S0;
				for (auto &bit : sig_b.to_sigbit_vector())
					if (bit == RTLIL::State::Sx) {
						if (new_b == RTLIL::State::S0)
							new_b = RTLIL::State::Sx;
					} else if (bit == RTLIL::State::S1) {
						new_b = RTLIL::State::S1;
						break;
					} else if (bit.wire != NULL) {
						new_b = RTLIL::State::Sm;
					}

				if (new_b != RTLIL::State::Sm && RTLIL::SigSpec(new_b) != sig_b) {
					log_debug("Replacing port B of %s cell `%s' in module `%s' with constant driver: %s -> %s\n",
							cell->type.c_str(), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str(), log_signal(sig_b), log_signal(new_b));
					cell->setPort(TW::B, sig_b = new_b);
					cell->parameters.at(ID::B_WIDTH) = 1;
					did_something = true;
				}
			}

			if (cell->type.in(TW($add), TW($sub)))
			{
				RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));
				RTLIL::SigSpec sig_b = assign_map(cell->getPort(TW::B));
				RTLIL::SigSpec sig_y = cell->getPort(TW::Y);
				bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
				bool sub = cell->type == TW($sub);

				int minsz = GetSize(sig_y);
				minsz = std::min(minsz, GetSize(sig_a));
				minsz = std::min(minsz, GetSize(sig_b));

				int i;
				for (i = 0; i < minsz; i++) {
					RTLIL::SigBit b = sig_b[i];
					RTLIL::SigBit a = sig_a[i];
					if (b == State::S0)
						module->connect(sig_y[i], a);
					else if (sub && b == State::S1 && a == State::S1)
						module->connect(sig_y[i], State::S0);
					else if (!sub && a == State::S0)
						module->connect(sig_y[i], b);
					else
						break;
				}
				if (i > 0) {
					log_debug("Stripping %d LSB bits of %s cell %s in module %s.\n", i, cell->type.unescaped(), cell, module);
					SigSpec new_a = sig_a.extract_end(i);
					SigSpec new_b = sig_b.extract_end(i);
					if (new_a.empty() && is_signed)
						new_a = sig_a[i-1];
					if (new_b.empty() && is_signed)
						new_b = sig_b[i-1];
					cell->setPort(TW::A, new_a);
					cell->setPort(TW::B, new_b);
					cell->setPort(TW::Y, sig_y.extract_end(i));
					cell->fixup_parameters();
					did_something = true;
				}
			}

			if (cell->type == TW($alu))
			{
				RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));
				RTLIL::SigSpec sig_b = assign_map(cell->getPort(TW::B));
				RTLIL::SigBit sig_ci = assign_map(cell->getPort(TW::CI));
				RTLIL::SigBit sig_bi = assign_map(cell->getPort(TW::BI));
				RTLIL::SigSpec sig_x = cell->getPort(TW::X);
				RTLIL::SigSpec sig_y = cell->getPort(TW::Y);
				RTLIL::SigSpec sig_co = cell->getPort(TW::CO);
				bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();

				if (sig_bi != State::S0 && sig_bi != State::S1)
					goto skip_fine_alu;
				if (sig_ci != State::S0 && sig_ci != State::S1)
					goto skip_fine_alu;

				bool bi = sig_bi == State::S1;
				bool ci = sig_ci == State::S1;

				int minsz = GetSize(sig_y);
				minsz = std::min(minsz, GetSize(sig_a));
				minsz = std::min(minsz, GetSize(sig_b));

				int i;
				for (i = 0; i < minsz; i++) {
					RTLIL::SigBit b = sig_b[i];
					RTLIL::SigBit a = sig_a[i];
					if (b == ((bi ^ ci) ? State::S1 : State::S0)) {
						module->connect(sig_y[i], a);
						module->connect(sig_x[i], ci ? module->Not(NEW_TWINE, a).as_bit() : a);
						module->connect(sig_co[i], ci ? State::S1 : State::S0);
					}
					else if (a == (ci ? State::S1 : State::S0)) {
						module->connect(sig_y[i], bi ? module->Not(NEW_TWINE, b).as_bit() : b);
						module->connect(sig_x[i], (bi ^ ci) ? module->Not(NEW_TWINE, b).as_bit() : b);
						module->connect(sig_co[i], ci ? State::S1 : State::S0);
					}
					else
						break;
				}
				if (i > 0) {
					log_debug("Stripping %d LSB bits of %s cell %s in module %s.\n", i, cell->type.unescaped(), cell, module);
					SigSpec new_a = sig_a.extract_end(i);
					SigSpec new_b = sig_b.extract_end(i);
					if (new_a.empty() && is_signed)
						new_a = sig_a[i-1];
					if (new_b.empty() && is_signed)
						new_b = sig_b[i-1];
					cell->setPort(TW::A, new_a);
					cell->setPort(TW::B, new_b);
					cell->setPort(TW::X, sig_x.extract_end(i));
					cell->setPort(TW::Y, sig_y.extract_end(i));
					cell->setPort(TW::CO, sig_co.extract_end(i));
					cell->fixup_parameters();
					did_something = true;
				}
			}
		}
skip_fine_alu:

		if (cell->type.in(TW($reduce_xor), TW($reduce_xnor), TW($shift), TW($shiftx), TW($shl), TW($shr), TW($sshl), TW($sshr),
					TW($lt), TW($le), TW($ge), TW($gt), TW($neg), TW($add), TW($sub), TW($mul), TW($div), TW($mod), TW($divfloor), TW($modfloor), TW($pow)))
		{
			RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));
			RTLIL::SigSpec sig_b = cell->hasPort(TW::B) ? assign_map(cell->getPort(TW::B)) : RTLIL::SigSpec();

			if (cell->type.in(TW($shl), TW($shr), TW($sshl), TW($sshr), TW($shift), TW($shiftx)))
				sig_a = RTLIL::SigSpec();

			for (auto &bit : sig_a.to_sigbit_vector())
				if (bit == RTLIL::State::Sx)
					goto found_the_x_bit;

			for (auto &bit : sig_b.to_sigbit_vector())
				if (bit == RTLIL::State::Sx)
					goto found_the_x_bit;

			if (0) {
		found_the_x_bit:
				OptExprPatcher patcher(module, &assign_map);
				if (cell->type.in(TW($reduce_xor), TW($reduce_xnor), TW($lt), TW($le), TW($ge), TW($gt)))
					patcher.patch(cell, TW::Y, RTLIL::State::Sx, "x-bit in input");
				else
					patcher.patch(cell, TW::Y, RTLIL::SigSpec(RTLIL::State::Sx, GetSize(cell->getPort(TW::Y))), "x-bit in input");
				goto next_cell;
			}
		}

		if (cell->type.in(TW($shiftx), TW($shift)) && (cell->type == TW($shiftx) || !cell->getParam(ID::A_SIGNED).as_bool())) {
			SigSpec sig_a = assign_map(cell->getPort(TW::A));
			int width;
			bool trim_x = cell->type == TW($shiftx) || !keepdc;
			bool trim_0 = cell->type == TW($shift);
			for (width = GetSize(sig_a); width > 1; width--) {
				if ((trim_x && sig_a[width-1] == State::Sx) ||
					(trim_0 && sig_a[width-1] == State::S0))
					continue;
				break;
			}

			if (width < GetSize(sig_a)) {
				sig_a.remove(width, GetSize(sig_a)-width);
				cell->setPort(TW::A, sig_a);
				cell->setParam(ID::A_WIDTH, width);
				did_something = true;
				goto next_cell;
			}
		}

		if (cell->type.in(TW($_NOT_), TW($not), TW($logic_not)) && GetSize(cell->getPort(TW::Y)) == 1 && GetSize(cell->getPort(TW::A)) == 1) {
			if (auto inv_a = get_inverted(cell->getPort(TW::A), assign_map)) {
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, *inv_a, "double_invert");
				goto next_cell;
			}
		}

		if (cell->type.in(TW($_MUX_), TW($mux))) {
			if (auto inv_a = get_inverted(cell->getPort(TW::S), assign_map)) {
				log_debug("Optimizing away select inverter for %s cell `%s' in module `%s'.\n", cell->type.unescaped(), cell, module);
				RTLIL::SigSpec tmp = cell->getPort(TW::A);
				cell->setPort(TW::A, cell->getPort(TW::B));
				cell->setPort(TW::B, tmp);
				cell->setPort(TW::S, *inv_a);
				did_something = true;
				goto next_cell;
			}
		}

		if (cell->type == TW($_NOT_)) {
			RTLIL::SigSpec input = cell->getPort(TW::A);
			assign_map.apply(input);
			if (input.match("1")) ACTION_DO_Y(0);
			if (input.match("0")) ACTION_DO_Y(1);
			if (input.match("*")) ACTION_DO_Y(x);
		}

		if (cell->type == TW($_AND_)) {
			RTLIL::SigSpec input;
			input.append(cell->getPort(TW::B));
			input.append(cell->getPort(TW::A));
			assign_map.apply(input);
			if (input.match(" 0")) ACTION_DO_Y(0);
			if (input.match("0 ")) ACTION_DO_Y(0);
			if (input.match("11")) ACTION_DO_Y(1);
			if (input.match("**")) ACTION_DO_Y(x);
			if (input.match("1*")) ACTION_DO_Y(x);
			if (input.match("*1")) ACTION_DO_Y(x);
			if (consume_x) {
				if (input.match(" *")) ACTION_DO_Y(0);
				if (input.match("* ")) ACTION_DO_Y(0);
			}
			if (input.match(" 1")) ACTION_DO(TW::Y, input.extract(1, 1));
			if (input.match("1 ")) ACTION_DO(TW::Y, input.extract(0, 1));
		}

		if (cell->type == TW($_OR_)) {
			RTLIL::SigSpec input;
			input.append(cell->getPort(TW::B));
			input.append(cell->getPort(TW::A));
			assign_map.apply(input);
			if (input.match(" 1")) ACTION_DO_Y(1);
			if (input.match("1 ")) ACTION_DO_Y(1);
			if (input.match("00")) ACTION_DO_Y(0);
			if (input.match("**")) ACTION_DO_Y(x);
			if (input.match("0*")) ACTION_DO_Y(x);
			if (input.match("*0")) ACTION_DO_Y(x);
			if (consume_x) {
				if (input.match(" *")) ACTION_DO_Y(1);
				if (input.match("* ")) ACTION_DO_Y(1);
			}
			if (input.match(" 0")) ACTION_DO(TW::Y, input.extract(1, 1));
			if (input.match("0 ")) ACTION_DO(TW::Y, input.extract(0, 1));
		}

		if (cell->type == TW($_XOR_)) {
			RTLIL::SigSpec input;
			input.append(cell->getPort(TW::B));
			input.append(cell->getPort(TW::A));
			assign_map.apply(input);
			if (input.match("00")) ACTION_DO_Y(0);
			if (input.match("01")) ACTION_DO_Y(1);
			if (input.match("10")) ACTION_DO_Y(1);
			if (input.match("11")) ACTION_DO_Y(0);
			if (consume_x) {
				if (input.match(" *")) ACTION_DO_Y(0);
				if (input.match("* ")) ACTION_DO_Y(0);
			}
		}

		if (cell->type == TW($_MUX_)) {
			RTLIL::SigSpec input;
			input.append(cell->getPort(TW::S));
			input.append(cell->getPort(TW::B));
			input.append(cell->getPort(TW::A));
			assign_map.apply(input);
			if (input.extract(2, 1) == input.extract(1, 1))
				ACTION_DO(TW::Y, input.extract(2, 1));
			if (input.match("  0")) ACTION_DO(TW::Y, input.extract(2, 1));
			if (input.match("  1")) ACTION_DO(TW::Y, input.extract(1, 1));
			if (input.match("01 ")) ACTION_DO(TW::Y, input.extract(0, 1));
			if (input.match("10 ")) {
				cell->setPort(TW::A, input.extract(0, 1));
				cell->unsetPort(TW::B);
				cell->unsetPort(TW::S);
				cell->type_impl = TW::$_NOT_;
				goto next_cell;
			}
			if (input.match("11 ")) ACTION_DO_Y(1);
			if (input.match("00 ")) ACTION_DO_Y(0);
			if (input.match("** ")) ACTION_DO_Y(x);
			if (input.match("01*")) ACTION_DO_Y(x);
			if (input.match("10*")) ACTION_DO_Y(x);
			if (mux_undef) {
				if (input.match("*  ")) ACTION_DO(TW::Y, input.extract(1, 1));
				if (input.match(" * ")) ACTION_DO(TW::Y, input.extract(2, 1));
				if (input.match("  *")) ACTION_DO(TW::Y, input.extract(2, 1));
			}
		}

		if (cell->type.in(TW($_TBUF_), TW($tribuf))) {
			RTLIL::SigSpec input = cell->getPort(cell->type == TW($_TBUF_) ? TW::E : TW::EN);
			RTLIL::SigSpec a = cell->getPort(TW::A);
			assign_map.apply(input);
			assign_map.apply(a);
			if (input == State::S1)
				ACTION_DO(TW::Y, cell->getPort(TW::A));
			if (input == State::S0 && !a.is_fully_undef()) {
				log_debug("Replacing data input of %s cell `%s' in module `%s' with constant undef.\n",
					cell->type.c_str(), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str());
				cell->setPort(TW::A, SigSpec(State::Sx, GetSize(a)));
				did_something = true;
				goto next_cell;
			}
		}

		if (cell->type.in(TW($eq), TW($ne), TW($eqx), TW($nex)))
		{
			RTLIL::SigSpec a = cell->getPort(TW::A);
			RTLIL::SigSpec b = cell->getPort(TW::B);

			if (cell->parameters[ID::A_WIDTH].as_int() != cell->parameters[ID::B_WIDTH].as_int()) {
				int width = max(cell->parameters[ID::A_WIDTH].as_int(), cell->parameters[ID::B_WIDTH].as_int());
				a.extend_u0(width, cell->parameters[ID::A_SIGNED].as_bool() && cell->parameters[ID::B_SIGNED].as_bool());
				b.extend_u0(width, cell->parameters[ID::A_SIGNED].as_bool() && cell->parameters[ID::B_SIGNED].as_bool());
			}

			RTLIL::SigSpec new_a, new_b;

			log_assert(GetSize(a) == GetSize(b));
			for (int i = 0; i < GetSize(a); i++) {
				if (a[i].wire == NULL && b[i].wire == NULL && a[i] != b[i] && a[i].data <= RTLIL::State::S1 && b[i].data <= RTLIL::State::S1) {
					RTLIL::SigSpec new_y = RTLIL::SigSpec(cell->type.in(TW($eq), TW($eqx)) ?  RTLIL::State::S0 : RTLIL::State::S1);
					new_y.extend_u0(cell->parameters[ID::Y_WIDTH].as_int(), false);
					OptExprPatcher patcher(module, &assign_map);
					patcher.patch(cell, TW::Y, new_y, "isneq");
					goto next_cell;
				}
				if (keepdc) {
					if (!a[i].is_wire() && !b[i].is_wire() && a[i].data != RTLIL::State::Sx && b[i].data != RTLIL::State::Sx && a[i] == b[i])
						continue;
				} else {
					if (a[i] == b[i])
						continue;
				}
				new_a.append(a[i]);
				new_b.append(b[i]);
			}

			if (new_a.size() == 0) {
				RTLIL::SigSpec new_y = RTLIL::SigSpec(cell->type.in(TW($eq), TW($eqx)) ?  RTLIL::State::S1 : RTLIL::State::S0);
				new_y.extend_u0(cell->parameters[ID::Y_WIDTH].as_int(), false);
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, new_y, "empty");
				goto next_cell;
			}

			if (new_a.size() < a.size() || new_b.size() < b.size()) {
				cell->setPort(TW::A, new_a);
				cell->setPort(TW::B, new_b);
				cell->parameters[ID::A_WIDTH] = new_a.size();
				cell->parameters[ID::B_WIDTH] = new_b.size();
			}
		}

		if (cell->type.in(TW($eq), TW($ne)) && cell->parameters[ID::Y_WIDTH].as_int() == 1 &&
				cell->parameters[ID::A_WIDTH].as_int() == 1 && cell->parameters[ID::B_WIDTH].as_int() == 1)
		{
			RTLIL::SigSpec a = assign_map(cell->getPort(TW::A));
			RTLIL::SigSpec b = assign_map(cell->getPort(TW::B));

			if (a.is_fully_const() && !b.is_fully_const()) {
				cell->setPort(TW::A, b);
				cell->setPort(TW::B, a);
				std::swap(a, b);
			}

			if (b.is_fully_const()) {
				if (b.is_fully_undef()) {
					RTLIL::SigSpec input = b;
					ACTION_DO(TW::Y, Const(State::Sx, GetSize(cell->getPort(TW::Y))));
				} else
				if (b.as_bool() == (cell->type == TW($eq))) {
					RTLIL::SigSpec input = b;
					ACTION_DO(TW::Y, cell->getPort(TW::A));
				} else {
					log_debug("Replacing %s cell `%s' in module `%s' with inverter.\n", cell->type.unescaped(), cell, module);
					cell->parameters.erase(ID::B_WIDTH);
					cell->parameters.erase(ID::B_SIGNED);
					cell->unsetPort(TW::B);
					cell->type_impl = TW::$not;
					did_something = true;
				}
				goto next_cell;
			}
		}

		if (cell->type.in(TW($eq), TW($ne)) &&
				(assign_map(cell->getPort(TW::A)).is_fully_zero() || assign_map(cell->getPort(TW::B)).is_fully_zero()))
		{
			log_debug("Replacing %s cell `%s' in module `%s' with %s.\n", cell->type.unescaped(), cell,
					module, cell->type == TW($eq) ? "$logic_not" : "$reduce_bool");
			if (assign_map(cell->getPort(TW::A)).is_fully_zero()) {
				cell->setPort(TW::A, cell->getPort(TW::B));
				cell->setParam(ID::A_SIGNED, cell->getParam(ID::B_SIGNED));
				cell->setParam(ID::A_WIDTH, cell->getParam(ID::B_WIDTH));
			}
			cell->unsetPort(TW::B);
			cell->unsetParam(ID::B_SIGNED);
			cell->unsetParam(ID::B_WIDTH);
			cell->type_impl = (cell->type == TW($eq)) ? TW::$logic_not : TW::$reduce_bool;
			did_something = true;
			goto next_cell;
		}

		if (cell->type.in(TW($shl), TW($shr), TW($sshl), TW($sshr), TW($shift), TW($shiftx)) && (keepdc ? assign_map(cell->getPort(TW::B)).is_fully_def() : assign_map(cell->getPort(TW::B)).is_fully_const()))
		{
			bool sign_ext = cell->type == TW($sshr) && cell->getParam(ID::A_SIGNED).as_bool();
			RTLIL::SigSpec sig_b = assign_map(cell->getPort(TW::B));
			const bool b_sign_ext = cell->type.in(TW($shift), TW($shiftx)) && cell->getParam(ID::B_SIGNED).as_bool();
			// We saturate the value to prevent overflow, but note that this could
			// cause incorrect opimization in the impractical case that A is 2^32 bits
			// wide
			int shift_bits = sig_b.as_int_saturating(b_sign_ext);

			if (cell->type.in(TW($shl), TW($sshl)))
				shift_bits *= -1;

			RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));
			RTLIL::SigSpec sig_y(cell->type == TW($shiftx) ? RTLIL::State::Sx : RTLIL::State::S0, cell->getParam(ID::Y_WIDTH).as_int());

			if (cell->type != TW($shiftx) && GetSize(sig_a) < GetSize(sig_y))
				sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());

			// Limit indexing to the size of a, which is behaviourally identical (result is all 0)
			// and avoids integer overflow of i + shift_bits when e.g. ID::B == INT_MAX.
			// We do this after sign-extending a so this accounts for the output size
			shift_bits = min(shift_bits, GetSize(sig_a));

			for (int i = 0; i < GetSize(sig_y); i++) {
				int idx = i + shift_bits;
				if (0 <= idx && idx < GetSize(sig_a))
					sig_y[i] = sig_a[idx];
				else if (GetSize(sig_a) <= idx && sign_ext)
					sig_y[i] = sig_a[GetSize(sig_a)-1];
			}

			log_debug("Replacing %s cell `%s' (B=%s, SHR=%d) in module `%s' with fixed wiring: %s\n",
					cell->type.unescape(), cell, log_signal(assign_map(cell->getPort(TW::B))), shift_bits, module, log_signal(sig_y));

			OptExprPatcher patcher(module, &assign_map);
			patcher.patch(cell, TW::Y, sig_y, "shift_const");
			goto next_cell;
		}

		if (consume_x)
		{
			bool identity_wrt_a = false;
			bool identity_wrt_b = false;
			bool arith_inverse = false;

			if (cell->type.in(TW($add), TW($sub), TW($alu), TW($or), TW($xor)))
			{
				RTLIL::SigSpec a = assign_map(cell->getPort(TW::A));
				RTLIL::SigSpec b = assign_map(cell->getPort(TW::B));

				bool sub = cell->type == TW($sub);

				if (cell->type == TW($alu)) {
					RTLIL::SigBit sig_ci = assign_map(cell->getPort(TW::CI));
					RTLIL::SigBit sig_bi = assign_map(cell->getPort(TW::BI));

					sub = (sig_ci == State::S1 && sig_bi == State::S1);

					// If not a subtraction, yet there is a carry or B is inverted
					//   then no optimisation is possible as carry will not be constant
					if (!sub && (sig_ci != State::S0 || sig_bi != State::S0))
						goto skip_identity;
				}

				if (!sub && a.is_fully_const() && a.as_bool() == false)
					identity_wrt_b = true;

				if (b.is_fully_const() && b.as_bool() == false)
					identity_wrt_a = true;
			}

			if (cell->type.in(TW($shl), TW($shr), TW($sshl), TW($sshr), TW($shift), TW($shiftx)))
			{
				RTLIL::SigSpec b = assign_map(cell->getPort(TW::B));

				if (b.is_fully_const() && b.as_bool() == false)
					identity_wrt_a = true;
			}

			if (cell->type == TW($mul))
			{
				RTLIL::SigSpec a = assign_map(cell->getPort(TW::A));
				RTLIL::SigSpec b = assign_map(cell->getPort(TW::B));

				if (a.is_fully_const() && is_one_or_minus_one(a.as_const(), cell->getParam(ID::A_SIGNED).as_bool(), arith_inverse))
					identity_wrt_b = true;
				else
				if (b.is_fully_const() && is_one_or_minus_one(b.as_const(), cell->getParam(ID::B_SIGNED).as_bool(), arith_inverse))
					identity_wrt_a = true;
			}

			if (cell->type == TW($div))
			{
				RTLIL::SigSpec b = assign_map(cell->getPort(TW::B));

				if (b.is_fully_const() && b.size() <= 32 && b.as_int() == 1)
					identity_wrt_a = true;
			}

			if (identity_wrt_a || identity_wrt_b)
			{
				log_debug("Replacing %s cell `%s' in module `%s' with identity for port %c.\n",
					cell->type.c_str(), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str(), identity_wrt_a ? 'A' : 'B');

				if (cell->type == TW($alu)) {
					bool a_signed = cell->parameters[ID::A_SIGNED].as_bool();
					bool b_signed = cell->parameters[ID::B_SIGNED].as_bool();
					bool is_signed = a_signed && b_signed;
					RTLIL::SigBit sig_ci = assign_map(cell->getPort(TW::CI));
					int y_width = GetSize(cell->getPort(TW::Y));

					OptExprPatcher patcher(module, &assign_map);
					SigSpec new_x, new_co;
					SigSpec a_port;
					bool a_port_signed;
					int a_port_width;
					if (sig_ci == State::S1) {
						/* sub, b is 0 */
						RTLIL::SigSpec a = cell->getPort(TW::A);
						a.extend_u0(y_width, is_signed);
						new_x = patcher.Not(NEW_TWINE, a);
						new_co = RTLIL::Const(State::S1, y_width);
						a_port = cell->getPort(TW::A);
						a_port_signed = a_signed;
						a_port_width = cell->getParam(ID::A_WIDTH).as_int();
					} else {
						/* add */
						RTLIL::SigSpec ab = cell->getPort(identity_wrt_a ? TW::A : TW::B);
						ab.extend_u0(y_width, is_signed);
						new_x = ab;
						new_co = RTLIL::Const(State::S0, y_width);
						a_port = cell->getPort(identity_wrt_a ? TW::A : TW::B);
						a_port_signed = identity_wrt_a ? a_signed : b_signed;
						a_port_width = cell->getParam(identity_wrt_a ? ID::A_WIDTH : ID::B_WIDTH).as_int();
					}

					TwineRef new_type = arith_inverse ? TW($neg) : TW($pos);
					SigSpec new_y = patcher.addWire(NEW_TWINE, y_width);
					Cell *new_cell = patcher.addCell(NEW_TWINE, new_type);
					new_cell->setPort(TW::A, a_port);
					new_cell->setPort(TW::Y, new_y);
					new_cell->setParam(ID::A_WIDTH, a_port_width);
					new_cell->setParam(ID::A_SIGNED, a_port_signed);
					new_cell->setParam(ID::Y_WIDTH, y_width);

					patcher.patch_multi(cell, {{TW::Y, new_y}, {TW::X, new_x}, {TW::CO, new_co}}, "alu_identity");
					goto next_cell;
				}

				if (!identity_wrt_a) {
					cell->setPort(TW::A, cell->getPort(TW::B));
					cell->setParam(ID::A_WIDTH, cell->getParam(ID::B_WIDTH));
					cell->setParam(ID::A_SIGNED, cell->getParam(ID::B_SIGNED));
				}

				cell->unsetPort(TW::B);
				cell->parameters.erase(ID::B_WIDTH);
				cell->parameters.erase(ID::B_SIGNED);
				cell->type_impl = arith_inverse ? TW::$neg : TW::$pos;
				cell->check();

				did_something = true;
				goto next_cell;
			}
		}
skip_identity:

		if (mux_bool && cell->type.in(TW($mux), TW($_MUX_)) &&
				cell->getPort(TW::A) == State::S0 && cell->getPort(TW::B) == State::S1) {
			OptExprPatcher patcher(module, &assign_map);
			patcher.patch(cell, TW::Y, cell->getPort(TW::S), "mux_bool");
			goto next_cell;
		}

		if (mux_bool && cell->type.in(TW($mux), TW($_MUX_)) &&
				cell->getPort(TW::A) == State::S1 && cell->getPort(TW::B) == State::S0) {
			log_debug("Replacing %s cell `%s' in module `%s' with inverter.\n", cell->type.unescaped(), cell, module);
			cell->setPort(TW::A, cell->getPort(TW::S));
			cell->unsetPort(TW::B);
			cell->unsetPort(TW::S);
			if (cell->type == TW($mux)) {
				Const width = cell->parameters[ID::WIDTH];
				cell->parameters[ID::A_WIDTH] = width;
				cell->parameters[ID::Y_WIDTH] = width;
				cell->parameters[ID::A_SIGNED] = 0;
				cell->parameters.erase(ID::WIDTH);
				cell->type_impl = TW::$not;
			} else
				cell->type_impl = TW::$_NOT_;
			did_something = true;
			goto next_cell;
		}

		if (consume_x && mux_bool && cell->type.in(TW($mux), TW($_MUX_)) && cell->getPort(TW::A) == State::S0) {
			log_debug("Replacing %s cell `%s' in module `%s' with and-gate.\n", cell->type.unescaped(), cell, module);
			cell->setPort(TW::A, cell->getPort(TW::S));
			cell->unsetPort(TW::S);
			if (cell->type == TW($mux)) {
				Const width = cell->parameters[ID::WIDTH];
				cell->parameters[ID::A_WIDTH] = width;
				cell->parameters[ID::B_WIDTH] = width;
				cell->parameters[ID::Y_WIDTH] = width;
				cell->parameters[ID::A_SIGNED] = 0;
				cell->parameters[ID::B_SIGNED] = 0;
				cell->parameters.erase(ID::WIDTH);
				cell->type_impl = TW::$and;
			} else
				cell->type_impl = TW::$_AND_;
			did_something = true;
			goto next_cell;
		}

		if (consume_x && mux_bool && cell->type.in(TW($mux), TW($_MUX_)) && cell->getPort(TW::B) == State::S1) {
			log_debug("Replacing %s cell `%s' in module `%s' with or-gate.\n", cell->type.unescaped(), cell, module);
			cell->setPort(TW::B, cell->getPort(TW::S));
			cell->unsetPort(TW::S);
			if (cell->type == TW($mux)) {
				Const width = cell->parameters[ID::WIDTH];
				cell->parameters[ID::A_WIDTH] = width;
				cell->parameters[ID::B_WIDTH] = width;
				cell->parameters[ID::Y_WIDTH] = width;
				cell->parameters[ID::A_SIGNED] = 0;
				cell->parameters[ID::B_SIGNED] = 0;
				cell->parameters.erase(ID::WIDTH);
				cell->type_impl = TW::$or;
			} else
				cell->type_impl = TW::$_OR_;
			did_something = true;
			goto next_cell;
		}

		if (mux_undef && cell->type.in(TW($mux), TW($pmux))) {
			RTLIL::SigSpec new_a, new_b, new_s;
			int width = GetSize(cell->getPort(TW::A));
			if ((cell->getPort(TW::A).is_fully_undef() && cell->getPort(TW::B).is_fully_undef()) ||
					cell->getPort(TW::S).is_fully_undef()) {
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, cell->getPort(TW::A), "mux_undef");
				goto next_cell;
			}
			for (int i = 0; i < cell->getPort(TW::S).size(); i++) {
				RTLIL::SigSpec old_b = cell->getPort(TW::B).extract(i*width, width);
				RTLIL::SigSpec old_s = cell->getPort(TW::S).extract(i, 1);
				if (old_b.is_fully_undef() || old_s.is_fully_undef())
					continue;
				new_b.append(old_b);
				new_s.append(old_s);
			}
			new_a = cell->getPort(TW::A);
			if (new_a.is_fully_undef() && new_s.size() > 0) {
				new_a = new_b.extract((new_s.size()-1)*width, width);
				new_b = new_b.extract(0, (new_s.size()-1)*width);
				new_s = new_s.extract(0, new_s.size()-1);
			}
			if (new_s.size() == 0) {
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, new_a, "mux_empty");
				goto next_cell;
			}
			if (new_a == RTLIL::SigSpec(RTLIL::State::S0) && new_b == RTLIL::SigSpec(RTLIL::State::S1)) {
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, new_s, "mux_sel01");
				goto next_cell;
			}
			if (cell->getPort(TW::S).size() != new_s.size()) {
				log_debug("Optimized away %d select inputs of %s cell `%s' in module `%s'.\n",
						GetSize(cell->getPort(TW::S)) - GetSize(new_s), cell->type.unescaped(), cell, module);
				cell->setPort(TW::A, new_a);
				cell->setPort(TW::B, new_b);
				cell->setPort(TW::S, new_s);
				if (new_s.size() > 1) {
					cell->type_impl = TW::$pmux;
					cell->parameters[ID::S_WIDTH] = new_s.size();
				} else {
					cell->type_impl = TW::$mux;
					cell->parameters.erase(ID::S_WIDTH);
				}
				did_something = true;
			}
		}

		if (mux_undef && cell->type.in(TW($_MUX4_), TW($_MUX8_), TW($_MUX16_))) {
			int num_inputs = 4;
			if (cell->type == TW($_MUX8_)) num_inputs = 8;
			if (cell->type == TW($_MUX16_)) num_inputs = 16;
			int undef_inputs = 0;
			for (auto &conn : cell->connections())
				if (conn.first != TW::S && conn.first != TW::T && conn.first != TW::U && conn.first != TW::V && conn.first != TW::Y)
					undef_inputs += conn.second.is_fully_undef();
			if (undef_inputs == num_inputs) {
				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, cell->getPort(TW::A), "mux_undef");
				goto next_cell;
			}
		}

#define FOLD_1ARG_CELL(_t) \
		if (cell->type == TW($##_t)) { \
			RTLIL::SigSpec a = cell->getPort(TW::A); \
			assign_map.apply(a); \
			if (a.is_fully_const()) { \
				RTLIL::Const dummy_arg(RTLIL::State::S0, 1); \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.as_const(), dummy_arg, \
						cell->parameters[ID::A_SIGNED].as_bool(), false, \
						cell->parameters[ID::Y_WIDTH].as_int())); \
				OptExprPatcher patcher(module, &assign_map); \
				patcher.patch(cell, TW::Y, y, stringf("%s", log_signal(a))); \
				goto next_cell; \
			} \
		}
#define FOLD_2ARG_CELL(_t) \
		if (cell->type == TW($##_t)) { \
			RTLIL::SigSpec a = cell->getPort(TW::A); \
			RTLIL::SigSpec b = cell->getPort(TW::B); \
			assign_map.apply(a), assign_map.apply(b); \
			if (a.is_fully_const() && b.is_fully_const()) { \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.as_const(), b.as_const(), \
						cell->parameters[ID::A_SIGNED].as_bool(), \
						cell->parameters[ID::B_SIGNED].as_bool(), \
						cell->parameters[ID::Y_WIDTH].as_int())); \
				OptExprPatcher patcher(module, &assign_map); \
				patcher.patch(cell, TW::Y, y, stringf("%s, %s", log_signal(a), log_signal(b))); \
				goto next_cell; \
			} \
		}
#define FOLD_2ARG_SIMPLE_CELL(_t, B_ID) \
		if (cell->type == TW($##_t)) { \
			RTLIL::SigSpec a = cell->getPort(TW::A); \
			RTLIL::SigSpec b = cell->getPort(B_ID); \
			assign_map.apply(a), assign_map.apply(b); \
			if (a.is_fully_const() && b.is_fully_const()) { \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.as_const(), b.as_const())); \
				OptExprPatcher patcher(module, &assign_map); \
				patcher.patch(cell, TW::Y, y, stringf("%s, %s", log_signal(a), log_signal(b))); \
				goto next_cell; \
			} \
		}
#define FOLD_MUX_CELL(_t) \
		if (cell->type == TW($##_t)) { \
			RTLIL::SigSpec a = cell->getPort(TW::A); \
			RTLIL::SigSpec b = cell->getPort(TW::B); \
			RTLIL::SigSpec s = cell->getPort(TW::S); \
			assign_map.apply(a), assign_map.apply(b), assign_map.apply(s); \
			if (a.is_fully_const() && b.is_fully_const() && s.is_fully_const()) { \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.as_const(), b.as_const(), s.as_const())); \
				OptExprPatcher patcher(module, &assign_map); \
				patcher.patch(cell, TW::Y, y, stringf("%s, %s, %s", log_signal(a), log_signal(b), log_signal(s))); \
				goto next_cell; \
			} \
		}

		FOLD_1ARG_CELL(not)
		FOLD_2ARG_CELL(and)
		FOLD_2ARG_CELL(or)
		FOLD_2ARG_CELL(xor)
		FOLD_2ARG_CELL(xnor)

		FOLD_1ARG_CELL(reduce_and)
		FOLD_1ARG_CELL(reduce_or)
		FOLD_1ARG_CELL(reduce_xor)
		FOLD_1ARG_CELL(reduce_xnor)
		FOLD_1ARG_CELL(reduce_bool)

		FOLD_1ARG_CELL(logic_not)
		FOLD_2ARG_CELL(logic_and)
		FOLD_2ARG_CELL(logic_or)

		FOLD_2ARG_CELL(shl)
		FOLD_2ARG_CELL(shr)
		FOLD_2ARG_CELL(sshl)
		FOLD_2ARG_CELL(sshr)
		FOLD_2ARG_CELL(shift)
		FOLD_2ARG_CELL(shiftx)

		FOLD_2ARG_CELL(lt)
		FOLD_2ARG_CELL(le)
		FOLD_2ARG_CELL(eq)
		FOLD_2ARG_CELL(ne)
		FOLD_2ARG_CELL(gt)
		FOLD_2ARG_CELL(ge)

		FOLD_2ARG_CELL(eqx)
		FOLD_2ARG_CELL(nex)

		FOLD_2ARG_CELL(add)
		FOLD_2ARG_CELL(sub)
		FOLD_2ARG_CELL(mul)
		FOLD_2ARG_CELL(div)
		FOLD_2ARG_CELL(mod)
		FOLD_2ARG_CELL(divfloor)
		FOLD_2ARG_CELL(modfloor)
		FOLD_2ARG_CELL(pow)

		FOLD_1ARG_CELL(pos)
		FOLD_1ARG_CELL(neg)

		FOLD_MUX_CELL(mux);
		FOLD_MUX_CELL(pmux);
		FOLD_2ARG_SIMPLE_CELL(bmux, TW::S);
		FOLD_2ARG_SIMPLE_CELL(demux, TW::S);
		FOLD_2ARG_SIMPLE_CELL(bweqx, TW::B);
		FOLD_MUX_CELL(bwmux);

		// be very conservative with optimizing $mux cells as we do not want to break mux trees
		if (cell->type == TW($mux)) {
			RTLIL::SigSpec input = assign_map(cell->getPort(TW::S));
			RTLIL::SigSpec inA = assign_map(cell->getPort(TW::A));
			RTLIL::SigSpec inB = assign_map(cell->getPort(TW::B));
			if (input.is_fully_const() && (!keepdc || input.is_fully_def()))
				ACTION_DO(TW::Y, input.as_bool() ? cell->getPort(TW::B) : cell->getPort(TW::A));
			else if (inA == inB)
				ACTION_DO(TW::Y, cell->getPort(TW::A));
		}
		if (cell->type == TW($pow) && cell->getPort(TW::A).is_fully_const() && !cell->parameters[ID::B_SIGNED].as_bool()) {
			SigSpec sig_a = assign_map(cell->getPort(TW::A));
			SigSpec sig_y = assign_map(cell->getPort(TW::Y));
			int y_size = GetSize(sig_y);

			int bit_idx;
			const auto onehot = sig_a.is_onehot(&bit_idx);

			// Power of two
			// A is unsigned or positive
			if (onehot && (!cell->parameters[ID::A_SIGNED].as_bool() || bit_idx < sig_a.size() - 1)) {
				cell->parameters[ID::A_SIGNED] = 0;
				// 2^B = 1<<B
				if (bit_idx == 1) {
					log_debug("Replacing pow cell `%s' in module `%s' with left-shift\n",
							cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str());
					cell->type_impl = TW::$shl;
					cell->parameters[ID::A_WIDTH] = 1;
					cell->setPort(TW::A, Const(State::S1, 1));
				}
				else {
					log_debug("Replacing pow cell `%s' in module `%s' with multiply and left-shift\n",
							cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str());
					OptExprPatcher patcher(module, &assign_map);
					int a_width = cell->parameters[ID::A_WIDTH].as_int();

					SigSpec y_wire = patcher.addWire(NEW_TWINE, y_size);
					Cell *mul = patcher.addCell(NEW_TWINE, TW($mul));
					mul->setPort(TW::A, Const(bit_idx, a_width));
					mul->setPort(TW::B, cell->getPort(TW::B));
					mul->setPort(TW::Y, y_wire);
					mul->parameters[ID::A_WIDTH] = a_width;
					mul->parameters[ID::A_SIGNED] = 0;
					mul->parameters[ID::B_WIDTH] = cell->parameters[ID::B_WIDTH];
					mul->parameters[ID::B_SIGNED] = cell->parameters[ID::B_SIGNED];
					mul->parameters[ID::Y_WIDTH] = y_size;

					SigSpec new_y = patcher.addWire(NEW_TWINE, y_size);
					patcher.addShl(NEW_TWINE, Const(State::S1, 1), y_wire, new_y);

					patcher.patch(cell, TW::Y, new_y, "pow_to_mul_shl");
					goto next_cell;
				}
				did_something = true;
				goto next_cell;
			}
		}
		if (!keepdc && cell->type == TW($mul))
		{
			bool a_signed = cell->parameters[ID::A_SIGNED].as_bool();
			bool b_signed = cell->parameters[ID::B_SIGNED].as_bool();
			bool swapped_ab = false;

			RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));
			RTLIL::SigSpec sig_b = assign_map(cell->getPort(TW::B));
			RTLIL::SigSpec sig_y = assign_map(cell->getPort(TW::Y));

			if (sig_b.is_fully_const())
				std::swap(sig_a, sig_b), std::swap(a_signed, b_signed), swapped_ab = true;

			if (sig_a.is_fully_def())
			{
				if (sig_a.is_fully_zero())
				{
					log_debug("Replacing multiply-by-zero cell `%s' in module `%s' with zero-driver.\n",
							cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str());

					OptExprPatcher patcher(module, &assign_map);
					patcher.patch(cell, TW::Y, RTLIL::SigSpec(0, sig_y.size()), "mul_zero");
					goto next_cell;
				}

				int exp;
				if (sig_a.is_onehot(&exp) && !(a_signed && exp == GetSize(sig_a) - 1))
				{
					log_debug("Replacing multiply-by-%s cell `%s' in module `%s' with shift-by-%d.\n",
							log_signal(sig_a), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str(), exp);

					if (!swapped_ab) {
						cell->setPort(TW::A, cell->getPort(TW::B));
						cell->parameters.at(ID::A_WIDTH) = cell->parameters.at(ID::B_WIDTH);
						cell->parameters.at(ID::A_SIGNED) = cell->parameters.at(ID::B_SIGNED);
					}

					Const new_b = exp;

					cell->type_impl = TW::$shl;
					cell->parameters[ID::B_WIDTH] = GetSize(new_b);
					cell->parameters[ID::B_SIGNED] = false;
					cell->setPort(TW::B, new_b);
					cell->check();

					did_something = true;
					goto next_cell;
				}
			}

			sig_a = assign_map(cell->getPort(TW::A));
			sig_b = assign_map(cell->getPort(TW::B));
			int a_zeros, b_zeros;
			for (a_zeros = 0; a_zeros < GetSize(sig_a); a_zeros++)
				if (sig_a[a_zeros] != RTLIL::State::S0)
					break;
			for (b_zeros = 0; b_zeros < GetSize(sig_b); b_zeros++)
				if (sig_b[b_zeros] != RTLIL::State::S0)
					break;
			if (a_zeros || b_zeros) {
				int y_zeros = a_zeros + b_zeros;
				log_debug("Removing low %d A and %d B bits from cell `%s' in module `%s'.\n",
						a_zeros, b_zeros, cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str());

				if (y_zeros >= GetSize(sig_y)) {
					OptExprPatcher patcher(module, &assign_map);
					patcher.patch(cell, TW::Y, RTLIL::SigSpec(0, GetSize(sig_y)), "mul_low_zeros");
					goto next_cell;
				}

				if (a_zeros) {
					cell->setPort(TW::A, sig_a.extract_end(a_zeros));
					cell->parameters[ID::A_WIDTH] = GetSize(sig_a) - a_zeros;
				}
				if (b_zeros) {
					cell->setPort(TW::B, sig_b.extract_end(b_zeros));
					cell->parameters[ID::B_WIDTH] = GetSize(sig_b) - b_zeros;
				}
				cell->setPort(TW::Y, sig_y.extract_end(y_zeros));
				cell->parameters[ID::Y_WIDTH] = GetSize(sig_y) - y_zeros;
				module->connect(RTLIL::SigSig(sig_y.extract(0, y_zeros), RTLIL::SigSpec(0, y_zeros)));
				cell->check();

				did_something = true;
				goto next_cell;
			}
		}

		if (cell->type.in(TW($div), TW($mod), TW($divfloor), TW($modfloor)))
		{
			bool a_signed = cell->parameters[ID::A_SIGNED].as_bool();
			bool b_signed = cell->parameters[ID::B_SIGNED].as_bool();
			SigSpec sig_a = assign_map(cell->getPort(TW::A));
			SigSpec sig_b = assign_map(cell->getPort(TW::B));
			SigSpec sig_y = assign_map(cell->getPort(TW::Y));

			if (sig_b.is_fully_def())
			{
				if (sig_b.is_fully_zero())
				{
					log_debug("Replacing divide-by-zero cell `%s' in module `%s' with undef-driver.\n",
							cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str());

					OptExprPatcher patcher(module, &assign_map);
					patcher.patch(cell, TW::Y, RTLIL::SigSpec(State::Sx, sig_y.size()), "div_zero");
					goto next_cell;
				}

				int exp;
				if (!keepdc && sig_b.is_onehot(&exp) && !(b_signed && exp == GetSize(sig_b) - 1))
				{
					if (cell->type.in(TW($div), TW($divfloor)))
					{
						bool is_truncating = cell->type == TW($div);
						log_debug("Replacing %s-divide-by-%s cell `%s' in module `%s' with shift-by-%d.\n",
								is_truncating ? "truncating" : "flooring",
								log_signal(sig_b), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str(), exp);

						Const new_b = exp;

						cell->type_impl = TW::$sshr;
						cell->parameters[ID::B_WIDTH] = GetSize(new_b);
						cell->parameters[ID::B_SIGNED] = false;
						cell->setPort(TW::B, new_b);

						// Truncating division is the same as flooring division, except when
						// the result is negative and there is a remainder - then trunc = floor + 1
						if (is_truncating && a_signed && GetSize(sig_a) != 0 && exp != 0) {
							Wire *flooring = module->addWire(NEW_TWINE, sig_y.size());
							cell->setPort(TW::Y, flooring);

							SigSpec a_sign = sig_a[sig_a.size()-1];
							SigSpec rem_nonzero = module->ReduceOr(NEW_TWINE, sig_a.extract(0, exp));
							SigSpec should_add = module->And(NEW_TWINE, a_sign, rem_nonzero);
							module->addAdd(NEW_TWINE, flooring, should_add, sig_y);
						}

						cell->check();
					}
					else if (cell->type.in(TW($mod), TW($modfloor)))
					{
						bool is_truncating = cell->type == TW($mod);
						log_debug("Replacing %s-modulo-by-%s cell `%s' in module `%s' with bitmask.\n",
								is_truncating ? "truncating" : "flooring",
								log_signal(sig_b), cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str());

						// truncating modulo has the same masked bits as flooring modulo, but
						// the sign bits are those of A (except when R=0)
						if (is_truncating && a_signed && GetSize(sig_a) != 0 && exp != 0)
						{
							OptExprPatcher patcher(module, &assign_map);
							SigSpec truncating = sig_a.extract(0, exp);

							SigSpec a_sign = sig_a[sig_a.size()-1];
							SigSpec rem_nonzero = patcher.ReduceOr(NEW_TWINE, sig_a.extract(0, exp));
							SigSpec extend_bit = patcher.And(NEW_TWINE, a_sign, rem_nonzero);

							truncating.append(extend_bit);
							SigSpec new_y = truncating;
							new_y.extend_u0(GetSize(sig_y), true);
							patcher.patch(cell, TW::Y, new_y, "mod_truncating");
							goto next_cell;
						}
						else
						{
							std::vector<RTLIL::SigBit> new_b = RTLIL::SigSpec(State::S1, exp);

							if (b_signed || exp == 0)
								new_b.push_back(State::S0);

							cell->type_impl = TW::$and;
							cell->parameters[ID::B_WIDTH] = GetSize(new_b);
							cell->setPort(TW::B, new_b);
							cell->check();
						}
					}

					did_something = true;
					goto next_cell;
				}
			}
		}

		// Find places in $alu cell where the carry is constant, and split it at these points.
		if (do_fine && !keepdc && cell->type == TW($alu))
		{
			bool a_signed = cell->parameters[ID::A_SIGNED].as_bool();
			bool b_signed = cell->parameters[ID::B_SIGNED].as_bool();
			bool is_signed = a_signed && b_signed;

			RTLIL::SigSpec sig_a = assign_map(cell->getPort(TW::A));
			RTLIL::SigSpec sig_b = assign_map(cell->getPort(TW::B));
			RTLIL::SigSpec sig_y = assign_map(cell->getPort(TW::Y));
			RTLIL::SigSpec sig_bi = assign_map(cell->getPort(TW::BI));
			if (GetSize(sig_a) == 0)
				sig_a = State::S0;
			if (GetSize(sig_b) == 0)
				sig_b = State::S0;
			sig_a.extend_u0(GetSize(sig_y), is_signed);
			sig_b.extend_u0(GetSize(sig_y), is_signed);

			if (sig_bi != State::S0 && sig_bi != State::S1)
				goto skip_alu_split;

			std::vector<std::pair<int, State>> split_points;

			for (int i = 0; i < GetSize(sig_y); i++) {
				SigBit bit_a = sig_a[i];
				SigBit bit_b = sig_b[i];
				if (bit_a != State::S0 && bit_a != State::S1)
					continue;
				if (bit_b != State::S0 && bit_b != State::S1)
					continue;
				if (sig_bi == State::S1) {
					if (bit_b == State::S0)
						bit_b = State::S1;
					else
						bit_b = State::S0;
				}
				if (bit_a != bit_b)
					continue;
				split_points.push_back(std::make_pair(i + 1, bit_a.data));
			}

			if (split_points.empty() || split_points[0].first == GetSize(sig_y))
				goto skip_alu_split;

			for (auto &p : split_points)
				log_debug("Splitting $alu cell `%s' in module `%s' at const-carry point %d.\n",
					cell->name.c_str(), module->design->twines.str(module->meta_->name).c_str(), p.first);

			if (split_points.back().first != GetSize(sig_y))
				split_points.push_back(std::make_pair(GetSize(sig_y), State::Sx));

			RTLIL::SigSpec sig_ci = assign_map(cell->getPort(TW::CI));
			int prev = 0;

			OptExprPatcher patcher(module, &assign_map);
			SigSpec new_y, new_x, new_co_concat;

			for (auto &p : split_points) {
				int cur = p.first;
				int sz = cur - prev;
				bool last = cur == GetSize(sig_y);

				SigSpec slice_y = patcher.addWire(NEW_TWINE, sz);
				SigSpec slice_x = patcher.addWire(NEW_TWINE, sz);
				SigSpec slice_co = patcher.addWire(NEW_TWINE, sz);

				RTLIL::Cell *c = patcher.addCell(NEW_TWINE, cell->type_impl);
				c->setPort(TW::A, sig_a.extract(prev, sz));
				c->setPort(TW::B, sig_b.extract(prev, sz));
				c->setPort(TW::BI, sig_bi);
				c->setPort(TW::CI, sig_ci);
				c->setPort(TW::Y, slice_y);
				c->setPort(TW::X, slice_x);
				c->setPort(TW::CO, slice_co);
				c->parameters[ID::A_WIDTH] = sz;
				c->parameters[ID::B_WIDTH] = sz;
				c->parameters[ID::Y_WIDTH] = sz;
				c->parameters[ID::A_SIGNED] = last ? a_signed : false;
				c->parameters[ID::B_SIGNED] = last ? b_signed : false;

				new_y.append(slice_y);
				new_x.append(slice_x);
				SigSpec exported_co = slice_co;
				if (p.second != State::Sx)
					exported_co[sz-1] = p.second;
				new_co_concat.append(exported_co);

				prev = p.first;
				sig_ci = p.second;
			}

			patcher.patch_multi(cell, {{TW::Y, new_y}, {TW::X, new_x}, {TW::CO, new_co_concat}}, "alu_split");
			goto next_cell;
		}
skip_alu_split:

		// replace (2^k-1)-x with ~x when x is known to be smaller than 2^k
		if (do_fine && cell->type == ID($sub))
		{
			int y_width = GetSize(cell->getPort(ID::Y));
			bool a_signed = cell->getParam(ID::A_SIGNED).as_bool();

			RTLIL::SigSpec sig_a = assign_map(cell->getPort(ID::A));
			sig_a.extend_u0(y_width, a_signed);

			if (y_width > 0 && sig_a.is_fully_const())
			{
				RTLIL::Const a_val = sig_a.as_const();

				int k = 0;
				while (k < y_width && a_val[k] == State::S1)
					k++;

				bool a_is_mask = k > 0;
				for (int i = k; a_is_mask && i < y_width; i++)
					if (a_val[i] != State::S0)
						a_is_mask = false;

				if (a_is_mask)
				{
					bool b_signed = cell->getParam(ID::B_SIGNED).as_bool();
					RTLIL::SigSpec sig_b = assign_map(cell->getPort(ID::B));
					sig_b.extend_u0(y_width, b_signed);

					bool b_fits = true;
					for (int i = k; b_fits && i < y_width; i++)
						if (sig_b[i] != State::S0)
							b_fits = false;

					if (b_fits)
					{
						RTLIL::SigSpec sig_y = module->Not(NEW_ID, sig_b.extract(0, k));
						if (y_width > k)
							sig_y.append(RTLIL::SigSpec(State::S0, y_width - k));

						log_debug("Replacing `(2^%d-1) - B` $sub cell `%s' in module `%s' with $not.\n",
								k, cell->name.c_str(), module->name.c_str());
						module->connect(cell->getPort(ID::Y), sig_y);
						module->remove(cell);
						did_something = true;
						goto next_cell;
					}
				}
			}
		}

		// remove redundant pairs of bits in ==, ===, !=, and !==
		// replace cell with const driver if inputs can't be equal
		if (do_fine && cell->type.in(TW($eq), TW($ne), TW($eqx), TW($nex)))
		{
			pool<pair<SigBit, SigBit>> redundant_cache;
			mfp<SigBit> contradiction_cache;

			contradiction_cache.promote(State::S0);
			contradiction_cache.promote(State::S1);

			int a_width = cell->getParam(ID::A_WIDTH).as_int();
			int b_width = cell->getParam(ID::B_WIDTH).as_int();

			bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
			int width = is_signed ? std::min(a_width, b_width) : std::max(a_width, b_width);

			SigSpec sig_a = cell->getPort(TW::A);
			SigSpec sig_b = cell->getPort(TW::B);

			int redundant_bits = 0;

			for (int i = width-1; i >= 0; i--)
			{
				SigBit bit_a = i < a_width ? assign_map(sig_a[i]) : State::S0;
				SigBit bit_b = i < b_width ? assign_map(sig_b[i]) : State::S0;

				if (bit_a != State::Sx && bit_a != State::Sz &&
						bit_b != State::Sx && bit_b != State::Sz)
					contradiction_cache.merge(bit_a, bit_b);

				if (bit_b < bit_a)
					std::swap(bit_a, bit_b);

				pair<SigBit, SigBit> key(bit_a, bit_b);

				if (redundant_cache.count(key)) {
					if (i < a_width) sig_a.remove(i);
					if (i < b_width) sig_b.remove(i);
					redundant_bits++;
					continue;
				}

				redundant_cache.insert(key);
			}

			if (contradiction_cache.find(State::S0) == contradiction_cache.find(State::S1))
			{
				SigSpec y_sig = cell->getPort(TW::Y);
				Const y_value(cell->type.in(TW($eq), TW($eqx)) ? 0 : 1, GetSize(y_sig));

				log_debug("Replacing cell `%s' in module `%s' with constant driver %s.\n",
					cell, module, log_signal(y_value));

				OptExprPatcher patcher(module, &assign_map);
				patcher.patch(cell, TW::Y, y_value, "eq_contradiction");
				goto next_cell;
			}

			if (redundant_bits)
			{
				log_debug("Removed %d redundant input bits from %s cell `%s' in module `%s'.\n",
						redundant_bits, cell->type.unescaped(), cell, module);

				cell->setPort(TW::A, sig_a);
				cell->setPort(TW::B, sig_b);
				cell->setParam(ID::A_WIDTH, GetSize(sig_a));
				cell->setParam(ID::B_WIDTH, GetSize(sig_b));

				did_something = true;
				goto next_cell;
			}
		}

		// simplify comparisons
		if (do_fine && cell->type.in(TW($lt), TW($ge), TW($gt), TW($le)))
		{
			IdString cmp_type = cell->type;
			SigSpec var_sig = cell->getPort(TW::A);
			SigSpec const_sig = cell->getPort(TW::B);
			int var_width = cell->parameters[ID::A_WIDTH].as_int();
			int const_width = cell->parameters[ID::B_WIDTH].as_int();
			bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();

			if (!const_sig.is_fully_const())
			{
				std::swap(var_sig, const_sig);
				std::swap(var_width, const_width);
				if (cmp_type == TW($gt))
					cmp_type = TW($lt);
				else if (cmp_type == TW($lt))
					cmp_type = TW($gt);
				else if (cmp_type == TW($ge))
					cmp_type = TW($le);
				else if (cmp_type == TW($le))
					cmp_type = TW($ge);
			}

			if (const_sig.is_fully_def() && const_sig.is_fully_const())
			{
				std::string condition, replacement;
				SigSpec replace_sig(State::S0, GetSize(cell->getPort(TW::Y)));
				bool replace = false;
				OptExprPatcher patcher(module, &assign_map);

				if (!is_signed)
				{ /* unsigned */
					if (const_sig.is_fully_zero() && cmp_type == TW($lt)) {
						condition   = "unsigned X<0";
						replacement = "constant 0";
						replace_sig[0] = State::S0;
						replace = true;
					}
					if (const_sig.is_fully_zero() && cmp_type == TW($ge)) {
						condition   = "unsigned X>=0";
						replacement = "constant 1";
						replace_sig[0] = State::S1;
						replace = true;
					}
					if (const_width == var_width && const_sig.is_fully_ones() && cmp_type == TW($gt)) {
						condition   = "unsigned X>~0";
						replacement = "constant 0";
						replace_sig[0] = State::S0;
						replace = true;
					}
					if (const_width == var_width && const_sig.is_fully_ones() && cmp_type == TW($le)) {
						condition   = "unsigned X<=~0";
						replacement = "constant 1";
						replace_sig[0] = State::S1;
						replace = true;
					}

					int const_bit_hot;
					if (const_sig.is_onehot(&const_bit_hot) && const_bit_hot < var_width)
					{
						RTLIL::SigSpec var_high_sig(RTLIL::State::S0, var_width - const_bit_hot);
						for (int i = const_bit_hot; i < var_width; i++) {
							var_high_sig[i - const_bit_hot] = var_sig[i];
						}

						if (cmp_type == TW($lt))
						{
							condition   = stringf("unsigned X<%s", log_signal(const_sig));
							replacement = stringf("!X[%d:%d]", var_width - 1, const_bit_hot);
							replace_sig[0] = patcher.LogicNot(NEW_TWINE, var_high_sig).as_bit();
							replace = true;
						}
						if (cmp_type == TW($ge))
						{
							condition   = stringf("unsigned X>=%s", log_signal(const_sig));
							replacement = stringf("|X[%d:%d]", var_width - 1, const_bit_hot);
							replace_sig[0] = patcher.ReduceOr(NEW_TWINE, var_high_sig).as_bit();
							replace = true;
						}
					}

					int const_bit_set = get_highest_hot_index(const_sig);
					if (const_bit_set >= var_width)
					{
						string cmp_name;
						if (cmp_type == TW($lt) || cmp_type == TW($le))
						{
							if (cmp_type == TW($lt)) cmp_name = "<";
							if (cmp_type == TW($le)) cmp_name = "<=";
							condition   = stringf("unsigned X[%d:0]%s%s", var_width - 1, cmp_name, log_signal(const_sig));
							replacement = "constant 1";
							replace_sig[0] = State::S1;
							replace = true;
						}
						if (cmp_type == TW($gt) || cmp_type == TW($ge))
						{
							if (cmp_type == TW($gt)) cmp_name = ">";
							if (cmp_type == TW($ge)) cmp_name = ">=";
							condition   = stringf("unsigned X[%d:0]%s%s", var_width - 1, cmp_name, log_signal(const_sig));
							replacement = "constant 0";
							replace_sig[0] = State::S0;
							replace = true;
						}
					}
				}
				else
				{ /* signed */
					if (const_sig.is_fully_zero() && cmp_type == TW($lt))
					{
						condition   = "signed X<0";
						replacement = stringf("X[%d]", var_width - 1);
						replace_sig[0] = var_sig[var_width - 1];
						replace = true;
					}
					if (const_sig.is_fully_zero() && cmp_type == TW($ge))
					{
						condition   = "signed X>=0";
						replacement = stringf("X[%d]", var_width - 1);
						replace_sig[0] = patcher.LogicNot(NEW_TWINE, var_sig[var_width - 1]).as_bit();
						replace = true;
					}
				}

				if (replace)
				{
					log_debug("Replacing %s cell `%s' (implementing %s) with %s.\n",
							cell->type.unescape(), cell, condition.c_str(), replacement.c_str());
					patcher.patch(cell, TW::Y, replace_sig, condition);
					goto next_cell;
				}
			}
		}

	next_cell:;
#undef ACTION_DO
#undef ACTION_DO_Y
#undef FOLD_1ARG_CELL
#undef FOLD_2ARG_CELL
	}
}

void replace_const_connections(RTLIL::Module *module) {
	SigMap assign_map(module);
	for (auto cell : module->selected_cells())
	{
		std::vector<std::pair<TwineRef, SigSpec>> changes;
		for (auto &conn : cell->connections()) {
			SigSpec mapped = assign_map(conn.second);
			if (conn.second != mapped && mapped.is_fully_const())
				changes.push_back({conn.first, mapped});
		}
		if (!changes.empty())
			did_something = true;
		for (auto &it : changes)
			cell->setPort(it.first, it.second);
	}
}

struct OptExprPass : public Pass {
	OptExprPass() : Pass("opt_expr", "perform const folding and simple expression rewriting") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_expr [options] [selection]\n");
		log("\n");
		log("This pass performs const folding on internal cell types with constant inputs.\n");
		log("It also performs some simple expression rewriting.\n");
		log("\n");
		log("    -mux_undef\n");
		log("        remove 'undef' inputs from $mux, $pmux and $_MUX_ cells\n");
		log("\n");
		log("    -mux_bool\n");
		log("        replace $mux cells with inverters or buffers when possible\n");
		log("\n");
		log("    -undriven\n");
		log("        replace undriven nets with undef (x) constants\n");
		log("\n");
		log("    -noclkinv\n");
		log("        do not optimize clock inverters by changing FF types\n");
		log("\n");
		log("    -fine\n");
		log("        perform fine-grain optimizations\n");
		log("\n");
		log("    -full\n");
		log("        alias for -mux_undef -mux_bool -undriven -fine\n");
		log("\n");
		log("    -keepdc\n");
		log("        some optimizations change the behavior of the circuit with respect to\n");
		log("        don't-care bits. for example in 'a+0' a single x-bit in 'a' will cause\n");
		log("        all result bits to be set to x. this behavior changes when 'a+0' is\n");
		log("        replaced by 'a'. the -keepdc option disables all such optimizations.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool mux_undef = false;
		bool mux_bool = false;
		bool undriven = false;
		bool noclkinv = false;
		bool do_fine = false;
		bool keepdc = false;

		log_header(design, "Executing OPT_EXPR pass (perform const folding).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-mux_undef") {
				mux_undef = true;
				continue;
			}
			if (args[argidx] == "-mux_bool") {
				mux_bool = true;
				continue;
			}
			if (args[argidx] == "-undriven") {
				undriven = true;
				continue;
			}
			if (args[argidx] == "-noclkinv") {
				noclkinv = true;
				continue;
			}
			if (args[argidx] == "-fine") {
				do_fine = true;
				continue;
			}
			if (args[argidx] == "-full") {
				mux_undef = true;
				mux_bool = true;
				undriven = true;
				do_fine = true;
				continue;
			}
			if (args[argidx] == "-keepdc") {
				keepdc = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		design->sigNormalize(true);

		NewCellTypes ct(design);
		for (auto module : design->selected_modules())
		{

			int replace_const_cells_timestamp = INT_MIN;
			int replace_const_cells_consume_x_timestamp = INT_MIN;
			log("Optimizing module %s.\n", module);

			if (undriven) {
				did_something = false;
				replace_undriven(module, ct);
				if (did_something)
					design->scratchpad_set_bool("opt.did_something", true);
			}

			do {
				do {
					did_something = false;
					module->next_timestamp();
					replace_const_cells(design, module, false /* consume_x */, mux_undef, mux_bool, do_fine, keepdc, noclkinv, replace_const_cells_timestamp);
					replace_const_cells_timestamp = module->timestamp();
					if (did_something)
						design->scratchpad_set_bool("opt.did_something", true);
				} while (did_something);
				if (!keepdc) {
					module->next_timestamp();
					replace_const_cells(design, module, true /* consume_x */, mux_undef, mux_bool, do_fine, keepdc, noclkinv, replace_const_cells_consume_x_timestamp);
					replace_const_cells_consume_x_timestamp = module->timestamp();
				}
				if (did_something)
					design->scratchpad_set_bool("opt.did_something", true);
			} while (did_something);

			did_something = false;
			replace_const_connections(module);
			if (did_something)
				design->scratchpad_set_bool("opt.did_something", true);

			log_suppressed();
		}

		log_pop();
	}
} OptExprPass;

PRIVATE_NAMESPACE_END
