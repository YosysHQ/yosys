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

#include "simplemap.h"
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

USING_YOSYS_NAMESPACE
YOSYS_NAMESPACE_BEGIN

static void transfer_src (Cell* to, const Cell* from) {
	if (from->src_id() != Twine::Null && to->module && to->module->design)
		to->set_src_id(from->src_id());
}

void simplemap_not(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at(ID::A_SIGNED).as_bool());

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_TWINE, TW($_NOT_));
		transfer_src(gate, cell);
		gate->setPort(TW::A, sig_a[i]);
		gate->setPort(TW::Y, sig_y[i]);
	}
}

void simplemap_buf(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	if (sig_a.has_const(State::Sz)) {
		SigSpec new_a;
		SigSpec new_y;
		for (int i = 0; i < GetSize(sig_a); ++i) {
			SigBit b = sig_a[i];
			if (b == State::Sz)
				continue;
			new_a.append(b);
			new_y.append(sig_y[i]);
		}
		sig_a = std::move(new_a);
		sig_y = std::move(new_y);
	}

	if (!sig_y.empty())
		module->connect(RTLIL::SigSig(sig_y, sig_a));
}

void simplemap_pos(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at(ID::A_SIGNED).as_bool());

	module->connect(RTLIL::SigSig(sig_y, sig_a));
}

void simplemap_bitop(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_b = cell->getPort(TW::B);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	if (cell->type != TW($bweqx)) {
		sig_a.extend_u0(GetSize(sig_y), cell->parameters.at(ID::A_SIGNED).as_bool());
		sig_b.extend_u0(GetSize(sig_y), cell->parameters.at(ID::B_SIGNED).as_bool());
	}

	IdString gate_type;
	if (cell->type == TW($and))   gate_type = TW($_AND_);
	if (cell->type == TW($or))    gate_type = TW($_OR_);
	if (cell->type == TW($xor))   gate_type = TW($_XOR_);
	if (cell->type == TW($xnor))  gate_type = TW($_XNOR_);
	if (cell->type == TW($bweqx)) gate_type = TW($_XNOR_);
	log_assert(!gate_type.empty());

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_TWINE, gate_type);
		transfer_src(gate, cell);
		gate->setPort(TW::A, sig_a[i]);
		gate->setPort(TW::B, sig_b[i]);
		gate->setPort(TW::Y, sig_y[i]);
	}
}

void simplemap_reduce(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	if (sig_y.size() == 0)
		return;

	if (sig_a.size() == 0) {
		if (cell->type == TW($reduce_and))  module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.size())));
		if (cell->type == TW($reduce_or))   module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		if (cell->type == TW($reduce_xor))  module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		if (cell->type == TW($reduce_xnor)) module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.size())));
		if (cell->type == TW($reduce_bool)) module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		return;
	}

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	IdString gate_type;
	if (cell->type == TW($reduce_and))  gate_type = TW($_AND_);
	if (cell->type == TW($reduce_or))   gate_type = TW($_OR_);
	if (cell->type == TW($reduce_xor))  gate_type = TW($_XOR_);
	if (cell->type == TW($reduce_xnor)) gate_type = TW($_XOR_);
	if (cell->type == TW($reduce_bool)) gate_type = TW($_OR_);
	log_assert(!gate_type.empty());

	RTLIL::Cell *last_output_cell = NULL;

	while (sig_a.size() > 1)
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_TWINE, sig_a.size() / 2);

		for (int i = 0; i < sig_a.size(); i += 2)
		{
			if (i+1 == sig_a.size()) {
				sig_t.append(sig_a[i]);
				continue;
			}

			RTLIL::Cell *gate = module->addCell(NEW_TWINE, gate_type);
			transfer_src(gate, cell);
			gate->setPort(TW::A, sig_a[i]);
			gate->setPort(TW::B, sig_a[i+1]);
			gate->setPort(TW::Y, sig_t[i/2]);
			last_output_cell = gate;
		}

		sig_a = sig_t;
	}

	if (cell->type == TW($reduce_xnor)) {
		RTLIL::SigSpec sig_t = module->addWire(NEW_TWINE);
		RTLIL::Cell *gate = module->addCell(NEW_TWINE, TW($_NOT_));
		transfer_src(gate, cell);
		gate->setPort(TW::A, sig_a);
		gate->setPort(TW::Y, sig_t);
		last_output_cell = gate;
		sig_a = sig_t;
	}

	if (last_output_cell == NULL) {
		module->connect(RTLIL::SigSig(sig_y, sig_a));
	} else {
		last_output_cell->setPort(TW::Y, sig_y);
	}
}

static void logic_reduce(RTLIL::Module *module, RTLIL::SigSpec &sig, RTLIL::Cell *cell)
{
	while (sig.size() > 1)
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_TWINE, sig.size() / 2);

		for (int i = 0; i < sig.size(); i += 2)
		{
			if (i+1 == sig.size()) {
				sig_t.append(sig[i]);
				continue;
			}

			RTLIL::Cell *gate = module->addCell(NEW_TWINE, TW($_OR_));
			transfer_src(gate, cell);
			gate->setPort(TW::A, sig[i]);
			gate->setPort(TW::B, sig[i+1]);
			gate->setPort(TW::Y, sig_t[i/2]);
		}

		sig = sig_t;
	}

	if (sig.size() == 0)
		sig = State::S0;
}

void simplemap_lognot(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	logic_reduce(module, sig_a, cell);

	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	if (sig_y.size() == 0)
		return;

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	RTLIL::Cell *gate = module->addCell(NEW_TWINE, TW($_NOT_));
	transfer_src(gate, cell);
	gate->setPort(TW::A, sig_a);
	gate->setPort(TW::Y, sig_y);
}

void simplemap_logbin(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	logic_reduce(module, sig_a, cell);

	RTLIL::SigSpec sig_b = cell->getPort(TW::B);
	logic_reduce(module, sig_b, cell);

	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	if (sig_y.size() == 0)
		return;

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	IdString gate_type;
	if (cell->type == TW($logic_and)) gate_type = TW($_AND_);
	if (cell->type == TW($logic_or))  gate_type = TW($_OR_);
	log_assert(!gate_type.empty());

	RTLIL::Cell *gate = module->addCell(NEW_TWINE, gate_type);
	transfer_src(gate, cell);
	gate->setPort(TW::A, sig_a);
	gate->setPort(TW::B, sig_b);
	gate->setPort(TW::Y, sig_y);
}

void simplemap_eqne(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_b = cell->getPort(TW::B);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);
	bool is_signed = cell->parameters.at(ID::A_SIGNED).as_bool();
	bool is_ne = cell->type.in(TW($ne), TW($nex));

	RTLIL::SigSpec xor_out = module->addWire(NEW_TWINE, max(GetSize(sig_a), GetSize(sig_b)));
	RTLIL::Cell *xor_cell = module->addXor(NEW_TWINE, sig_a, sig_b, xor_out, is_signed);
	transfer_src(xor_cell, cell);
	simplemap_bitop(module, xor_cell);
	module->remove(xor_cell);

	RTLIL::SigSpec reduce_out = is_ne ? sig_y : module->addWire(NEW_TWINE);
	RTLIL::Cell *reduce_cell = module->addReduceOr(NEW_TWINE, xor_out, reduce_out);
	transfer_src(reduce_cell, cell);
	simplemap_reduce(module, reduce_cell);
	module->remove(reduce_cell);

	if (!is_ne) {
		RTLIL::Cell *not_cell = module->addLogicNot(NEW_TWINE, reduce_out, sig_y);
		transfer_src(not_cell, cell);
		simplemap_lognot(module, not_cell);
		module->remove(not_cell);
	}
}

void simplemap_mux(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_b = cell->getPort(TW::B);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_TWINE, TW($_MUX_));
		transfer_src(gate, cell);
		gate->setPort(TW::A, sig_a[i]);
		gate->setPort(TW::B, sig_b[i]);
		gate->setPort(TW::S, cell->getPort(TW::S));
		gate->setPort(TW::Y, sig_y[i]);
	}
}

void simplemap_bwmux(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_b = cell->getPort(TW::B);
	RTLIL::SigSpec sig_s = cell->getPort(TW::S);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_TWINE, TW($_MUX_));
		transfer_src(gate, cell);
		gate->setPort(TW::A, sig_a[i]);
		gate->setPort(TW::B, sig_b[i]);
		gate->setPort(TW::S, sig_s[i]);
		gate->setPort(TW::Y, sig_y[i]);
	}
}

void simplemap_tribuf(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_e = cell->getPort(TW::EN);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_TWINE, TW($_TBUF_));
		transfer_src(gate, cell);
		gate->setPort(TW::A, sig_a[i]);
		gate->setPort(TW::E, sig_e);
		gate->setPort(TW::Y, sig_y[i]);
	}
}

void simplemap_bmux(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec sel = cell->getPort(TW::S);
	SigSpec data = cell->getPort(TW::A);
	int width = GetSize(cell->getPort(TW::Y));

	for (int idx = 0; idx < GetSize(sel); idx++) {
		SigSpec new_data = module->addWire(NEW_TWINE, GetSize(data)/2);
		for (int i = 0; i < GetSize(new_data); i += width) {
			for (int k = 0; k < width; k++) {
				RTLIL::Cell *gate = module->addCell(NEW_TWINE, TW($_MUX_));
				transfer_src(gate, cell);
				gate->setPort(TW::A, data[i*2+k]);
				gate->setPort(TW::B, data[i*2+width+k]);
				gate->setPort(TW::S, sel[idx]);
				gate->setPort(TW::Y, new_data[i+k]);
			}
		}
		data = new_data;
	}

	module->connect(cell->getPort(TW::Y), data);
}

void simplemap_lut(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec lut_ctrl = cell->getPort(TW::A);
	SigSpec lut_data = cell->getParam(ID::LUT);
	lut_data.extend_u0(1 << cell->getParam(ID::WIDTH).as_int());

	for (int idx = 0; GetSize(lut_data) > 1; idx++) {
		SigSpec new_lut_data = module->addWire(NEW_TWINE, GetSize(lut_data)/2);
		for (int i = 0; i < GetSize(lut_data); i += 2) {
			RTLIL::Cell *gate = module->addCell(NEW_TWINE, TW($_MUX_));
			transfer_src(gate, cell);
			gate->setPort(TW::A, lut_data[i]);
			gate->setPort(TW::B, lut_data[i+1]);
			gate->setPort(TW::S, lut_ctrl[idx]);
			gate->setPort(TW::Y, new_lut_data[i/2]);
		}
		lut_data = new_lut_data;
	}

	module->connect(cell->getPort(TW::Y), lut_data);
}

void simplemap_sop(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec ctrl = cell->getPort(TW::A);
	SigSpec table = cell->getParam(ID::TABLE);

	int width = cell->getParam(ID::WIDTH).as_int();
	int depth = cell->getParam(ID::DEPTH).as_int();
	table.extend_u0(2 * width * depth);

	SigSpec products;

	for (int i = 0; i < depth; i++) {
		SigSpec in, pat;
		for (int j = 0; j < width; j++) {
			if (table[2*i*width + 2*j + 0] == State::S1) {
				in.append(ctrl[j]);
				pat.append(State::S0);
			}
			if (table[2*i*width + 2*j + 1] == State::S1) {
				in.append(ctrl[j]);
				pat.append(State::S1);
			}
		}

		products.append(GetSize(in) > 0 ? module->Eq(NEW_TWINE, in, pat) : State::S1);
	}

	module->connect(cell->getPort(TW::Y), module->ReduceOr(NEW_TWINE, products));
}

void simplemap_slice(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int offset = cell->parameters.at(ID::OFFSET).as_int();
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);
	module->connect(RTLIL::SigSig(sig_y, sig_a.extract(offset, sig_y.size())));
}

void simplemap_concat(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_ab = cell->getPort(TW::A);
	sig_ab.append(cell->getPort(TW::B));
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);
	module->connect(RTLIL::SigSig(sig_y, sig_ab));
}

void simplemap_ff(RTLIL::Module *, RTLIL::Cell *cell)
{
	FfData ff(nullptr, cell);
	for (int i = 0; i < ff.width; i++) {
		FfData fff = ff.slice({i});
		fff.is_fine = true;
		fff.emit();
	}
}

void simplemap_pmux(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(TW::A);
	RTLIL::SigSpec sig_b = cell->getPort(TW::B);
	RTLIL::SigSpec sig_s = cell->getPort(TW::S);
	RTLIL::SigSpec sig_y = cell->getPort(TW::Y);

	int width = GetSize(sig_a);
	int s_width = GetSize(sig_s);

	// Implement: |S
	RTLIL::SigSpec any_s = sig_s;
	logic_reduce(module, any_s, cell);

	for (int i = 0; i < width; i++) {
		RTLIL::SigSpec b_and_bits;

		// Implement: B_AND_BITS = B_AND_S[WIDTH*j+i]
		for (int j = 0; j < s_width; j++) {
			RTLIL::Cell *and_gate = module->addCell(NEW_TWINE, TW($_AND_));
			transfer_src(and_gate, cell);
			and_gate->setPort(TW::A, sig_b[j * width + i]);
			and_gate->setPort(TW::B, sig_s[j]);

			RTLIL::SigSpec and_y = module->addWire(NEW_TWINE, 1);
			and_gate->setPort(TW::Y, and_y);
			b_and_bits.append(and_y);
		}

		// Implement: Y_B[i] = |B_AND_BITS
		logic_reduce(module, b_and_bits, cell);

		// Implement: Y[i] = |S ? Y_B[i] : A[i]
		RTLIL::Cell *mux_gate = module->addCell(NEW_TWINE, TW($_MUX_));
		transfer_src(mux_gate, cell);
		mux_gate->setPort(TW::A, sig_a[i]);
		mux_gate->setPort(TW::B, b_and_bits);
		mux_gate->setPort(TW::S, any_s);
		mux_gate->setPort(TW::Y, sig_y[i]);
	}
}

void simplemap_get_mappers(dict<IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> &mappers)
{
	mappers[TW($not)]         = simplemap_not;
	mappers[TW($pos)]         = simplemap_pos;
	mappers[TW($buf)]         = simplemap_buf;
	mappers[TW($and)]         = simplemap_bitop;
	mappers[TW($or)]          = simplemap_bitop;
	mappers[TW($xor)]         = simplemap_bitop;
	mappers[TW($xnor)]        = simplemap_bitop;
	mappers[TW($bweqx)]       = simplemap_bitop;
	mappers[TW($reduce_and)]  = simplemap_reduce;
	mappers[TW($reduce_or)]   = simplemap_reduce;
	mappers[TW($reduce_xor)]  = simplemap_reduce;
	mappers[TW($reduce_xnor)] = simplemap_reduce;
	mappers[TW($reduce_bool)] = simplemap_reduce;
	mappers[TW($logic_not)]   = simplemap_lognot;
	mappers[TW($logic_and)]   = simplemap_logbin;
	mappers[TW($logic_or)]    = simplemap_logbin;
	mappers[TW($eq)]          = simplemap_eqne;
	mappers[TW($eqx)]         = simplemap_eqne;
	mappers[TW($ne)]          = simplemap_eqne;
	mappers[TW($nex)]         = simplemap_eqne;
	mappers[TW($mux)]         = simplemap_mux;
	mappers[TW($pmux)]        = simplemap_pmux;
	mappers[TW($bwmux)]       = simplemap_bwmux;
	mappers[TW($tribuf)]      = simplemap_tribuf;
	mappers[TW($bmux)]        = simplemap_bmux;
	mappers[TW($lut)]         = simplemap_lut;
	mappers[TW($sop)]         = simplemap_sop;
	mappers[TW($slice)]       = simplemap_slice;
	mappers[TW($concat)]      = simplemap_concat;
	mappers[TW($sr)]          = simplemap_ff;
	mappers[TW($ff)]          = simplemap_ff;
	mappers[TW($dff)]         = simplemap_ff;
	mappers[TW($dffe)]        = simplemap_ff;
	mappers[TW($dffsr)]       = simplemap_ff;
	mappers[TW($dffsre)]      = simplemap_ff;
	mappers[TW($adff)]        = simplemap_ff;
	mappers[TW($sdff)]        = simplemap_ff;
	mappers[TW($adffe)]       = simplemap_ff;
	mappers[TW($sdffe)]       = simplemap_ff;
	mappers[TW($sdffce)]      = simplemap_ff;
	mappers[TW($aldff)]       = simplemap_ff;
	mappers[TW($aldffe)]      = simplemap_ff;
	mappers[TW($dlatch)]      = simplemap_ff;
	mappers[TW($adlatch)]     = simplemap_ff;
	mappers[TW($dlatchsr)]    = simplemap_ff;
}

void simplemap(RTLIL::Module *module, RTLIL::Cell *cell)
{
	static dict<IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> mappers;
	static bool initialized_mappers = false;

	if (!initialized_mappers) {
		simplemap_get_mappers(mappers);
		initialized_mappers = true;
	}

	mappers.at(cell->type)(module, cell);
}

YOSYS_NAMESPACE_END
PRIVATE_NAMESPACE_BEGIN

struct SimplemapPass : public Pass {
	SimplemapPass() : Pass("simplemap", "mapping simple coarse-grain cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    simplemap [selection]\n");
		log("\n");
		log("This pass maps a small selection of simple coarse-grain cells to yosys gate\n");
		log("primitives. The following internal cell types are mapped by this pass:\n");
		log("\n");
		log("  $not, $pos, $and, $or, $xor, $xnor\n");
		log("  $reduce_and, $reduce_or, $reduce_xor, $reduce_xnor, $reduce_bool\n");
		log("  $logic_not, $logic_and, $logic_or, $mux, $pmux, $tribuf\n");
		log("  $sr, $ff, $dff, $dffe, $dffsr, $dffsre, $adff, $adffe, $aldff, $aldffe, $sdff,\n");
		log("  $sdffe, $sdffce, $dlatch, $adlatch, $dlatchsr\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing SIMPLEMAP pass (map simple cells to gate primitives).\n");
		extra_args(args, 1, design);

		dict<IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> mappers;
		simplemap_get_mappers(mappers);

		for (auto mod : design->modules()) {
			if (!design->selected(mod) || mod->get_blackbox_attribute())
				continue;
			std::vector<RTLIL::Cell*> cells = mod->cells();
			for (auto cell : cells) {
				if (mappers.count(cell->type) == 0)
					continue;
				if (!design->selected(mod, cell))
					continue;
				log("Mapping %s.%s (%s).\n", mod, cell, cell->type.unescaped());
				mappers.at(cell->type)(mod, cell);
				mod->remove(cell);
			}
		}
	}
} SimplemapPass;

PRIVATE_NAMESPACE_END
