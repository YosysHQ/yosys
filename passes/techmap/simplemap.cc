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

void simplemap_not(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at(ID::A_SIGNED).as_bool());

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_NOT_));
		gate->attributes[ID::src] = cell->attributes[ID::src];
		gate->setPort(ID::A, sig_a[i]);
		gate->setPort(ID::Y, sig_y[i]);
	}
}

void simplemap_pos(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at(ID::A_SIGNED).as_bool());

	module->connect(RTLIL::SigSig(sig_y, sig_a));
}

void simplemap_bitop(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_b = cell->getPort(ID::B);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	if (cell->type != ID($bweqx)) {
		sig_a.extend_u0(GetSize(sig_y), cell->parameters.at(ID::A_SIGNED).as_bool());
		sig_b.extend_u0(GetSize(sig_y), cell->parameters.at(ID::B_SIGNED).as_bool());
	}

	IdString gate_type;
	if (cell->type == ID($and))   gate_type = ID($_AND_);
	if (cell->type == ID($or))    gate_type = ID($_OR_);
	if (cell->type == ID($xor))   gate_type = ID($_XOR_);
	if (cell->type == ID($xnor))  gate_type = ID($_XNOR_);
	if (cell->type == ID($bweqx)) gate_type = ID($_XNOR_);
	log_assert(!gate_type.empty());

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->attributes[ID::src] = cell->attributes[ID::src];
		gate->setPort(ID::A, sig_a[i]);
		gate->setPort(ID::B, sig_b[i]);
		gate->setPort(ID::Y, sig_y[i]);
	}
}

void simplemap_reduce(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	if (sig_y.size() == 0)
		return;

	if (sig_a.size() == 0) {
		if (cell->type == ID($reduce_and))  module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.size())));
		if (cell->type == ID($reduce_or))   module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		if (cell->type == ID($reduce_xor))  module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		if (cell->type == ID($reduce_xnor)) module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.size())));
		if (cell->type == ID($reduce_bool)) module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		return;
	}

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	IdString gate_type;
	if (cell->type == ID($reduce_and))  gate_type = ID($_AND_);
	if (cell->type == ID($reduce_or))   gate_type = ID($_OR_);
	if (cell->type == ID($reduce_xor))  gate_type = ID($_XOR_);
	if (cell->type == ID($reduce_xnor)) gate_type = ID($_XOR_);
	if (cell->type == ID($reduce_bool)) gate_type = ID($_OR_);
	log_assert(!gate_type.empty());

	RTLIL::Cell *last_output_cell = NULL;

	while (sig_a.size() > 1)
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID, sig_a.size() / 2);

		for (int i = 0; i < sig_a.size(); i += 2)
		{
			if (i+1 == sig_a.size()) {
				sig_t.append(sig_a[i]);
				continue;
			}

			RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
			gate->attributes[ID::src] = cell->attributes[ID::src];
			gate->setPort(ID::A, sig_a[i]);
			gate->setPort(ID::B, sig_a[i+1]);
			gate->setPort(ID::Y, sig_t[i/2]);
			last_output_cell = gate;
		}

		sig_a = sig_t;
	}

	if (cell->type == ID($reduce_xnor)) {
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID);
		RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_NOT_));
		gate->attributes[ID::src] = cell->attributes[ID::src];
		gate->setPort(ID::A, sig_a);
		gate->setPort(ID::Y, sig_t);
		last_output_cell = gate;
		sig_a = sig_t;
	}

	if (last_output_cell == NULL) {
		module->connect(RTLIL::SigSig(sig_y, sig_a));
	} else {
		last_output_cell->setPort(ID::Y, sig_y);
	}
}

static void logic_reduce(RTLIL::Module *module, RTLIL::SigSpec &sig, RTLIL::Cell *cell)
{
	while (sig.size() > 1)
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID, sig.size() / 2);

		for (int i = 0; i < sig.size(); i += 2)
		{
			if (i+1 == sig.size()) {
				sig_t.append(sig[i]);
				continue;
			}

			RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_OR_));
			gate->attributes[ID::src] = cell->attributes[ID::src];
			gate->setPort(ID::A, sig[i]);
			gate->setPort(ID::B, sig[i+1]);
			gate->setPort(ID::Y, sig_t[i/2]);
		}

		sig = sig_t;
	}

	if (sig.size() == 0)
		sig = State::S0;
}

void simplemap_lognot(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	logic_reduce(module, sig_a, cell);

	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	if (sig_y.size() == 0)
		return;

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_NOT_));
	gate->attributes[ID::src] = cell->attributes[ID::src];
	gate->setPort(ID::A, sig_a);
	gate->setPort(ID::Y, sig_y);
}

void simplemap_logbin(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	logic_reduce(module, sig_a, cell);

	RTLIL::SigSpec sig_b = cell->getPort(ID::B);
	logic_reduce(module, sig_b, cell);

	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	if (sig_y.size() == 0)
		return;

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	IdString gate_type;
	if (cell->type == ID($logic_and)) gate_type = ID($_AND_);
	if (cell->type == ID($logic_or))  gate_type = ID($_OR_);
	log_assert(!gate_type.empty());

	RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
	gate->attributes[ID::src] = cell->attributes[ID::src];
	gate->setPort(ID::A, sig_a);
	gate->setPort(ID::B, sig_b);
	gate->setPort(ID::Y, sig_y);
}

void simplemap_eqne(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_b = cell->getPort(ID::B);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);
	bool is_signed = cell->parameters.at(ID::A_SIGNED).as_bool();
	bool is_ne = cell->type.in(ID($ne), ID($nex));

	RTLIL::SigSpec xor_out = module->addWire(NEW_ID, max(GetSize(sig_a), GetSize(sig_b)));
	RTLIL::Cell *xor_cell = module->addXor(NEW_ID, sig_a, sig_b, xor_out, is_signed);
	xor_cell->attributes[ID::src] = cell->attributes[ID::src];
	simplemap_bitop(module, xor_cell);
	module->remove(xor_cell);

	RTLIL::SigSpec reduce_out = is_ne ? sig_y : module->addWire(NEW_ID);
	RTLIL::Cell *reduce_cell = module->addReduceOr(NEW_ID, xor_out, reduce_out);
	reduce_cell->attributes[ID::src] = cell->attributes[ID::src];
	simplemap_reduce(module, reduce_cell);
	module->remove(reduce_cell);

	if (!is_ne) {
		RTLIL::Cell *not_cell = module->addLogicNot(NEW_ID, reduce_out, sig_y);
		not_cell->attributes[ID::src] = cell->attributes[ID::src];
                simplemap_lognot(module, not_cell);
		module->remove(not_cell);
	}
}

void simplemap_mux(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_b = cell->getPort(ID::B);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_MUX_));
		gate->attributes[ID::src] = cell->attributes[ID::src];
		gate->setPort(ID::A, sig_a[i]);
		gate->setPort(ID::B, sig_b[i]);
		gate->setPort(ID::S, cell->getPort(ID::S));
		gate->setPort(ID::Y, sig_y[i]);
	}
}

void simplemap_bwmux(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_b = cell->getPort(ID::B);
	RTLIL::SigSpec sig_s = cell->getPort(ID::S);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_MUX_));
		gate->attributes[ID::src] = cell->attributes[ID::src];
		gate->setPort(ID::A, sig_a[i]);
		gate->setPort(ID::B, sig_b[i]);
		gate->setPort(ID::S, sig_s[i]);
		gate->setPort(ID::Y, sig_y[i]);
	}
}

void simplemap_tribuf(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_e = cell->getPort(ID::EN);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_TBUF_));
		gate->attributes[ID::src] = cell->attributes[ID::src];
		gate->setPort(ID::A, sig_a[i]);
		gate->setPort(ID::E, sig_e);
		gate->setPort(ID::Y, sig_y[i]);
	}
}

void simplemap_bmux(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec sel = cell->getPort(ID::S);
	SigSpec data = cell->getPort(ID::A);
	int width = GetSize(cell->getPort(ID::Y));

	for (int idx = 0; idx < GetSize(sel); idx++) {
		SigSpec new_data = module->addWire(NEW_ID, GetSize(data)/2);
		for (int i = 0; i < GetSize(new_data); i += width) {
			for (int k = 0; k < width; k++) {
				RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_MUX_));
				gate->attributes[ID::src] = cell->attributes[ID::src];
				gate->setPort(ID::A, data[i*2+k]);
				gate->setPort(ID::B, data[i*2+width+k]);
				gate->setPort(ID::S, sel[idx]);
				gate->setPort(ID::Y, new_data[i+k]);
			}
		}
		data = new_data;
	}

	module->connect(cell->getPort(ID::Y), data);
}

void simplemap_lut(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec lut_ctrl = cell->getPort(ID::A);
	SigSpec lut_data = cell->getParam(ID::LUT);
	lut_data.extend_u0(1 << cell->getParam(ID::WIDTH).as_int());

	for (int idx = 0; GetSize(lut_data) > 1; idx++) {
		SigSpec new_lut_data = module->addWire(NEW_ID, GetSize(lut_data)/2);
		for (int i = 0; i < GetSize(lut_data); i += 2) {
			RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_MUX_));
			gate->attributes[ID::src] = cell->attributes[ID::src];
			gate->setPort(ID::A, lut_data[i]);
			gate->setPort(ID::B, lut_data[i+1]);
			gate->setPort(ID::S, lut_ctrl[idx]);
			gate->setPort(ID::Y, new_lut_data[i/2]);
		}
		lut_data = new_lut_data;
	}

	module->connect(cell->getPort(ID::Y), lut_data);
}

void simplemap_sop(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec ctrl = cell->getPort(ID::A);
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

		products.append(GetSize(in) > 0 ? module->Eq(NEW_ID, in, pat) : State::S1);
	}

	module->connect(cell->getPort(ID::Y), module->ReduceOr(NEW_ID, products));
}

void simplemap_slice(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int offset = cell->parameters.at(ID::OFFSET).as_int();
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);
	module->connect(RTLIL::SigSig(sig_y, sig_a.extract(offset, sig_y.size())));
}

void simplemap_concat(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_ab = cell->getPort(ID::A);
	sig_ab.append(cell->getPort(ID::B));
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);
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

void simplemap_get_mappers(dict<IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> &mappers)
{
	mappers[ID($not)]         = simplemap_not;
	mappers[ID($pos)]         = simplemap_pos;
	mappers[ID($and)]         = simplemap_bitop;
	mappers[ID($or)]          = simplemap_bitop;
	mappers[ID($xor)]         = simplemap_bitop;
	mappers[ID($xnor)]        = simplemap_bitop;
	mappers[ID($bweqx)]       = simplemap_bitop;
	mappers[ID($reduce_and)]  = simplemap_reduce;
	mappers[ID($reduce_or)]   = simplemap_reduce;
	mappers[ID($reduce_xor)]  = simplemap_reduce;
	mappers[ID($reduce_xnor)] = simplemap_reduce;
	mappers[ID($reduce_bool)] = simplemap_reduce;
	mappers[ID($logic_not)]   = simplemap_lognot;
	mappers[ID($logic_and)]   = simplemap_logbin;
	mappers[ID($logic_or)]    = simplemap_logbin;
	mappers[ID($eq)]          = simplemap_eqne;
	mappers[ID($eqx)]         = simplemap_eqne;
	mappers[ID($ne)]          = simplemap_eqne;
	mappers[ID($nex)]         = simplemap_eqne;
	mappers[ID($mux)]         = simplemap_mux;
	mappers[ID($bwmux)]       = simplemap_bwmux;
	mappers[ID($tribuf)]      = simplemap_tribuf;
	mappers[ID($bmux)]        = simplemap_bmux;
	mappers[ID($lut)]         = simplemap_lut;
	mappers[ID($sop)]         = simplemap_sop;
	mappers[ID($slice)]       = simplemap_slice;
	mappers[ID($concat)]      = simplemap_concat;
	mappers[ID($sr)]          = simplemap_ff;
	mappers[ID($ff)]          = simplemap_ff;
	mappers[ID($dff)]         = simplemap_ff;
	mappers[ID($dffe)]        = simplemap_ff;
	mappers[ID($dffsr)]       = simplemap_ff;
	mappers[ID($dffsre)]      = simplemap_ff;
	mappers[ID($adff)]        = simplemap_ff;
	mappers[ID($sdff)]        = simplemap_ff;
	mappers[ID($adffe)]       = simplemap_ff;
	mappers[ID($sdffe)]       = simplemap_ff;
	mappers[ID($sdffce)]      = simplemap_ff;
	mappers[ID($aldff)]       = simplemap_ff;
	mappers[ID($aldffe)]      = simplemap_ff;
	mappers[ID($dlatch)]      = simplemap_ff;
	mappers[ID($adlatch)]     = simplemap_ff;
	mappers[ID($dlatchsr)]    = simplemap_ff;
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
		log("  $logic_not, $logic_and, $logic_or, $mux, $tribuf\n");
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
				log("Mapping %s.%s (%s).\n", log_id(mod), log_id(cell), log_id(cell->type));
				mappers.at(cell->type)(mod, cell);
				mod->remove(cell);
			}
		}
	}
} SimplemapPass;

PRIVATE_NAMESPACE_END
