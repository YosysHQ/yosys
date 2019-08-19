/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

USING_YOSYS_NAMESPACE
YOSYS_NAMESPACE_BEGIN

void simplemap_not(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at(ID(A_SIGNED)).as_bool());

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_NOT_));
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID::A, sig_a[i]);
		gate->setPort(ID::Y, sig_y[i]);
	}
}

void simplemap_pos(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at(ID(A_SIGNED)).as_bool());

	module->connect(RTLIL::SigSig(sig_y, sig_a));
}

void simplemap_bitop(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_b = cell->getPort(ID::B);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at(ID(A_SIGNED)).as_bool());
	sig_b.extend_u0(GetSize(sig_y), cell->parameters.at(ID(B_SIGNED)).as_bool());

	if (cell->type == ID($xnor))
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID, GetSize(sig_y));

		for (int i = 0; i < GetSize(sig_y); i++) {
			RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_NOT_));
			gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
			gate->setPort(ID::A, sig_t[i]);
			gate->setPort(ID::Y, sig_y[i]);
		}

		sig_y = sig_t;
	}

	IdString gate_type;
	if (cell->type == ID($and))  gate_type = ID($_AND_);
	if (cell->type == ID($or))   gate_type = ID($_OR_);
	if (cell->type == ID($xor))  gate_type = ID($_XOR_);
	if (cell->type == ID($xnor)) gate_type = ID($_XOR_);
	log_assert(!gate_type.empty());

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
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
			gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
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
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
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
			gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
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
	gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
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
	gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
	gate->setPort(ID::A, sig_a);
	gate->setPort(ID::B, sig_b);
	gate->setPort(ID::Y, sig_y);
}

void simplemap_eqne(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_b = cell->getPort(ID::B);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);
	bool is_signed = cell->parameters.at(ID(A_SIGNED)).as_bool();
	bool is_ne = cell->type.in(ID($ne), ID($nex));

	RTLIL::SigSpec xor_out = module->addWire(NEW_ID, max(GetSize(sig_a), GetSize(sig_b)));
	RTLIL::Cell *xor_cell = module->addXor(NEW_ID, sig_a, sig_b, xor_out, is_signed);
	xor_cell->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
	simplemap_bitop(module, xor_cell);
	module->remove(xor_cell);

	RTLIL::SigSpec reduce_out = is_ne ? sig_y : module->addWire(NEW_ID);
	RTLIL::Cell *reduce_cell = module->addReduceOr(NEW_ID, xor_out, reduce_out);
	reduce_cell->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
	simplemap_reduce(module, reduce_cell);
	module->remove(reduce_cell);

	if (!is_ne) {
		RTLIL::Cell *not_cell = module->addLogicNot(NEW_ID, reduce_out, sig_y);
		not_cell->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
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
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID::A, sig_a[i]);
		gate->setPort(ID::B, sig_b[i]);
		gate->setPort(ID(S), cell->getPort(ID(S)));
		gate->setPort(ID::Y, sig_y[i]);
	}
}

void simplemap_tribuf(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_e = cell->getPort(ID(EN));
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_TBUF_));
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID::A, sig_a[i]);
		gate->setPort(ID(E), sig_e);
		gate->setPort(ID::Y, sig_y[i]);
	}
}

void simplemap_lut(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec lut_ctrl = cell->getPort(ID::A);
	SigSpec lut_data = cell->getParam(ID(LUT));
	lut_data.extend_u0(1 << cell->getParam(ID(WIDTH)).as_int());

	for (int idx = 0; GetSize(lut_data) > 1; idx++) {
		SigSpec sig_s = lut_ctrl[idx];
		SigSpec new_lut_data = module->addWire(NEW_ID, GetSize(lut_data)/2);
		for (int i = 0; i < GetSize(lut_data); i += 2) {
			RTLIL::Cell *gate = module->addCell(NEW_ID, ID($_MUX_));
			gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
			gate->setPort(ID::A, lut_data[i]);
			gate->setPort(ID::B, lut_data[i+1]);
			gate->setPort(ID(S), lut_ctrl[idx]);
			gate->setPort(ID::Y, new_lut_data[i/2]);
		}
		lut_data = new_lut_data;
	}

	module->connect(cell->getPort(ID::Y), lut_data);
}

void simplemap_sop(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec ctrl = cell->getPort(ID::A);
	SigSpec table = cell->getParam(ID(TABLE));

	int width = cell->getParam(ID(WIDTH)).as_int();
	int depth = cell->getParam(ID(DEPTH)).as_int();
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
	int offset = cell->parameters.at(ID(OFFSET)).as_int();
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

void simplemap_sr(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at(ID(WIDTH)).as_int();
	char set_pol = cell->parameters.at(ID(SET_POLARITY)).as_bool() ? 'P' : 'N';
	char clr_pol = cell->parameters.at(ID(CLR_POLARITY)).as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_s = cell->getPort(ID(SET));
	RTLIL::SigSpec sig_r = cell->getPort(ID(CLR));
	RTLIL::SigSpec sig_q = cell->getPort(ID(Q));

	std::string gate_type = stringf("$_SR_%c%c_", set_pol, clr_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID(S), sig_s[i]);
		gate->setPort(ID(R), sig_r[i]);
		gate->setPort(ID(Q), sig_q[i]);
	}
}

void simplemap_ff(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at(ID(WIDTH)).as_int();

	RTLIL::SigSpec sig_d = cell->getPort(ID(D));
	RTLIL::SigSpec sig_q = cell->getPort(ID(Q));

	IdString gate_type = ID($_FF_);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID(D), sig_d[i]);
		gate->setPort(ID(Q), sig_q[i]);
	}
}

void simplemap_dff(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at(ID(WIDTH)).as_int();
	char clk_pol = cell->parameters.at(ID(CLK_POLARITY)).as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_clk = cell->getPort(ID(CLK));
	RTLIL::SigSpec sig_d = cell->getPort(ID(D));
	RTLIL::SigSpec sig_q = cell->getPort(ID(Q));

	IdString gate_type = stringf("$_DFF_%c_", clk_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID(C), sig_clk);
		gate->setPort(ID(D), sig_d[i]);
		gate->setPort(ID(Q), sig_q[i]);
	}
}

void simplemap_dffe(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at(ID(WIDTH)).as_int();
	char clk_pol = cell->parameters.at(ID(CLK_POLARITY)).as_bool() ? 'P' : 'N';
	char en_pol = cell->parameters.at(ID(EN_POLARITY)).as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_clk = cell->getPort(ID(CLK));
	RTLIL::SigSpec sig_en = cell->getPort(ID(EN));
	RTLIL::SigSpec sig_d = cell->getPort(ID(D));
	RTLIL::SigSpec sig_q = cell->getPort(ID(Q));

	IdString gate_type = stringf("$_DFFE_%c%c_", clk_pol, en_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID(C), sig_clk);
		gate->setPort(ID(E), sig_en);
		gate->setPort(ID(D), sig_d[i]);
		gate->setPort(ID(Q), sig_q[i]);
	}
}

void simplemap_dffsr(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at(ID(WIDTH)).as_int();
	char clk_pol = cell->parameters.at(ID(CLK_POLARITY)).as_bool() ? 'P' : 'N';
	char set_pol = cell->parameters.at(ID(SET_POLARITY)).as_bool() ? 'P' : 'N';
	char clr_pol = cell->parameters.at(ID(CLR_POLARITY)).as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_clk = cell->getPort(ID(CLK));
	RTLIL::SigSpec sig_s = cell->getPort(ID(SET));
	RTLIL::SigSpec sig_r = cell->getPort(ID(CLR));
	RTLIL::SigSpec sig_d = cell->getPort(ID(D));
	RTLIL::SigSpec sig_q = cell->getPort(ID(Q));

	IdString gate_type = stringf("$_DFFSR_%c%c%c_", clk_pol, set_pol, clr_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID(C), sig_clk);
		gate->setPort(ID(S), sig_s[i]);
		gate->setPort(ID(R), sig_r[i]);
		gate->setPort(ID(D), sig_d[i]);
		gate->setPort(ID(Q), sig_q[i]);
	}
}

void simplemap_adff(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at(ID(WIDTH)).as_int();
	char clk_pol = cell->parameters.at(ID(CLK_POLARITY)).as_bool() ? 'P' : 'N';
	char rst_pol = cell->parameters.at(ID(ARST_POLARITY)).as_bool() ? 'P' : 'N';

	std::vector<RTLIL::State> rst_val = cell->parameters.at(ID(ARST_VALUE)).bits;
	while (int(rst_val.size()) < width)
		rst_val.push_back(RTLIL::State::S0);

	RTLIL::SigSpec sig_clk = cell->getPort(ID(CLK));
	RTLIL::SigSpec sig_rst = cell->getPort(ID(ARST));
	RTLIL::SigSpec sig_d = cell->getPort(ID(D));
	RTLIL::SigSpec sig_q = cell->getPort(ID(Q));

	IdString gate_type_0 = stringf("$_DFF_%c%c0_", clk_pol, rst_pol);
	IdString gate_type_1 = stringf("$_DFF_%c%c1_", clk_pol, rst_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, rst_val.at(i) == RTLIL::State::S1 ? gate_type_1 : gate_type_0);
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID(C), sig_clk);
		gate->setPort(ID(R), sig_rst);
		gate->setPort(ID(D), sig_d[i]);
		gate->setPort(ID(Q), sig_q[i]);
	}
}

void simplemap_dlatch(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at(ID(WIDTH)).as_int();
	char en_pol = cell->parameters.at(ID(EN_POLARITY)).as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_en = cell->getPort(ID(EN));
	RTLIL::SigSpec sig_d = cell->getPort(ID(D));
	RTLIL::SigSpec sig_q = cell->getPort(ID(Q));

	IdString gate_type = stringf("$_DLATCH_%c_", en_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute(ID(src), cell->get_strpool_attribute(ID(src)));
		gate->setPort(ID(E), sig_en);
		gate->setPort(ID(D), sig_d[i]);
		gate->setPort(ID(Q), sig_q[i]);
	}
}

void simplemap_get_mappers(std::map<RTLIL::IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> &mappers)
{
	mappers[ID($not)]         = simplemap_not;
	mappers[ID($pos)]         = simplemap_pos;
	mappers[ID($and)]         = simplemap_bitop;
	mappers[ID($or)]          = simplemap_bitop;
	mappers[ID($xor)]         = simplemap_bitop;
	mappers[ID($xnor)]        = simplemap_bitop;
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
	mappers[ID($tribuf)]      = simplemap_tribuf;
	mappers[ID($lut)]         = simplemap_lut;
	mappers[ID($sop)]         = simplemap_sop;
	mappers[ID($slice)]       = simplemap_slice;
	mappers[ID($concat)]      = simplemap_concat;
	mappers[ID($sr)]          = simplemap_sr;
	mappers[ID($ff)]          = simplemap_ff;
	mappers[ID($dff)]         = simplemap_dff;
	mappers[ID($dffe)]        = simplemap_dffe;
	mappers[ID($dffsr)]       = simplemap_dffsr;
	mappers[ID($adff)]        = simplemap_adff;
	mappers[ID($dlatch)]      = simplemap_dlatch;
}

void simplemap(RTLIL::Module *module, RTLIL::Cell *cell)
{
	static std::map<RTLIL::IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> mappers;
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
	void help() YS_OVERRIDE
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
		log("  $sr, $ff, $dff, $dffsr, $adff, $dlatch\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing SIMPLEMAP pass (map simple cells to gate primitives).\n");
		extra_args(args, 1, design);

		std::map<RTLIL::IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> mappers;
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
