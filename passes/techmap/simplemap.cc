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
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	RTLIL::SigSpec sig_y = cell->getPort("\\Y");

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at("\\A_SIGNED").as_bool());

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, "$_NOT_");
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\A", sig_a[i]);
		gate->setPort("\\Y", sig_y[i]);
	}
}

void simplemap_pos(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	RTLIL::SigSpec sig_y = cell->getPort("\\Y");

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at("\\A_SIGNED").as_bool());

	module->connect(RTLIL::SigSig(sig_y, sig_a));
}

void simplemap_bitop(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	RTLIL::SigSpec sig_b = cell->getPort("\\B");
	RTLIL::SigSpec sig_y = cell->getPort("\\Y");

	sig_a.extend_u0(GetSize(sig_y), cell->parameters.at("\\A_SIGNED").as_bool());
	sig_b.extend_u0(GetSize(sig_y), cell->parameters.at("\\B_SIGNED").as_bool());

	if (cell->type == "$xnor")
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID, GetSize(sig_y));

		for (int i = 0; i < GetSize(sig_y); i++) {
			RTLIL::Cell *gate = module->addCell(NEW_ID, "$_NOT_");
			gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
			gate->setPort("\\A", sig_t[i]);
			gate->setPort("\\Y", sig_y[i]);
		}

		sig_y = sig_t;
	}

	std::string gate_type;
	if (cell->type == "$and")  gate_type = "$_AND_";
	if (cell->type == "$or")   gate_type = "$_OR_";
	if (cell->type == "$xor")  gate_type = "$_XOR_";
	if (cell->type == "$xnor") gate_type = "$_XOR_";
	log_assert(!gate_type.empty());

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\A", sig_a[i]);
		gate->setPort("\\B", sig_b[i]);
		gate->setPort("\\Y", sig_y[i]);
	}
}

void simplemap_reduce(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	RTLIL::SigSpec sig_y = cell->getPort("\\Y");

	if (sig_y.size() == 0)
		return;

	if (sig_a.size() == 0) {
		if (cell->type == "$reduce_and")  module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.size())));
		if (cell->type == "$reduce_or")   module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		if (cell->type == "$reduce_xor")  module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		if (cell->type == "$reduce_xnor") module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.size())));
		if (cell->type == "$reduce_bool") module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		return;
	}

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	std::string gate_type;
	if (cell->type == "$reduce_and")  gate_type = "$_AND_";
	if (cell->type == "$reduce_or")   gate_type = "$_OR_";
	if (cell->type == "$reduce_xor")  gate_type = "$_XOR_";
	if (cell->type == "$reduce_xnor") gate_type = "$_XOR_";
	if (cell->type == "$reduce_bool") gate_type = "$_OR_";
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
			gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
			gate->setPort("\\A", sig_a[i]);
			gate->setPort("\\B", sig_a[i+1]);
			gate->setPort("\\Y", sig_t[i/2]);
			last_output_cell = gate;
		}

		sig_a = sig_t;
	}

	if (cell->type == "$reduce_xnor") {
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID);
		RTLIL::Cell *gate = module->addCell(NEW_ID, "$_NOT_");
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\A", sig_a);
		gate->setPort("\\Y", sig_t);
		last_output_cell = gate;
		sig_a = sig_t;
	}

	if (last_output_cell == NULL) {
		module->connect(RTLIL::SigSig(sig_y, sig_a));
	} else {
		last_output_cell->setPort("\\Y", sig_y);
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

			RTLIL::Cell *gate = module->addCell(NEW_ID, "$_OR_");
			gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
			gate->setPort("\\A", sig[i]);
			gate->setPort("\\B", sig[i+1]);
			gate->setPort("\\Y", sig_t[i/2]);
		}

		sig = sig_t;
	}

	if (sig.size() == 0)
		sig = RTLIL::SigSpec(0, 1);
}

void simplemap_lognot(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	logic_reduce(module, sig_a, cell);

	RTLIL::SigSpec sig_y = cell->getPort("\\Y");

	if (sig_y.size() == 0)
		return;

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	RTLIL::Cell *gate = module->addCell(NEW_ID, "$_NOT_");
	gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
	gate->setPort("\\A", sig_a);
	gate->setPort("\\Y", sig_y);
}

void simplemap_logbin(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	logic_reduce(module, sig_a, cell);

	RTLIL::SigSpec sig_b = cell->getPort("\\B");
	logic_reduce(module, sig_b, cell);

	RTLIL::SigSpec sig_y = cell->getPort("\\Y");

	if (sig_y.size() == 0)
		return;

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	std::string gate_type;
	if (cell->type == "$logic_and") gate_type = "$_AND_";
	if (cell->type == "$logic_or")  gate_type = "$_OR_";
	log_assert(!gate_type.empty());

	RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
	gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
	gate->setPort("\\A", sig_a);
	gate->setPort("\\B", sig_b);
	gate->setPort("\\Y", sig_y);
}

void simplemap_eqne(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	RTLIL::SigSpec sig_b = cell->getPort("\\B");
	RTLIL::SigSpec sig_y = cell->getPort("\\Y");
	bool is_signed = cell->parameters.at("\\A_SIGNED").as_bool();
	bool is_ne = cell->type == "$ne" || cell->type == "$nex";

	RTLIL::SigSpec xor_out = module->addWire(NEW_ID, max(GetSize(sig_a), GetSize(sig_b)));
	RTLIL::Cell *xor_cell = module->addXor(NEW_ID, sig_a, sig_b, xor_out, is_signed);
	xor_cell->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
	simplemap_bitop(module, xor_cell);
	module->remove(xor_cell);

	RTLIL::SigSpec reduce_out = is_ne ? sig_y : module->addWire(NEW_ID);
	RTLIL::Cell *reduce_cell = module->addReduceOr(NEW_ID, xor_out, reduce_out);
	reduce_cell->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
	simplemap_reduce(module, reduce_cell);
	module->remove(reduce_cell);

	if (!is_ne) {
		RTLIL::Cell *not_cell = module->addLogicNot(NEW_ID, reduce_out, sig_y);
		not_cell->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		simplemap_lognot(module, not_cell);
		module->remove(not_cell);
	}
}

void simplemap_mux(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	RTLIL::SigSpec sig_b = cell->getPort("\\B");
	RTLIL::SigSpec sig_y = cell->getPort("\\Y");

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, "$_MUX_");
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\A", sig_a[i]);
		gate->setPort("\\B", sig_b[i]);
		gate->setPort("\\S", cell->getPort("\\S"));
		gate->setPort("\\Y", sig_y[i]);
	}
}

void simplemap_tribuf(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	RTLIL::SigSpec sig_e = cell->getPort("\\EN");
	RTLIL::SigSpec sig_y = cell->getPort("\\Y");

	for (int i = 0; i < GetSize(sig_y); i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, "$_TBUF_");
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\A", sig_a[i]);
		gate->setPort("\\E", sig_e);
		gate->setPort("\\Y", sig_y[i]);
	}
}

void simplemap_lut(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec lut_ctrl = cell->getPort("\\A");
	SigSpec lut_data = cell->getParam("\\LUT");
	lut_data.extend_u0(1 << cell->getParam("\\WIDTH").as_int());

	for (int idx = 0; GetSize(lut_data) > 1; idx++) {
		SigSpec sig_s = lut_ctrl[idx];
		SigSpec new_lut_data = module->addWire(NEW_ID, GetSize(lut_data)/2);
		for (int i = 0; i < GetSize(lut_data); i += 2) {
			RTLIL::Cell *gate = module->addCell(NEW_ID, "$_MUX_");
			gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
			gate->setPort("\\A", lut_data[i]);
			gate->setPort("\\B", lut_data[i+1]);
			gate->setPort("\\S", lut_ctrl[idx]);
			gate->setPort("\\Y", new_lut_data[i/2]);
		}
		lut_data = new_lut_data;
	}

	module->connect(cell->getPort("\\Y"), lut_data);
}

void simplemap_sop(RTLIL::Module *module, RTLIL::Cell *cell)
{
	SigSpec ctrl = cell->getPort("\\A");
	SigSpec table = cell->getParam("\\TABLE");

	int width = cell->getParam("\\WIDTH").as_int();
	int depth = cell->getParam("\\DEPTH").as_int();
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

	module->connect(cell->getPort("\\Y"), module->ReduceOr(NEW_ID, products));
}

void simplemap_slice(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int offset = cell->parameters.at("\\OFFSET").as_int();
	RTLIL::SigSpec sig_a = cell->getPort("\\A");
	RTLIL::SigSpec sig_y = cell->getPort("\\Y");
	module->connect(RTLIL::SigSig(sig_y, sig_a.extract(offset, sig_y.size())));
}

void simplemap_concat(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_ab = cell->getPort("\\A");
	sig_ab.append(cell->getPort("\\B"));
	RTLIL::SigSpec sig_y = cell->getPort("\\Y");
	module->connect(RTLIL::SigSig(sig_y, sig_ab));
}

void simplemap_sr(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char set_pol = cell->parameters.at("\\SET_POLARITY").as_bool() ? 'P' : 'N';
	char clr_pol = cell->parameters.at("\\CLR_POLARITY").as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_s = cell->getPort("\\SET");
	RTLIL::SigSpec sig_r = cell->getPort("\\CLR");
	RTLIL::SigSpec sig_q = cell->getPort("\\Q");

	std::string gate_type = stringf("$_SR_%c%c_", set_pol, clr_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\S", sig_s[i]);
		gate->setPort("\\R", sig_r[i]);
		gate->setPort("\\Q", sig_q[i]);
	}
}

void simplemap_ff(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();

	RTLIL::SigSpec sig_d = cell->getPort("\\D");
	RTLIL::SigSpec sig_q = cell->getPort("\\Q");

	std::string gate_type = "$_FF_";

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\D", sig_d[i]);
		gate->setPort("\\Q", sig_q[i]);
	}
}

void simplemap_dff(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char clk_pol = cell->parameters.at("\\CLK_POLARITY").as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_clk = cell->getPort("\\CLK");
	RTLIL::SigSpec sig_d = cell->getPort("\\D");
	RTLIL::SigSpec sig_q = cell->getPort("\\Q");

	std::string gate_type = stringf("$_DFF_%c_", clk_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\C", sig_clk);
		gate->setPort("\\D", sig_d[i]);
		gate->setPort("\\Q", sig_q[i]);
	}
}

void simplemap_dffe(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char clk_pol = cell->parameters.at("\\CLK_POLARITY").as_bool() ? 'P' : 'N';
	char en_pol = cell->parameters.at("\\EN_POLARITY").as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_clk = cell->getPort("\\CLK");
	RTLIL::SigSpec sig_en = cell->getPort("\\EN");
	RTLIL::SigSpec sig_d = cell->getPort("\\D");
	RTLIL::SigSpec sig_q = cell->getPort("\\Q");

	std::string gate_type = stringf("$_DFFE_%c%c_", clk_pol, en_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\C", sig_clk);
		gate->setPort("\\E", sig_en);
		gate->setPort("\\D", sig_d[i]);
		gate->setPort("\\Q", sig_q[i]);
	}
}

void simplemap_dffsr(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char clk_pol = cell->parameters.at("\\CLK_POLARITY").as_bool() ? 'P' : 'N';
	char set_pol = cell->parameters.at("\\SET_POLARITY").as_bool() ? 'P' : 'N';
	char clr_pol = cell->parameters.at("\\CLR_POLARITY").as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_clk = cell->getPort("\\CLK");
	RTLIL::SigSpec sig_s = cell->getPort("\\SET");
	RTLIL::SigSpec sig_r = cell->getPort("\\CLR");
	RTLIL::SigSpec sig_d = cell->getPort("\\D");
	RTLIL::SigSpec sig_q = cell->getPort("\\Q");

	std::string gate_type = stringf("$_DFFSR_%c%c%c_", clk_pol, set_pol, clr_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\C", sig_clk);
		gate->setPort("\\S", sig_s[i]);
		gate->setPort("\\R", sig_r[i]);
		gate->setPort("\\D", sig_d[i]);
		gate->setPort("\\Q", sig_q[i]);
	}
}

void simplemap_adff(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char clk_pol = cell->parameters.at("\\CLK_POLARITY").as_bool() ? 'P' : 'N';
	char rst_pol = cell->parameters.at("\\ARST_POLARITY").as_bool() ? 'P' : 'N';

	std::vector<RTLIL::State> rst_val = cell->parameters.at("\\ARST_VALUE").bits;
	while (int(rst_val.size()) < width)
		rst_val.push_back(RTLIL::State::S0);

	RTLIL::SigSpec sig_clk = cell->getPort("\\CLK");
	RTLIL::SigSpec sig_rst = cell->getPort("\\ARST");
	RTLIL::SigSpec sig_d = cell->getPort("\\D");
	RTLIL::SigSpec sig_q = cell->getPort("\\Q");

	std::string gate_type_0 = stringf("$_DFF_%c%c0_", clk_pol, rst_pol);
	std::string gate_type_1 = stringf("$_DFF_%c%c1_", clk_pol, rst_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, rst_val.at(i) == RTLIL::State::S1 ? gate_type_1 : gate_type_0);
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\C", sig_clk);
		gate->setPort("\\R", sig_rst);
		gate->setPort("\\D", sig_d[i]);
		gate->setPort("\\Q", sig_q[i]);
	}
}

void simplemap_dlatch(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char en_pol = cell->parameters.at("\\EN_POLARITY").as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_en = cell->getPort("\\EN");
	RTLIL::SigSpec sig_d = cell->getPort("\\D");
	RTLIL::SigSpec sig_q = cell->getPort("\\Q");

	std::string gate_type = stringf("$_DLATCH_%c_", en_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = module->addCell(NEW_ID, gate_type);
		gate->add_strpool_attribute("\\src", cell->get_strpool_attribute("\\src"));
		gate->setPort("\\E", sig_en);
		gate->setPort("\\D", sig_d[i]);
		gate->setPort("\\Q", sig_q[i]);
	}
}

void simplemap_get_mappers(std::map<RTLIL::IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> &mappers)
{
	mappers["$not"]         = simplemap_not;
	mappers["$pos"]         = simplemap_pos;
	mappers["$and"]         = simplemap_bitop;
	mappers["$or"]          = simplemap_bitop;
	mappers["$xor"]         = simplemap_bitop;
	mappers["$xnor"]        = simplemap_bitop;
	mappers["$reduce_and"]  = simplemap_reduce;
	mappers["$reduce_or"]   = simplemap_reduce;
	mappers["$reduce_xor"]  = simplemap_reduce;
	mappers["$reduce_xnor"] = simplemap_reduce;
	mappers["$reduce_bool"] = simplemap_reduce;
	mappers["$logic_not"]   = simplemap_lognot;
	mappers["$logic_and"]   = simplemap_logbin;
	mappers["$logic_or"]    = simplemap_logbin;
	mappers["$eq"]          = simplemap_eqne;
	mappers["$eqx"]         = simplemap_eqne;
	mappers["$ne"]          = simplemap_eqne;
	mappers["$nex"]         = simplemap_eqne;
	mappers["$mux"]         = simplemap_mux;
	mappers["$tribuf"]      = simplemap_tribuf;
	mappers["$lut"]         = simplemap_lut;
	mappers["$sop"]         = simplemap_sop;
	mappers["$slice"]       = simplemap_slice;
	mappers["$concat"]      = simplemap_concat;
	mappers["$sr"]          = simplemap_sr;
	mappers["$ff"]          = simplemap_ff;
	mappers["$dff"]         = simplemap_dff;
	mappers["$dffe"]        = simplemap_dffe;
	mappers["$dffsr"]       = simplemap_dffsr;
	mappers["$adff"]        = simplemap_adff;
	mappers["$dlatch"]      = simplemap_dlatch;
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
	virtual void help()
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
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing SIMPLEMAP pass (map simple cells to gate primitives).\n");
		extra_args(args, 1, design);

		std::map<RTLIL::IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> mappers;
		simplemap_get_mappers(mappers);

		for (auto mod : design->modules()) {
			if (!design->selected(mod))
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
