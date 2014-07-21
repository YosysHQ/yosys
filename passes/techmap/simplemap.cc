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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>

extern void simplemap_get_mappers(std::map<std::string, void(*)(RTLIL::Module*, RTLIL::Cell*)> &mappers);

static void simplemap_not(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\Y_WIDTH").as_int();

	RTLIL::SigSpec sig_a = cell->connections.at("\\A");
	sig_a.extend(width, cell->parameters.at("\\A_SIGNED").as_bool());
	sig_a.expand();

	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");
	sig_y.expand();

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = new RTLIL::Cell;
		gate->name = NEW_ID;
		gate->type = "$_INV_";
		gate->connections["\\A"] = sig_a.chunks.at(i);
		gate->connections["\\Y"] = sig_y.chunks.at(i);
		module->add(gate);
	}
}

static void simplemap_pos(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\Y_WIDTH").as_int();

	RTLIL::SigSpec sig_a = cell->connections.at("\\A");
	sig_a.extend(width, cell->parameters.at("\\A_SIGNED").as_bool());

	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");

	module->connections.push_back(RTLIL::SigSig(sig_y, sig_a));
}

static void simplemap_bu0(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\Y_WIDTH").as_int();

	RTLIL::SigSpec sig_a = cell->connections.at("\\A");
	sig_a.extend_u0(width, cell->parameters.at("\\A_SIGNED").as_bool());

	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");

	module->connections.push_back(RTLIL::SigSig(sig_y, sig_a));
}

static void simplemap_bitop(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\Y_WIDTH").as_int();

	RTLIL::SigSpec sig_a = cell->connections.at("\\A");
	sig_a.extend_u0(width, cell->parameters.at("\\A_SIGNED").as_bool());
	sig_a.expand();

	RTLIL::SigSpec sig_b = cell->connections.at("\\B");
	sig_b.extend_u0(width, cell->parameters.at("\\B_SIGNED").as_bool());
	sig_b.expand();

	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");
	sig_y.expand();

	if (cell->type == "$xnor")
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID, width);
		sig_t.expand();

		for (int i = 0; i < width; i++) {
			RTLIL::Cell *gate = new RTLIL::Cell;
			gate->name = NEW_ID;
			gate->type = "$_INV_";
			gate->connections["\\A"] = sig_t.chunks.at(i);
			gate->connections["\\Y"] = sig_y.chunks.at(i);
			module->add(gate);
		}

		sig_y = sig_t;
	}

	std::string gate_type;
	if (cell->type == "$and")  gate_type = "$_AND_";
	if (cell->type == "$or")   gate_type = "$_OR_";
	if (cell->type == "$xor")  gate_type = "$_XOR_";
	if (cell->type == "$xnor") gate_type = "$_XOR_";
	log_assert(!gate_type.empty());

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = new RTLIL::Cell;
		gate->name = NEW_ID;
		gate->type = gate_type;
		gate->connections["\\A"] = sig_a.chunks.at(i);
		gate->connections["\\B"] = sig_b.chunks.at(i);
		gate->connections["\\Y"] = sig_y.chunks.at(i);
		module->add(gate);
	}
}

static void simplemap_reduce(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->connections.at("\\A");
	sig_a.expand();

	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");

	if (sig_y.width == 0)
		return;
	
	if (sig_a.width == 0) {
		if (cell->type == "$reduce_and")  module->connections.push_back(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.width)));
		if (cell->type == "$reduce_or")   module->connections.push_back(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.width)));
		if (cell->type == "$reduce_xor")  module->connections.push_back(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.width)));
		if (cell->type == "$reduce_xnor") module->connections.push_back(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.width)));
		if (cell->type == "$reduce_bool") module->connections.push_back(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.width)));
		return;
	}

	if (sig_y.width > 1) {
		module->connections.push_back(RTLIL::SigSig(sig_y.extract(1, sig_y.width-1), RTLIL::SigSpec(0, sig_y.width-1)));
		sig_y = sig_y.extract(0, 1);
	}

	std::string gate_type;
	if (cell->type == "$reduce_and")  gate_type = "$_AND_";
	if (cell->type == "$reduce_or")   gate_type = "$_OR_";
	if (cell->type == "$reduce_xor")  gate_type = "$_XOR_";
	if (cell->type == "$reduce_xnor") gate_type = "$_XOR_";
	if (cell->type == "$reduce_bool") gate_type = "$_OR_";
	log_assert(!gate_type.empty());

	RTLIL::SigSpec *last_output = NULL;

	while (sig_a.width > 1)
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID, sig_a.width / 2);
		sig_t.expand();

		for (int i = 0; i < sig_a.width; i += 2)
		{
			if (i+1 == sig_a.width) {
				sig_t.append(sig_a.chunks.at(i));
				continue;
			}

			RTLIL::Cell *gate = new RTLIL::Cell;
			gate->name = NEW_ID;
			gate->type = gate_type;
			gate->connections["\\A"] = sig_a.chunks.at(i);
			gate->connections["\\B"] = sig_a.chunks.at(i+1);
			gate->connections["\\Y"] = sig_t.chunks.at(i/2);
			last_output = &gate->connections["\\Y"];
			module->add(gate);
		}

		sig_a = sig_t;
	}

	if (cell->type == "$reduce_xnor") {
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID);
		RTLIL::Cell *gate = new RTLIL::Cell;
		gate->name = NEW_ID;
		gate->type = "$_INV_";
		gate->connections["\\A"] = sig_a;
		gate->connections["\\Y"] = sig_t;
		last_output = &gate->connections["\\Y"];
		module->add(gate);
		sig_a = sig_t;
	}

	if (last_output == NULL) {
		module->connections.push_back(RTLIL::SigSig(sig_y, sig_a));
	} else {
		*last_output = sig_y;
	}
}

static void logic_reduce(RTLIL::Module *module, RTLIL::SigSpec &sig)
{
	sig.expand();

	while (sig.width > 1)
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID, sig.width / 2);
		sig_t.expand();

		for (int i = 0; i < sig.width; i += 2)
		{
			if (i+1 == sig.width) {
				sig_t.append(sig.chunks.at(i));
				continue;
			}

			RTLIL::Cell *gate = new RTLIL::Cell;
			gate->name = NEW_ID;
			gate->type = "$_OR_";
			gate->connections["\\A"] = sig.chunks.at(i);
			gate->connections["\\B"] = sig.chunks.at(i+1);
			gate->connections["\\Y"] = sig_t.chunks.at(i/2);
			module->add(gate);
		}

		sig = sig_t;
	}

	if (sig.width == 0)
		sig = RTLIL::SigSpec(0, 1);
}

static void simplemap_lognot(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->connections.at("\\A");
	logic_reduce(module, sig_a);

	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");

	if (sig_y.width == 0)
		return;
	
	if (sig_y.width > 1) {
		module->connections.push_back(RTLIL::SigSig(sig_y.extract(1, sig_y.width-1), RTLIL::SigSpec(0, sig_y.width-1)));
		sig_y = sig_y.extract(0, 1);
	}

	RTLIL::Cell *gate = new RTLIL::Cell;
	gate->name = NEW_ID;
	gate->type = "$_INV_";
	gate->connections["\\A"] = sig_a;
	gate->connections["\\Y"] = sig_y;
	module->add(gate);
}

static void simplemap_logbin(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->connections.at("\\A");
	logic_reduce(module, sig_a);

	RTLIL::SigSpec sig_b = cell->connections.at("\\B");
	logic_reduce(module, sig_b);

	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");

	if (sig_y.width == 0)
		return;
	
	if (sig_y.width > 1) {
		module->connections.push_back(RTLIL::SigSig(sig_y.extract(1, sig_y.width-1), RTLIL::SigSpec(0, sig_y.width-1)));
		sig_y = sig_y.extract(0, 1);
	}

	std::string gate_type;
	if (cell->type == "$logic_and") gate_type = "$_AND_";
	if (cell->type == "$logic_or")  gate_type = "$_OR_";
	log_assert(!gate_type.empty());

	RTLIL::Cell *gate = new RTLIL::Cell;
	gate->name = NEW_ID;
	gate->type = gate_type;
	gate->connections["\\A"] = sig_a;
	gate->connections["\\B"] = sig_b;
	gate->connections["\\Y"] = sig_y;
	module->add(gate);
}

static void simplemap_mux(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();

	RTLIL::SigSpec sig_a = cell->connections.at("\\A");
	sig_a.expand();

	RTLIL::SigSpec sig_b = cell->connections.at("\\B");
	sig_b.expand();

	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");
	sig_y.expand();

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = new RTLIL::Cell;
		gate->name = NEW_ID;
		gate->type = "$_MUX_";
		gate->connections["\\A"] = sig_a.chunks.at(i);
		gate->connections["\\B"] = sig_b.chunks.at(i);
		gate->connections["\\S"] = cell->connections.at("\\S");
		gate->connections["\\Y"] = sig_y.chunks.at(i);
		module->add(gate);
	}
}

static void simplemap_slice(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int offset = cell->parameters.at("\\OFFSET").as_int();
	RTLIL::SigSpec sig_a = cell->connections.at("\\A");
	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");
	module->connections.push_back(RTLIL::SigSig(sig_y, sig_a.extract(offset, sig_y.width)));
}

static void simplemap_concat(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_ab = cell->connections.at("\\A");
	sig_ab.append(cell->connections.at("\\B"));
	RTLIL::SigSpec sig_y = cell->connections.at("\\Y");
	module->connections.push_back(RTLIL::SigSig(sig_y, sig_ab));
}

static void simplemap_sr(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char set_pol = cell->parameters.at("\\SET_POLARITY").as_bool() ? 'P' : 'N';
	char clr_pol = cell->parameters.at("\\CLR_POLARITY").as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_s = cell->connections.at("\\SET");
	sig_s.expand();

	RTLIL::SigSpec sig_r = cell->connections.at("\\CLR");
	sig_r.expand();

	RTLIL::SigSpec sig_q = cell->connections.at("\\Q");
	sig_q.expand();

	std::string gate_type = stringf("$_SR_%c%c_", set_pol, clr_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = new RTLIL::Cell;
		gate->name = NEW_ID;
		gate->type = gate_type;
		gate->connections["\\S"] = sig_s.chunks.at(i);
		gate->connections["\\R"] = sig_r.chunks.at(i);
		gate->connections["\\Q"] = sig_q.chunks.at(i);
		module->add(gate);
	}
}

static void simplemap_dff(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char clk_pol = cell->parameters.at("\\CLK_POLARITY").as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_clk = cell->connections.at("\\CLK");

	RTLIL::SigSpec sig_d = cell->connections.at("\\D");
	sig_d.expand();

	RTLIL::SigSpec sig_q = cell->connections.at("\\Q");
	sig_q.expand();

	std::string gate_type = stringf("$_DFF_%c_", clk_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = new RTLIL::Cell;
		gate->name = NEW_ID;
		gate->type = gate_type;
		gate->connections["\\C"] = sig_clk;
		gate->connections["\\D"] = sig_d.chunks.at(i);
		gate->connections["\\Q"] = sig_q.chunks.at(i);
		module->add(gate);
	}
}

static void simplemap_dffsr(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char clk_pol = cell->parameters.at("\\CLK_POLARITY").as_bool() ? 'P' : 'N';
	char set_pol = cell->parameters.at("\\SET_POLARITY").as_bool() ? 'P' : 'N';
	char clr_pol = cell->parameters.at("\\CLR_POLARITY").as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_clk = cell->connections.at("\\CLK");

	RTLIL::SigSpec sig_s = cell->connections.at("\\SET");
	sig_s.expand();

	RTLIL::SigSpec sig_r = cell->connections.at("\\CLR");
	sig_r.expand();

	RTLIL::SigSpec sig_d = cell->connections.at("\\D");
	sig_d.expand();

	RTLIL::SigSpec sig_q = cell->connections.at("\\Q");
	sig_q.expand();

	std::string gate_type = stringf("$_DFFSR_%c%c%c_", clk_pol, set_pol, clr_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = new RTLIL::Cell;
		gate->name = NEW_ID;
		gate->type = gate_type;
		gate->connections["\\C"] = sig_clk;
		gate->connections["\\S"] = sig_s.chunks.at(i);
		gate->connections["\\R"] = sig_r.chunks.at(i);
		gate->connections["\\D"] = sig_d.chunks.at(i);
		gate->connections["\\Q"] = sig_q.chunks.at(i);
		module->add(gate);
	}
}

static void simplemap_adff(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char clk_pol = cell->parameters.at("\\CLK_POLARITY").as_bool() ? 'P' : 'N';
	char rst_pol = cell->parameters.at("\\ARST_POLARITY").as_bool() ? 'P' : 'N';

	std::vector<RTLIL::State> rst_val = cell->parameters.at("\\ARST_VALUE").bits;
	while (int(rst_val.size()) < width)
		rst_val.push_back(RTLIL::State::S0);

	RTLIL::SigSpec sig_clk = cell->connections.at("\\CLK");
	RTLIL::SigSpec sig_rst = cell->connections.at("\\ARST");

	RTLIL::SigSpec sig_d = cell->connections.at("\\D");
	sig_d.expand();

	RTLIL::SigSpec sig_q = cell->connections.at("\\Q");
	sig_q.expand();

	std::string gate_type_0 = stringf("$_DFF_%c%c0_", clk_pol, rst_pol);
	std::string gate_type_1 = stringf("$_DFF_%c%c1_", clk_pol, rst_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = new RTLIL::Cell;
		gate->name = NEW_ID;
		gate->type = rst_val.at(i) == RTLIL::State::S1 ? gate_type_1 : gate_type_0;
		gate->connections["\\C"] = sig_clk;
		gate->connections["\\R"] = sig_rst;
		gate->connections["\\D"] = sig_d.chunks.at(i);
		gate->connections["\\Q"] = sig_q.chunks.at(i);
		module->add(gate);
	}
}

static void simplemap_dlatch(RTLIL::Module *module, RTLIL::Cell *cell)
{
	int width = cell->parameters.at("\\WIDTH").as_int();
	char en_pol = cell->parameters.at("\\EN_POLARITY").as_bool() ? 'P' : 'N';

	RTLIL::SigSpec sig_en = cell->connections.at("\\EN");

	RTLIL::SigSpec sig_d = cell->connections.at("\\D");
	sig_d.expand();

	RTLIL::SigSpec sig_q = cell->connections.at("\\Q");
	sig_q.expand();

	std::string gate_type = stringf("$_DLATCH_%c_", en_pol);

	for (int i = 0; i < width; i++) {
		RTLIL::Cell *gate = new RTLIL::Cell;
		gate->name = NEW_ID;
		gate->type = gate_type;
		gate->connections["\\E"] = sig_en;
		gate->connections["\\D"] = sig_d.chunks.at(i);
		gate->connections["\\Q"] = sig_q.chunks.at(i);
		module->add(gate);
	}
}

void simplemap_get_mappers(std::map<std::string, void(*)(RTLIL::Module*, RTLIL::Cell*)> &mappers)
{
	mappers["$not"]         = simplemap_not;
	mappers["$pos"]         = simplemap_pos;
	mappers["$bu0"]         = simplemap_bu0;
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
	mappers["$mux"]         = simplemap_mux;
	mappers["$slice"]       = simplemap_slice;
	mappers["$concat"]      = simplemap_concat;
	mappers["$sr"]          = simplemap_sr;
	mappers["$dff"]         = simplemap_dff;
	mappers["$dffsr"]       = simplemap_dffsr;
	mappers["$adff"]        = simplemap_adff;
	mappers["$dlatch"]      = simplemap_dlatch;
}

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
		log("  $not, $pos, $bu0, $and, $or, $xor, $xnor\n");
		log("  $reduce_and, $reduce_or, $reduce_xor, $reduce_xnor, $reduce_bool\n");
		log("  $logic_not, $logic_and, $logic_or, $mux\n");
		log("  $sr, $dff, $dffsr, $adff, $dlatch\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing SIMPLEMAP pass (map simple cells to gate primitives).\n");
		extra_args(args, 1, design);

		std::map<std::string, void(*)(RTLIL::Module*, RTLIL::Cell*)> mappers;
		simplemap_get_mappers(mappers);

		for (auto &mod_it : design->modules) {
			if (!design->selected(mod_it.second))
				continue;
			std::vector<RTLIL::Cell*> delete_cells;
			for (auto &cell_it : mod_it.second->cells) {
				if (mappers.count(cell_it.second->type) == 0)
					continue;
				if (!design->selected(mod_it.second, cell_it.second))
					continue;
				log("Mapping %s.%s (%s).\n", RTLIL::id2cstr(mod_it.first), RTLIL::id2cstr(cell_it.first), RTLIL::id2cstr(cell_it.second->type));
				mappers.at(cell_it.second->type)(mod_it.second, cell_it.second);
				delete_cells.push_back(cell_it.second);
			}
			for (auto &it : delete_cells) {
				mod_it.second->cells.erase(it->name);
				delete it;
			}
		}
	}
} SimplemapPass;
 
