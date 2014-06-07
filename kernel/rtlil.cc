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

#include "kernel/compatibility.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
#include "frontends/verilog/verilog_frontend.h"
#include "backends/ilang/ilang_backend.h"

#include <assert.h>
#include <string.h>
#include <algorithm>

int RTLIL::autoidx = 1;

RTLIL::Const::Const()
{
	flags = RTLIL::CONST_FLAG_NONE;
}

RTLIL::Const::Const(std::string str)
{
	flags = RTLIL::CONST_FLAG_STRING;
	for (int i = str.size()-1; i >= 0; i--) {
		unsigned char ch = str[i];
		for (int j = 0; j < 8; j++) {
			bits.push_back((ch & 1) != 0 ? RTLIL::S1 : RTLIL::S0);
			ch = ch >> 1;
		}
	}
}

RTLIL::Const::Const(int val, int width)
{
	flags = RTLIL::CONST_FLAG_NONE;
	for (int i = 0; i < width; i++) {
		bits.push_back((val & 1) != 0 ? RTLIL::S1 : RTLIL::S0);
		val = val >> 1;
	}
}

RTLIL::Const::Const(RTLIL::State bit, int width)
{
	flags = RTLIL::CONST_FLAG_NONE;
	for (int i = 0; i < width; i++)
		bits.push_back(bit);
}

bool RTLIL::Const::operator <(const RTLIL::Const &other) const
{
	if (bits.size() != other.bits.size())
		return bits.size() < other.bits.size();
	for (size_t i = 0; i < bits.size(); i++)
		if (bits[i] != other.bits[i])
			return bits[i] < other.bits[i];
	return false;
}

bool RTLIL::Const::operator ==(const RTLIL::Const &other) const
{
	return bits == other.bits;
}

bool RTLIL::Const::operator !=(const RTLIL::Const &other) const
{
	return bits != other.bits;
}

bool RTLIL::Const::as_bool() const
{
	for (size_t i = 0; i < bits.size(); i++)
		if (bits[i] == RTLIL::S1)
			return true;
	return false;
}

int RTLIL::Const::as_int() const
{
	int ret = 0;
	for (size_t i = 0; i < bits.size() && i < 32; i++)
		if (bits[i] == RTLIL::S1)
			ret |= 1 << i;
	return ret;
}

std::string RTLIL::Const::as_string() const
{
	std::string ret;
	for (size_t i = bits.size(); i > 0; i--)
		switch (bits[i-1]) {
			case S0: ret += "0"; break;
			case S1: ret += "1"; break;
			case Sx: ret += "x"; break;
			case Sz: ret += "z"; break;
			case Sa: ret += "-"; break;
			case Sm: ret += "m"; break;
		}
	return ret;
}

std::string RTLIL::Const::decode_string() const
{
	std::string string;
	std::vector <char> string_chars;
	for (int i = 0; i < int (bits.size()); i += 8) {
		char ch = 0;
		for (int j = 0; j < 8 && i + j < int (bits.size()); j++)
			if (bits[i + j] == RTLIL::State::S1)
				ch |= 1 << j;
		if (ch != 0)
			string_chars.push_back(ch);
	}
	for (int i = int (string_chars.size()) - 1; i >= 0; i--)
		string += string_chars[i];
	return string;
}

bool RTLIL::Selection::selected_module(RTLIL::IdString mod_name) const
{
	if (full_selection)
		return true;
	if (selected_modules.count(mod_name) > 0)
		return true;
	if (selected_members.count(mod_name) > 0)
		return true;
	return false;
}

bool RTLIL::Selection::selected_whole_module(RTLIL::IdString mod_name) const
{
	if (full_selection)
		return true;
	if (selected_modules.count(mod_name) > 0)
		return true;
	return false;
}

bool RTLIL::Selection::selected_member(RTLIL::IdString mod_name, RTLIL::IdString memb_name) const
{
	if (full_selection)
		return true;
	if (selected_modules.count(mod_name) > 0)
		return true;
	if (selected_members.count(mod_name) > 0)
		if (selected_members.at(mod_name).count(memb_name) > 0)
			return true;
	return false;
}

void RTLIL::Selection::optimize(RTLIL::Design *design)
{
	if (full_selection) {
		selected_modules.clear();
		selected_members.clear();
		return;
	}

	std::vector<RTLIL::IdString> del_list, add_list;

	del_list.clear();
	for (auto mod_name : selected_modules) {
		if (design->modules.count(mod_name) == 0)
			del_list.push_back(mod_name);
		selected_members.erase(mod_name);
	}
	for (auto mod_name : del_list)
		selected_modules.erase(mod_name);

	del_list.clear();
	for (auto &it : selected_members)
		if (design->modules.count(it.first) == 0)
			del_list.push_back(it.first);
	for (auto mod_name : del_list)
		selected_members.erase(mod_name);

	for (auto &it : selected_members) {
		del_list.clear();
		for (auto memb_name : it.second)
			if (design->modules[it.first]->count_id(memb_name) == 0)
				del_list.push_back(memb_name);
		for (auto memb_name : del_list)
			it.second.erase(memb_name);
	}

	del_list.clear();
	add_list.clear();
	for (auto &it : selected_members)
		if (it.second.size() == 0)
			del_list.push_back(it.first);
		else if (it.second.size() == design->modules[it.first]->wires.size() + design->modules[it.first]->memories.size() +
				design->modules[it.first]->cells.size() + design->modules[it.first]->processes.size())
			add_list.push_back(it.first);
	for (auto mod_name : del_list)
		selected_members.erase(mod_name);
	for (auto mod_name : add_list) {
		selected_members.erase(mod_name);
		selected_modules.insert(mod_name);
	}

	if (selected_modules.size() == design->modules.size()) {
		full_selection = true;
		selected_modules.clear();
		selected_members.clear();
	}
}

RTLIL::Design::~Design()
{
	for (auto it = modules.begin(); it != modules.end(); it++)
		delete it->second;
}

void RTLIL::Design::check()
{
#ifndef NDEBUG
	for (auto &it : modules) {
		assert(it.first == it.second->name);
		assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		it.second->check();
	}
#endif
}

void RTLIL::Design::optimize()
{
	for (auto &it : modules)
		it.second->optimize();
	for (auto &it : selection_stack)
		it.optimize(this);
	for (auto &it : selection_vars)
		it.second.optimize(this);
}

bool RTLIL::Design::selected_module(RTLIL::IdString mod_name) const
{
	if (!selected_active_module.empty() && mod_name != selected_active_module)
		return false;
	if (selection_stack.size() == 0)
		return true;
	return selection_stack.back().selected_module(mod_name);
}

bool RTLIL::Design::selected_whole_module(RTLIL::IdString mod_name) const
{
	if (!selected_active_module.empty() && mod_name != selected_active_module)
		return false;
	if (selection_stack.size() == 0)
		return true;
	return selection_stack.back().selected_whole_module(mod_name);
}

bool RTLIL::Design::selected_member(RTLIL::IdString mod_name, RTLIL::IdString memb_name) const
{
	if (!selected_active_module.empty() && mod_name != selected_active_module)
		return false;
	if (selection_stack.size() == 0)
		return true;
	return selection_stack.back().selected_member(mod_name, memb_name);
}

RTLIL::Module::~Module()
{
	for (auto it = wires.begin(); it != wires.end(); it++)
		delete it->second;
	for (auto it = memories.begin(); it != memories.end(); it++)
		delete it->second;
	for (auto it = cells.begin(); it != cells.end(); it++)
		delete it->second;
	for (auto it = processes.begin(); it != processes.end(); it++)
		delete it->second;
}

RTLIL::IdString RTLIL::Module::derive(RTLIL::Design*, std::map<RTLIL::IdString, RTLIL::Const>)
{
	log_error("Module `%s' is used with parameters but is not parametric!\n", id2cstr(name));
}

size_t RTLIL::Module::count_id(RTLIL::IdString id)
{
	return wires.count(id) + memories.count(id) + cells.count(id) + processes.count(id);
}

#ifndef NDEBUG
namespace {
	struct InternalCellChecker
	{
		RTLIL::Module *module;
		RTLIL::Cell *cell;
		std::set<RTLIL::IdString> expected_params, expected_ports;

		InternalCellChecker(RTLIL::Module *module, RTLIL::Cell *cell) : module(module), cell(cell) { }

		void error(int linenr)
		{
			char *ptr;
			size_t size;

			FILE *f = open_memstream(&ptr, &size);
			ILANG_BACKEND::dump_cell(f, "  ", cell);
			fputc(0, f);
			fclose(f);

			log_error("Found error in internal cell %s.%s (%s) at %s:%d:\n%s",
					module->name.c_str(), cell->name.c_str(), cell->type.c_str(),
					__FILE__, linenr, ptr);
		}

		int param(const char *name)
		{
			if (cell->parameters.count(name) == 0)
				error(__LINE__);
			expected_params.insert(name);
			return cell->parameters.at(name).as_int();
		}

		int param_bool(const char *name)
		{
			int v = param(name);
			if (cell->parameters.at(name).bits.size() > 32)
				error(__LINE__);
			if (v != 0 && v != 1)
				error(__LINE__);
			return v;
		}

		void param_bits(const char *name, int width)
		{
			param(name);
			if (int(cell->parameters.at(name).bits.size()) != width)
				error(__LINE__);
		}

		void port(const char *name, int width)
		{
			if (cell->connections.count(name) == 0)
				error(__LINE__);
			if (cell->connections.at(name).width != width)
				error(__LINE__);
			expected_ports.insert(name);
		}

		void check_expected(bool check_matched_sign = true)
		{
			for (auto &para : cell->parameters)
				if (expected_params.count(para.first) == 0)
					error(__LINE__);
			for (auto &conn : cell->connections)
				if (expected_ports.count(conn.first) == 0)
					error(__LINE__);

			if (expected_params.count("\\A_SIGNED") != 0 && expected_params.count("\\B_SIGNED") && check_matched_sign) {
				bool a_is_signed = param("\\A_SIGNED") != 0;
				bool b_is_signed = param("\\B_SIGNED") != 0;
				if (a_is_signed != b_is_signed)
					error(__LINE__);
			}
		}

		void check_gate(const char *ports)
		{
			if (cell->parameters.size() != 0)
				error(__LINE__);

			for (const char *p = ports; *p; p++) {
				char portname[3] = { '\\', *p, 0 };
				if (cell->connections.count(portname) == 0)
					error(__LINE__);
				if (cell->connections.at(portname).width != 1)
					error(__LINE__);
			}

			for (auto &conn : cell->connections) {
				if (conn.first.size() != 2 || conn.first.at(0) != '\\')
					error(__LINE__);
				if (strchr(ports, conn.first.at(1)) == NULL)
					error(__LINE__);
			}
		}

		void check()
		{
			if (cell->type == "$not" || cell->type == "$pos" || cell->type == "$bu0" || cell->type == "$neg") {
				param_bool("\\A_SIGNED");
				port("\\A", param("\\A_WIDTH"));
				port("\\Y", param("\\Y_WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$and" || cell->type == "$or" || cell->type == "$xor" || cell->type == "$xnor") {
				param_bool("\\A_SIGNED");
				param_bool("\\B_SIGNED");
				port("\\A", param("\\A_WIDTH"));
				port("\\B", param("\\B_WIDTH"));
				port("\\Y", param("\\Y_WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$reduce_and" || cell->type == "$reduce_or" || cell->type == "$reduce_xor" ||
					cell->type == "$reduce_xnor" || cell->type == "$reduce_bool") {
				param_bool("\\A_SIGNED");
				port("\\A", param("\\A_WIDTH"));
				port("\\Y", param("\\Y_WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr") {
				param_bool("\\A_SIGNED");
				param_bool("\\B_SIGNED");
				port("\\A", param("\\A_WIDTH"));
				port("\\B", param("\\B_WIDTH"));
				port("\\Y", param("\\Y_WIDTH"));
				check_expected(false);
				return;
			}

			if (cell->type == "$lt" || cell->type == "$le" || cell->type == "$eq" || cell->type == "$ne" ||
					cell->type == "$eqx" || cell->type == "$nex" || cell->type == "$ge" || cell->type == "$gt") {
				param_bool("\\A_SIGNED");
				param_bool("\\B_SIGNED");
				port("\\A", param("\\A_WIDTH"));
				port("\\B", param("\\B_WIDTH"));
				port("\\Y", param("\\Y_WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$add" || cell->type == "$sub" || cell->type == "$mul" || cell->type == "$div" ||
					cell->type == "$mod" || cell->type == "$pow") {
				param_bool("\\A_SIGNED");
				param_bool("\\B_SIGNED");
				port("\\A", param("\\A_WIDTH"));
				port("\\B", param("\\B_WIDTH"));
				port("\\Y", param("\\Y_WIDTH"));
				check_expected(cell->type != "$pow");
				return;
			}

			if (cell->type == "$logic_not") {
				param_bool("\\A_SIGNED");
				port("\\A", param("\\A_WIDTH"));
				port("\\Y", param("\\Y_WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$logic_and" || cell->type == "$logic_or") {
				param_bool("\\A_SIGNED");
				param_bool("\\B_SIGNED");
				port("\\A", param("\\A_WIDTH"));
				port("\\B", param("\\B_WIDTH"));
				port("\\Y", param("\\Y_WIDTH"));
				check_expected(false);
				return;
			}

			if (cell->type == "$slice") {
				param("\\OFFSET");
				port("\\A", param("\\A_WIDTH"));
				port("\\Y", param("\\Y_WIDTH"));
				if (param("\\OFFSET") + param("\\Y_WIDTH") > param("\\A_WIDTH"))
					error(__LINE__);
				check_expected();
				return;
			}

			if (cell->type == "$concat") {
				port("\\A", param("\\A_WIDTH"));
				port("\\B", param("\\B_WIDTH"));
				port("\\Y", param("\\A_WIDTH") + param("\\B_WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$mux") {
				port("\\A", param("\\WIDTH"));
				port("\\B", param("\\WIDTH"));
				port("\\S", 1);
				port("\\Y", param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$pmux" || cell->type == "$safe_pmux") {
				port("\\A", param("\\WIDTH"));
				port("\\B", param("\\WIDTH") * param("\\S_WIDTH"));
				port("\\S", param("\\S_WIDTH"));
				port("\\Y", param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$lut") {
				param("\\LUT");
				port("\\I", param("\\WIDTH"));
				port("\\O", 1);
				check_expected();
				return;
			}

			if (cell->type == "$sr") {
				param_bool("\\SET_POLARITY");
				param_bool("\\CLR_POLARITY");
				port("\\SET", param("\\WIDTH"));
				port("\\CLR", param("\\WIDTH"));
				port("\\Q",   param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$dff") {
				param_bool("\\CLK_POLARITY");
				port("\\CLK", 1);
				port("\\D", param("\\WIDTH"));
				port("\\Q", param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$dffsr") {
				param_bool("\\CLK_POLARITY");
				param_bool("\\SET_POLARITY");
				param_bool("\\CLR_POLARITY");
				port("\\CLK", 1);
				port("\\SET", param("\\WIDTH"));
				port("\\CLR", param("\\WIDTH"));
				port("\\D", param("\\WIDTH"));
				port("\\Q", param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$adff") {
				param_bool("\\CLK_POLARITY");
				param_bool("\\ARST_POLARITY");
				param_bits("\\ARST_VALUE", param("\\WIDTH"));
				port("\\CLK", 1);
				port("\\ARST", 1);
				port("\\D", param("\\WIDTH"));
				port("\\Q", param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$dlatch") {
				param_bool("\\EN_POLARITY");
				port("\\EN", 1);
				port("\\D", param("\\WIDTH"));
				port("\\Q", param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$dlatchsr") {
				param_bool("\\EN_POLARITY");
				param_bool("\\SET_POLARITY");
				param_bool("\\CLR_POLARITY");
				port("\\EN", 1);
				port("\\SET", param("\\WIDTH"));
				port("\\CLR", param("\\WIDTH"));
				port("\\D", param("\\WIDTH"));
				port("\\Q", param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$fsm") {
				param("\\NAME");
				param_bool("\\CLK_POLARITY");
				param_bool("\\ARST_POLARITY");
				param("\\STATE_BITS");
				param("\\STATE_NUM");
				param("\\STATE_NUM_LOG2");
				param("\\STATE_RST");
				param_bits("\\STATE_TABLE", param("\\STATE_BITS") * param("\\STATE_NUM"));
				param("\\TRANS_NUM");
				param_bits("\\TRANS_TABLE", param("\\TRANS_NUM") * (2*param("\\STATE_NUM_LOG2") + param("\\CTRL_IN_WIDTH") + param("\\CTRL_OUT_WIDTH")));
				port("\\CLK", 1);
				port("\\ARST", 1);
				port("\\CTRL_IN", param("\\CTRL_IN_WIDTH"));
				port("\\CTRL_OUT", param("\\CTRL_OUT_WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$memrd") {
				param("\\MEMID");
				param_bool("\\CLK_ENABLE");
				param_bool("\\CLK_POLARITY");
				param_bool("\\TRANSPARENT");
				port("\\CLK", 1);
				port("\\ADDR", param("\\ABITS"));
				port("\\DATA", param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$memwr") {
				param("\\MEMID");
				param_bool("\\CLK_ENABLE");
				param_bool("\\CLK_POLARITY");
				param("\\PRIORITY");
				port("\\CLK", 1);
				port("\\EN", 1);
				port("\\ADDR", param("\\ABITS"));
				port("\\DATA", param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$mem") {
				param("\\MEMID");
				param("\\SIZE");
				param("\\OFFSET");
				param_bits("\\RD_CLK_ENABLE", param("\\RD_PORTS"));
				param_bits("\\RD_CLK_POLARITY", param("\\RD_PORTS"));
				param_bits("\\RD_TRANSPARENT", param("\\RD_PORTS"));
				param_bits("\\WR_CLK_ENABLE", param("\\WR_PORTS"));
				param_bits("\\WR_CLK_POLARITY", param("\\WR_PORTS"));
				port("\\RD_CLK", param("\\RD_PORTS"));
				port("\\RD_ADDR", param("\\RD_PORTS") * param("\\ABITS"));
				port("\\RD_DATA", param("\\RD_PORTS") * param("\\WIDTH"));
				port("\\WR_CLK", param("\\WR_PORTS"));
				port("\\WR_EN", param("\\WR_PORTS"));
				port("\\WR_ADDR", param("\\WR_PORTS") * param("\\ABITS"));
				port("\\WR_DATA", param("\\WR_PORTS") * param("\\WIDTH"));
				check_expected();
				return;
			}

			if (cell->type == "$assert") {
				port("\\A", 1);
				port("\\EN", 1);
				check_expected();
				return;
			}

			if (cell->type == "$_INV_") { check_gate("AY"); return; }
			if (cell->type == "$_AND_") { check_gate("ABY"); return; }
			if (cell->type == "$_OR_")  { check_gate("ABY"); return; }
			if (cell->type == "$_XOR_") { check_gate("ABY"); return; }
			if (cell->type == "$_MUX_") { check_gate("ABSY"); return; }

			if (cell->type == "$_SR_NN_") { check_gate("SRQ"); return; }
			if (cell->type == "$_SR_NP_") { check_gate("SRQ"); return; }
			if (cell->type == "$_SR_PN_") { check_gate("SRQ"); return; }
			if (cell->type == "$_SR_PP_") { check_gate("SRQ"); return; }

			if (cell->type == "$_DFF_N_") { check_gate("DQC"); return; }
			if (cell->type == "$_DFF_P_") { check_gate("DQC"); return; }

			if (cell->type == "$_DFF_NN0_") { check_gate("DQCR"); return; }
			if (cell->type == "$_DFF_NN1_") { check_gate("DQCR"); return; }
			if (cell->type == "$_DFF_NP0_") { check_gate("DQCR"); return; }
			if (cell->type == "$_DFF_NP1_") { check_gate("DQCR"); return; }
			if (cell->type == "$_DFF_PN0_") { check_gate("DQCR"); return; }
			if (cell->type == "$_DFF_PN1_") { check_gate("DQCR"); return; }
			if (cell->type == "$_DFF_PP0_") { check_gate("DQCR"); return; }
			if (cell->type == "$_DFF_PP1_") { check_gate("DQCR"); return; }

			if (cell->type == "$_DFFSR_NNN_") { check_gate("CSRDQ"); return; }
			if (cell->type == "$_DFFSR_NNP_") { check_gate("CSRDQ"); return; }
			if (cell->type == "$_DFFSR_NPN_") { check_gate("CSRDQ"); return; }
			if (cell->type == "$_DFFSR_NPP_") { check_gate("CSRDQ"); return; }
			if (cell->type == "$_DFFSR_PNN_") { check_gate("CSRDQ"); return; }
			if (cell->type == "$_DFFSR_PNP_") { check_gate("CSRDQ"); return; }
			if (cell->type == "$_DFFSR_PPN_") { check_gate("CSRDQ"); return; }
			if (cell->type == "$_DFFSR_PPP_") { check_gate("CSRDQ"); return; }

			if (cell->type == "$_DLATCH_N_") { check_gate("EDQ"); return; }
			if (cell->type == "$_DLATCH_P_") { check_gate("EDQ"); return; }

			if (cell->type == "$_DLATCHSR_NNN_") { check_gate("ESRDQ"); return; }
			if (cell->type == "$_DLATCHSR_NNP_") { check_gate("ESRDQ"); return; }
			if (cell->type == "$_DLATCHSR_NPN_") { check_gate("ESRDQ"); return; }
			if (cell->type == "$_DLATCHSR_NPP_") { check_gate("ESRDQ"); return; }
			if (cell->type == "$_DLATCHSR_PNN_") { check_gate("ESRDQ"); return; }
			if (cell->type == "$_DLATCHSR_PNP_") { check_gate("ESRDQ"); return; }
			if (cell->type == "$_DLATCHSR_PPN_") { check_gate("ESRDQ"); return; }
			if (cell->type == "$_DLATCHSR_PPP_") { check_gate("ESRDQ"); return; }

			error(__LINE__);
		}
	};
}
#endif

void RTLIL::Module::check()
{
#ifndef NDEBUG
	for (auto &it : wires) {
		assert(it.first == it.second->name);
		assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		assert(it.second->width >= 0);
		assert(it.second->port_id >= 0);
		for (auto &it2 : it.second->attributes) {
			assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
		}
	}

	for (auto &it : memories) {
		assert(it.first == it.second->name);
		assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		assert(it.second->width >= 0);
		assert(it.second->size >= 0);
		for (auto &it2 : it.second->attributes) {
			assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
		}
	}

	for (auto &it : cells) {
		assert(it.first == it.second->name);
		assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		assert(it.second->type.size() > 0 && (it.second->type[0] == '\\' || it.second->type[0] == '$'));
		for (auto &it2 : it.second->connections) {
			assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
			it2.second.check();
		}
		for (auto &it2 : it.second->attributes) {
			assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
		}
		for (auto &it2 : it.second->parameters) {
			assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
		}
		if (it.second->type[0] == '$' && it.second->type.substr(0, 3) != "$__" && it.second->type.substr(0, 8) != "$paramod" &&
				it.second->type.substr(0, 9) != "$verific$" && it.second->type.substr(0, 7) != "$array:") {
			InternalCellChecker checker(this, it.second);
			checker.check();
		}
	}

	for (auto &it : processes) {
		assert(it.first == it.second->name);
		assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		// FIXME: More checks here..
	}

	for (auto &it : connections) {
		assert(it.first.width == it.second.width);
		it.first.check();
		it.second.check();
	}

	for (auto &it : attributes) {
		assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
	}
#endif
}

void RTLIL::Module::optimize()
{
	for (auto &it : cells)
		it.second->optimize();
	for (auto &it : processes)
		it.second->optimize();
	for (auto &it : connections) {
		it.first.optimize();
		it.second.optimize();
	}
}

void RTLIL::Module::cloneInto(RTLIL::Module *new_mod) const
{
	new_mod->name = name;
	new_mod->connections = connections;
	new_mod->attributes = attributes;

	for (auto &it : wires)
		new_mod->wires[it.first] = new RTLIL::Wire(*it.second);

	for (auto &it : memories)
		new_mod->memories[it.first] = new RTLIL::Memory(*it.second);

	for (auto &it : cells)
		new_mod->cells[it.first] = new RTLIL::Cell(*it.second);

	for (auto &it : processes)
		new_mod->processes[it.first] = it.second->clone();

	struct RewriteSigSpecWorker
	{
		RTLIL::Module *mod;
		void operator()(RTLIL::SigSpec &sig)
		{
			for (auto &c : sig.chunks)
				if (c.wire != NULL)
					c.wire = mod->wires.at(c.wire->name);
		}
	};

	RewriteSigSpecWorker rewriteSigSpecWorker;
	rewriteSigSpecWorker.mod = new_mod;
	new_mod->rewrite_sigspecs(rewriteSigSpecWorker);
}

RTLIL::Module *RTLIL::Module::clone() const
{
	RTLIL::Module *new_mod = new RTLIL::Module;
	cloneInto(new_mod);
	return new_mod;
}

RTLIL::Wire *RTLIL::Module::new_wire(int width, RTLIL::IdString name)
{
	RTLIL::Wire *wire = new RTLIL::Wire;
	wire->width = width;
	wire->name = name;
	add(wire);
	return wire;
}

void RTLIL::Module::add(RTLIL::Wire *wire)
{
	assert(!wire->name.empty());
	assert(count_id(wire->name) == 0);
	wires[wire->name] = wire;
}

void RTLIL::Module::add(RTLIL::Cell *cell)
{
	assert(!cell->name.empty());
	assert(count_id(cell->name) == 0);
	cells[cell->name] = cell;
}

static bool fixup_ports_compare(const RTLIL::Wire *a, const RTLIL::Wire *b)
{
	if (a->port_id && !b->port_id)
		return true;
	if (!a->port_id && b->port_id)
		return false;

	if (a->port_id == b->port_id)
		return a->name < b->name;
	return a->port_id < b->port_id;
}

void RTLIL::Module::fixup_ports()
{
	std::vector<RTLIL::Wire*> all_ports;

	for (auto &w : wires)
		if (w.second->port_input || w.second->port_output)
			all_ports.push_back(w.second);
		else
			w.second->port_id = 0;

	std::sort(all_ports.begin(), all_ports.end(), fixup_ports_compare);
	for (size_t i = 0; i < all_ports.size(); i++)
		all_ports[i]->port_id = i+1;
}


#define DEF_METHOD(_func, _type) \
	RTLIL::Cell* RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed) { \
		RTLIL::Cell *cell = new RTLIL::Cell;                \
		cell->name = name;                                  \
		cell->type = _type;                                 \
		cell->parameters["\\A_SIGNED"] = is_signed;         \
		cell->parameters["\\A_WIDTH"] = sig_a.width;        \
		cell->parameters["\\Y_WIDTH"] = sig_y.width;        \
		cell->connections["\\A"] = sig_a;                   \
		cell->connections["\\Y"] = sig_y;                   \
		add(cell);                                          \
		return cell;                                        \
	}
DEF_METHOD(addNot,        "$not")
DEF_METHOD(addPos,        "$pos")
DEF_METHOD(addBu0,        "$bu0")
DEF_METHOD(addNeg,        "$neg")
DEF_METHOD(addReduceAnd,  "$reduce_and")
DEF_METHOD(addReduceOr,   "$reduce_or")
DEF_METHOD(addReduceXor,  "$reduce_xor")
DEF_METHOD(addReduceXnor, "$reduce_xnor")
DEF_METHOD(addReduceBool, "$reduce_bool")
DEF_METHOD(addLogicNot,   "$logic_not")
#undef DEF_METHOD

#define DEF_METHOD(_func, _type) \
	RTLIL::Cell* RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed) { \
		RTLIL::Cell *cell = new RTLIL::Cell;                \
		cell->name = name;                                  \
		cell->type = _type;                                 \
		cell->parameters["\\A_SIGNED"] = is_signed;         \
		cell->parameters["\\B_SIGNED"] = is_signed;         \
		cell->parameters["\\A_WIDTH"] = sig_a.width;        \
		cell->parameters["\\B_WIDTH"] = sig_b.width;        \
		cell->parameters["\\Y_WIDTH"] = sig_y.width;        \
		cell->connections["\\A"] = sig_a;                   \
		cell->connections["\\B"] = sig_b;                   \
		cell->connections["\\Y"] = sig_y;                   \
		add(cell);                                          \
		return cell;                                        \
	}
DEF_METHOD(addAnd,      "$and")
DEF_METHOD(addOr,       "$or")
DEF_METHOD(addXor,      "$xor")
DEF_METHOD(addXnor,     "$xnor")
DEF_METHOD(addShl,      "$shl")
DEF_METHOD(addShr,      "$shr")
DEF_METHOD(addSshl,     "$sshl")
DEF_METHOD(addSshr,     "$sshr")
DEF_METHOD(addLt,       "$lt")
DEF_METHOD(addLe,       "$le")
DEF_METHOD(addEq,       "$eq")
DEF_METHOD(addNe,       "$ne")
DEF_METHOD(addEqx,      "$eqx")
DEF_METHOD(addNex,      "$nex")
DEF_METHOD(addGe,       "$ge")
DEF_METHOD(addGt,       "$gt")
DEF_METHOD(addAdd,      "$add")
DEF_METHOD(addSub,      "$sub")
DEF_METHOD(addMul,      "$mul")
DEF_METHOD(addDiv,      "$div")
DEF_METHOD(addMod,      "$mod")
DEF_METHOD(addLogicAnd, "$logic_and")
DEF_METHOD(addLogicOr,  "$logic_or")
#undef DEF_METHOD

#define DEF_METHOD(_func, _type, _pmux) \
	RTLIL::Cell* RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y) { \
		RTLIL::Cell *cell = new RTLIL::Cell;                     \
		cell->name = name;                                       \
		cell->type = _type;                                      \
		cell->parameters["\\WIDTH"] = sig_a.width;               \
		cell->parameters["\\WIDTH"] = sig_b.width;               \
		if (_pmux) cell->parameters["\\S_WIDTH"] = sig_s.width;  \
		cell->connections["\\A"] = sig_a;                        \
		cell->connections["\\B"] = sig_b;                        \
		cell->connections["\\S"] = sig_s;                        \
		cell->connections["\\Y"] = sig_y;                        \
		add(cell);                                               \
		return cell;                                             \
	}
DEF_METHOD(addMux,      "$mux",        0)
DEF_METHOD(addPmux,     "$pmux",       1)
DEF_METHOD(addSafePmux, "$safe_pmux",  1)
#undef DEF_METHOD

#define DEF_METHOD_2(_func, _type, _P1, _P2) \
	RTLIL::Cell* RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig1, RTLIL::SigSpec sig2) { \
		RTLIL::Cell *cell = new RTLIL::Cell;                \
		cell->name = name;                                  \
		cell->type = _type;                                 \
		cell->connections["\\" #_P1] = sig1;               \
		cell->connections["\\" #_P2] = sig2;               \
		add(cell);                                          \
		return cell;                                        \
	}
#define DEF_METHOD_3(_func, _type, _P1, _P2, _P3) \
	RTLIL::Cell* RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig1, RTLIL::SigSpec sig2, RTLIL::SigSpec sig3) { \
		RTLIL::Cell *cell = new RTLIL::Cell;                \
		cell->name = name;                                  \
		cell->type = _type;                                 \
		cell->connections["\\" #_P1] = sig1;               \
		cell->connections["\\" #_P2] = sig2;               \
		cell->connections["\\" #_P3] = sig3;               \
		add(cell);                                          \
		return cell;                                        \
	}
#define DEF_METHOD_4(_func, _type, _P1, _P2, _P3, _P4) \
	RTLIL::Cell* RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig1, RTLIL::SigSpec sig2, RTLIL::SigSpec sig3, RTLIL::SigSpec sig4) { \
		RTLIL::Cell *cell = new RTLIL::Cell;                \
		cell->name = name;                                  \
		cell->type = _type;                                 \
		cell->connections["\\" #_P1] = sig1;                \
		cell->connections["\\" #_P2] = sig2;                \
		cell->connections["\\" #_P3] = sig3;                \
		cell->connections["\\" #_P4] = sig4;                \
		add(cell);                                          \
		return cell;                                        \
	}
DEF_METHOD_2(addInvGate, "$_INV_", A, Y)
DEF_METHOD_3(addAndGate, "$_AND_", A, B, Y)
DEF_METHOD_3(addOrGate,  "$_OR_",  A, B, Y)
DEF_METHOD_3(addXorGate, "$_XOR_", A, B, Y)
DEF_METHOD_4(addMuxGate, "$_MUX_", A, B, S, Y)
#undef DEF_METHOD_2
#undef DEF_METHOD_3
#undef DEF_METHOD_4

RTLIL::Cell* RTLIL::Module::addPow(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool a_signed, bool b_signed)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$pow";
	cell->parameters["\\A_SIGNED"] = a_signed;
	cell->parameters["\\B_SIGNED"] = b_signed;
	cell->parameters["\\A_WIDTH"] = sig_a.width;
	cell->parameters["\\B_WIDTH"] = sig_b.width;
	cell->parameters["\\Y_WIDTH"] = sig_y.width;
	cell->connections["\\A"] = sig_a;
	cell->connections["\\B"] = sig_b;
	cell->connections["\\Y"] = sig_y;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addSlice(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, RTLIL::Const offset)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$slice";
	cell->parameters["\\A_WIDTH"] = sig_a.width;
	cell->parameters["\\Y_WIDTH"] = sig_y.width;
	cell->parameters["\\OFFSET"] = offset;
	cell->connections["\\A"] = sig_a;
	cell->connections["\\Y"] = sig_y;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addConcat(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$concat";
	cell->parameters["\\A_WIDTH"] = sig_a.width;
	cell->parameters["\\B_WIDTH"] = sig_b.width;
	cell->connections["\\A"] = sig_a;
	cell->connections["\\B"] = sig_b;
	cell->connections["\\Y"] = sig_y;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addLut(RTLIL::IdString name, RTLIL::SigSpec sig_i, RTLIL::SigSpec sig_o, RTLIL::Const lut)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$lut";
	cell->parameters["\\LUT"] = lut;
	cell->parameters["\\WIDTH"] = sig_i.width;
	cell->connections["\\I"] = sig_i;
	cell->connections["\\O"] = sig_o;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAssert(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$assert";
	cell->connections["\\A"] = sig_a;
	cell->connections["\\EN"] = sig_en;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addSr(RTLIL::IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, RTLIL::SigSpec sig_q, bool set_polarity, bool clr_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$sr";
	cell->parameters["\\SET_POLARITY"] = set_polarity;
	cell->parameters["\\CLR_POLARITY"] = clr_polarity;
	cell->parameters["\\WIDTH"] = sig_q.width;
	cell->connections["\\SET"] = sig_set;
	cell->connections["\\CLR"] = sig_clr;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDff(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d,   RTLIL::SigSpec sig_q, bool clk_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$dff";
	cell->parameters["\\CLK_POLARITY"] = clk_polarity;
	cell->parameters["\\WIDTH"] = sig_q.width;
	cell->connections["\\CLK"] = sig_clk;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffsr(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$dffsr";
	cell->parameters["\\CLK_POLARITY"] = clk_polarity;
	cell->parameters["\\SET_POLARITY"] = set_polarity;
	cell->parameters["\\CLR_POLARITY"] = clr_polarity;
	cell->parameters["\\WIDTH"] = sig_q.width;
	cell->connections["\\CLK"] = sig_clk;
	cell->connections["\\SET"] = sig_set;
	cell->connections["\\CLR"] = sig_clr;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAdff(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,
		RTLIL::Const arst_value, bool clk_polarity, bool arst_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$adff";
	cell->parameters["\\CLK_POLARITY"] = clk_polarity;
	cell->parameters["\\ARST_POLARITY"] = arst_polarity;
	cell->parameters["\\ARST_VALUE"] = arst_value;
	cell->parameters["\\WIDTH"] = sig_q.width;
	cell->connections["\\CLK"] = sig_clk;
	cell->connections["\\ARST"] = sig_arst;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatch(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$dlatch";
	cell->parameters["\\EN_POLARITY"] = en_polarity;
	cell->parameters["\\WIDTH"] = sig_q.width;
	cell->connections["\\EN"] = sig_en;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatchsr(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity, bool set_polarity, bool clr_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$dlatchsr";
	cell->parameters["\\EN_POLARITY"] = en_polarity;
	cell->parameters["\\SET_POLARITY"] = set_polarity;
	cell->parameters["\\CLR_POLARITY"] = clr_polarity;
	cell->parameters["\\WIDTH"] = sig_q.width;
	cell->connections["\\EN"] = sig_en;
	cell->connections["\\SET"] = sig_set;
	cell->connections["\\CLR"] = sig_clr;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DFF_%c_", clk_polarity ? 'P' : 'N');
	cell->connections["\\C"] = sig_clk;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DFFSR_%c%c%c_", clk_polarity ? 'P' : 'N', set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N');
	cell->connections["\\C"] = sig_clk;
	cell->connections["\\S"] = sig_set;
	cell->connections["\\R"] = sig_clr;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAdffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,
		bool arst_value, bool clk_polarity, bool arst_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DFF_%c%c%c_", clk_polarity ? 'P' : 'N', arst_polarity ? 'P' : 'N', arst_value ? '1' : '0');
	cell->connections["\\C"] = sig_clk;
	cell->connections["\\R"] = sig_arst;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatchGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DLATCH_%c_", en_polarity ? 'P' : 'N');
	cell->connections["\\E"] = sig_en;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatchsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity, bool set_polarity, bool clr_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DLATCHSR_%c%c%c_", en_polarity ? 'P' : 'N', set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N');
	cell->connections["\\E"] = sig_en;
	cell->connections["\\S"] = sig_set;
	cell->connections["\\R"] = sig_clr;
	cell->connections["\\D"] = sig_d;
	cell->connections["\\Q"] = sig_q;
	add(cell);
	return cell;
}


RTLIL::Wire::Wire()
{
	width = 1;
	start_offset = 0;
	port_id = 0;
	port_input = false;
	port_output = false;
}

RTLIL::Memory::Memory()
{
	width = 1;
	size = 0;
}

void RTLIL::Cell::optimize()
{
	for (auto &it : connections)
		it.second.optimize();
}

RTLIL::SigChunk::SigChunk()
{
	wire = NULL;
	width = 0;
	offset = 0;
}

RTLIL::SigChunk::SigChunk(const RTLIL::Const &data)
{
	wire = NULL;
	this->data = data;
	width = data.bits.size();
	offset = 0;
}

RTLIL::SigChunk::SigChunk(RTLIL::Wire *wire, int width, int offset)
{
	this->wire = wire;
	this->width = width >= 0 ? width : wire->width;
	this->offset = offset;
}

RTLIL::SigChunk::SigChunk(const std::string &str)
{
	wire = NULL;
	data = RTLIL::Const(str);
	width = data.bits.size();
	offset = 0;
}

RTLIL::SigChunk::SigChunk(int val, int width)
{
	wire = NULL;
	data = RTLIL::Const(val, width);
	this->width = data.bits.size();
	offset = 0;
}

RTLIL::SigChunk::SigChunk(RTLIL::State bit, int width)
{
	wire = NULL;
	data = RTLIL::Const(bit, width);
	this->width = data.bits.size();
	offset = 0;
}

RTLIL::SigChunk::SigChunk(RTLIL::SigBit bit)
{
	wire = bit.wire;
	if (wire == NULL)
		data = RTLIL::Const(bit.data);
	offset = bit.offset;
	width = 1;
}

RTLIL::SigChunk RTLIL::SigChunk::extract(int offset, int length) const
{
	RTLIL::SigChunk ret;
	if (wire) {
		ret.wire = wire;
		ret.offset = this->offset + offset;
		ret.width = length;
	} else {
		for (int i = 0; i < length; i++)
			ret.data.bits.push_back(data.bits[offset+i]);
		ret.width = length;
	}
	return ret;
}

bool RTLIL::SigChunk::operator <(const RTLIL::SigChunk &other) const
{
	if (wire && other.wire)
		if (wire->name != other.wire->name)
			return wire->name < other.wire->name;
	if (wire != other.wire)
		return wire < other.wire;

	if (offset != other.offset)
		return offset < other.offset;

	if (width != other.width)
		return width < other.width;

	if (data.bits != other.data.bits)
		return data.bits < other.data.bits;
	
	return false;
}

bool RTLIL::SigChunk::operator ==(const RTLIL::SigChunk &other) const
{
	if (wire != other.wire || width != other.width || offset != other.offset)
		return false;
	if (data.bits != other.data.bits)
		return false;
	return true;
}

bool RTLIL::SigChunk::operator !=(const RTLIL::SigChunk &other) const
{
	if (*this == other)
		return false;
	return true;
}

RTLIL::SigSpec::SigSpec()
{
	width = 0;
}

RTLIL::SigSpec::SigSpec(const RTLIL::Const &data)
{
	chunks.push_back(RTLIL::SigChunk(data));
	width = chunks.back().width;
	check();
}

RTLIL::SigSpec::SigSpec(const RTLIL::SigChunk &chunk)
{
	chunks.push_back(chunk);
	width = chunks.back().width;
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::Wire *wire, int width, int offset)
{
	chunks.push_back(RTLIL::SigChunk(wire, width, offset));
	this->width = chunks.back().width;
	check();
}

RTLIL::SigSpec::SigSpec(const std::string &str)
{
	chunks.push_back(RTLIL::SigChunk(str));
	width = chunks.back().width;
	check();
}

RTLIL::SigSpec::SigSpec(int val, int width)
{
	chunks.push_back(RTLIL::SigChunk(val, width));
	this->width = width;
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::State bit, int width)
{
	chunks.push_back(RTLIL::SigChunk(bit, width));
	this->width = width;
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::SigBit bit, int width)
{
	if (bit.wire == NULL)
		chunks.push_back(RTLIL::SigChunk(bit.data, width));
	else
		for (int i = 0; i < width; i++)
			chunks.push_back(bit);
	this->width = width;
	check();
}

RTLIL::SigSpec::SigSpec(std::vector<RTLIL::SigBit> bits)
{
	chunks.reserve(bits.size());
	for (auto &bit : bits)
		chunks.push_back(bit);
	this->width = bits.size();
	check();
}

void RTLIL::SigSpec::expand()
{
	std::vector<RTLIL::SigChunk> new_chunks;
	for (size_t i = 0; i < chunks.size(); i++) {
		for (int j = 0; j < chunks[i].width; j++)
			new_chunks.push_back(chunks[i].extract(j, 1));
	}
	chunks.swap(new_chunks);
	check();
}

void RTLIL::SigSpec::optimize()
{
	std::vector<RTLIL::SigChunk> new_chunks;
	for (auto &c : chunks)
		if (new_chunks.size() == 0) {
			new_chunks.push_back(c);
		} else {
			RTLIL::SigChunk &cc = new_chunks.back();
			if (c.wire == NULL && cc.wire == NULL)
				cc.data.bits.insert(cc.data.bits.end(), c.data.bits.begin(), c.data.bits.end());
			if (c.wire == cc.wire && (c.wire == NULL || cc.offset + cc.width == c.offset))
				cc.width += c.width;
			else
				new_chunks.push_back(c);
		}
	chunks.swap(new_chunks);
	check();
}

RTLIL::SigSpec RTLIL::SigSpec::optimized() const
{
	RTLIL::SigSpec ret = *this;
	ret.optimize();
	return ret;
}

bool RTLIL::SigChunk::compare(const RTLIL::SigChunk &a, const RTLIL::SigChunk &b)
{
	if (a.wire != b.wire) {
		if (a.wire == NULL || b.wire == NULL)
			return a.wire < b.wire;
		else if (a.wire->name != b.wire->name)
			return a.wire->name < b.wire->name;
		else
			return a.wire < b.wire;
	}
	if (a.offset != b.offset)
		return a.offset < b.offset;
	if (a.width != b.width)
		return a.width < b.width;
	return a.data.bits < b.data.bits;
}

void RTLIL::SigSpec::sort()
{
	expand();
	std::sort(chunks.begin(), chunks.end(), RTLIL::SigChunk::compare);
	optimize();
}

void RTLIL::SigSpec::sort_and_unify()
{
	expand();
	std::sort(chunks.begin(), chunks.end(), RTLIL::SigChunk::compare);
	for (size_t i = 1; i < chunks.size(); i++) {
		RTLIL::SigChunk &ch1 = chunks[i-1];
		RTLIL::SigChunk &ch2 = chunks[i];
		if (!RTLIL::SigChunk::compare(ch1, ch2) && !RTLIL::SigChunk::compare(ch2, ch1)) {
			chunks.erase(chunks.begin()+i);
			width -= chunks[i].width;
			i--;
		}
	}
	optimize();
}

void RTLIL::SigSpec::replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with)
{
	replace(pattern, with, this);
}

void RTLIL::SigSpec::replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with, RTLIL::SigSpec *other) const
{
	int pos = 0, restart_pos = 0;
	assert(other == NULL || width == other->width);
	for (size_t i = 0; i < chunks.size(); i++) {
restart:
		const RTLIL::SigChunk &ch1 = chunks[i];
		if (chunks[i].wire != NULL && pos >= restart_pos)
			for (size_t j = 0, poff = 0; j < pattern.chunks.size(); j++) {
				const RTLIL::SigChunk &ch2 = pattern.chunks[j];
				assert(ch2.wire != NULL);
				if (ch1.wire == ch2.wire) {
					int lower = std::max(ch1.offset, ch2.offset);
					int upper = std::min(ch1.offset + ch1.width, ch2.offset + ch2.width);
					if (lower < upper) {
						restart_pos = pos+upper-ch1.offset;
						other->replace(pos+lower-ch1.offset, with.extract(poff+lower-ch2.offset, upper-lower));
						goto restart;
					}
				}
				poff += ch2.width;
			}
		pos += chunks[i].width;
	}
	check();
}

void RTLIL::SigSpec::remove(const RTLIL::SigSpec &pattern)
{
	remove2(pattern, NULL);
}

void RTLIL::SigSpec::remove(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other) const
{
	RTLIL::SigSpec tmp = *this;
	tmp.remove2(pattern, other);
}

void RTLIL::SigSpec::remove2(const RTLIL::SigSpec &pattern, RTLIL::SigSpec *other)
{
	int pos = 0;
	assert(other == NULL || width == other->width);
	for (size_t i = 0; i < chunks.size(); i++) {
restart:
		const RTLIL::SigChunk &ch1 = chunks[i];
		if (chunks[i].wire != NULL)
			for (size_t j = 0; j < pattern.chunks.size(); j++) {
				const RTLIL::SigChunk &ch2 = pattern.chunks[j];
				assert(ch2.wire != NULL);
				if (ch1.wire == ch2.wire) {
					int lower = std::max(ch1.offset, ch2.offset);
					int upper = std::min(ch1.offset + ch1.width, ch2.offset + ch2.width);
					if (lower < upper) {
						if (other)
							other->remove(pos+lower-ch1.offset, upper-lower);
						remove(pos+lower-ch1.offset, upper-lower);
						if (i == chunks.size())
							break;
						goto restart;
					}
				}
			}
		pos += chunks[i].width;
	}
	check();
}

RTLIL::SigSpec RTLIL::SigSpec::extract(RTLIL::SigSpec pattern, RTLIL::SigSpec *other) const
{
	assert(other == NULL || width == other->width);

	std::set<RTLIL::SigBit> pat = pattern.to_sigbit_set();
	std::vector<RTLIL::SigBit> bits_match = to_sigbit_vector();
	RTLIL::SigSpec ret;

	if (other) {
		std::vector<RTLIL::SigBit> bits_other = other ? other->to_sigbit_vector() : bits_match;
		for (int i = 0; i < width; i++)
			if (bits_match[i].wire && pat.count(bits_match[i]))
				ret.append_bit(bits_other[i]);
	} else {
		for (int i = 0; i < width; i++)
			if (bits_match[i].wire && pat.count(bits_match[i]))
				ret.append_bit(bits_match[i]);
	}

	ret.check();
	return ret;
}

void RTLIL::SigSpec::replace(int offset, const RTLIL::SigSpec &with)
{
	int pos = 0;
	assert(offset >= 0);
	assert(with.width >= 0);
	assert(offset+with.width <= width);
	remove(offset, with.width);
	for (size_t i = 0; i < chunks.size(); i++) {
		if (pos == offset) {
			chunks.insert(chunks.begin()+i, with.chunks.begin(), with.chunks.end());
			width += with.width;
			check();
			return;
		}
		pos += chunks[i].width;
	}
	assert(pos == offset);
	chunks.insert(chunks.end(), with.chunks.begin(), with.chunks.end());
	width += with.width;
	check();
}

void RTLIL::SigSpec::remove_const()
{
	for (size_t i = 0; i < chunks.size(); i++) {
		if (chunks[i].wire != NULL)
			continue;
		width -= chunks[i].width;
		chunks.erase(chunks.begin() + (i--));
	}
	check();
}

void RTLIL::SigSpec::remove(int offset, int length)
{
	int pos = 0;
	assert(offset >= 0);
	assert(length >= 0);
	assert(offset+length <= width);
	for (size_t i = 0; i < chunks.size(); i++) {
		int orig_width = chunks[i].width;
		if (pos+chunks[i].width > offset && pos < offset+length) {
			int off = offset - pos;
			int len = length;
			if (off < 0) {
				len += off;
				off = 0;
			}
			if (len > chunks[i].width-off)
				len = chunks[i].width-off;
			RTLIL::SigChunk lsb_chunk = chunks[i].extract(0, off);
			RTLIL::SigChunk msb_chunk = chunks[i].extract(off+len, chunks[i].width-off-len);
			if (lsb_chunk.width == 0 && msb_chunk.width == 0) {
				chunks.erase(chunks.begin()+i);
				i--;
			} else if (lsb_chunk.width == 0 && msb_chunk.width != 0) {
				chunks[i] = msb_chunk;
			} else if (lsb_chunk.width != 0 && msb_chunk.width == 0) {
				chunks[i] = lsb_chunk;
			} else if (lsb_chunk.width != 0 && msb_chunk.width != 0) {
				chunks[i] = lsb_chunk;
				chunks.insert(chunks.begin()+i+1, msb_chunk);
				i++;
			} else
				assert(0);
			width -= len;
		}
		pos += orig_width;
	}
	check();
}

RTLIL::SigSpec RTLIL::SigSpec::extract(int offset, int length) const
{
	int pos = 0;
	RTLIL::SigSpec ret;
	assert(offset >= 0);
	assert(length >= 0);
	assert(offset+length <= width);
	for (size_t i = 0; i < chunks.size(); i++) {
		if (pos+chunks[i].width > offset && pos < offset+length) {
			int off = offset - pos;
			int len = length;
			if (off < 0) {
				len += off;
				off = 0;
			}
			if (len > chunks[i].width-off)
				len = chunks[i].width-off;
			ret.chunks.push_back(chunks[i].extract(off, len));
			ret.width += len;
			offset += len;
			length -= len;
		}
		pos += chunks[i].width;
	}
	assert(length == 0);
	ret.check();
	return ret;
}

void RTLIL::SigSpec::append(const RTLIL::SigSpec &signal)
{
	for (size_t i = 0; i < signal.chunks.size(); i++) {
		chunks.push_back(signal.chunks[i]);
		width += signal.chunks[i].width;
	}
	// check();
}

void RTLIL::SigSpec::append_bit(const RTLIL::SigBit &bit)
{
	if (chunks.size() == 0)
		chunks.push_back(bit);
	else
		if (bit.wire == NULL)
			if (chunks.back().wire == NULL)
				chunks.back().data.bits.push_back(bit.data);
			else
				chunks.push_back(bit);
		else
			if (chunks.back().wire == bit.wire && chunks.back().offset + chunks.back().width == bit.offset)
				chunks.back().width++;
			else
				chunks.push_back(bit);
	width++;
	// check();
}

bool RTLIL::SigSpec::combine(RTLIL::SigSpec signal, RTLIL::State freeState, bool override)
{
	bool no_collisions = true;

	assert(width == signal.width);
	expand();
	signal.expand();

	for (size_t i = 0; i < chunks.size(); i++) {
		bool self_free = chunks[i].wire == NULL && chunks[i].data.bits[0] == freeState;
		bool other_free = signal.chunks[i].wire == NULL && signal.chunks[i].data.bits[0] == freeState;
		if (!self_free && !other_free) {
			if (override)
				chunks[i] = signal.chunks[i];
			else
				chunks[i] = RTLIL::SigChunk(RTLIL::State::Sx, 1);
			no_collisions = false;
		}
		if (self_free && !other_free)
			chunks[i] = signal.chunks[i];
	}

	optimize();
	return no_collisions;
}

void RTLIL::SigSpec::extend(int width, bool is_signed)
{
	if (this->width > width)
		remove(width, this->width - width);
	
	if (this->width < width) {
		RTLIL::SigSpec padding = this->width > 0 ? extract(this->width - 1, 1) : RTLIL::SigSpec(RTLIL::State::S0);
		if (!is_signed && padding != RTLIL::SigSpec(RTLIL::State::Sx) && padding != RTLIL::SigSpec(RTLIL::State::Sz) &&
				padding != RTLIL::SigSpec(RTLIL::State::Sa) && padding != RTLIL::SigSpec(RTLIL::State::Sm))
			padding = RTLIL::SigSpec(RTLIL::State::S0);
		while (this->width < width)
			append(padding);
	}

	optimize();
}

void RTLIL::SigSpec::extend_u0(int width, bool is_signed)
{
	if (this->width > width)
		remove(width, this->width - width);
	
	if (this->width < width) {
		RTLIL::SigSpec padding = this->width > 0 ? extract(this->width - 1, 1) : RTLIL::SigSpec(RTLIL::State::S0);
		if (!is_signed)
			padding = RTLIL::SigSpec(RTLIL::State::S0);
		while (this->width < width)
			append(padding);
	}

	optimize();
}

void RTLIL::SigSpec::check() const
{
	int w = 0;
	for (size_t i = 0; i < chunks.size(); i++) {
		const RTLIL::SigChunk chunk = chunks[i];
		if (chunk.wire == NULL) {
			assert(chunk.offset == 0);
			assert(chunk.data.bits.size() == (size_t)chunk.width);
		} else {
			assert(chunk.offset >= 0);
			assert(chunk.width >= 0);
			assert(chunk.offset + chunk.width <= chunk.wire->width);
			assert(chunk.data.bits.size() == 0);
		}
		w += chunk.width;
	}
	assert(w == width);
}

bool RTLIL::SigSpec::operator <(const RTLIL::SigSpec &other) const
{
	if (width != other.width)
		return width < other.width;

	RTLIL::SigSpec a = *this, b = other;
	a.optimize();
	b.optimize();

	if (a.chunks.size() != b.chunks.size())
		return a.chunks.size() < b.chunks.size();

	for (size_t i = 0; i < a.chunks.size(); i++)
		if (a.chunks[i] != b.chunks[i])
			return a.chunks[i] < b.chunks[i];

	return false;
}

bool RTLIL::SigSpec::operator ==(const RTLIL::SigSpec &other) const
{
	if (width != other.width)
		return false;

	RTLIL::SigSpec a = *this, b = other;
	a.optimize();
	b.optimize();

	if (a.chunks.size() != b.chunks.size())
		return false;

	for (size_t i = 0; i < a.chunks.size(); i++)
		if (a.chunks[i] != b.chunks[i])
			return false;

	return true;
}

bool RTLIL::SigSpec::operator !=(const RTLIL::SigSpec &other) const
{
	if (*this == other)
		return false;
	return true;
}

bool RTLIL::SigSpec::is_fully_const() const
{
	for (auto it = chunks.begin(); it != chunks.end(); it++)
		if (it->width > 0 && it->wire != NULL)
			return false;
	return true;
}

bool RTLIL::SigSpec::is_fully_def() const
{
	for (auto it = chunks.begin(); it != chunks.end(); it++) {
		if (it->width > 0 && it->wire != NULL)
			return false;
		for (size_t i = 0; i < it->data.bits.size(); i++)
			if (it->data.bits[i] != RTLIL::State::S0 && it->data.bits[i] != RTLIL::State::S1)
				return false;
	}
	return true;
}

bool RTLIL::SigSpec::is_fully_undef() const
{
	for (auto it = chunks.begin(); it != chunks.end(); it++) {
		if (it->width > 0 && it->wire != NULL)
			return false;
		for (size_t i = 0; i < it->data.bits.size(); i++)
			if (it->data.bits[i] != RTLIL::State::Sx && it->data.bits[i] != RTLIL::State::Sz)
				return false;
	}
	return true;
}

bool RTLIL::SigSpec::has_marked_bits() const
{
	for (auto it = chunks.begin(); it != chunks.end(); it++)
		if (it->width > 0 && it->wire == NULL) {
			for (size_t i = 0; i < it->data.bits.size(); i++)
				if (it->data.bits[i] == RTLIL::State::Sm)
					return true;
		}
	return false;
}

bool RTLIL::SigSpec::as_bool() const
{
	assert(is_fully_const());
	SigSpec sig = *this;
	sig.optimize();
	if (sig.width)
		return sig.chunks[0].data.as_bool();
	return false;
}

int RTLIL::SigSpec::as_int() const
{
	assert(is_fully_const());
	SigSpec sig = *this;
	sig.optimize();
	if (sig.width)
		return sig.chunks[0].data.as_int();
	return 0;
}

std::string RTLIL::SigSpec::as_string() const
{
	std::string str;
	for (size_t i = chunks.size(); i > 0; i--) {
		const RTLIL::SigChunk &chunk = chunks[i-1];
		if (chunk.wire != NULL)
			for (int j = 0; j < chunk.width; j++)
				str += "?";
		else
			str += chunk.data.as_string();
	}
	return str;
}

RTLIL::Const RTLIL::SigSpec::as_const() const
{
	assert(is_fully_const());
	SigSpec sig = *this;
	sig.optimize();
	if (sig.width)
		return sig.chunks[0].data;
	return RTLIL::Const();
}

bool RTLIL::SigSpec::match(std::string pattern) const
{
	std::string str = as_string();
	assert(pattern.size() == str.size());

	for (size_t i = 0; i < pattern.size(); i++) {
		if (pattern[i] == ' ')
			continue;
		if (pattern[i] == '*') {
			if (str[i] != 'z' && str[i] != 'x')
				return false;
			continue;
		}
		if (pattern[i] != str[i])
			return false;
	}

	return true;
}

std::set<RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_set() const
{
	std::set<RTLIL::SigBit> sigbits;
	for (auto &c : chunks)
		for (int i = 0; i < c.width; i++)
			sigbits.insert(RTLIL::SigBit(c, i));
	return sigbits;
}

std::vector<RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_vector() const
{
	std::vector<RTLIL::SigBit> sigbits;
	sigbits.reserve(width);
	for (auto &c : chunks)
		for (int i = 0; i < c.width; i++)
			sigbits.push_back(RTLIL::SigBit(c, i));
	return sigbits;
}

RTLIL::SigBit RTLIL::SigSpec::to_single_sigbit() const
{
	log_assert(width == 1);
	for (auto &c : chunks)
		if (c.width)
			return RTLIL::SigBit(c);
	log_abort();
}

static void sigspec_parse_split(std::vector<std::string> &tokens, const std::string &text, char sep)
{
	size_t start = 0, end = 0;
	while ((end = text.find(sep, start)) != std::string::npos) {
		tokens.push_back(text.substr(start, end - start));
		start = end + 1;
	}
	tokens.push_back(text.substr(start));
}

static int sigspec_parse_get_dummy_line_num()
{
	return 0;
}

bool RTLIL::SigSpec::parse(RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str)
{
	std::vector<std::string> tokens;
	sigspec_parse_split(tokens, str, ',');

	sig = RTLIL::SigSpec();
	for (int tokidx = int(tokens.size())-1; tokidx >= 0; tokidx--)
	{
		std::string netname = tokens[tokidx];
		std::string indices;

		if (netname.size() == 0)
			continue;

		if ('0' <= netname[0] && netname[0] <= '9') {
			AST::get_line_num = sigspec_parse_get_dummy_line_num;
			AST::AstNode *ast = VERILOG_FRONTEND::const2ast(netname);
			if (ast == NULL)
				return false;
			sig.append(RTLIL::Const(ast->bits));
			delete ast;
			continue;
		}

		if (module == NULL)
			return false;

		if (netname[0] != '$' && netname[0] != '\\')
			netname = "\\" + netname;

		if (module->wires.count(netname) == 0) {
			size_t indices_pos = netname.size()-1;
			if (indices_pos > 2 && netname[indices_pos] == ']')
			{
				indices_pos--;
				while (indices_pos > 0 && ('0' <= netname[indices_pos] && netname[indices_pos] <= '9')) indices_pos--;
				if (indices_pos > 0 && netname[indices_pos] == ':') {
					indices_pos--;
					while (indices_pos > 0 && ('0' <= netname[indices_pos] && netname[indices_pos] <= '9')) indices_pos--;
				}
				if (indices_pos > 0 && netname[indices_pos] == '[') {
					indices = netname.substr(indices_pos);
					netname = netname.substr(0, indices_pos);
				}
			}
		}

		if (module->wires.count(netname) == 0)
			return false;

		RTLIL::Wire *wire = module->wires.at(netname);
		if (!indices.empty()) {
			std::vector<std::string> index_tokens;
			sigspec_parse_split(index_tokens, indices.substr(1, indices.size()-2), ':');
			if (index_tokens.size() == 1)
				sig.append(RTLIL::SigSpec(wire, 1, atoi(index_tokens.at(0).c_str())));
			else {
				int a = atoi(index_tokens.at(0).c_str());
				int b = atoi(index_tokens.at(1).c_str());
				if (a > b) {
					int tmp = a;
					a = b, b = tmp;
				}
				sig.append(RTLIL::SigSpec(wire, b-a+1, a));
			}
		} else
			sig.append(wire);
	}

	return true;
}

bool RTLIL::SigSpec::parse_sel(RTLIL::SigSpec &sig, RTLIL::Design *design, RTLIL::Module *module, std::string str)
{
	if (str.empty() || str[0] != '@')
		return parse(sig, module, str);

	str = RTLIL::escape_id(str.substr(1));
	if (design->selection_vars.count(str) == 0)
		return false;

	sig = RTLIL::SigSpec();
	RTLIL::Selection &sel = design->selection_vars.at(str);
	for (auto &it : module->wires)
		if (sel.selected_member(module->name, it.first))
			sig.append(it.second);

	return true;
}

bool RTLIL::SigSpec::parse_rhs(const RTLIL::SigSpec &lhs, RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str)
{
	if (str == "0") {
		sig = RTLIL::SigSpec(RTLIL::State::S0, lhs.width);
		return true;
	}

	if (str == "~0") {
		sig = RTLIL::SigSpec(RTLIL::State::S1, lhs.width);
		return true;
	}

	if (lhs.chunks.size() == 1) {
		char *p = (char*)str.c_str(), *endptr;
		long long int val = strtoll(p, &endptr, 10);
		if (endptr && endptr != p && *endptr == 0) {
			sig = RTLIL::SigSpec(val, lhs.width);
			return true;
		}
	}

	return parse(sig, module, str);
}

RTLIL::CaseRule::~CaseRule()
{
	for (auto it = switches.begin(); it != switches.end(); it++)
		delete *it;
}

void RTLIL::CaseRule::optimize()
{
	for (auto it : switches)
		it->optimize();
	for (auto &it : compare)
		it.optimize();
	for (auto &it : actions) {
		it.first.optimize();
		it.second.optimize();
	}
}

RTLIL::CaseRule *RTLIL::CaseRule::clone() const
{
	RTLIL::CaseRule *new_caserule = new RTLIL::CaseRule;
	new_caserule->compare = compare;
	new_caserule->actions = actions;
	for (auto &it : switches)
		new_caserule->switches.push_back(it->clone());
	return new_caserule;
}

RTLIL::SwitchRule::~SwitchRule()
{
	for (auto it = cases.begin(); it != cases.end(); it++)
		delete *it;
}

void RTLIL::SwitchRule::optimize()
{
	signal.optimize();
	for (auto it : cases)
		it->optimize();
}

RTLIL::SwitchRule *RTLIL::SwitchRule::clone() const
{
	RTLIL::SwitchRule *new_switchrule = new RTLIL::SwitchRule;
	new_switchrule->signal = signal;
	new_switchrule->attributes = attributes;
	for (auto &it : cases)
		new_switchrule->cases.push_back(it->clone());
	return new_switchrule;
	
}

void RTLIL::SyncRule::optimize()
{
	signal.optimize();
	for (auto &it : actions) {
		it.first.optimize();
		it.second.optimize();
	}
}

RTLIL::SyncRule *RTLIL::SyncRule::clone() const
{
	RTLIL::SyncRule *new_syncrule = new RTLIL::SyncRule;
	new_syncrule->type = type;
	new_syncrule->signal = signal;
	new_syncrule->actions = actions;
	return new_syncrule;
}

RTLIL::Process::~Process()
{
	for (auto it = syncs.begin(); it != syncs.end(); it++)
		delete *it;
}

void RTLIL::Process::optimize()
{
	root_case.optimize();
	for (auto it : syncs)
		it->optimize();
}

RTLIL::Process *RTLIL::Process::clone() const
{
	RTLIL::Process *new_proc = new RTLIL::Process;

	new_proc->name = name;
	new_proc->attributes = attributes;

	RTLIL::CaseRule *rc_ptr = root_case.clone();
	new_proc->root_case = *rc_ptr;
	rc_ptr->switches.clear();
	delete rc_ptr;

	for (auto &it : syncs)
		new_proc->syncs.push_back(it->clone());
	
	return new_proc;
}

