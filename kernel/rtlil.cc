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

#include "kernel/yosys.h"
#include "frontends/verilog/verilog_frontend.h"
#include "backends/ilang/ilang_backend.h"

#include <string.h>
#include <algorithm>

YOSYS_NAMESPACE_BEGIN

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
		if (design->modules_.count(mod_name) == 0)
			del_list.push_back(mod_name);
		selected_members.erase(mod_name);
	}
	for (auto mod_name : del_list)
		selected_modules.erase(mod_name);

	del_list.clear();
	for (auto &it : selected_members)
		if (design->modules_.count(it.first) == 0)
			del_list.push_back(it.first);
	for (auto mod_name : del_list)
		selected_members.erase(mod_name);

	for (auto &it : selected_members) {
		del_list.clear();
		for (auto memb_name : it.second)
			if (design->modules_[it.first]->count_id(memb_name) == 0)
				del_list.push_back(memb_name);
		for (auto memb_name : del_list)
			it.second.erase(memb_name);
	}

	del_list.clear();
	add_list.clear();
	for (auto &it : selected_members)
		if (it.second.size() == 0)
			del_list.push_back(it.first);
		else if (it.second.size() == design->modules_[it.first]->wires_.size() + design->modules_[it.first]->memories.size() +
				design->modules_[it.first]->cells_.size() + design->modules_[it.first]->processes.size())
			add_list.push_back(it.first);
	for (auto mod_name : del_list)
		selected_members.erase(mod_name);
	for (auto mod_name : add_list) {
		selected_members.erase(mod_name);
		selected_modules.insert(mod_name);
	}

	if (selected_modules.size() == design->modules_.size()) {
		full_selection = true;
		selected_modules.clear();
		selected_members.clear();
	}
}

RTLIL::Design::Design()
{
	refcount_modules_ = 0;
}

RTLIL::Design::~Design()
{
	for (auto it = modules_.begin(); it != modules_.end(); it++)
		delete it->second;
}

RTLIL::ObjRange<RTLIL::Module*> RTLIL::Design::modules()
{
	return RTLIL::ObjRange<RTLIL::Module*>(&modules_, &refcount_modules_);
}

RTLIL::Module *RTLIL::Design::module(RTLIL::IdString name)
{
	return modules_.count(name) ? modules_.at(name) : NULL;
}

void RTLIL::Design::add(RTLIL::Module *module)
{
	log_assert(modules_.count(module->name) == 0);
	log_assert(refcount_modules_ == 0);
	modules_[module->name] = module;
	module->design = this;
}

RTLIL::Module *RTLIL::Design::addModule(RTLIL::IdString name)
{
	log_assert(modules_.count(name) == 0);
	log_assert(refcount_modules_ == 0);
	modules_[name] = new RTLIL::Module;
	modules_[name]->design = this;
	modules_[name]->name = name;
	return modules_[name];
}

void RTLIL::Design::remove(RTLIL::Module *module)
{
	log_assert(modules_.at(module->name) == module);
	modules_.erase(module->name);
	delete module;
}

void RTLIL::Design::check()
{
#ifndef NDEBUG
	for (auto &it : modules_) {
		log_assert(this == it.second->design);
		log_assert(it.first == it.second->name);
		log_assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		it.second->check();
	}
#endif
}

void RTLIL::Design::optimize()
{
	for (auto &it : modules_)
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

bool RTLIL::Design::selected_module(RTLIL::Module *mod) const
{
	return selected_module(mod->name);
}

bool RTLIL::Design::selected_whole_module(RTLIL::Module *mod) const
{
	return selected_whole_module(mod->name);
}

std::vector<RTLIL::Module*> RTLIL::Design::selected_modules() const
{
	std::vector<RTLIL::Module*> result;
	result.reserve(modules_.size());
	for (auto &it : modules_)
		if (selected_module(it.first))
			result.push_back(it.second);
	return result;
}

std::vector<RTLIL::Module*> RTLIL::Design::selected_whole_modules() const
{
	std::vector<RTLIL::Module*> result;
	result.reserve(modules_.size());
	for (auto &it : modules_)
		if (selected_whole_module(it.first))
			result.push_back(it.second);
	return result;
}

std::vector<RTLIL::Module*> RTLIL::Design::selected_whole_modules_warn() const
{
	std::vector<RTLIL::Module*> result;
	result.reserve(modules_.size());
	for (auto &it : modules_)
		if (selected_whole_module(it.first))
			result.push_back(it.second);
		else if (selected_module(it.first))
			log("Warning: Ignoring partially selected module %s.\n", log_id(it.first));
	return result;
}

RTLIL::Module::Module()
{
	refcount_wires_ = 0;
	refcount_cells_ = 0;
}

RTLIL::Module::~Module()
{
	for (auto it = wires_.begin(); it != wires_.end(); it++)
		delete it->second;
	for (auto it = memories.begin(); it != memories.end(); it++)
		delete it->second;
	for (auto it = cells_.begin(); it != cells_.end(); it++)
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
	return wires_.count(id) + memories.count(id) + cells_.count(id) + processes.count(id);
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

			log_error("Found error in internal cell %s%s%s (%s) at %s:%d:\n%s",
					module ? module->name.c_str() : "", module ? "." : "",
					cell->name.c_str(), cell->type.c_str(), __FILE__, linenr, ptr);
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
			if (!cell->has(name))
				error(__LINE__);
			if (cell->get(name).size() != width)
				error(__LINE__);
			expected_ports.insert(name);
		}

		void check_expected(bool check_matched_sign = true)
		{
			for (auto &para : cell->parameters)
				if (expected_params.count(para.first) == 0)
					error(__LINE__);
			for (auto &conn : cell->connections())
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
				if (!cell->has(portname))
					error(__LINE__);
				if (cell->get(portname).size() != 1)
					error(__LINE__);
			}

			for (auto &conn : cell->connections()) {
				if (conn.first.size() != 2 || conn.first.at(0) != '\\')
					error(__LINE__);
				if (strchr(ports, conn.first.at(1)) == NULL)
					error(__LINE__);
			}
		}

		void check()
		{
			if (cell->type[0] != '$' || cell->type.substr(0, 3) == "$__" || cell->type.substr(0, 8) == "$paramod" ||
					cell->type.substr(0, 9) == "$verific$" || cell->type.substr(0, 7) == "$array:" || cell->type.substr(0, 8) == "$extern:")
				return;

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

			if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr" ||
					cell->type == "$shift" || cell->type == "$shiftx") {
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
				port("\\EN", param("\\WIDTH"));
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
				port("\\WR_EN", param("\\WR_PORTS") * param("\\WIDTH"));
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
	for (auto &it : wires_) {
		log_assert(this == it.second->module);
		log_assert(it.first == it.second->name);
		log_assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		log_assert(it.second->width >= 0);
		log_assert(it.second->port_id >= 0);
		for (auto &it2 : it.second->attributes) {
			log_assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
		}
	}

	for (auto &it : memories) {
		log_assert(it.first == it.second->name);
		log_assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		log_assert(it.second->width >= 0);
		log_assert(it.second->size >= 0);
		for (auto &it2 : it.second->attributes) {
			log_assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
		}
	}

	for (auto &it : cells_) {
		log_assert(this == it.second->module);
		log_assert(it.first == it.second->name);
		log_assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		log_assert(it.second->type.size() > 0 && (it.second->type[0] == '\\' || it.second->type[0] == '$'));
		for (auto &it2 : it.second->connections()) {
			log_assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
			it2.second.check();
		}
		for (auto &it2 : it.second->attributes) {
			log_assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
		}
		for (auto &it2 : it.second->parameters) {
			log_assert(it2.first.size() > 0 && (it2.first[0] == '\\' || it2.first[0] == '$'));
		}
		InternalCellChecker checker(this, it.second);
		checker.check();
	}

	for (auto &it : processes) {
		log_assert(it.first == it.second->name);
		log_assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
		// FIXME: More checks here..
	}

	for (auto &it : connections_) {
		log_assert(it.first.size() == it.second.size());
		it.first.check();
		it.second.check();
	}

	for (auto &it : attributes) {
		log_assert(it.first.size() > 0 && (it.first[0] == '\\' || it.first[0] == '$'));
	}
#endif
}

void RTLIL::Module::optimize()
{
}

void RTLIL::Module::cloneInto(RTLIL::Module *new_mod) const
{
	log_assert(new_mod->refcount_wires_ == 0);
	log_assert(new_mod->refcount_cells_ == 0);

	new_mod->connections_ = connections_;
	new_mod->attributes = attributes;

	for (auto &it : wires_)
		new_mod->addWire(it.first, it.second);

	for (auto &it : memories)
		new_mod->memories[it.first] = new RTLIL::Memory(*it.second);

	for (auto &it : cells_)
		new_mod->addCell(it.first, it.second);

	for (auto &it : processes)
		new_mod->processes[it.first] = it.second->clone();

	struct RewriteSigSpecWorker
	{
		RTLIL::Module *mod;
		void operator()(RTLIL::SigSpec &sig)
		{
			std::vector<RTLIL::SigChunk> chunks = sig.chunks();
			for (auto &c : chunks)
				if (c.wire != NULL)
					c.wire = mod->wires_.at(c.wire->name);
			sig = chunks;
		}
	};

	RewriteSigSpecWorker rewriteSigSpecWorker;
	rewriteSigSpecWorker.mod = new_mod;
	new_mod->rewrite_sigspecs(rewriteSigSpecWorker);
}

RTLIL::Module *RTLIL::Module::clone() const
{
	RTLIL::Module *new_mod = new RTLIL::Module;
	new_mod->name = name;
	cloneInto(new_mod);
	return new_mod;
}

bool RTLIL::Module::has_memories() const
{
	return !memories.empty();
}

bool RTLIL::Module::has_processes() const
{
	return !processes.empty();
}

bool RTLIL::Module::has_memories_warn() const
{
	if (!memories.empty())
		log("Warning: Ignoring module %s because it contains memories (run 'memory' command first).\n", log_id(this));
	return !memories.empty();
}

bool RTLIL::Module::has_processes_warn() const
{
	if (!processes.empty())
		log("Warning: Ignoring module %s because it contains processes (run 'proc' command first).\n", log_id(this));
	return !processes.empty();
}

std::vector<RTLIL::Wire*> RTLIL::Module::selected_wires() const
{
	std::vector<RTLIL::Wire*> result;
	result.reserve(wires_.size());
	for (auto &it : wires_)
		if (design->selected(this, it.second))
			result.push_back(it.second);
	return result;
}

std::vector<RTLIL::Cell*> RTLIL::Module::selected_cells() const
{
	std::vector<RTLIL::Cell*> result;
	result.reserve(wires_.size());
	for (auto &it : cells_)
		if (design->selected(this, it.second))
			result.push_back(it.second);
	return result;
}

void RTLIL::Module::add(RTLIL::Wire *wire)
{
	log_assert(!wire->name.empty());
	log_assert(count_id(wire->name) == 0);
	log_assert(refcount_wires_ == 0);
	wires_[wire->name] = wire;
	wire->module = this;
}

void RTLIL::Module::add(RTLIL::Cell *cell)
{
	log_assert(!cell->name.empty());
	log_assert(count_id(cell->name) == 0);
	log_assert(refcount_cells_ == 0);
	cells_[cell->name] = cell;
	cell->module = this;
}

namespace {
	struct DeleteWireWorker
	{
		RTLIL::Module *module;
		const std::set<RTLIL::Wire*> *wires_p;

		void operator()(RTLIL::SigSpec &sig) {
			std::vector<RTLIL::SigChunk> chunks = sig;
			for (auto &c : chunks)
				if (c.wire != NULL && wires_p->count(c.wire)) {
					c.wire = module->addWire(NEW_ID, c.width);
					c.offset = 0;
				}
			sig = chunks;
		}
	};
}

#if 0
void RTLIL::Module::remove(RTLIL::Wire *wire)
{
	std::set<RTLIL::Wire*> wires_;
	wires_.insert(wire);
	remove(wires_);
}
#endif

void RTLIL::Module::remove(const std::set<RTLIL::Wire*> &wires)
{
	log_assert(refcount_wires_ == 0);

	DeleteWireWorker delete_wire_worker;
	delete_wire_worker.module = this;
	delete_wire_worker.wires_p = &wires;
	rewrite_sigspecs(delete_wire_worker);

	for (auto &it : wires) {
		log_assert(wires_.count(it->name) != 0);
		wires_.erase(it->name);
		delete it;
	}
}

void RTLIL::Module::remove(RTLIL::Cell *cell)
{
	log_assert(cells_.count(cell->name) != 0);
	log_assert(refcount_cells_ == 0);
	cells_.erase(cell->name);
	delete cell;
}

void RTLIL::Module::rename(RTLIL::Wire *wire, RTLIL::IdString new_name)
{
	log_assert(wires_[wire->name] == wire);
	log_assert(refcount_wires_ == 0);
	wires_.erase(wire->name);
	wire->name = new_name;
	add(wire);
}

void RTLIL::Module::rename(RTLIL::Cell *cell, RTLIL::IdString new_name)
{
	log_assert(cells_[cell->name] == cell);
	log_assert(refcount_wires_ == 0);
	cells_.erase(cell->name);
	cell->name = new_name;
	add(cell);
}

void RTLIL::Module::rename(RTLIL::IdString old_name, RTLIL::IdString new_name)
{
	log_assert(count_id(old_name) != 0);
	if (wires_.count(old_name))
		rename(wires_.at(old_name), new_name);
	else if (cells_.count(old_name))
		rename(cells_.at(old_name), new_name);
	else
		log_abort();
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

void RTLIL::Module::connect(const RTLIL::SigSig &conn)
{
	connections_.push_back(conn);
}

void RTLIL::Module::connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs)
{
	connections_.push_back(RTLIL::SigSig(lhs, rhs));
}

const std::vector<RTLIL::SigSig> &RTLIL::Module::connections() const
{
	return connections_;
}

void RTLIL::Module::fixup_ports()
{
	std::vector<RTLIL::Wire*> all_ports;

	for (auto &w : wires_)
		if (w.second->port_input || w.second->port_output)
			all_ports.push_back(w.second);
		else
			w.second->port_id = 0;

	std::sort(all_ports.begin(), all_ports.end(), fixup_ports_compare);
	for (size_t i = 0; i < all_ports.size(); i++)
		all_ports[i]->port_id = i+1;
}

RTLIL::Wire *RTLIL::Module::addWire(RTLIL::IdString name, int width)
{
	RTLIL::Wire *wire = new RTLIL::Wire;
	wire->name = name;
	wire->width = width;
	add(wire);
	return wire;
}

RTLIL::Wire *RTLIL::Module::addWire(RTLIL::IdString name, const RTLIL::Wire *other)
{
	RTLIL::Wire *wire = addWire(name);
	wire->width = other->width;
	wire->start_offset = other->start_offset;
	wire->port_id = other->port_id;
	wire->port_input = other->port_input;
	wire->port_output = other->port_output;
	wire->upto = other->upto;
	wire->attributes = other->attributes;
	return wire;
}

RTLIL::Cell *RTLIL::Module::addCell(RTLIL::IdString name, RTLIL::IdString type)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = type;
	add(cell);
	return cell;
}

RTLIL::Cell *RTLIL::Module::addCell(RTLIL::IdString name, const RTLIL::Cell *other)
{
	RTLIL::Cell *cell = addCell(name, other->type);
	cell->connections_ = other->connections_;
	cell->parameters = other->parameters;
	cell->attributes = other->attributes;
	return cell;
}

#define DEF_METHOD(_func, _y_size, _type) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed) { \
		RTLIL::Cell *cell = new RTLIL::Cell;                \
		cell->name = name;                                  \
		cell->type = _type;                                 \
		cell->parameters["\\A_SIGNED"] = is_signed;         \
		cell->parameters["\\A_WIDTH"] = sig_a.size();        \
		cell->parameters["\\Y_WIDTH"] = sig_y.size();        \
		cell->set("\\A", sig_a);                   \
		cell->set("\\Y", sig_y);                   \
		add(cell);                                          \
		return cell;                                        \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed) { \
		RTLIL::SigSpec sig_y = addWire(NEW_ID, _y_size);    \
		add ## _func(name, sig_a, sig_y, is_signed);        \
		return sig_y;                                       \
	}
DEF_METHOD(Not,        sig_a.size(), "$not")
DEF_METHOD(Pos,        sig_a.size(), "$pos")
DEF_METHOD(Bu0,        sig_a.size(), "$bu0")
DEF_METHOD(Neg,        sig_a.size(), "$neg")
DEF_METHOD(ReduceAnd,  1, "$reduce_and")
DEF_METHOD(ReduceOr,   1, "$reduce_or")
DEF_METHOD(ReduceXor,  1, "$reduce_xor")
DEF_METHOD(ReduceXnor, 1, "$reduce_xnor")
DEF_METHOD(ReduceBool, 1, "$reduce_bool")
DEF_METHOD(LogicNot,   1, "$logic_not")
#undef DEF_METHOD

#define DEF_METHOD(_func, _y_size, _type) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed) { \
		RTLIL::Cell *cell = new RTLIL::Cell;                \
		cell->name = name;                                  \
		cell->type = _type;                                 \
		cell->parameters["\\A_SIGNED"] = is_signed;         \
		cell->parameters["\\B_SIGNED"] = is_signed;         \
		cell->parameters["\\A_WIDTH"] = sig_a.size();        \
		cell->parameters["\\B_WIDTH"] = sig_b.size();        \
		cell->parameters["\\Y_WIDTH"] = sig_y.size();        \
		cell->set("\\A", sig_a);                   \
		cell->set("\\B", sig_b);                   \
		cell->set("\\Y", sig_y);                   \
		add(cell);                                          \
		return cell;                                        \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed) { \
		RTLIL::SigSpec sig_y = addWire(NEW_ID, _y_size);    \
		add ## _func(name, sig_a, sig_b, sig_y, is_signed); \
		return sig_y;                                       \
	}
DEF_METHOD(And,      std::max(sig_a.size(), sig_b.size()), "$and")
DEF_METHOD(Or,       std::max(sig_a.size(), sig_b.size()), "$or")
DEF_METHOD(Xor,      std::max(sig_a.size(), sig_b.size()), "$xor")
DEF_METHOD(Xnor,     std::max(sig_a.size(), sig_b.size()), "$xnor")
DEF_METHOD(Shl,      sig_a.size(), "$shl")
DEF_METHOD(Shr,      sig_a.size(), "$shr")
DEF_METHOD(Sshl,     sig_a.size(), "$sshl")
DEF_METHOD(Sshr,     sig_a.size(), "$sshr")
DEF_METHOD(Shift,    sig_a.size(), "$shift")
DEF_METHOD(Shiftx,   sig_a.size(), "$shiftx")
DEF_METHOD(Lt,       1, "$lt")
DEF_METHOD(Le,       1, "$le")
DEF_METHOD(Eq,       1, "$eq")
DEF_METHOD(Ne,       1, "$ne")
DEF_METHOD(Eqx,      1, "$eqx")
DEF_METHOD(Nex,      1, "$nex")
DEF_METHOD(Ge,       1, "$ge")
DEF_METHOD(Gt,       1, "$gt")
DEF_METHOD(Add,      std::max(sig_a.size(), sig_b.size()), "$add")
DEF_METHOD(Sub,      std::max(sig_a.size(), sig_b.size()), "$sub")
DEF_METHOD(Mul,      std::max(sig_a.size(), sig_b.size()), "$mul")
DEF_METHOD(Div,      std::max(sig_a.size(), sig_b.size()), "$div")
DEF_METHOD(Mod,      std::max(sig_a.size(), sig_b.size()), "$mod")
DEF_METHOD(LogicAnd, 1, "$logic_and")
DEF_METHOD(LogicOr,  1, "$logic_or")
#undef DEF_METHOD

#define DEF_METHOD(_func, _type, _pmux) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y) { \
		RTLIL::Cell *cell = new RTLIL::Cell;                     \
		cell->name = name;                                       \
		cell->type = _type;                                      \
		cell->parameters["\\WIDTH"] = sig_a.size();               \
		cell->parameters["\\WIDTH"] = sig_b.size();               \
		if (_pmux) cell->parameters["\\S_WIDTH"] = sig_s.size();  \
		cell->set("\\A", sig_a);                        \
		cell->set("\\B", sig_b);                        \
		cell->set("\\S", sig_s);                        \
		cell->set("\\Y", sig_y);                        \
		add(cell);                                               \
		return cell;                                             \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s) { \
		RTLIL::SigSpec sig_y = addWire(NEW_ID, sig_a.size());     \
		add ## _func(name, sig_a, sig_b, sig_s, sig_y);          \
		return sig_y;                                            \
	}
DEF_METHOD(Mux,      "$mux",        0)
DEF_METHOD(Pmux,     "$pmux",       1)
DEF_METHOD(SafePmux, "$safe_pmux",  1)
#undef DEF_METHOD

#define DEF_METHOD_2(_func, _type, _P1, _P2) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig1, RTLIL::SigSpec sig2) { \
		RTLIL::Cell *cell = new RTLIL::Cell;        \
		cell->name = name;                          \
		cell->type = _type;                         \
		cell->set("\\" #_P1, sig1);                 \
		cell->set("\\" #_P2, sig2);                 \
		add(cell);                                  \
		return cell;                                \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig1) { \
		RTLIL::SigSpec sig2 = addWire(NEW_ID);      \
		add ## _func(name, sig1, sig2);             \
		return sig2;                                \
	}
#define DEF_METHOD_3(_func, _type, _P1, _P2, _P3) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig1, RTLIL::SigSpec sig2, RTLIL::SigSpec sig3) { \
		RTLIL::Cell *cell = new RTLIL::Cell;        \
		cell->name = name;                          \
		cell->type = _type;                         \
		cell->set("\\" #_P1, sig1);                 \
		cell->set("\\" #_P2, sig2);                 \
		cell->set("\\" #_P3, sig3);                 \
		add(cell);                                  \
		return cell;                                \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig1, RTLIL::SigSpec sig2) { \
		RTLIL::SigSpec sig3 = addWire(NEW_ID);      \
		add ## _func(name, sig1, sig2, sig3);       \
		return sig3;                                \
	}
#define DEF_METHOD_4(_func, _type, _P1, _P2, _P3, _P4) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig1, RTLIL::SigSpec sig2, RTLIL::SigSpec sig3, RTLIL::SigSpec sig4) { \
		RTLIL::Cell *cell = new RTLIL::Cell;        \
		cell->name = name;                          \
		cell->type = _type;                         \
		cell->set("\\" #_P1, sig1);                 \
		cell->set("\\" #_P2, sig2);                 \
		cell->set("\\" #_P3, sig3);                 \
		cell->set("\\" #_P4, sig4);                 \
		add(cell);                                  \
		return cell;                                \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig1, RTLIL::SigSpec sig2, RTLIL::SigSpec sig3) { \
		RTLIL::SigSpec sig4 = addWire(NEW_ID);      \
		add ## _func(name, sig1, sig2, sig3, sig4); \
		return sig4;                                \
	}
DEF_METHOD_2(InvGate, "$_INV_", A, Y)
DEF_METHOD_3(AndGate, "$_AND_", A, B, Y)
DEF_METHOD_3(OrGate,  "$_OR_",  A, B, Y)
DEF_METHOD_3(XorGate, "$_XOR_", A, B, Y)
DEF_METHOD_4(MuxGate, "$_MUX_", A, B, S, Y)
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
	cell->parameters["\\A_WIDTH"] = sig_a.size();
	cell->parameters["\\B_WIDTH"] = sig_b.size();
	cell->parameters["\\Y_WIDTH"] = sig_y.size();
	cell->set("\\A", sig_a);
	cell->set("\\B", sig_b);
	cell->set("\\Y", sig_y);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addSlice(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, RTLIL::Const offset)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$slice";
	cell->parameters["\\A_WIDTH"] = sig_a.size();
	cell->parameters["\\Y_WIDTH"] = sig_y.size();
	cell->parameters["\\OFFSET"] = offset;
	cell->set("\\A", sig_a);
	cell->set("\\Y", sig_y);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addConcat(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$concat";
	cell->parameters["\\A_WIDTH"] = sig_a.size();
	cell->parameters["\\B_WIDTH"] = sig_b.size();
	cell->set("\\A", sig_a);
	cell->set("\\B", sig_b);
	cell->set("\\Y", sig_y);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addLut(RTLIL::IdString name, RTLIL::SigSpec sig_i, RTLIL::SigSpec sig_o, RTLIL::Const lut)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$lut";
	cell->parameters["\\LUT"] = lut;
	cell->parameters["\\WIDTH"] = sig_i.size();
	cell->set("\\I", sig_i);
	cell->set("\\O", sig_o);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAssert(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$assert";
	cell->set("\\A", sig_a);
	cell->set("\\EN", sig_en);
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
	cell->parameters["\\WIDTH"] = sig_q.size();
	cell->set("\\SET", sig_set);
	cell->set("\\CLR", sig_clr);
	cell->set("\\Q", sig_q);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDff(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d,   RTLIL::SigSpec sig_q, bool clk_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$dff";
	cell->parameters["\\CLK_POLARITY"] = clk_polarity;
	cell->parameters["\\WIDTH"] = sig_q.size();
	cell->set("\\CLK", sig_clk);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
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
	cell->parameters["\\WIDTH"] = sig_q.size();
	cell->set("\\CLK", sig_clk);
	cell->set("\\SET", sig_set);
	cell->set("\\CLR", sig_clr);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
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
	cell->parameters["\\WIDTH"] = sig_q.size();
	cell->set("\\CLK", sig_clk);
	cell->set("\\ARST", sig_arst);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatch(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = "$dlatch";
	cell->parameters["\\EN_POLARITY"] = en_polarity;
	cell->parameters["\\WIDTH"] = sig_q.size();
	cell->set("\\EN", sig_en);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
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
	cell->parameters["\\WIDTH"] = sig_q.size();
	cell->set("\\EN", sig_en);
	cell->set("\\SET", sig_set);
	cell->set("\\CLR", sig_clr);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DFF_%c_", clk_polarity ? 'P' : 'N');
	cell->set("\\C", sig_clk);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DFFSR_%c%c%c_", clk_polarity ? 'P' : 'N', set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N');
	cell->set("\\C", sig_clk);
	cell->set("\\S", sig_set);
	cell->set("\\R", sig_clr);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAdffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,
		bool arst_value, bool clk_polarity, bool arst_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DFF_%c%c%c_", clk_polarity ? 'P' : 'N', arst_polarity ? 'P' : 'N', arst_value ? '1' : '0');
	cell->set("\\C", sig_clk);
	cell->set("\\R", sig_arst);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatchGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DLATCH_%c_", en_polarity ? 'P' : 'N');
	cell->set("\\E", sig_en);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
	add(cell);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatchsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity, bool set_polarity, bool clr_polarity)
{
	RTLIL::Cell *cell = new RTLIL::Cell;
	cell->name = name;
	cell->type = stringf("$_DLATCHSR_%c%c%c_", en_polarity ? 'P' : 'N', set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N');
	cell->set("\\E", sig_en);
	cell->set("\\S", sig_set);
	cell->set("\\R", sig_clr);
	cell->set("\\D", sig_d);
	cell->set("\\Q", sig_q);
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
	upto = false;
}

RTLIL::Memory::Memory()
{
	width = 1;
	size = 0;
}

bool RTLIL::Cell::has(RTLIL::IdString portname)
{
	return connections_.count(portname) != 0;
}

void RTLIL::Cell::unset(RTLIL::IdString portname)
{
	connections_.erase(portname);
}

void RTLIL::Cell::set(RTLIL::IdString portname, RTLIL::SigSpec signal)
{
	connections_[portname] = signal;
}

const RTLIL::SigSpec &RTLIL::Cell::get(RTLIL::IdString portname) const
{
	return connections_.at(portname);
}

const std::map<RTLIL::IdString, RTLIL::SigSpec> &RTLIL::Cell::connections() const
{
	return connections_;
}

void RTLIL::Cell::check()
{
#ifndef NDEBUG
	InternalCellChecker checker(NULL, this);
	checker.check();
#endif
}

void RTLIL::Cell::fixup_parameters(bool set_a_signed, bool set_b_signed)
{
	if (type[0] != '$' || type.substr(0, 2) == "$_" || type.substr(0, 8) == "$paramod" ||
			type.substr(0, 9) == "$verific$" || type.substr(0, 7) == "$array:" || type.substr(0, 8) == "$extern:")
		return;

	if (type == "$mux" || type == "$pmux" || type == "$safe_pmux")
	{
		parameters["\\WIDTH"] = SIZE(connections_["\\Y"]);
		if (type == "$pmux" || type == "$safe_pmux")
			parameters["\\S_WIDTH"] = SIZE(connections_["\\S"]);
		check();
		return;
	}

	bool signedness_ab = type != "$slice" && type != "$concat";

	if (connections_.count("\\A")) {
		if (signedness_ab) {
			if (set_a_signed)
				parameters["\\A_SIGNED"] = true;
			else if (parameters.count("\\A_SIGNED") == 0)
				parameters["\\A_SIGNED"] = false;
		}
		parameters["\\A_WIDTH"] = SIZE(connections_["\\A"]);
	}

	if (connections_.count("\\B")) {
		if (signedness_ab) {
			if (set_b_signed)
				parameters["\\B_SIGNED"] = true;
			else if (parameters.count("\\B_SIGNED") == 0)
				parameters["\\B_SIGNED"] = false;
		}
		parameters["\\B_WIDTH"] = SIZE(connections_["\\B"]);
	}

	if (connections_.count("\\Y"))
		parameters["\\Y_WIDTH"] = SIZE(connections_["\\Y"]);

	check();
}

RTLIL::SigChunk::SigChunk()
{
	wire = NULL;
	width = 0;
	offset = 0;
}

RTLIL::SigChunk::SigChunk(const RTLIL::Const &value)
{
	wire = NULL;
	data = value;
	width = data.bits.size();
	offset = 0;
}

RTLIL::SigChunk::SigChunk(RTLIL::Wire *wire)
{
	log_assert(wire != nullptr);
	this->wire = wire;
	this->width = wire->width;
	this->offset = 0;
}

RTLIL::SigChunk::SigChunk(RTLIL::Wire *wire, int offset, int width)
{
	log_assert(wire != nullptr);
	this->wire = wire;
	this->width = width;
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

	return data.bits < other.data.bits;
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
	width_ = 0;
	hash_ = 0;
}

RTLIL::SigSpec::SigSpec(const RTLIL::SigSpec &other)
{
	*this = other;
}

RTLIL::SigSpec::SigSpec(std::initializer_list<RTLIL::SigSpec> parts)
{
	cover("kernel.rtlil.sigspec.init.list");

	width_ = 0;
	hash_ = 0;

	std::vector<RTLIL::SigSpec> parts_vec(parts.begin(), parts.end());
	for (auto it = parts_vec.rbegin(); it != parts_vec.rend(); it++)
		append(*it);
}

const RTLIL::SigSpec &RTLIL::SigSpec::operator=(const RTLIL::SigSpec &other)
{
	cover("kernel.rtlil.sigspec.assign");

	width_ = other.width_;
	hash_ = other.hash_;
	chunks_ = other.chunks_;
	bits_.clear();

	if (!other.bits_.empty())
	{
		RTLIL::SigChunk *last = NULL;
		int last_end_offset = 0;

		for (auto &bit : other.bits_) {
			if (last && bit.wire == last->wire) {
				if (bit.wire == NULL) {
					last->data.bits.push_back(bit.data);
					last->width++;
					continue;
				} else if (last_end_offset == bit.offset) {
					last_end_offset++;
					last->width++;
					continue;
				}
			}
			chunks_.push_back(bit);
			last = &chunks_.back();
			last_end_offset = bit.offset + 1;
		}

		check();
	}

	return *this;
}

RTLIL::SigSpec::SigSpec(const RTLIL::Const &value)
{
	cover("kernel.rtlil.sigspec.init.const");

	chunks_.push_back(RTLIL::SigChunk(value));
	width_ = chunks_.back().width;
	hash_ = 0;
	check();
}

RTLIL::SigSpec::SigSpec(const RTLIL::SigChunk &chunk)
{
	cover("kernel.rtlil.sigspec.init.chunk");

	chunks_.push_back(chunk);
	width_ = chunks_.back().width;
	hash_ = 0;
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::Wire *wire)
{
	cover("kernel.rtlil.sigspec.init.wire");

	chunks_.push_back(RTLIL::SigChunk(wire));
	width_ = chunks_.back().width;
	hash_ = 0;
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::Wire *wire, int offset, int width)
{
	cover("kernel.rtlil.sigspec.init.wire_part");

	chunks_.push_back(RTLIL::SigChunk(wire, offset, width));
	width_ = chunks_.back().width;
	hash_ = 0;
	check();
}

RTLIL::SigSpec::SigSpec(const std::string &str)
{
	cover("kernel.rtlil.sigspec.init.str");

	chunks_.push_back(RTLIL::SigChunk(str));
	width_ = chunks_.back().width;
	hash_ = 0;
	check();
}

RTLIL::SigSpec::SigSpec(int val, int width)
{
	cover("kernel.rtlil.sigspec.init.int");

	chunks_.push_back(RTLIL::SigChunk(val, width));
	width_ = width;
	hash_ = 0;
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::State bit, int width)
{
	cover("kernel.rtlil.sigspec.init.state");

	chunks_.push_back(RTLIL::SigChunk(bit, width));
	width_ = width;
	hash_ = 0;
	check();
}

RTLIL::SigSpec::SigSpec(RTLIL::SigBit bit, int width)
{
	cover("kernel.rtlil.sigspec.init.bit");

	if (bit.wire == NULL)
		chunks_.push_back(RTLIL::SigChunk(bit.data, width));
	else
		for (int i = 0; i < width; i++)
			chunks_.push_back(bit);
	width_ = width;
	hash_ = 0;
	check();
}

RTLIL::SigSpec::SigSpec(std::vector<RTLIL::SigChunk> chunks)
{
	cover("kernel.rtlil.sigspec.init.stdvec_chunks");

	width_ = 0;
	hash_ = 0;
	for (auto &c : chunks)
		append(c);
	check();
}

RTLIL::SigSpec::SigSpec(std::vector<RTLIL::SigBit> bits)
{
	cover("kernel.rtlil.sigspec.init.stdvec_bits");

	width_ = 0;
	hash_ = 0;
	for (auto &bit : bits)
		append_bit(bit);
	check();
}

RTLIL::SigSpec::SigSpec(std::set<RTLIL::SigBit> bits)
{
	cover("kernel.rtlil.sigspec.init.stdset_bits");

	width_ = 0;
	hash_ = 0;
	for (auto &bit : bits)
		append_bit(bit);
	check();
}

void RTLIL::SigSpec::pack() const
{
	RTLIL::SigSpec *that = (RTLIL::SigSpec*)this;

	if (that->bits_.empty())
		return;

	cover("kernel.rtlil.sigspec.convert.pack");
	log_assert(that->chunks_.empty());

	std::vector<RTLIL::SigBit> old_bits;
	old_bits.swap(that->bits_);

	RTLIL::SigChunk *last = NULL;
	int last_end_offset = 0;

	for (auto &bit : old_bits) {
		if (last && bit.wire == last->wire) {
			if (bit.wire == NULL) {
				last->data.bits.push_back(bit.data);
				last->width++;
				continue;
			} else if (last_end_offset == bit.offset) {
				last_end_offset++;
				last->width++;
				continue;
			}
		}
		that->chunks_.push_back(bit);
		last = &that->chunks_.back();
		last_end_offset = bit.offset + 1;
	}

	check();
}

void RTLIL::SigSpec::unpack() const
{
	RTLIL::SigSpec *that = (RTLIL::SigSpec*)this;

	if (that->chunks_.empty())
		return;

	cover("kernel.rtlil.sigspec.convert.unpack");
	log_assert(that->bits_.empty());

	that->bits_.reserve(that->width_);
	for (auto &c : that->chunks_)
		for (int i = 0; i < c.width; i++)
			that->bits_.push_back(RTLIL::SigBit(c, i));

	that->chunks_.clear();
	that->hash_ = 0;
}

#define DJB2(_hash, _value) do { (_hash) = (((_hash) << 5) + (_hash)) + (_value); } while (0)

void RTLIL::SigSpec::hash() const
{
	RTLIL::SigSpec *that = (RTLIL::SigSpec*)this;

	if (that->hash_ != 0)
		return;

	cover("kernel.rtlil.sigspec.hash");
	that->pack();

	that->hash_ = 5381;
	for (auto &c : that->chunks_)
		if (c.wire == NULL) {
			for (auto &v : c.data.bits)
				DJB2(that->hash_, v);
		} else {
			for (auto &v : c.wire->name)
				DJB2(that->hash_, v);
			DJB2(that->hash_, c.offset);
			DJB2(that->hash_, c.width);
		}

	if (that->hash_ == 0)
		that->hash_ = 1;
}

void RTLIL::SigSpec::sort()
{
	unpack();
	cover("kernel.rtlil.sigspec.sort");
	std::sort(bits_.begin(), bits_.end());
}

void RTLIL::SigSpec::sort_and_unify()
{
	cover("kernel.rtlil.sigspec.sort_and_unify");
	*this = this->to_sigbit_set();
}

void RTLIL::SigSpec::replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with)
{
	replace(pattern, with, this);
}

void RTLIL::SigSpec::replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with, RTLIL::SigSpec *other) const
{
	cover("kernel.rtlil.sigspec.replace");

	unpack();
	pattern.unpack();
	with.unpack();

	log_assert(other != NULL);
	log_assert(width_ == other->width_);
	other->unpack();

	log_assert(pattern.width_ == with.width_);

	std::map<RTLIL::SigBit, RTLIL::SigBit> pattern_map;
	for (int i = 0; i < SIZE(pattern.bits_); i++)
		if (pattern.bits_[i].wire != NULL)
			pattern_map[pattern.bits_[i]] = with.bits_[i];

	for (int i = 0; i < SIZE(bits_); i++)
		if (pattern_map.count(bits_[i]))
			other->bits_[i] = pattern_map.at(bits_[i]);

	other->check();
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
	if (other)
		cover("kernel.rtlil.sigspec.remove_other");
	else
		cover("kernel.rtlil.sigspec.remove");

	unpack();

	if (other != NULL) {
		log_assert(width_ == other->width_);
		other->unpack();
	}

	std::set<RTLIL::SigBit> pattern_bits = pattern.to_sigbit_set();
	std::vector<RTLIL::SigBit> new_bits, new_other_bits;

	for (int i = 0; i < SIZE(bits_); i++) {
		if (bits_[i].wire != NULL && pattern_bits.count(bits_[i]))
			continue;
		if (other != NULL)
			new_other_bits.push_back(other->bits_[i]);
		new_bits.push_back(bits_[i]);
	}

	bits_.swap(new_bits);
	width_ = SIZE(bits_);

	if (other != NULL) {
		other->bits_.swap(new_other_bits);
		other->width_ = SIZE(other->bits_);
	}

	check();
}

RTLIL::SigSpec RTLIL::SigSpec::extract(RTLIL::SigSpec pattern, const RTLIL::SigSpec *other) const
{
	if (other)
		cover("kernel.rtlil.sigspec.extract_other");
	else
		cover("kernel.rtlil.sigspec.extract");

	pack();
	pattern.pack();

	if (other != NULL)
		other->pack();

	log_assert(other == NULL || width_ == other->width_);

	std::set<RTLIL::SigBit> pat = pattern.to_sigbit_set();
	std::vector<RTLIL::SigBit> bits_match = to_sigbit_vector();
	RTLIL::SigSpec ret;

	if (other) {
		std::vector<RTLIL::SigBit> bits_other = other->to_sigbit_vector();
		for (int i = 0; i < width_; i++)
			if (bits_match[i].wire && pat.count(bits_match[i]))
				ret.append_bit(bits_other[i]);
	} else {
		for (int i = 0; i < width_; i++)
			if (bits_match[i].wire && pat.count(bits_match[i]))
				ret.append_bit(bits_match[i]);
	}

	ret.check();
	return ret;
}

void RTLIL::SigSpec::replace(int offset, const RTLIL::SigSpec &with)
{
	cover("kernel.rtlil.sigspec.replace_pos");

	unpack();
	with.unpack();

	log_assert(offset >= 0);
	log_assert(with.width_ >= 0);
	log_assert(offset+with.width_ <= width_);

	for (int i = 0; i < with.width_; i++)
		bits_.at(offset + i) = with.bits_.at(i);

	check();
}

void RTLIL::SigSpec::remove_const()
{
	if (packed())
	{
		cover("kernel.rtlil.sigspec.remove_const.packed");

		std::vector<RTLIL::SigChunk> new_chunks;
		new_chunks.reserve(SIZE(chunks_));

		width_ = 0;
		for (auto &chunk : chunks_)
			if (chunk.wire != NULL) {
				new_chunks.push_back(chunk);
				width_ += chunk.width;
			}

		chunks_.swap(new_chunks);
	}
	else
	{
		cover("kernel.rtlil.sigspec.remove_const.unpacked");

		std::vector<RTLIL::SigBit> new_bits;
		new_bits.reserve(width_);

		for (auto &bit : bits_)
			if (bit.wire != NULL)
				new_bits.push_back(bit);

		bits_.swap(new_bits);
		width_ = bits_.size();
	}

	check();
}

void RTLIL::SigSpec::remove(int offset, int length)
{
	cover("kernel.rtlil.sigspec.remove_pos");

	unpack();

	log_assert(offset >= 0);
	log_assert(length >= 0);
	log_assert(offset + length <= width_);

	bits_.erase(bits_.begin() + offset, bits_.begin() + offset + length);
	width_ = bits_.size();

	check();
}

RTLIL::SigSpec RTLIL::SigSpec::extract(int offset, int length) const
{
	unpack();
	cover("kernel.rtlil.sigspec.extract_pos");
	return std::vector<RTLIL::SigBit>(bits_.begin() + offset, bits_.begin() + offset + length);
}

void RTLIL::SigSpec::append(const RTLIL::SigSpec &signal)
{
	if (signal.width_ == 0)
		return;

	if (width_ == 0) {
		*this = signal;
		return;
	}

	cover("kernel.rtlil.sigspec.append");

	if (packed() != signal.packed()) {
		pack();
		signal.pack();
	}

	if (packed())
		for (auto &other_c : signal.chunks_)
		{
			auto &my_last_c = chunks_.back();
			if (my_last_c.wire == NULL && other_c.wire == NULL) {
				auto &this_data = my_last_c.data.bits;
				auto &other_data = other_c.data.bits;
				this_data.insert(this_data.end(), other_data.begin(), other_data.end());
				my_last_c.width += other_c.width;
			} else
			if (my_last_c.wire == other_c.wire && my_last_c.offset + my_last_c.width == other_c.offset) {
				my_last_c.width += other_c.width;
			} else
				chunks_.push_back(other_c);
		}
	else
		bits_.insert(bits_.end(), signal.bits_.begin(), signal.bits_.end());

	width_ += signal.width_;
	check();
}

void RTLIL::SigSpec::append_bit(const RTLIL::SigBit &bit)
{
	if (packed())
	{
		cover("kernel.rtlil.sigspec.append_bit.packed");

		if (chunks_.size() == 0)
			chunks_.push_back(bit);
		else
			if (bit.wire == NULL)
				if (chunks_.back().wire == NULL) {
					chunks_.back().data.bits.push_back(bit.data);
					chunks_.back().width++;
				} else
					chunks_.push_back(bit);
			else
				if (chunks_.back().wire == bit.wire && chunks_.back().offset + chunks_.back().width == bit.offset)
					chunks_.back().width++;
				else
					chunks_.push_back(bit);
	}
	else
	{
		cover("kernel.rtlil.sigspec.append_bit.unpacked");
		bits_.push_back(bit);
	}

	width_++;
	check();
}

void RTLIL::SigSpec::extend(int width, bool is_signed)
{
	cover("kernel.rtlil.sigspec.extend");

	pack();

	if (width_ > width)
		remove(width, width_ - width);
	
	if (width_ < width) {
		RTLIL::SigSpec padding = width_ > 0 ? extract(width_ - 1, 1) : RTLIL::SigSpec(RTLIL::State::S0);
		if (!is_signed && padding != RTLIL::SigSpec(RTLIL::State::Sx) && padding != RTLIL::SigSpec(RTLIL::State::Sz) &&
				padding != RTLIL::SigSpec(RTLIL::State::Sa) && padding != RTLIL::SigSpec(RTLIL::State::Sm))
			padding = RTLIL::SigSpec(RTLIL::State::S0);
		while (width_ < width)
			append(padding);
	}
}

void RTLIL::SigSpec::extend_u0(int width, bool is_signed)
{
	cover("kernel.rtlil.sigspec.extend_u0");

	pack();

	if (width_ > width)
		remove(width, width_ - width);
	
	if (width_ < width) {
		RTLIL::SigSpec padding = width_ > 0 ? extract(width_ - 1, 1) : RTLIL::SigSpec(RTLIL::State::S0);
		if (!is_signed)
			padding = RTLIL::SigSpec(RTLIL::State::S0);
		while (width_ < width)
			append(padding);
	}

}

RTLIL::SigSpec RTLIL::SigSpec::repeat(int num) const
{
	cover("kernel.rtlil.sigspec.repeat");

	RTLIL::SigSpec sig;
	for (int i = 0; i < num; i++)
		sig.append(*this);
	return sig;
}

#ifndef NDEBUG
void RTLIL::SigSpec::check() const
{
	if (width_ > 64)
	{
		cover("kernel.rtlil.sigspec.check.skip");
	}
	else if (packed())
	{
		cover("kernel.rtlil.sigspec.check.packed");

		int w = 0;
		for (size_t i = 0; i < chunks_.size(); i++) {
			const RTLIL::SigChunk chunk = chunks_[i];
			if (chunk.wire == NULL) {
				if (i > 0)
					log_assert(chunks_[i-1].wire != NULL);
				log_assert(chunk.offset == 0);
				log_assert(chunk.data.bits.size() == (size_t)chunk.width);
			} else {
				if (i > 0 && chunks_[i-1].wire == chunk.wire)
					log_assert(chunk.offset != chunks_[i-1].offset + chunks_[i-1].width);
				log_assert(chunk.offset >= 0);
				log_assert(chunk.width >= 0);
				log_assert(chunk.offset + chunk.width <= chunk.wire->width);
				log_assert(chunk.data.bits.size() == 0);
			}
			w += chunk.width;
		}
		log_assert(w == width_);
		log_assert(bits_.empty());
	}
	else
	{
		cover("kernel.rtlil.sigspec.check.unpacked");

		log_assert(width_ == SIZE(bits_));
		log_assert(chunks_.empty());
	}
}
#endif

bool RTLIL::SigSpec::operator <(const RTLIL::SigSpec &other) const
{
	cover("kernel.rtlil.sigspec.comp_lt");

	if (this == &other)
		return false;

	if (width_ != other.width_)
		return width_ < other.width_;

	pack();
	other.pack();

	if (chunks_.size() != other.chunks_.size())
		return chunks_.size() < other.chunks_.size();

	hash();
	other.hash();

	if (hash_ != other.hash_)
		return hash_ < other.hash_;

	for (size_t i = 0; i < chunks_.size(); i++)
		if (chunks_[i] != other.chunks_[i]) {
			cover("kernel.rtlil.sigspec.comp_lt.hash_collision");
			return chunks_[i] < other.chunks_[i];
		}

	cover("kernel.rtlil.sigspec.comp_lt.equal");
	return false;
}

bool RTLIL::SigSpec::operator ==(const RTLIL::SigSpec &other) const
{
	cover("kernel.rtlil.sigspec.comp_eq");

	if (this == &other)
		return true;

	if (width_ != other.width_)
		return false;

	pack();
	other.pack();

	if (chunks_.size() != chunks_.size())
		return false;

	hash();
	other.hash();

	if (hash_ != other.hash_)
		return false;

	for (size_t i = 0; i < chunks_.size(); i++)
		if (chunks_[i] != other.chunks_[i]) {
			cover("kernel.rtlil.sigspec.comp_eq.hash_collision");
			return false;
		}

	cover("kernel.rtlil.sigspec.comp_eq.equal");
	return true;
}

bool RTLIL::SigSpec::is_wire() const
{
	cover("kernel.rtlil.sigspec.is_wire");

	pack();
	return SIZE(chunks_) == 1 && chunks_[0].wire && chunks_[0].wire->width == width_;
}

bool RTLIL::SigSpec::is_chunk() const
{
	cover("kernel.rtlil.sigspec.is_chunk");

	pack();
	return SIZE(chunks_) == 1;
}

bool RTLIL::SigSpec::is_fully_const() const
{
	cover("kernel.rtlil.sigspec.is_fully_const");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++)
		if (it->width > 0 && it->wire != NULL)
			return false;
	return true;
}

bool RTLIL::SigSpec::is_fully_def() const
{
	cover("kernel.rtlil.sigspec.is_fully_def");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
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
	cover("kernel.rtlil.sigspec.is_fully_undef");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
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
	cover("kernel.rtlil.sigspec.has_marked_bits");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++)
		if (it->width > 0 && it->wire == NULL) {
			for (size_t i = 0; i < it->data.bits.size(); i++)
				if (it->data.bits[i] == RTLIL::State::Sm)
					return true;
		}
	return false;
}

bool RTLIL::SigSpec::as_bool() const
{
	cover("kernel.rtlil.sigspec.as_bool");

	pack();
	log_assert(is_fully_const() && SIZE(chunks_) <= 1);
	if (width_)
		return chunks_[0].data.as_bool();
	return false;
}

int RTLIL::SigSpec::as_int() const
{
	cover("kernel.rtlil.sigspec.as_int");

	pack();
	log_assert(is_fully_const() && SIZE(chunks_) <= 1);
	if (width_)
		return chunks_[0].data.as_int();
	return 0;
}

std::string RTLIL::SigSpec::as_string() const
{
	cover("kernel.rtlil.sigspec.as_string");

	pack();
	std::string str;
	for (size_t i = chunks_.size(); i > 0; i--) {
		const RTLIL::SigChunk &chunk = chunks_[i-1];
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
	cover("kernel.rtlil.sigspec.as_const");

	pack();
	log_assert(is_fully_const() && SIZE(chunks_) <= 1);
	if (width_)
		return chunks_[0].data;
	return RTLIL::Const();
}

RTLIL::Wire *RTLIL::SigSpec::as_wire() const
{
	cover("kernel.rtlil.sigspec.as_wire");

	pack();
	log_assert(is_wire());
	return chunks_[0].wire;
}

RTLIL::SigChunk RTLIL::SigSpec::as_chunk() const
{
	cover("kernel.rtlil.sigspec.as_chunk");

	pack();
	log_assert(is_chunk());
	return chunks_[0];
}

bool RTLIL::SigSpec::match(std::string pattern) const
{
	cover("kernel.rtlil.sigspec.match");

	pack();
	std::string str = as_string();
	log_assert(pattern.size() == str.size());

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
	cover("kernel.rtlil.sigspec.to_sigbit_set");

	pack();
	std::set<RTLIL::SigBit> sigbits;
	for (auto &c : chunks_)
		for (int i = 0; i < c.width; i++)
			sigbits.insert(RTLIL::SigBit(c, i));
	return sigbits;
}

std::vector<RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_vector() const
{
	cover("kernel.rtlil.sigspec.to_sigbit_vector");

	unpack();
	return bits_;
}

RTLIL::SigBit RTLIL::SigSpec::to_single_sigbit() const
{
	cover("kernel.rtlil.sigspec.to_single_sigbit");

	pack();
	log_assert(width_ == 1);
	for (auto &c : chunks_)
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
	cover("kernel.rtlil.sigspec.parse");

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
			cover("kernel.rtlil.sigspec.parse.const");
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

		cover("kernel.rtlil.sigspec.parse.net");

		if (netname[0] != '$' && netname[0] != '\\')
			netname = "\\" + netname;

		if (module->wires_.count(netname) == 0) {
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

		if (module->wires_.count(netname) == 0)
			return false;

		RTLIL::Wire *wire = module->wires_.at(netname);
		if (!indices.empty()) {
			std::vector<std::string> index_tokens;
			sigspec_parse_split(index_tokens, indices.substr(1, indices.size()-2), ':');
			if (index_tokens.size() == 1) {
				cover("kernel.rtlil.sigspec.parse.bit_sel");
				sig.append(RTLIL::SigSpec(wire, atoi(index_tokens.at(0).c_str())));
			} else {
				cover("kernel.rtlil.sigspec.parse.part_sel");
				int a = atoi(index_tokens.at(0).c_str());
				int b = atoi(index_tokens.at(1).c_str());
				if (a > b) {
					int tmp = a;
					a = b, b = tmp;
				}
				sig.append(RTLIL::SigSpec(wire, a, b-a+1));
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

	cover("kernel.rtlil.sigspec.parse.sel");

	str = RTLIL::escape_id(str.substr(1));
	if (design->selection_vars.count(str) == 0)
		return false;

	sig = RTLIL::SigSpec();
	RTLIL::Selection &sel = design->selection_vars.at(str);
	for (auto &it : module->wires_)
		if (sel.selected_member(module->name, it.first))
			sig.append(it.second);

	return true;
}

bool RTLIL::SigSpec::parse_rhs(const RTLIL::SigSpec &lhs, RTLIL::SigSpec &sig, RTLIL::Module *module, std::string str)
{
	if (str == "0") {
		cover("kernel.rtlil.sigspec.parse.rhs_zeros");
		sig = RTLIL::SigSpec(RTLIL::State::S0, lhs.width_);
		return true;
	}

	if (str == "~0") {
		cover("kernel.rtlil.sigspec.parse.rhs_ones");
		sig = RTLIL::SigSpec(RTLIL::State::S1, lhs.width_);
		return true;
	}

	if (lhs.chunks_.size() == 1) {
		char *p = (char*)str.c_str(), *endptr;
		long long int val = strtoll(p, &endptr, 10);
		if (endptr && endptr != p && *endptr == 0) {
			sig = RTLIL::SigSpec(val, lhs.width_);
			cover("kernel.rtlil.sigspec.parse.rhs_dec");
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

RTLIL::SwitchRule *RTLIL::SwitchRule::clone() const
{
	RTLIL::SwitchRule *new_switchrule = new RTLIL::SwitchRule;
	new_switchrule->signal = signal;
	new_switchrule->attributes = attributes;
	for (auto &it : cases)
		new_switchrule->cases.push_back(it->clone());
	return new_switchrule;
	
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

YOSYS_NAMESPACE_END

