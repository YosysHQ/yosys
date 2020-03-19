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
#include "kernel/macc.h"
#include "kernel/celltypes.h"
#include "frontends/verilog/verilog_frontend.h"
#include "backends/ilang/ilang_backend.h"

#include <string.h>
#include <algorithm>

YOSYS_NAMESPACE_BEGIN

RTLIL::IdString::destruct_guard_t RTLIL::IdString::destruct_guard;
std::vector<char*> RTLIL::IdString::global_id_storage_;
dict<char*, int, hash_cstr_ops> RTLIL::IdString::global_id_index_;
#ifndef YOSYS_NO_IDS_REFCNT
std::vector<int> RTLIL::IdString::global_refcount_storage_;
std::vector<int> RTLIL::IdString::global_free_idx_list_;
#endif
#ifdef YOSYS_USE_STICKY_IDS
int RTLIL::IdString::last_created_idx_[8];
int RTLIL::IdString::last_created_idx_ptr_;
#endif

IdString RTLIL::ID::A;
IdString RTLIL::ID::B;
IdString RTLIL::ID::Y;
IdString RTLIL::ID::keep;
IdString RTLIL::ID::whitebox;
IdString RTLIL::ID::blackbox;
dict<std::string, std::string> RTLIL::constpad;

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
			bits.push_back((ch & 1) != 0 ? State::S1 : State::S0);
			ch = ch >> 1;
		}
	}
}

RTLIL::Const::Const(int val, int width)
{
	flags = RTLIL::CONST_FLAG_NONE;
	for (int i = 0; i < width; i++) {
		bits.push_back((val & 1) != 0 ? State::S1 : State::S0);
		val = val >> 1;
	}
}

RTLIL::Const::Const(RTLIL::State bit, int width)
{
	flags = RTLIL::CONST_FLAG_NONE;
	for (int i = 0; i < width; i++)
		bits.push_back(bit);
}

RTLIL::Const::Const(const std::vector<bool> &bits)
{
	flags = RTLIL::CONST_FLAG_NONE;
	for (auto b : bits)
		this->bits.push_back(b ? State::S1 : State::S0);
}

RTLIL::Const::Const(const RTLIL::Const &c)
{
	flags = c.flags;
	for (auto b : c.bits)
		this->bits.push_back(b);
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
		if (bits[i] == State::S1)
			return true;
	return false;
}

int RTLIL::Const::as_int(bool is_signed) const
{
	int32_t ret = 0;
	for (size_t i = 0; i < bits.size() && i < 32; i++)
		if (bits[i] == State::S1)
			ret |= 1 << i;
	if (is_signed && bits.back() == State::S1)
		for (size_t i = bits.size(); i < 32; i++)
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

RTLIL::Const RTLIL::Const::from_string(std::string str)
{
	Const c;
	for (auto it = str.rbegin(); it != str.rend(); it++)
		switch (*it) {
			case '0': c.bits.push_back(State::S0); break;
			case '1': c.bits.push_back(State::S1); break;
			case 'x': c.bits.push_back(State::Sx); break;
			case 'z': c.bits.push_back(State::Sz); break;
			case 'm': c.bits.push_back(State::Sm); break;
			default: c.bits.push_back(State::Sa);
		}
	return c;
}

std::string RTLIL::Const::decode_string() const
{
	std::string string;
	std::vector<char> string_chars;
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

bool RTLIL::Const::is_fully_zero() const
{
	cover("kernel.rtlil.const.is_fully_zero");

	for (auto bit : bits)
		if (bit != RTLIL::State::S0)
			return false;

	return true;
}

bool RTLIL::Const::is_fully_ones() const
{
	cover("kernel.rtlil.const.is_fully_ones");

	for (auto bit : bits)
		if (bit != RTLIL::State::S1)
			return false;

	return true;
}

bool RTLIL::Const::is_fully_def() const
{
	cover("kernel.rtlil.const.is_fully_def");

	for (auto bit : bits)
		if (bit != RTLIL::State::S0 && bit != RTLIL::State::S1)
			return false;

	return true;
}

bool RTLIL::Const::is_fully_undef() const
{
	cover("kernel.rtlil.const.is_fully_undef");

	for (auto bit : bits)
		if (bit != RTLIL::State::Sx && bit != RTLIL::State::Sz)
			return false;

	return true;
}

void RTLIL::AttrObject::set_bool_attribute(RTLIL::IdString id, bool value)
{
	if (value)
		attributes[id] = RTLIL::Const(1);
	else {
                const auto it = attributes.find(id);
                if (it != attributes.end())
			attributes.erase(it);
	}
}

bool RTLIL::AttrObject::get_bool_attribute(RTLIL::IdString id) const
{
	const auto it = attributes.find(id);
	if (it == attributes.end())
		return false;
	return it->second.as_bool();
}

void RTLIL::AttrObject::set_strpool_attribute(RTLIL::IdString id, const pool<string> &data)
{
	string attrval;
	for (auto &s : data) {
		if (!attrval.empty())
			attrval += "|";
		attrval += s;
	}
	attributes[id] = RTLIL::Const(attrval);
}

void RTLIL::AttrObject::add_strpool_attribute(RTLIL::IdString id, const pool<string> &data)
{
	pool<string> union_data = get_strpool_attribute(id);
	union_data.insert(data.begin(), data.end());
	if (!union_data.empty())
		set_strpool_attribute(id, union_data);
}

pool<string> RTLIL::AttrObject::get_strpool_attribute(RTLIL::IdString id) const
{
	pool<string> data;
	if (attributes.count(id) != 0)
		for (auto s : split_tokens(attributes.at(id).decode_string(), "|"))
			data.insert(s);
	return data;
}

void RTLIL::AttrObject::set_src_attribute(const std::string &src)
{
	if (src.empty())
		attributes.erase(ID(src));
	else
		attributes[ID(src)] = src;
}

std::string RTLIL::AttrObject::get_src_attribute() const
{
	std::string src;
	if (attributes.count(ID(src)))
		src = attributes.at(ID(src)).decode_string();
	return src;
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
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	refcount_modules_ = 0;
	selection_stack.push_back(RTLIL::Selection());

#ifdef WITH_PYTHON
	RTLIL::Design::get_all_designs()->insert(std::pair<unsigned int, RTLIL::Design*>(hashidx_, this));
#endif
}

RTLIL::Design::~Design()
{
	for (auto it = modules_.begin(); it != modules_.end(); ++it)
		delete it->second;
	for (auto n : verilog_packages)
		delete n;
	for (auto n : verilog_globals)
		delete n;
#ifdef WITH_PYTHON
	RTLIL::Design::get_all_designs()->erase(hashidx_);
#endif
}

#ifdef WITH_PYTHON
static std::map<unsigned int, RTLIL::Design*> all_designs;
std::map<unsigned int, RTLIL::Design*> *RTLIL::Design::get_all_designs(void)
{
	return &all_designs;
}
#endif

RTLIL::ObjRange<RTLIL::Module*> RTLIL::Design::modules()
{
	return RTLIL::ObjRange<RTLIL::Module*>(&modules_, &refcount_modules_);
}

RTLIL::Module *RTLIL::Design::module(RTLIL::IdString name)
{
	return modules_.count(name) ? modules_.at(name) : NULL;
}

RTLIL::Module *RTLIL::Design::top_module()
{
	RTLIL::Module *module = nullptr;
	int module_count = 0;

	for (auto mod : selected_modules()) {
		if (mod->get_bool_attribute(ID(top)))
			return mod;
		module_count++;
		module = mod;
	}

	return module_count == 1 ? module : nullptr;
}

void RTLIL::Design::add(RTLIL::Module *module)
{
	log_assert(modules_.count(module->name) == 0);
	log_assert(refcount_modules_ == 0);
	modules_[module->name] = module;
	module->design = this;

	for (auto mon : monitors)
		mon->notify_module_add(module);

	if (yosys_xtrace) {
		log("#X# New Module: %s\n", log_id(module));
		log_backtrace("-X- ", yosys_xtrace-1);
	}
}

RTLIL::Module *RTLIL::Design::addModule(RTLIL::IdString name)
{
	log_assert(modules_.count(name) == 0);
	log_assert(refcount_modules_ == 0);

	RTLIL::Module *module = new RTLIL::Module;
	modules_[name] = module;
	module->design = this;
	module->name = name;

	for (auto mon : monitors)
		mon->notify_module_add(module);

	if (yosys_xtrace) {
		log("#X# New Module: %s\n", log_id(module));
		log_backtrace("-X- ", yosys_xtrace-1);
	}

	return module;
}

void RTLIL::Design::scratchpad_unset(std::string varname)
{
	scratchpad.erase(varname);
}

void RTLIL::Design::scratchpad_set_int(std::string varname, int value)
{
	scratchpad[varname] = stringf("%d", value);
}

void RTLIL::Design::scratchpad_set_bool(std::string varname, bool value)
{
	scratchpad[varname] = value ? "true" : "false";
}

void RTLIL::Design::scratchpad_set_string(std::string varname, std::string value)
{
	scratchpad[varname] = value;
}

int RTLIL::Design::scratchpad_get_int(std::string varname, int default_value) const
{
	if (scratchpad.count(varname) == 0)
		return default_value;

	std::string str = scratchpad.at(varname);

	if (str == "0" || str == "false")
		return 0;

	if (str == "1" || str == "true")
		return 1;

	char *endptr = nullptr;
	long int parsed_value = strtol(str.c_str(), &endptr, 10);
	return *endptr ? default_value : parsed_value;
}

bool RTLIL::Design::scratchpad_get_bool(std::string varname, bool default_value) const
{
	if (scratchpad.count(varname) == 0)
		return default_value;

	std::string str = scratchpad.at(varname);

	if (str == "0" || str == "false")
		return false;

	if (str == "1" || str == "true")
		return true;

	return default_value;
}

std::string RTLIL::Design::scratchpad_get_string(std::string varname, std::string default_value) const
{
	if (scratchpad.count(varname) == 0)
		return default_value;
	return scratchpad.at(varname);
}

void RTLIL::Design::remove(RTLIL::Module *module)
{
	for (auto mon : monitors)
		mon->notify_module_del(module);

	if (yosys_xtrace) {
		log("#X# Remove Module: %s\n", log_id(module));
		log_backtrace("-X- ", yosys_xtrace-1);
	}

	log_assert(modules_.at(module->name) == module);
	modules_.erase(module->name);
	delete module;
}

void RTLIL::Design::rename(RTLIL::Module *module, RTLIL::IdString new_name)
{
	modules_.erase(module->name);
	module->name = new_name;
	add(module);
}

void RTLIL::Design::sort()
{
	scratchpad.sort();
	modules_.sort(sort_by_id_str());
	for (auto &it : modules_)
		it.second->sort();
}

void RTLIL::Design::check()
{
#ifndef NDEBUG
	for (auto &it : modules_) {
		log_assert(this == it.second->design);
		log_assert(it.first == it.second->name);
		log_assert(!it.first.empty());
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
		if (selected_module(it.first) && !it.second->get_blackbox_attribute())
			result.push_back(it.second);
	return result;
}

std::vector<RTLIL::Module*> RTLIL::Design::selected_whole_modules() const
{
	std::vector<RTLIL::Module*> result;
	result.reserve(modules_.size());
	for (auto &it : modules_)
		if (selected_whole_module(it.first) && !it.second->get_blackbox_attribute())
			result.push_back(it.second);
	return result;
}

std::vector<RTLIL::Module*> RTLIL::Design::selected_whole_modules_warn() const
{
	std::vector<RTLIL::Module*> result;
	result.reserve(modules_.size());
	for (auto &it : modules_)
		if (it.second->get_blackbox_attribute())
			continue;
		else if (selected_whole_module(it.first))
			result.push_back(it.second);
		else if (selected_module(it.first))
			log_warning("Ignoring partially selected module %s.\n", log_id(it.first));
	return result;
}

RTLIL::Module::Module()
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	design = nullptr;
	refcount_wires_ = 0;
	refcount_cells_ = 0;

#ifdef WITH_PYTHON
	RTLIL::Module::get_all_modules()->insert(std::pair<unsigned int, RTLIL::Module*>(hashidx_, this));
#endif
}

RTLIL::Module::~Module()
{
	for (auto it = wires_.begin(); it != wires_.end(); ++it)
		delete it->second;
	for (auto it = memories.begin(); it != memories.end(); ++it)
		delete it->second;
	for (auto it = cells_.begin(); it != cells_.end(); ++it)
		delete it->second;
	for (auto it = processes.begin(); it != processes.end(); ++it)
		delete it->second;
#ifdef WITH_PYTHON
	RTLIL::Module::get_all_modules()->erase(hashidx_);
#endif
}

#ifdef WITH_PYTHON
static std::map<unsigned int, RTLIL::Module*> all_modules;
std::map<unsigned int, RTLIL::Module*> *RTLIL::Module::get_all_modules(void)
{
	return &all_modules;
}
#endif

void RTLIL::Module::makeblackbox()
{
	pool<RTLIL::Wire*> delwires;

	for (auto it = wires_.begin(); it != wires_.end(); ++it)
		if (!it->second->port_input && !it->second->port_output)
			delwires.insert(it->second);

	for (auto it = memories.begin(); it != memories.end(); ++it)
		delete it->second;
	memories.clear();

	for (auto it = cells_.begin(); it != cells_.end(); ++it)
		delete it->second;
	cells_.clear();

	for (auto it = processes.begin(); it != processes.end(); ++it)
		delete it->second;
	processes.clear();

	remove(delwires);
	set_bool_attribute(ID::blackbox);
}

void RTLIL::Module::reprocess_module(RTLIL::Design *, dict<RTLIL::IdString, RTLIL::Module *>)
{
	log_error("Cannot reprocess_module module `%s' !\n", id2cstr(name));
}

RTLIL::IdString RTLIL::Module::derive(RTLIL::Design*, dict<RTLIL::IdString, RTLIL::Const>, bool mayfail)
{
	if (mayfail)
		return RTLIL::IdString();
	log_error("Module `%s' is used with parameters but is not parametric!\n", id2cstr(name));
}


RTLIL::IdString RTLIL::Module::derive(RTLIL::Design*, dict<RTLIL::IdString, RTLIL::Const>, dict<RTLIL::IdString, RTLIL::Module*>, dict<RTLIL::IdString, RTLIL::IdString>, bool mayfail)
{
	if (mayfail)
		return RTLIL::IdString();
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
		pool<RTLIL::IdString> expected_params, expected_ports;

		InternalCellChecker(RTLIL::Module *module, RTLIL::Cell *cell) : module(module), cell(cell) { }

		void error(int linenr)
		{
			std::stringstream buf;
			ILANG_BACKEND::dump_cell(buf, "  ", cell);

			log_error("Found error in internal cell %s%s%s (%s) at %s:%d:\n%s",
					module ? module->name.c_str() : "", module ? "." : "",
					cell->name.c_str(), cell->type.c_str(), __FILE__, linenr, buf.str().c_str());
		}

		int param(RTLIL::IdString name)
		{
			if (cell->parameters.count(name) == 0)
				error(__LINE__);
			expected_params.insert(name);
			return cell->parameters.at(name).as_int();
		}

		int param_bool(RTLIL::IdString name)
		{
			int v = param(name);
			if (cell->parameters.at(name).bits.size() > 32)
				error(__LINE__);
			if (v != 0 && v != 1)
				error(__LINE__);
			return v;
		}

		int param_bool(RTLIL::IdString name, bool expected)
		{
			int v = param_bool(name);
			if (v != expected)
				error(__LINE__);
			return v;
		}

		void param_bits(RTLIL::IdString name, int width)
		{
			param(name);
			if (int(cell->parameters.at(name).bits.size()) != width)
				error(__LINE__);
		}

		void port(RTLIL::IdString name, int width)
		{
			if (!cell->hasPort(name))
				error(__LINE__);
			if (cell->getPort(name).size() != width)
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

			if (expected_params.count(ID(A_SIGNED)) != 0 && expected_params.count(ID(B_SIGNED)) && check_matched_sign) {
				bool a_is_signed = param(ID(A_SIGNED)) != 0;
				bool b_is_signed = param(ID(B_SIGNED)) != 0;
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
				if (!cell->hasPort(portname))
					error(__LINE__);
				if (cell->getPort(portname).size() != 1)
					error(__LINE__);
			}

			for (auto &conn : cell->connections()) {
				if (conn.first.size() != 2 || conn.first[0] != '\\')
					error(__LINE__);
				if (strchr(ports, conn.first[1]) == NULL)
					error(__LINE__);
			}
		}

		void check()
		{
			if (!cell->type.begins_with("$") || cell->type.begins_with("$__") || cell->type.begins_with("$paramod") || cell->type.begins_with("$fmcombine") ||
					cell->type.begins_with("$verific$") || cell->type.begins_with("$array:") || cell->type.begins_with("$extern:"))
				return;

			if (cell->type.in(ID($not), ID($pos), ID($neg))) {
				param_bool(ID(A_SIGNED));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected();
				return;
			}

			if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
				param_bool(ID(A_SIGNED));
				param_bool(ID(B_SIGNED));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::B, param(ID(B_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected();
				return;
			}

			if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool))) {
				param_bool(ID(A_SIGNED));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected();
				return;
			}

			if (cell->type.in(ID($shl), ID($shr), ID($sshl), ID($sshr))) {
				param_bool(ID(A_SIGNED));
				param_bool(ID(B_SIGNED), /*expected=*/false);
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::B, param(ID(B_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected(/*check_matched_sign=*/false);
				return;
			}

			if (cell->type.in(ID($shift), ID($shiftx))) {
				param_bool(ID(A_SIGNED));
				param_bool(ID(B_SIGNED));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::B, param(ID(B_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected(/*check_matched_sign=*/false);
				return;
			}

			if (cell->type.in(ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt))) {
				param_bool(ID(A_SIGNED));
				param_bool(ID(B_SIGNED));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::B, param(ID(B_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected();
				return;
			}

			if (cell->type.in(ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($pow))) {
				param_bool(ID(A_SIGNED));
				param_bool(ID(B_SIGNED));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::B, param(ID(B_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected(cell->type != ID($pow));
				return;
			}

			if (cell->type == ID($fa)) {
				port(ID::A, param(ID(WIDTH)));
				port(ID::B, param(ID(WIDTH)));
				port(ID(C), param(ID(WIDTH)));
				port(ID(X), param(ID(WIDTH)));
				port(ID::Y, param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($lcu)) {
				port(ID(P), param(ID(WIDTH)));
				port(ID(G), param(ID(WIDTH)));
				port(ID(CI), 1);
				port(ID(CO), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($alu)) {
				param_bool(ID(A_SIGNED));
				param_bool(ID(B_SIGNED));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::B, param(ID(B_WIDTH)));
				port(ID(CI), 1);
				port(ID(BI), 1);
				port(ID(X), param(ID(Y_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				port(ID(CO), param(ID(Y_WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($macc)) {
				param(ID(CONFIG));
				param(ID(CONFIG_WIDTH));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::B, param(ID(B_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected();
				Macc().from_cell(cell);
				return;
			}

			if (cell->type == ID($logic_not)) {
				param_bool(ID(A_SIGNED));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected();
				return;
			}

			if (cell->type.in(ID($logic_and), ID($logic_or))) {
				param_bool(ID(A_SIGNED));
				param_bool(ID(B_SIGNED));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::B, param(ID(B_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				check_expected(/*check_matched_sign=*/false);
				return;
			}

			if (cell->type == ID($slice)) {
				param(ID(OFFSET));
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::Y, param(ID(Y_WIDTH)));
				if (param(ID(OFFSET)) + param(ID(Y_WIDTH)) > param(ID(A_WIDTH)))
					error(__LINE__);
				check_expected();
				return;
			}

			if (cell->type == ID($concat)) {
				port(ID::A, param(ID(A_WIDTH)));
				port(ID::B, param(ID(B_WIDTH)));
				port(ID::Y, param(ID(A_WIDTH)) + param(ID(B_WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($mux)) {
				port(ID::A, param(ID(WIDTH)));
				port(ID::B, param(ID(WIDTH)));
				port(ID(S), 1);
				port(ID::Y, param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($pmux)) {
				port(ID::A, param(ID(WIDTH)));
				port(ID::B, param(ID(WIDTH)) * param(ID(S_WIDTH)));
				port(ID(S), param(ID(S_WIDTH)));
				port(ID::Y, param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($lut)) {
				param(ID(LUT));
				port(ID::A, param(ID(WIDTH)));
				port(ID::Y, 1);
				check_expected();
				return;
			}

			if (cell->type == ID($sop)) {
				param(ID(DEPTH));
				param(ID(TABLE));
				port(ID::A, param(ID(WIDTH)));
				port(ID::Y, 1);
				check_expected();
				return;
			}

			if (cell->type == ID($sr)) {
				param_bool(ID(SET_POLARITY));
				param_bool(ID(CLR_POLARITY));
				port(ID(SET), param(ID(WIDTH)));
				port(ID(CLR), param(ID(WIDTH)));
				port(ID(Q),   param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($ff)) {
				port(ID(D), param(ID(WIDTH)));
				port(ID(Q), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($dff)) {
				param_bool(ID(CLK_POLARITY));
				port(ID(CLK), 1);
				port(ID(D), param(ID(WIDTH)));
				port(ID(Q), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($dffe)) {
				param_bool(ID(CLK_POLARITY));
				param_bool(ID(EN_POLARITY));
				port(ID(CLK), 1);
				port(ID(EN), 1);
				port(ID(D), param(ID(WIDTH)));
				port(ID(Q), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($dffsr)) {
				param_bool(ID(CLK_POLARITY));
				param_bool(ID(SET_POLARITY));
				param_bool(ID(CLR_POLARITY));
				port(ID(CLK), 1);
				port(ID(SET), param(ID(WIDTH)));
				port(ID(CLR), param(ID(WIDTH)));
				port(ID(D), param(ID(WIDTH)));
				port(ID(Q), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($adff)) {
				param_bool(ID(CLK_POLARITY));
				param_bool(ID(ARST_POLARITY));
				param_bits(ID(ARST_VALUE), param(ID(WIDTH)));
				port(ID(CLK), 1);
				port(ID(ARST), 1);
				port(ID(D), param(ID(WIDTH)));
				port(ID(Q), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($dlatch)) {
				param_bool(ID(EN_POLARITY));
				port(ID(EN), 1);
				port(ID(D), param(ID(WIDTH)));
				port(ID(Q), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($dlatchsr)) {
				param_bool(ID(EN_POLARITY));
				param_bool(ID(SET_POLARITY));
				param_bool(ID(CLR_POLARITY));
				port(ID(EN), 1);
				port(ID(SET), param(ID(WIDTH)));
				port(ID(CLR), param(ID(WIDTH)));
				port(ID(D), param(ID(WIDTH)));
				port(ID(Q), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($fsm)) {
				param(ID(NAME));
				param_bool(ID(CLK_POLARITY));
				param_bool(ID(ARST_POLARITY));
				param(ID(STATE_BITS));
				param(ID(STATE_NUM));
				param(ID(STATE_NUM_LOG2));
				param(ID(STATE_RST));
				param_bits(ID(STATE_TABLE), param(ID(STATE_BITS)) * param(ID(STATE_NUM)));
				param(ID(TRANS_NUM));
				param_bits(ID(TRANS_TABLE), param(ID(TRANS_NUM)) * (2*param(ID(STATE_NUM_LOG2)) + param(ID(CTRL_IN_WIDTH)) + param(ID(CTRL_OUT_WIDTH))));
				port(ID(CLK), 1);
				port(ID(ARST), 1);
				port(ID(CTRL_IN), param(ID(CTRL_IN_WIDTH)));
				port(ID(CTRL_OUT), param(ID(CTRL_OUT_WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($memrd)) {
				param(ID(MEMID));
				param_bool(ID(CLK_ENABLE));
				param_bool(ID(CLK_POLARITY));
				param_bool(ID(TRANSPARENT));
				port(ID(CLK), 1);
				port(ID(EN), 1);
				port(ID(ADDR), param(ID(ABITS)));
				port(ID(DATA), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($memwr)) {
				param(ID(MEMID));
				param_bool(ID(CLK_ENABLE));
				param_bool(ID(CLK_POLARITY));
				param(ID(PRIORITY));
				port(ID(CLK), 1);
				port(ID(EN), param(ID(WIDTH)));
				port(ID(ADDR), param(ID(ABITS)));
				port(ID(DATA), param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($meminit)) {
				param(ID(MEMID));
				param(ID(PRIORITY));
				port(ID(ADDR), param(ID(ABITS)));
				port(ID(DATA), param(ID(WIDTH)) * param(ID(WORDS)));
				check_expected();
				return;
			}

			if (cell->type == ID($mem)) {
				param(ID(MEMID));
				param(ID(SIZE));
				param(ID(OFFSET));
				param(ID(INIT));
				param_bits(ID(RD_CLK_ENABLE), max(1, param(ID(RD_PORTS))));
				param_bits(ID(RD_CLK_POLARITY), max(1, param(ID(RD_PORTS))));
				param_bits(ID(RD_TRANSPARENT), max(1, param(ID(RD_PORTS))));
				param_bits(ID(WR_CLK_ENABLE), max(1, param(ID(WR_PORTS))));
				param_bits(ID(WR_CLK_POLARITY), max(1, param(ID(WR_PORTS))));
				port(ID(RD_CLK), param(ID(RD_PORTS)));
				port(ID(RD_EN), param(ID(RD_PORTS)));
				port(ID(RD_ADDR), param(ID(RD_PORTS)) * param(ID(ABITS)));
				port(ID(RD_DATA), param(ID(RD_PORTS)) * param(ID(WIDTH)));
				port(ID(WR_CLK), param(ID(WR_PORTS)));
				port(ID(WR_EN), param(ID(WR_PORTS)) * param(ID(WIDTH)));
				port(ID(WR_ADDR), param(ID(WR_PORTS)) * param(ID(ABITS)));
				port(ID(WR_DATA), param(ID(WR_PORTS)) * param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($tribuf)) {
				port(ID::A, param(ID(WIDTH)));
				port(ID::Y, param(ID(WIDTH)));
				port(ID(EN), 1);
				check_expected();
				return;
			}

			if (cell->type.in(ID($assert), ID($assume), ID($live), ID($fair), ID($cover))) {
				port(ID::A, 1);
				port(ID(EN), 1);
				check_expected();
				return;
			}

			if (cell->type == ID($initstate)) {
				port(ID::Y, 1);
				check_expected();
				return;
			}

			if (cell->type.in(ID($anyconst), ID($anyseq), ID($allconst), ID($allseq))) {
				port(ID::Y, param(ID(WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($equiv)) {
				port(ID::A, 1);
				port(ID::B, 1);
				port(ID::Y, 1);
				check_expected();
				return;
			}

			if (cell->type.in(ID($specify2), ID($specify3))) {
				param_bool(ID(FULL));
				param_bool(ID(SRC_DST_PEN));
				param_bool(ID(SRC_DST_POL));
				param(ID(T_RISE_MIN));
				param(ID(T_RISE_TYP));
				param(ID(T_RISE_MAX));
				param(ID(T_FALL_MIN));
				param(ID(T_FALL_TYP));
				param(ID(T_FALL_MAX));
				port(ID(EN), 1);
				port(ID(SRC), param(ID(SRC_WIDTH)));
				port(ID(DST), param(ID(DST_WIDTH)));
				if (cell->type == ID($specify3)) {
					param_bool(ID(EDGE_EN));
					param_bool(ID(EDGE_POL));
					param_bool(ID(DAT_DST_PEN));
					param_bool(ID(DAT_DST_POL));
					port(ID(DAT), param(ID(DST_WIDTH)));
				}
				check_expected();
				return;
			}

			if (cell->type == ID($specrule)) {
				param(ID(TYPE));
				param_bool(ID(SRC_PEN));
				param_bool(ID(SRC_POL));
				param_bool(ID(DST_PEN));
				param_bool(ID(DST_POL));
				param(ID(T_LIMIT_MIN));
				param(ID(T_LIMIT_TYP));
				param(ID(T_LIMIT_MAX));
				param(ID(T_LIMIT2_MIN));
				param(ID(T_LIMIT2_TYP));
				param(ID(T_LIMIT2_MAX));
				port(ID(SRC_EN), 1);
				port(ID(DST_EN), 1);
				port(ID(SRC), param(ID(SRC_WIDTH)));
				port(ID(DST), param(ID(DST_WIDTH)));
				check_expected();
				return;
			}

			if (cell->type == ID($_BUF_))    { check_gate("AY"); return; }
			if (cell->type == ID($_NOT_))    { check_gate("AY"); return; }
			if (cell->type == ID($_AND_))    { check_gate("ABY"); return; }
			if (cell->type == ID($_NAND_))   { check_gate("ABY"); return; }
			if (cell->type == ID($_OR_))     { check_gate("ABY"); return; }
			if (cell->type == ID($_NOR_))    { check_gate("ABY"); return; }
			if (cell->type == ID($_XOR_))    { check_gate("ABY"); return; }
			if (cell->type == ID($_XNOR_))   { check_gate("ABY"); return; }
			if (cell->type == ID($_ANDNOT_)) { check_gate("ABY"); return; }
			if (cell->type == ID($_ORNOT_))  { check_gate("ABY"); return; }
			if (cell->type == ID($_MUX_))    { check_gate("ABSY"); return; }
			if (cell->type == ID($_NMUX_))   { check_gate("ABSY"); return; }
			if (cell->type == ID($_AOI3_))   { check_gate("ABCY"); return; }
			if (cell->type == ID($_OAI3_))   { check_gate("ABCY"); return; }
			if (cell->type == ID($_AOI4_))   { check_gate("ABCDY"); return; }
			if (cell->type == ID($_OAI4_))   { check_gate("ABCDY"); return; }

			if (cell->type == ID($_TBUF_))  { check_gate("AYE"); return; }

			if (cell->type == ID($_MUX4_))  { check_gate("ABCDSTY"); return; }
			if (cell->type == ID($_MUX8_))  { check_gate("ABCDEFGHSTUY"); return; }
			if (cell->type == ID($_MUX16_)) { check_gate("ABCDEFGHIJKLMNOPSTUVY"); return; }

			if (cell->type == ID($_SR_NN_)) { check_gate("SRQ"); return; }
			if (cell->type == ID($_SR_NP_)) { check_gate("SRQ"); return; }
			if (cell->type == ID($_SR_PN_)) { check_gate("SRQ"); return; }
			if (cell->type == ID($_SR_PP_)) { check_gate("SRQ"); return; }

			if (cell->type == ID($_FF_))    { check_gate("DQ");  return; }
			if (cell->type == ID($_DFF_N_)) { check_gate("DQC"); return; }
			if (cell->type == ID($_DFF_P_)) { check_gate("DQC"); return; }

			if (cell->type == ID($_DFFE_NN_)) { check_gate("DQCE"); return; }
			if (cell->type == ID($_DFFE_NP_)) { check_gate("DQCE"); return; }
			if (cell->type == ID($_DFFE_PN_)) { check_gate("DQCE"); return; }
			if (cell->type == ID($_DFFE_PP_)) { check_gate("DQCE"); return; }

			if (cell->type == ID($_DFF_NN0_)) { check_gate("DQCR"); return; }
			if (cell->type == ID($_DFF_NN1_)) { check_gate("DQCR"); return; }
			if (cell->type == ID($_DFF_NP0_)) { check_gate("DQCR"); return; }
			if (cell->type == ID($_DFF_NP1_)) { check_gate("DQCR"); return; }
			if (cell->type == ID($_DFF_PN0_)) { check_gate("DQCR"); return; }
			if (cell->type == ID($_DFF_PN1_)) { check_gate("DQCR"); return; }
			if (cell->type == ID($_DFF_PP0_)) { check_gate("DQCR"); return; }
			if (cell->type == ID($_DFF_PP1_)) { check_gate("DQCR"); return; }

			if (cell->type == ID($_DFFSR_NNN_)) { check_gate("CSRDQ"); return; }
			if (cell->type == ID($_DFFSR_NNP_)) { check_gate("CSRDQ"); return; }
			if (cell->type == ID($_DFFSR_NPN_)) { check_gate("CSRDQ"); return; }
			if (cell->type == ID($_DFFSR_NPP_)) { check_gate("CSRDQ"); return; }
			if (cell->type == ID($_DFFSR_PNN_)) { check_gate("CSRDQ"); return; }
			if (cell->type == ID($_DFFSR_PNP_)) { check_gate("CSRDQ"); return; }
			if (cell->type == ID($_DFFSR_PPN_)) { check_gate("CSRDQ"); return; }
			if (cell->type == ID($_DFFSR_PPP_)) { check_gate("CSRDQ"); return; }

			if (cell->type == ID($_DLATCH_N_)) { check_gate("EDQ"); return; }
			if (cell->type == ID($_DLATCH_P_)) { check_gate("EDQ"); return; }

			if (cell->type == ID($_DLATCHSR_NNN_)) { check_gate("ESRDQ"); return; }
			if (cell->type == ID($_DLATCHSR_NNP_)) { check_gate("ESRDQ"); return; }
			if (cell->type == ID($_DLATCHSR_NPN_)) { check_gate("ESRDQ"); return; }
			if (cell->type == ID($_DLATCHSR_NPP_)) { check_gate("ESRDQ"); return; }
			if (cell->type == ID($_DLATCHSR_PNN_)) { check_gate("ESRDQ"); return; }
			if (cell->type == ID($_DLATCHSR_PNP_)) { check_gate("ESRDQ"); return; }
			if (cell->type == ID($_DLATCHSR_PPN_)) { check_gate("ESRDQ"); return; }
			if (cell->type == ID($_DLATCHSR_PPP_)) { check_gate("ESRDQ"); return; }

			error(__LINE__);
		}
	};
}
#endif

void RTLIL::Module::sort()
{
	wires_.sort(sort_by_id_str());
	cells_.sort(sort_by_id_str());
	avail_parameters.sort(sort_by_id_str());
	memories.sort(sort_by_id_str());
	processes.sort(sort_by_id_str());
	for (auto &it : cells_)
		it.second->sort();
	for (auto &it : wires_)
		it.second->attributes.sort(sort_by_id_str());
	for (auto &it : memories)
		it.second->attributes.sort(sort_by_id_str());
}

void RTLIL::Module::check()
{
#ifndef NDEBUG
	std::vector<bool> ports_declared;
	for (auto &it : wires_) {
		log_assert(this == it.second->module);
		log_assert(it.first == it.second->name);
		log_assert(!it.first.empty());
		log_assert(it.second->width >= 0);
		log_assert(it.second->port_id >= 0);
		for (auto &it2 : it.second->attributes)
			log_assert(!it2.first.empty());
		if (it.second->port_id) {
			log_assert(GetSize(ports) >= it.second->port_id);
			log_assert(ports.at(it.second->port_id-1) == it.first);
			log_assert(it.second->port_input || it.second->port_output);
			if (GetSize(ports_declared) < it.second->port_id)
				ports_declared.resize(it.second->port_id);
			log_assert(ports_declared[it.second->port_id-1] == false);
			ports_declared[it.second->port_id-1] = true;
		} else
			log_assert(!it.second->port_input && !it.second->port_output);
	}
	for (auto port_declared : ports_declared)
		log_assert(port_declared == true);
	log_assert(GetSize(ports) == GetSize(ports_declared));

	for (auto &it : memories) {
		log_assert(it.first == it.second->name);
		log_assert(!it.first.empty());
		log_assert(it.second->width >= 0);
		log_assert(it.second->size >= 0);
		for (auto &it2 : it.second->attributes)
			log_assert(!it2.first.empty());
	}

	for (auto &it : cells_) {
		log_assert(this == it.second->module);
		log_assert(it.first == it.second->name);
		log_assert(!it.first.empty());
		log_assert(!it.second->type.empty());
		for (auto &it2 : it.second->connections()) {
			log_assert(!it2.first.empty());
			it2.second.check();
		}
		for (auto &it2 : it.second->attributes)
			log_assert(!it2.first.empty());
		for (auto &it2 : it.second->parameters)
			log_assert(!it2.first.empty());
		InternalCellChecker checker(this, it.second);
		checker.check();
	}

	for (auto &it : processes) {
		log_assert(it.first == it.second->name);
		log_assert(!it.first.empty());
		log_assert(it.second->root_case.compare.empty());
		std::vector<CaseRule*> all_cases = {&it.second->root_case};
		for (size_t i = 0; i < all_cases.size(); i++) {
			for (auto &switch_it : all_cases[i]->switches) {
				for (auto &case_it : switch_it->cases) {
					for (auto &compare_it : case_it->compare) {
						log_assert(switch_it->signal.size() == compare_it.size());
					}
					all_cases.push_back(case_it);
				}
			}
		}
		for (auto &sync_it : it.second->syncs) {
			switch (sync_it->type) {
				case SyncType::ST0:
				case SyncType::ST1:
				case SyncType::STp:
				case SyncType::STn:
				case SyncType::STe:
					log_assert(!sync_it->signal.empty());
					break;
				case SyncType::STa:
				case SyncType::STg:
				case SyncType::STi:
					log_assert(sync_it->signal.empty());
					break;
			}
		}
	}

	for (auto &it : connections_) {
		log_assert(it.first.size() == it.second.size());
		log_assert(!it.first.has_const());
		it.first.check();
		it.second.check();
	}

	for (auto &it : attributes)
		log_assert(!it.first.empty());
#endif
}

void RTLIL::Module::optimize()
{
}

void RTLIL::Module::cloneInto(RTLIL::Module *new_mod) const
{
	log_assert(new_mod->refcount_wires_ == 0);
	log_assert(new_mod->refcount_cells_ == 0);

	new_mod->avail_parameters = avail_parameters;

	for (auto &conn : connections_)
		new_mod->connect(conn);

	for (auto &attr : attributes)
		new_mod->attributes[attr.first] = attr.second;

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
	new_mod->fixup_ports();
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
		log_warning("Ignoring module %s because it contains memories (run 'memory' command first).\n", log_id(this));
	return !memories.empty();
}

bool RTLIL::Module::has_processes_warn() const
{
	if (!processes.empty())
		log_warning("Ignoring module %s because it contains processes (run 'proc' command first).\n", log_id(this));
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
	result.reserve(cells_.size());
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

void RTLIL::Module::remove(const pool<RTLIL::Wire*> &wires)
{
	log_assert(refcount_wires_ == 0);

	struct DeleteWireWorker
	{
		RTLIL::Module *module;
		const pool<RTLIL::Wire*> *wires_p;

		void operator()(RTLIL::SigSpec &sig) {
			std::vector<RTLIL::SigChunk> chunks = sig;
			for (auto &c : chunks)
				if (c.wire != NULL && wires_p->count(c.wire)) {
					c.wire = module->addWire(NEW_ID, c.width);
					c.offset = 0;
				}
			sig = chunks;
		}

		void operator()(RTLIL::SigSpec &lhs, RTLIL::SigSpec &rhs) {
			log_assert(GetSize(lhs) == GetSize(rhs));
			RTLIL::SigSpec new_lhs, new_rhs;
			for (int i = 0; i < GetSize(lhs); i++) {
				RTLIL::SigBit lhs_bit = lhs[i];
				if (lhs_bit.wire != nullptr && wires_p->count(lhs_bit.wire))
					continue;
				RTLIL::SigBit rhs_bit = rhs[i];
				if (rhs_bit.wire != nullptr && wires_p->count(rhs_bit.wire))
					continue;
				new_lhs.append(lhs_bit);
				new_rhs.append(rhs_bit);
			}
			lhs = new_lhs;
			rhs = new_rhs;
		}
	};

	DeleteWireWorker delete_wire_worker;
	delete_wire_worker.module = this;
	delete_wire_worker.wires_p = &wires;
	rewrite_sigspecs2(delete_wire_worker);

	for (auto &it : wires) {
		log_assert(wires_.count(it->name) != 0);
		wires_.erase(it->name);
		delete it;
	}
}

void RTLIL::Module::remove(RTLIL::Cell *cell)
{
	while (!cell->connections_.empty())
		cell->unsetPort(cell->connections_.begin()->first);

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

void RTLIL::Module::swap_names(RTLIL::Wire *w1, RTLIL::Wire *w2)
{
	log_assert(wires_[w1->name] == w1);
	log_assert(wires_[w2->name] == w2);
	log_assert(refcount_wires_ == 0);

	wires_.erase(w1->name);
	wires_.erase(w2->name);

	std::swap(w1->name, w2->name);

	wires_[w1->name] = w1;
	wires_[w2->name] = w2;
}

void RTLIL::Module::swap_names(RTLIL::Cell *c1, RTLIL::Cell *c2)
{
	log_assert(cells_[c1->name] == c1);
	log_assert(cells_[c2->name] == c2);
	log_assert(refcount_cells_ == 0);

	cells_.erase(c1->name);
	cells_.erase(c2->name);

	std::swap(c1->name, c2->name);

	cells_[c1->name] = c1;
	cells_[c2->name] = c2;
}

RTLIL::IdString RTLIL::Module::uniquify(RTLIL::IdString name)
{
	int index = 0;
	return uniquify(name, index);
}

RTLIL::IdString RTLIL::Module::uniquify(RTLIL::IdString name, int &index)
{
	if (index == 0) {
		if (count_id(name) == 0)
			return name;
		index++;
	}

	while (1) {
		RTLIL::IdString new_name = stringf("%s_%d", name.c_str(), index);
		if (count_id(new_name) == 0)
			return new_name;
		index++;
	}
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
	for (auto mon : monitors)
		mon->notify_connect(this, conn);

	if (design)
		for (auto mon : design->monitors)
			mon->notify_connect(this, conn);

	// ignore all attempts to assign constants to other constants
	if (conn.first.has_const()) {
		RTLIL::SigSig new_conn;
		for (int i = 0; i < GetSize(conn.first); i++)
			if (conn.first[i].wire) {
				new_conn.first.append(conn.first[i]);
				new_conn.second.append(conn.second[i]);
			}
		if (GetSize(new_conn.first))
			connect(new_conn);
		return;
	}

	if (yosys_xtrace) {
		log("#X# Connect (SigSig) in %s: %s = %s (%d bits)\n", log_id(this), log_signal(conn.first), log_signal(conn.second), GetSize(conn.first));
		log_backtrace("-X- ", yosys_xtrace-1);
	}

	log_assert(GetSize(conn.first) == GetSize(conn.second));
	connections_.push_back(conn);
}

void RTLIL::Module::connect(const RTLIL::SigSpec &lhs, const RTLIL::SigSpec &rhs)
{
	connect(RTLIL::SigSig(lhs, rhs));
}

void RTLIL::Module::new_connections(const std::vector<RTLIL::SigSig> &new_conn)
{
	for (auto mon : monitors)
		mon->notify_connect(this, new_conn);

	if (design)
		for (auto mon : design->monitors)
			mon->notify_connect(this, new_conn);

	if (yosys_xtrace) {
		log("#X# New connections vector in %s:\n", log_id(this));
		for (auto &conn: new_conn)
			log("#X#    %s = %s (%d bits)\n", log_signal(conn.first), log_signal(conn.second), GetSize(conn.first));
		log_backtrace("-X- ", yosys_xtrace-1);
	}

	connections_ = new_conn;
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

	ports.clear();
	for (size_t i = 0; i < all_ports.size(); i++) {
		ports.push_back(all_ports[i]->name);
		all_ports[i]->port_id = i+1;
	}
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
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, bool is_signed, const std::string &src) { \
		RTLIL::Cell *cell = addCell(name, _type);           \
		cell->parameters[ID(A_SIGNED)] = is_signed;         \
		cell->parameters[ID(A_WIDTH)] = sig_a.size();       \
		cell->parameters[ID(Y_WIDTH)] = sig_y.size();       \
		cell->setPort(ID::A, sig_a);                        \
		cell->setPort(ID::Y, sig_y);                        \
		cell->set_src_attribute(src);                       \
		return cell;                                        \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, bool is_signed, const std::string &src) { \
		RTLIL::SigSpec sig_y = addWire(NEW_ID, _y_size);    \
		add ## _func(name, sig_a, sig_y, is_signed, src);   \
		return sig_y;                                       \
	}
DEF_METHOD(Not,        sig_a.size(), ID($not))
DEF_METHOD(Pos,        sig_a.size(), ID($pos))
DEF_METHOD(Neg,        sig_a.size(), ID($neg))
DEF_METHOD(ReduceAnd,  1, ID($reduce_and))
DEF_METHOD(ReduceOr,   1, ID($reduce_or))
DEF_METHOD(ReduceXor,  1, ID($reduce_xor))
DEF_METHOD(ReduceXnor, 1, ID($reduce_xnor))
DEF_METHOD(ReduceBool, 1, ID($reduce_bool))
DEF_METHOD(LogicNot,   1, ID($logic_not))
#undef DEF_METHOD

#define DEF_METHOD(_func, _y_size, _type) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed, const std::string &src) { \
		RTLIL::Cell *cell = addCell(name, _type);           \
		cell->parameters[ID(A_SIGNED)] = is_signed;         \
		cell->parameters[ID(B_SIGNED)] = is_signed;         \
		cell->parameters[ID(A_WIDTH)] = sig_a.size();       \
		cell->parameters[ID(B_WIDTH)] = sig_b.size();       \
		cell->parameters[ID(Y_WIDTH)] = sig_y.size();       \
		cell->setPort(ID::A, sig_a);                        \
		cell->setPort(ID::B, sig_b);                        \
		cell->setPort(ID::Y, sig_y);                        \
		cell->set_src_attribute(src);                       \
		return cell;                                        \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed, const std::string &src) { \
		RTLIL::SigSpec sig_y = addWire(NEW_ID, _y_size);         \
		add ## _func(name, sig_a, sig_b, sig_y, is_signed, src); \
		return sig_y;                                            \
	}
DEF_METHOD(And,      max(sig_a.size(), sig_b.size()), ID($and))
DEF_METHOD(Or,       max(sig_a.size(), sig_b.size()), ID($or))
DEF_METHOD(Xor,      max(sig_a.size(), sig_b.size()), ID($xor))
DEF_METHOD(Xnor,     max(sig_a.size(), sig_b.size()), ID($xnor))
DEF_METHOD(Shift,    sig_a.size(), ID($shift))
DEF_METHOD(Shiftx,   sig_a.size(), ID($shiftx))
DEF_METHOD(Lt,       1, ID($lt))
DEF_METHOD(Le,       1, ID($le))
DEF_METHOD(Eq,       1, ID($eq))
DEF_METHOD(Ne,       1, ID($ne))
DEF_METHOD(Eqx,      1, ID($eqx))
DEF_METHOD(Nex,      1, ID($nex))
DEF_METHOD(Ge,       1, ID($ge))
DEF_METHOD(Gt,       1, ID($gt))
DEF_METHOD(Add,      max(sig_a.size(), sig_b.size()), ID($add))
DEF_METHOD(Sub,      max(sig_a.size(), sig_b.size()), ID($sub))
DEF_METHOD(Mul,      max(sig_a.size(), sig_b.size()), ID($mul))
DEF_METHOD(Div,      max(sig_a.size(), sig_b.size()), ID($div))
DEF_METHOD(Mod,      max(sig_a.size(), sig_b.size()), ID($mod))
DEF_METHOD(LogicAnd, 1, ID($logic_and))
DEF_METHOD(LogicOr,  1, ID($logic_or))
#undef DEF_METHOD

#define DEF_METHOD(_func, _y_size, _type) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool is_signed, const std::string &src) { \
		RTLIL::Cell *cell = addCell(name, _type);           \
		cell->parameters[ID(A_SIGNED)] = is_signed;         \
		cell->parameters[ID(B_SIGNED)] = false;             \
		cell->parameters[ID(A_WIDTH)] = sig_a.size();       \
		cell->parameters[ID(B_WIDTH)] = sig_b.size();       \
		cell->parameters[ID(Y_WIDTH)] = sig_y.size();       \
		cell->setPort(ID::A, sig_a);                        \
		cell->setPort(ID::B, sig_b);                        \
		cell->setPort(ID::Y, sig_y);                        \
		cell->set_src_attribute(src);                       \
		return cell;                                        \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, bool is_signed, const std::string &src) { \
		RTLIL::SigSpec sig_y = addWire(NEW_ID, _y_size);         \
		add ## _func(name, sig_a, sig_b, sig_y, is_signed, src); \
		return sig_y;                                            \
	}
DEF_METHOD(Shl,      sig_a.size(), ID($shl))
DEF_METHOD(Shr,      sig_a.size(), ID($shr))
DEF_METHOD(Sshl,     sig_a.size(), ID($sshl))
DEF_METHOD(Sshr,     sig_a.size(), ID($sshr))
#undef DEF_METHOD

#define DEF_METHOD(_func, _type, _pmux) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, RTLIL::SigSpec sig_y, const std::string &src) { \
		RTLIL::Cell *cell = addCell(name, _type);                 \
		cell->parameters[ID(WIDTH)] = sig_a.size();               \
		if (_pmux) cell->parameters[ID(S_WIDTH)] = sig_s.size();  \
		cell->setPort(ID::A, sig_a);                              \
		cell->setPort(ID::B, sig_b);                              \
		cell->setPort(ID(S), sig_s);                              \
		cell->setPort(ID::Y, sig_y);                              \
		cell->set_src_attribute(src);                             \
		return cell;                                              \
	} \
	RTLIL::SigSpec RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_s, const std::string &src) { \
		RTLIL::SigSpec sig_y = addWire(NEW_ID, sig_a.size());     \
		add ## _func(name, sig_a, sig_b, sig_s, sig_y, src);      \
		return sig_y;                                             \
	}
DEF_METHOD(Mux,      ID($mux),        0)
DEF_METHOD(Pmux,     ID($pmux),       1)
#undef DEF_METHOD

#define DEF_METHOD_2(_func, _type, _P1, _P2) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigBit sig1, RTLIL::SigBit sig2, const std::string &src) { \
		RTLIL::Cell *cell = addCell(name, _type);         \
		cell->setPort("\\" #_P1, sig1);                   \
		cell->setPort("\\" #_P2, sig2);                   \
		cell->set_src_attribute(src);                     \
		return cell;                                      \
	} \
	RTLIL::SigBit RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigBit sig1, const std::string &src) { \
		RTLIL::SigBit sig2 = addWire(NEW_ID);             \
		add ## _func(name, sig1, sig2, src);              \
		return sig2;                                      \
	}
#define DEF_METHOD_3(_func, _type, _P1, _P2, _P3) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigBit sig1, RTLIL::SigBit sig2, RTLIL::SigBit sig3, const std::string &src) { \
		RTLIL::Cell *cell = addCell(name, _type);         \
		cell->setPort("\\" #_P1, sig1);                   \
		cell->setPort("\\" #_P2, sig2);                   \
		cell->setPort("\\" #_P3, sig3);                   \
		cell->set_src_attribute(src);                     \
		return cell;                                      \
	} \
	RTLIL::SigBit RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigBit sig1, RTLIL::SigBit sig2, const std::string &src) { \
		RTLIL::SigBit sig3 = addWire(NEW_ID);             \
		add ## _func(name, sig1, sig2, sig3, src);        \
		return sig3;                                      \
	}
#define DEF_METHOD_4(_func, _type, _P1, _P2, _P3, _P4) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigBit sig1, RTLIL::SigBit sig2, RTLIL::SigBit sig3, RTLIL::SigBit sig4, const std::string &src) { \
		RTLIL::Cell *cell = addCell(name, _type);         \
		cell->setPort("\\" #_P1, sig1);                   \
		cell->setPort("\\" #_P2, sig2);                   \
		cell->setPort("\\" #_P3, sig3);                   \
		cell->setPort("\\" #_P4, sig4);                   \
		cell->set_src_attribute(src);                     \
		return cell;                                      \
	} \
	RTLIL::SigBit RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigBit sig1, RTLIL::SigBit sig2, RTLIL::SigBit sig3, const std::string &src) { \
		RTLIL::SigBit sig4 = addWire(NEW_ID);             \
		add ## _func(name, sig1, sig2, sig3, sig4, src);  \
		return sig4;                                      \
	}
#define DEF_METHOD_5(_func, _type, _P1, _P2, _P3, _P4, _P5) \
	RTLIL::Cell* RTLIL::Module::add ## _func(RTLIL::IdString name, RTLIL::SigBit sig1, RTLIL::SigBit sig2, RTLIL::SigBit sig3, RTLIL::SigBit sig4, RTLIL::SigBit sig5, const std::string &src) { \
		RTLIL::Cell *cell = addCell(name, _type);         \
		cell->setPort("\\" #_P1, sig1);                   \
		cell->setPort("\\" #_P2, sig2);                   \
		cell->setPort("\\" #_P3, sig3);                   \
		cell->setPort("\\" #_P4, sig4);                   \
		cell->setPort("\\" #_P5, sig5);                   \
		cell->set_src_attribute(src);                     \
		return cell;                                      \
	} \
	RTLIL::SigBit RTLIL::Module::_func(RTLIL::IdString name, RTLIL::SigBit sig1, RTLIL::SigBit sig2, RTLIL::SigBit sig3, RTLIL::SigBit sig4, const std::string &src) { \
		RTLIL::SigBit sig5 = addWire(NEW_ID);                  \
		add ## _func(name, sig1, sig2, sig3, sig4, sig5, src); \
		return sig5;                                           \
	}
DEF_METHOD_2(BufGate,    ID($_BUF_),    A, Y)
DEF_METHOD_2(NotGate,    ID($_NOT_),    A, Y)
DEF_METHOD_3(AndGate,    ID($_AND_),    A, B, Y)
DEF_METHOD_3(NandGate,   ID($_NAND_),   A, B, Y)
DEF_METHOD_3(OrGate,     ID($_OR_),     A, B, Y)
DEF_METHOD_3(NorGate,    ID($_NOR_),    A, B, Y)
DEF_METHOD_3(XorGate,    ID($_XOR_),    A, B, Y)
DEF_METHOD_3(XnorGate,   ID($_XNOR_),   A, B, Y)
DEF_METHOD_3(AndnotGate, ID($_ANDNOT_), A, B, Y)
DEF_METHOD_3(OrnotGate,  ID($_ORNOT_),  A, B, Y)
DEF_METHOD_4(MuxGate,    ID($_MUX_),    A, B, S, Y)
DEF_METHOD_4(NmuxGate,   ID($_NMUX_),   A, B, S, Y)
DEF_METHOD_4(Aoi3Gate,   ID($_AOI3_),   A, B, C, Y)
DEF_METHOD_4(Oai3Gate,   ID($_OAI3_),   A, B, C, Y)
DEF_METHOD_5(Aoi4Gate,   ID($_AOI4_),   A, B, C, D, Y)
DEF_METHOD_5(Oai4Gate,   ID($_OAI4_),   A, B, C, D, Y)
#undef DEF_METHOD_2
#undef DEF_METHOD_3
#undef DEF_METHOD_4
#undef DEF_METHOD_5

RTLIL::Cell* RTLIL::Module::addPow(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, bool a_signed, bool b_signed, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($pow));
	cell->parameters[ID(A_SIGNED)] = a_signed;
	cell->parameters[ID(B_SIGNED)] = b_signed;
	cell->parameters[ID(A_WIDTH)] = sig_a.size();
	cell->parameters[ID(B_WIDTH)] = sig_b.size();
	cell->parameters[ID(Y_WIDTH)] = sig_y.size();
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID::B, sig_b);
	cell->setPort(ID::Y, sig_y);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addSlice(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, RTLIL::Const offset, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($slice));
	cell->parameters[ID(A_WIDTH)] = sig_a.size();
	cell->parameters[ID(Y_WIDTH)] = sig_y.size();
	cell->parameters[ID(OFFSET)] = offset;
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID::Y, sig_y);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addConcat(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($concat));
	cell->parameters[ID(A_WIDTH)] = sig_a.size();
	cell->parameters[ID(B_WIDTH)] = sig_b.size();
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID::B, sig_b);
	cell->setPort(ID::Y, sig_y);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addLut(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_y, RTLIL::Const lut, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($lut));
	cell->parameters[ID(LUT)] = lut;
	cell->parameters[ID(WIDTH)] = sig_a.size();
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID::Y, sig_y);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addTribuf(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_y, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($tribuf));
	cell->parameters[ID(WIDTH)] = sig_a.size();
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID(EN), sig_en);
	cell->setPort(ID::Y, sig_y);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAssert(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($assert));
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID(EN), sig_en);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAssume(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($assume));
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID(EN), sig_en);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addLive(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($live));
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID(EN), sig_en);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addFair(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($fair));
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID(EN), sig_en);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addCover(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_en, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($cover));
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID(EN), sig_en);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addEquiv(RTLIL::IdString name, RTLIL::SigSpec sig_a, RTLIL::SigSpec sig_b, RTLIL::SigSpec sig_y, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($equiv));
	cell->setPort(ID::A, sig_a);
	cell->setPort(ID::B, sig_b);
	cell->setPort(ID::Y, sig_y);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addSr(RTLIL::IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, RTLIL::SigSpec sig_q, bool set_polarity, bool clr_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($sr));
	cell->parameters[ID(SET_POLARITY)] = set_polarity;
	cell->parameters[ID(CLR_POLARITY)] = clr_polarity;
	cell->parameters[ID(WIDTH)] = sig_q.size();
	cell->setPort(ID(SET), sig_set);
	cell->setPort(ID(CLR), sig_clr);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addFf(RTLIL::IdString name, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($ff));
	cell->parameters[ID(WIDTH)] = sig_q.size();
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDff(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($dff));
	cell->parameters[ID(CLK_POLARITY)] = clk_polarity;
	cell->parameters[ID(WIDTH)] = sig_q.size();
	cell->setPort(ID(CLK), sig_clk);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffe(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity, bool en_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($dffe));
	cell->parameters[ID(CLK_POLARITY)] = clk_polarity;
	cell->parameters[ID(EN_POLARITY)] = en_polarity;
	cell->parameters[ID(WIDTH)] = sig_q.size();
	cell->setPort(ID(CLK), sig_clk);
	cell->setPort(ID(EN), sig_en);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffsr(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($dffsr));
	cell->parameters[ID(CLK_POLARITY)] = clk_polarity;
	cell->parameters[ID(SET_POLARITY)] = set_polarity;
	cell->parameters[ID(CLR_POLARITY)] = clr_polarity;
	cell->parameters[ID(WIDTH)] = sig_q.size();
	cell->setPort(ID(CLK), sig_clk);
	cell->setPort(ID(SET), sig_set);
	cell->setPort(ID(CLR), sig_clr);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAdff(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,
		RTLIL::Const arst_value, bool clk_polarity, bool arst_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($adff));
	cell->parameters[ID(CLK_POLARITY)] = clk_polarity;
	cell->parameters[ID(ARST_POLARITY)] = arst_polarity;
	cell->parameters[ID(ARST_VALUE)] = arst_value;
	cell->parameters[ID(WIDTH)] = sig_q.size();
	cell->setPort(ID(CLK), sig_clk);
	cell->setPort(ID(ARST), sig_arst);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatch(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($dlatch));
	cell->parameters[ID(EN_POLARITY)] = en_polarity;
	cell->parameters[ID(WIDTH)] = sig_q.size();
	cell->setPort(ID(EN), sig_en);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatchsr(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity, bool set_polarity, bool clr_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($dlatchsr));
	cell->parameters[ID(EN_POLARITY)] = en_polarity;
	cell->parameters[ID(SET_POLARITY)] = set_polarity;
	cell->parameters[ID(CLR_POLARITY)] = clr_polarity;
	cell->parameters[ID(WIDTH)] = sig_q.size();
	cell->setPort(ID(EN), sig_en);
	cell->setPort(ID(SET), sig_set);
	cell->setPort(ID(CLR), sig_clr);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addFfGate(RTLIL::IdString name, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, ID($_FF_));
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, stringf("$_DFF_%c_", clk_polarity ? 'P' : 'N'));
	cell->setPort(ID(C), sig_clk);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffeGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity, bool en_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, stringf("$_DFFE_%c%c_", clk_polarity ? 'P' : 'N', en_polarity ? 'P' : 'N'));
	cell->setPort(ID(C), sig_clk);
	cell->setPort(ID(E), sig_en);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDffsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool clk_polarity, bool set_polarity, bool clr_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, stringf("$_DFFSR_%c%c%c_", clk_polarity ? 'P' : 'N', set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N'));
	cell->setPort(ID(C), sig_clk);
	cell->setPort(ID(S), sig_set);
	cell->setPort(ID(R), sig_clr);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addAdffGate(RTLIL::IdString name, RTLIL::SigSpec sig_clk, RTLIL::SigSpec sig_arst, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q,
		bool arst_value, bool clk_polarity, bool arst_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, stringf("$_DFF_%c%c%c_", clk_polarity ? 'P' : 'N', arst_polarity ? 'P' : 'N', arst_value ? '1' : '0'));
	cell->setPort(ID(C), sig_clk);
	cell->setPort(ID(R), sig_arst);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatchGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, stringf("$_DLATCH_%c_", en_polarity ? 'P' : 'N'));
	cell->setPort(ID(E), sig_en);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::Cell* RTLIL::Module::addDlatchsrGate(RTLIL::IdString name, RTLIL::SigSpec sig_en, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr,
		RTLIL::SigSpec sig_d, RTLIL::SigSpec sig_q, bool en_polarity, bool set_polarity, bool clr_polarity, const std::string &src)
{
	RTLIL::Cell *cell = addCell(name, stringf("$_DLATCHSR_%c%c%c_", en_polarity ? 'P' : 'N', set_polarity ? 'P' : 'N', clr_polarity ? 'P' : 'N'));
	cell->setPort(ID(E), sig_en);
	cell->setPort(ID(S), sig_set);
	cell->setPort(ID(R), sig_clr);
	cell->setPort(ID(D), sig_d);
	cell->setPort(ID(Q), sig_q);
	cell->set_src_attribute(src);
	return cell;
}

RTLIL::SigSpec RTLIL::Module::Anyconst(RTLIL::IdString name, int width, const std::string &src)
{
	RTLIL::SigSpec sig = addWire(NEW_ID, width);
	Cell *cell = addCell(name, ID($anyconst));
	cell->setParam(ID(WIDTH), width);
	cell->setPort(ID::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::Anyseq(RTLIL::IdString name, int width, const std::string &src)
{
	RTLIL::SigSpec sig = addWire(NEW_ID, width);
	Cell *cell = addCell(name, ID($anyseq));
	cell->setParam(ID(WIDTH), width);
	cell->setPort(ID::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::Allconst(RTLIL::IdString name, int width, const std::string &src)
{
	RTLIL::SigSpec sig = addWire(NEW_ID, width);
	Cell *cell = addCell(name, ID($allconst));
	cell->setParam(ID(WIDTH), width);
	cell->setPort(ID::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::Allseq(RTLIL::IdString name, int width, const std::string &src)
{
	RTLIL::SigSpec sig = addWire(NEW_ID, width);
	Cell *cell = addCell(name, ID($allseq));
	cell->setParam(ID(WIDTH), width);
	cell->setPort(ID::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::SigSpec RTLIL::Module::Initstate(RTLIL::IdString name, const std::string &src)
{
	RTLIL::SigSpec sig = addWire(NEW_ID);
	Cell *cell = addCell(name, ID($initstate));
	cell->setPort(ID::Y, sig);
	cell->set_src_attribute(src);
	return sig;
}

RTLIL::Wire::Wire()
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	module = nullptr;
	width = 1;
	start_offset = 0;
	port_id = 0;
	port_input = false;
	port_output = false;
	upto = false;

#ifdef WITH_PYTHON
	RTLIL::Wire::get_all_wires()->insert(std::pair<unsigned int, RTLIL::Wire*>(hashidx_, this));
#endif
}

RTLIL::Wire::~Wire()
{
#ifdef WITH_PYTHON
	RTLIL::Wire::get_all_wires()->erase(hashidx_);
#endif
}

#ifdef WITH_PYTHON
static std::map<unsigned int, RTLIL::Wire*> all_wires;
std::map<unsigned int, RTLIL::Wire*> *RTLIL::Wire::get_all_wires(void)
{
	return &all_wires;
}
#endif

RTLIL::Memory::Memory()
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	width = 1;
	start_offset = 0;
	size = 0;
#ifdef WITH_PYTHON
	RTLIL::Memory::get_all_memorys()->insert(std::pair<unsigned int, RTLIL::Memory*>(hashidx_, this));
#endif
}

RTLIL::Cell::Cell() : module(nullptr)
{
	static unsigned int hashidx_count = 123456789;
	hashidx_count = mkhash_xorshift(hashidx_count);
	hashidx_ = hashidx_count;

	// log("#memtrace# %p\n", this);
	memhasher();

#ifdef WITH_PYTHON
	RTLIL::Cell::get_all_cells()->insert(std::pair<unsigned int, RTLIL::Cell*>(hashidx_, this));
#endif
}

RTLIL::Cell::~Cell()
{
#ifdef WITH_PYTHON
	RTLIL::Cell::get_all_cells()->erase(hashidx_);
#endif
}

#ifdef WITH_PYTHON
static std::map<unsigned int, RTLIL::Cell*> all_cells;
std::map<unsigned int, RTLIL::Cell*> *RTLIL::Cell::get_all_cells(void)
{
	return &all_cells;
}
#endif

bool RTLIL::Cell::hasPort(RTLIL::IdString portname) const
{
	return connections_.count(portname) != 0;
}

void RTLIL::Cell::unsetPort(RTLIL::IdString portname)
{
	RTLIL::SigSpec signal;
	auto conn_it = connections_.find(portname);

	if (conn_it != connections_.end())
	{
		for (auto mon : module->monitors)
			mon->notify_connect(this, conn_it->first, conn_it->second, signal);

		if (module->design)
			for (auto mon : module->design->monitors)
				mon->notify_connect(this, conn_it->first, conn_it->second, signal);

		if (yosys_xtrace) {
			log("#X# Unconnect %s.%s.%s\n", log_id(this->module), log_id(this), log_id(portname));
			log_backtrace("-X- ", yosys_xtrace-1);
		}

		connections_.erase(conn_it);
	}
}

void RTLIL::Cell::setPort(RTLIL::IdString portname, RTLIL::SigSpec signal)
{
	auto conn_it = connections_.find(portname);

	if (conn_it == connections_.end()) {
		connections_[portname] = RTLIL::SigSpec();
		conn_it = connections_.find(portname);
		log_assert(conn_it != connections_.end());
	} else
	if (conn_it->second == signal)
		return;

	for (auto mon : module->monitors)
		mon->notify_connect(this, conn_it->first, conn_it->second, signal);

	if (module->design)
		for (auto mon : module->design->monitors)
			mon->notify_connect(this, conn_it->first, conn_it->second, signal);

	if (yosys_xtrace) {
		log("#X# Connect %s.%s.%s = %s (%d)\n", log_id(this->module), log_id(this), log_id(portname), log_signal(signal), GetSize(signal));
		log_backtrace("-X- ", yosys_xtrace-1);
	}

	conn_it->second = signal;
}

const RTLIL::SigSpec &RTLIL::Cell::getPort(RTLIL::IdString portname) const
{
	return connections_.at(portname);
}

const dict<RTLIL::IdString, RTLIL::SigSpec> &RTLIL::Cell::connections() const
{
	return connections_;
}

bool RTLIL::Cell::known() const
{
	if (yosys_celltypes.cell_known(type))
		return true;
	if (module && module->design && module->design->module(type))
		return true;
	return false;
}

bool RTLIL::Cell::input(RTLIL::IdString portname) const
{
	if (yosys_celltypes.cell_known(type))
		return yosys_celltypes.cell_input(type, portname);
	if (module && module->design) {
		RTLIL::Module *m = module->design->module(type);
		RTLIL::Wire *w = m ? m->wire(portname) : nullptr;
		return w && w->port_input;
	}
	return false;
}

bool RTLIL::Cell::output(RTLIL::IdString portname) const
{
	if (yosys_celltypes.cell_known(type))
		return yosys_celltypes.cell_output(type, portname);
	if (module && module->design) {
		RTLIL::Module *m = module->design->module(type);
		RTLIL::Wire *w = m ? m->wire(portname) : nullptr;
		return w && w->port_output;
	}
	return false;
}

bool RTLIL::Cell::hasParam(RTLIL::IdString paramname) const
{
	return parameters.count(paramname) != 0;
}

void RTLIL::Cell::unsetParam(RTLIL::IdString paramname)
{
	parameters.erase(paramname);
}

void RTLIL::Cell::setParam(RTLIL::IdString paramname, RTLIL::Const value)
{
	parameters[paramname] = value;
}

const RTLIL::Const &RTLIL::Cell::getParam(RTLIL::IdString paramname) const
{
	return parameters.at(paramname);
}

void RTLIL::Cell::sort()
{
	connections_.sort(sort_by_id_str());
	parameters.sort(sort_by_id_str());
	attributes.sort(sort_by_id_str());
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
	if (!type.begins_with("$") || type.begins_with("$_") || type.begins_with("$paramod") || type.begins_with("$fmcombine") ||
			type.begins_with("$verific$") || type.begins_with("$array:") || type.begins_with("$extern:"))
		return;

	if (type == ID($mux) || type == ID($pmux)) {
		parameters[ID(WIDTH)] = GetSize(connections_[ID::Y]);
		if (type == ID($pmux))
			parameters[ID(S_WIDTH)] = GetSize(connections_[ID(S)]);
		check();
		return;
	}

	if (type == ID($lut) || type == ID($sop)) {
		parameters[ID(WIDTH)] = GetSize(connections_[ID::A]);
		return;
	}

	if (type == ID($fa)) {
		parameters[ID(WIDTH)] = GetSize(connections_[ID::Y]);
		return;
	}

	if (type == ID($lcu)) {
		parameters[ID(WIDTH)] = GetSize(connections_[ID(CO)]);
		return;
	}

	bool signedness_ab = !type.in(ID($slice), ID($concat), ID($macc));

	if (connections_.count(ID::A)) {
		if (signedness_ab) {
			if (set_a_signed)
				parameters[ID(A_SIGNED)] = true;
			else if (parameters.count(ID(A_SIGNED)) == 0)
				parameters[ID(A_SIGNED)] = false;
		}
		parameters[ID(A_WIDTH)] = GetSize(connections_[ID::A]);
	}

	if (connections_.count(ID::B)) {
		if (signedness_ab) {
			if (set_b_signed)
				parameters[ID(B_SIGNED)] = true;
			else if (parameters.count(ID(B_SIGNED)) == 0)
				parameters[ID(B_SIGNED)] = false;
		}
		parameters[ID(B_WIDTH)] = GetSize(connections_[ID::B]);
	}

	if (connections_.count(ID::Y))
		parameters[ID(Y_WIDTH)] = GetSize(connections_[ID::Y]);

	if (connections_.count(ID(Q)))
		parameters[ID(WIDTH)] = GetSize(connections_[ID(Q)]);

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
	data = value.bits;
	width = GetSize(data);
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
	data = RTLIL::Const(str).bits;
	width = GetSize(data);
	offset = 0;
}

RTLIL::SigChunk::SigChunk(int val, int width)
{
	wire = NULL;
	data = RTLIL::Const(val, width).bits;
	this->width = GetSize(data);
	offset = 0;
}

RTLIL::SigChunk::SigChunk(RTLIL::State bit, int width)
{
	wire = NULL;
	data = RTLIL::Const(bit, width).bits;
	this->width = GetSize(data);
	offset = 0;
}

RTLIL::SigChunk::SigChunk(RTLIL::SigBit bit)
{
	wire = bit.wire;
	offset = 0;
	if (wire == NULL)
		data = RTLIL::Const(bit.data).bits;
	else
		offset = bit.offset;
	width = 1;
}

RTLIL::SigChunk::SigChunk(const RTLIL::SigChunk &sigchunk) : data(sigchunk.data)
{
	wire = sigchunk.wire;
	data = sigchunk.data;
	width = sigchunk.width;
	offset = sigchunk.offset;
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
			ret.data.push_back(data[offset+i]);
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

	return data < other.data;
}

bool RTLIL::SigChunk::operator ==(const RTLIL::SigChunk &other) const
{
	return wire == other.wire && width == other.width && offset == other.offset && data == other.data;
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
					last->data.push_back(bit.data);
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

RTLIL::SigSpec::SigSpec(pool<RTLIL::SigBit> bits)
{
	cover("kernel.rtlil.sigspec.init.pool_bits");

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

RTLIL::SigSpec::SigSpec(bool bit)
{
	cover("kernel.rtlil.sigspec.init.bool");

	width_ = 0;
	hash_ = 0;
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
				last->data.push_back(bit.data);
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

void RTLIL::SigSpec::updhash() const
{
	RTLIL::SigSpec *that = (RTLIL::SigSpec*)this;

	if (that->hash_ != 0)
		return;

	cover("kernel.rtlil.sigspec.hash");
	that->pack();

	that->hash_ = mkhash_init;
	for (auto &c : that->chunks_)
		if (c.wire == NULL) {
			for (auto &v : c.data)
				that->hash_ = mkhash(that->hash_, v);
		} else {
			that->hash_ = mkhash(that->hash_, c.wire->name.index_);
			that->hash_ = mkhash(that->hash_, c.offset);
			that->hash_ = mkhash(that->hash_, c.width);
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
	unpack();
	cover("kernel.rtlil.sigspec.sort_and_unify");

	// A copy of the bits vector is used to prevent duplicating the logic from
	// SigSpec::SigSpec(std::vector<SigBit>).  This incurrs an extra copy but
	// that isn't showing up as significant in profiles.
	std::vector<SigBit> unique_bits = bits_;
	std::sort(unique_bits.begin(), unique_bits.end());
	auto last = std::unique(unique_bits.begin(), unique_bits.end());
	unique_bits.erase(last, unique_bits.end());

	*this = unique_bits;
}

void RTLIL::SigSpec::replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with)
{
	replace(pattern, with, this);
}

void RTLIL::SigSpec::replace(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec &with, RTLIL::SigSpec *other) const
{
	log_assert(other != NULL);
	log_assert(width_ == other->width_);
	log_assert(pattern.width_ == with.width_);

	pattern.unpack();
	with.unpack();
	unpack();
	other->unpack();

	for (int i = 0; i < GetSize(pattern.bits_); i++) {
		if (pattern.bits_[i].wire != NULL) {
			for (int j = 0; j < GetSize(bits_); j++) {
				if (bits_[j] == pattern.bits_[i]) {
					other->bits_[j] = with.bits_[i];
				}
			}
		}
	}

	other->check();
}

void RTLIL::SigSpec::replace(const dict<RTLIL::SigBit, RTLIL::SigBit> &rules)
{
	replace(rules, this);
}

void RTLIL::SigSpec::replace(const dict<RTLIL::SigBit, RTLIL::SigBit> &rules, RTLIL::SigSpec *other) const
{
	cover("kernel.rtlil.sigspec.replace_dict");

	log_assert(other != NULL);
	log_assert(width_ == other->width_);

	if (rules.empty()) return;
	unpack();
	other->unpack();

	for (int i = 0; i < GetSize(bits_); i++) {
		auto it = rules.find(bits_[i]);
		if (it != rules.end())
			other->bits_[i] = it->second;
	}

	other->check();
}

void RTLIL::SigSpec::replace(const std::map<RTLIL::SigBit, RTLIL::SigBit> &rules)
{
	replace(rules, this);
}

void RTLIL::SigSpec::replace(const std::map<RTLIL::SigBit, RTLIL::SigBit> &rules, RTLIL::SigSpec *other) const
{
	cover("kernel.rtlil.sigspec.replace_map");

	log_assert(other != NULL);
	log_assert(width_ == other->width_);

	if (rules.empty()) return;
	unpack();
	other->unpack();

	for (int i = 0; i < GetSize(bits_); i++) {
		auto it = rules.find(bits_[i]);
		if (it != rules.end())
			other->bits_[i] = it->second;
	}

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

	for (int i = GetSize(bits_) - 1; i >= 0; i--)
	{
		if (bits_[i].wire == NULL) continue;

		for (auto &pattern_chunk : pattern.chunks())
			if (bits_[i].wire == pattern_chunk.wire &&
				bits_[i].offset >= pattern_chunk.offset &&
				bits_[i].offset < pattern_chunk.offset + pattern_chunk.width) {
				bits_.erase(bits_.begin() + i);
				width_--;
				if (other != NULL) {
					other->bits_.erase(other->bits_.begin() + i);
					other->width_--;
				}
				break;
			}
	}

	check();
}

void RTLIL::SigSpec::remove(const pool<RTLIL::SigBit> &pattern)
{
	remove2(pattern, NULL);
}

void RTLIL::SigSpec::remove(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other) const
{
	RTLIL::SigSpec tmp = *this;
	tmp.remove2(pattern, other);
}

void RTLIL::SigSpec::remove2(const pool<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other)
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

	for (int i = GetSize(bits_) - 1; i >= 0; i--) {
		if (bits_[i].wire != NULL && pattern.count(bits_[i])) {
			bits_.erase(bits_.begin() + i);
			width_--;
			if (other != NULL) {
				other->bits_.erase(other->bits_.begin() + i);
				other->width_--;
			}
		}
	}

	check();
}

void RTLIL::SigSpec::remove2(const std::set<RTLIL::SigBit> &pattern, RTLIL::SigSpec *other)
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

	for (int i = GetSize(bits_) - 1; i >= 0; i--) {
		if (bits_[i].wire != NULL && pattern.count(bits_[i])) {
			bits_.erase(bits_.begin() + i);
			width_--;
			if (other != NULL) {
				other->bits_.erase(other->bits_.begin() + i);
				other->width_--;
			}
		}
	}

	check();
}

RTLIL::SigSpec RTLIL::SigSpec::extract(const RTLIL::SigSpec &pattern, const RTLIL::SigSpec *other) const
{
	if (other)
		cover("kernel.rtlil.sigspec.extract_other");
	else
		cover("kernel.rtlil.sigspec.extract");

	log_assert(other == NULL || width_ == other->width_);

	RTLIL::SigSpec ret;
	std::vector<RTLIL::SigBit> bits_match = to_sigbit_vector();

	for (auto& pattern_chunk : pattern.chunks()) {
		if (other) {
			std::vector<RTLIL::SigBit> bits_other = other->to_sigbit_vector();
			for (int i = 0; i < width_; i++)
				if (bits_match[i].wire &&
					bits_match[i].wire == pattern_chunk.wire &&
					bits_match[i].offset >= pattern_chunk.offset &&
					bits_match[i].offset < pattern_chunk.offset + pattern_chunk.width)
					ret.append_bit(bits_other[i]);
		} else {
			for (int i = 0; i < width_; i++)
				if (bits_match[i].wire &&
					bits_match[i].wire == pattern_chunk.wire &&
					bits_match[i].offset >= pattern_chunk.offset &&
					bits_match[i].offset < pattern_chunk.offset + pattern_chunk.width)
					ret.append_bit(bits_match[i]);
		}
	}

	ret.check();
	return ret;
}

RTLIL::SigSpec RTLIL::SigSpec::extract(const pool<RTLIL::SigBit> &pattern, const RTLIL::SigSpec *other) const
{
	if (other)
		cover("kernel.rtlil.sigspec.extract_other");
	else
		cover("kernel.rtlil.sigspec.extract");

	log_assert(other == NULL || width_ == other->width_);

	std::vector<RTLIL::SigBit> bits_match = to_sigbit_vector();
	RTLIL::SigSpec ret;

	if (other) {
		std::vector<RTLIL::SigBit> bits_other = other->to_sigbit_vector();
		for (int i = 0; i < width_; i++)
			if (bits_match[i].wire && pattern.count(bits_match[i]))
				ret.append_bit(bits_other[i]);
	} else {
		for (int i = 0; i < width_; i++)
			if (bits_match[i].wire && pattern.count(bits_match[i]))
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
		new_chunks.reserve(GetSize(chunks_));

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
				auto &this_data = my_last_c.data;
				auto &other_data = other_c.data;
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
					chunks_.back().data.push_back(bit.data);
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

void RTLIL::SigSpec::extend_u0(int width, bool is_signed)
{
	cover("kernel.rtlil.sigspec.extend_u0");

	pack();

	if (width_ > width)
		remove(width, width_ - width);

	if (width_ < width) {
		RTLIL::SigBit padding = width_ > 0 ? (*this)[width_ - 1] : RTLIL::State::Sx;
		if (!is_signed)
			padding = RTLIL::State::S0;
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
				log_assert(chunk.data.size() == (size_t)chunk.width);
			} else {
				if (i > 0 && chunks_[i-1].wire == chunk.wire)
					log_assert(chunk.offset != chunks_[i-1].offset + chunks_[i-1].width);
				log_assert(chunk.offset >= 0);
				log_assert(chunk.width >= 0);
				log_assert(chunk.offset + chunk.width <= chunk.wire->width);
				log_assert(chunk.data.size() == 0);
			}
			w += chunk.width;
		}
		log_assert(w == width_);
		log_assert(bits_.empty());
	}
	else
	{
		cover("kernel.rtlil.sigspec.check.unpacked");

		log_assert(width_ == GetSize(bits_));
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

	updhash();
	other.updhash();

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

	// Without this, SigSpec() == SigSpec(State::S0, 0) will fail
	//   since the RHS will contain one SigChunk of width 0 causing
	//   the size check below to fail
	if (width_ == 0)
		return true;

	pack();
	other.pack();

	if (chunks_.size() != other.chunks_.size())
		return false;

	updhash();
	other.updhash();

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
	return GetSize(chunks_) == 1 && chunks_[0].wire && chunks_[0].wire->width == width_;
}

bool RTLIL::SigSpec::is_chunk() const
{
	cover("kernel.rtlil.sigspec.is_chunk");

	pack();
	return GetSize(chunks_) == 1;
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

bool RTLIL::SigSpec::is_fully_zero() const
{
	cover("kernel.rtlil.sigspec.is_fully_zero");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
		if (it->width > 0 && it->wire != NULL)
			return false;
		for (size_t i = 0; i < it->data.size(); i++)
			if (it->data[i] != RTLIL::State::S0)
				return false;
	}
	return true;
}

bool RTLIL::SigSpec::is_fully_ones() const
{
	cover("kernel.rtlil.sigspec.is_fully_ones");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
		if (it->width > 0 && it->wire != NULL)
			return false;
		for (size_t i = 0; i < it->data.size(); i++)
			if (it->data[i] != RTLIL::State::S1)
				return false;
	}
	return true;
}

bool RTLIL::SigSpec::is_fully_def() const
{
	cover("kernel.rtlil.sigspec.is_fully_def");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++) {
		if (it->width > 0 && it->wire != NULL)
			return false;
		for (size_t i = 0; i < it->data.size(); i++)
			if (it->data[i] != RTLIL::State::S0 && it->data[i] != RTLIL::State::S1)
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
		for (size_t i = 0; i < it->data.size(); i++)
			if (it->data[i] != RTLIL::State::Sx && it->data[i] != RTLIL::State::Sz)
				return false;
	}
	return true;
}

bool RTLIL::SigSpec::has_const() const
{
	cover("kernel.rtlil.sigspec.has_const");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++)
		if (it->width > 0 && it->wire == NULL)
			return true;
	return false;
}

bool RTLIL::SigSpec::has_marked_bits() const
{
	cover("kernel.rtlil.sigspec.has_marked_bits");

	pack();
	for (auto it = chunks_.begin(); it != chunks_.end(); it++)
		if (it->width > 0 && it->wire == NULL) {
			for (size_t i = 0; i < it->data.size(); i++)
				if (it->data[i] == RTLIL::State::Sm)
					return true;
		}
	return false;
}

bool RTLIL::SigSpec::as_bool() const
{
	cover("kernel.rtlil.sigspec.as_bool");

	pack();
	log_assert(is_fully_const() && GetSize(chunks_) <= 1);
	if (width_)
		return RTLIL::Const(chunks_[0].data).as_bool();
	return false;
}

int RTLIL::SigSpec::as_int(bool is_signed) const
{
	cover("kernel.rtlil.sigspec.as_int");

	pack();
	log_assert(is_fully_const() && GetSize(chunks_) <= 1);
	if (width_)
		return RTLIL::Const(chunks_[0].data).as_int(is_signed);
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
			str += RTLIL::Const(chunk.data).as_string();
	}
	return str;
}

RTLIL::Const RTLIL::SigSpec::as_const() const
{
	cover("kernel.rtlil.sigspec.as_const");

	pack();
	log_assert(is_fully_const() && GetSize(chunks_) <= 1);
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

RTLIL::SigBit RTLIL::SigSpec::as_bit() const
{
	cover("kernel.rtlil.sigspec.as_bit");

	log_assert(width_ == 1);
	if (packed())
		return RTLIL::SigBit(*chunks_.begin());
	else
		return bits_[0];
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

pool<RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_pool() const
{
	cover("kernel.rtlil.sigspec.to_sigbit_pool");

	pack();
	pool<RTLIL::SigBit> sigbits;
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

std::map<RTLIL::SigBit, RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_map(const RTLIL::SigSpec &other) const
{
	cover("kernel.rtlil.sigspec.to_sigbit_map");

	unpack();
	other.unpack();

	log_assert(width_ == other.width_);

	std::map<RTLIL::SigBit, RTLIL::SigBit> new_map;
	for (int i = 0; i < width_; i++)
		new_map[bits_[i]] = other.bits_[i];

	return new_map;
}

dict<RTLIL::SigBit, RTLIL::SigBit> RTLIL::SigSpec::to_sigbit_dict(const RTLIL::SigSpec &other) const
{
	cover("kernel.rtlil.sigspec.to_sigbit_dict");

	unpack();
	other.unpack();

	log_assert(width_ == other.width_);

	dict<RTLIL::SigBit, RTLIL::SigBit> new_map;
	for (int i = 0; i < width_; i++)
		new_map[bits_[i]] = other.bits_[i];

	return new_map;
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

	AST::current_filename = "input";

	std::vector<std::string> tokens;
	sigspec_parse_split(tokens, str, ',');

	sig = RTLIL::SigSpec();
	for (int tokidx = int(tokens.size())-1; tokidx >= 0; tokidx--)
	{
		std::string netname = tokens[tokidx];
		std::string indices;

		if (netname.size() == 0)
			continue;

		if (('0' <= netname[0] && netname[0] <= '9') || netname[0] == '\'') {
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
				int a = atoi(index_tokens.at(0).c_str());
				if (a < 0 || a >= wire->width)
					return false;
				sig.append(RTLIL::SigSpec(wire, a));
			} else {
				cover("kernel.rtlil.sigspec.parse.part_sel");
				int a = atoi(index_tokens.at(0).c_str());
				int b = atoi(index_tokens.at(1).c_str());
				if (a > b) {
					int tmp = a;
					a = b, b = tmp;
				}
				if (a < 0 || a >= wire->width)
					return false;
				if (b < 0 || b >= wire->width)
					return false;
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
		long int val = strtol(p, &endptr, 10);
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

bool RTLIL::CaseRule::empty() const
{
	return actions.empty() && switches.empty();
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

bool RTLIL::SwitchRule::empty() const
{
	return cases.empty();
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

#ifdef WITH_PYTHON
RTLIL::Memory::~Memory()
{
	RTLIL::Memory::get_all_memorys()->erase(hashidx_);
}
static std::map<unsigned int, RTLIL::Memory*> all_memorys;
std::map<unsigned int, RTLIL::Memory*> *RTLIL::Memory::get_all_memorys(void)
{
	return &all_memorys;
}
#endif
YOSYS_NAMESPACE_END
