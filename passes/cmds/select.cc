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
#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include <string.h>
#include <errno.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using RTLIL::id2cstr;

static std::vector<RTLIL::Selection> work_stack;

static bool match_ids(RTLIL::IdString id, std::string pattern)
{
	if (id == pattern)
		return true;
	if (id.size() > 0 && id[0] == '\\' && id.substr(1) == pattern)
		return true;
	if (patmatch(pattern.c_str(), id.c_str()))
		return true;
	if (id.size() > 0 && id[0] == '\\' && patmatch(pattern.c_str(), id.substr(1).c_str()))
		return true;
	if (id.size() > 0 && id[0] == '$' && pattern.size() > 0 && pattern[0] == '$') {
		const char *p = id.c_str();
		const char *q = strrchr(p, '$');
		if (pattern == q)
			return true;
	}
	return false;
}

static bool match_attr_val(const RTLIL::Const &value, std::string pattern, char match_op)
{
	if (match_op == 0)
		return true;

	if ((value.flags & RTLIL::CONST_FLAG_STRING) == 0)
	{
		RTLIL::SigSpec sig_value;

		if (!RTLIL::SigSpec::parse(sig_value, NULL, pattern))
			return false;

		RTLIL::Const pattern_value = sig_value.as_const();

		if (match_op == '=')
			return value == pattern_value;
		if (match_op == '!')
			return value != pattern_value;
		if (match_op == '<')
			return value.as_int() < pattern_value.as_int();
		if (match_op == '>')
			return value.as_int() > pattern_value.as_int();
		if (match_op == '[')
			return value.as_int() <= pattern_value.as_int();
		if (match_op == ']')
			return value.as_int() >= pattern_value.as_int();
	}
	else
	{
		std::string value_str = value.decode_string();

		if (match_op == '=')
			if (patmatch(pattern.c_str(), value.decode_string().c_str()))
				return true;

		if (match_op == '=')
			return value_str == pattern;
		if (match_op == '!')
			return value_str != pattern;
		if (match_op == '<')
			return value_str < pattern;
		if (match_op == '>')
			return value_str > pattern;
		if (match_op == '[')
			return value_str <= pattern;
		if (match_op == ']')
			return value_str >= pattern;
	}

	log_abort();
}

static bool match_attr(const dict<RTLIL::IdString, RTLIL::Const> &attributes, std::string name_pat, std::string value_pat, char match_op)
{
	if (name_pat.find('*') != std::string::npos || name_pat.find('?') != std::string::npos || name_pat.find('[') != std::string::npos) {
		for (auto &it : attributes) {
			if (patmatch(name_pat.c_str(), it.first.c_str()) && match_attr_val(it.second, value_pat, match_op))
				return true;
			if (it.first.size() > 0 && it.first[0] == '\\' && patmatch(name_pat.c_str(), it.first.substr(1).c_str()) && match_attr_val(it.second, value_pat, match_op))
				return true;
		}
	} else {
		if (name_pat.size() > 0 && (name_pat[0] == '\\' || name_pat[0] == '$') && attributes.count(name_pat) && match_attr_val(attributes.at(name_pat), value_pat, match_op))
			return true;
		if (attributes.count("\\" + name_pat) && match_attr_val(attributes.at("\\" + name_pat), value_pat, match_op))
			return true;
	}
	return false;
}

static bool match_attr(const dict<RTLIL::IdString, RTLIL::Const> &attributes, std::string match_expr)
{
	size_t pos = match_expr.find_first_of("<!=>");

	if (pos != std::string::npos) {
		if (match_expr.substr(pos, 2) == "!=")
			return match_attr(attributes, match_expr.substr(0, pos), match_expr.substr(pos+2), '!');
		if (match_expr.substr(pos, 2) == "<=")
			return match_attr(attributes, match_expr.substr(0, pos), match_expr.substr(pos+2), '[');
		if (match_expr.substr(pos, 2) == ">=")
			return match_attr(attributes, match_expr.substr(0, pos), match_expr.substr(pos+2), ']');
		return match_attr(attributes, match_expr.substr(0, pos), match_expr.substr(pos+1), match_expr[pos]);
	}

	return match_attr(attributes, match_expr, std::string(), 0);
}

static void select_op_neg(RTLIL::Design *design, RTLIL::Selection &lhs)
{
	if (lhs.full_selection) {
		lhs.full_selection = false;
		lhs.selected_modules.clear();
		lhs.selected_members.clear();
		return;
	}

	if (lhs.selected_modules.size() == 0 && lhs.selected_members.size() == 0) {
		lhs.full_selection = true;
		return;
	}

	RTLIL::Selection new_sel(false);

	for (auto &mod_it : design->modules_)
	{
		if (lhs.selected_whole_module(mod_it.first))
			continue;
		if (!lhs.selected_module(mod_it.first)) {
			new_sel.selected_modules.insert(mod_it.first);
			continue;
		}

		RTLIL::Module *mod = mod_it.second;
		for (auto &it : mod->wires_)
			if (!lhs.selected_member(mod_it.first, it.first))
				new_sel.selected_members[mod->name].insert(it.first);
		for (auto &it : mod->memories)
			if (!lhs.selected_member(mod_it.first, it.first))
				new_sel.selected_members[mod->name].insert(it.first);
		for (auto &it : mod->cells_)
			if (!lhs.selected_member(mod_it.first, it.first))
				new_sel.selected_members[mod->name].insert(it.first);
		for (auto &it : mod->processes)
			if (!lhs.selected_member(mod_it.first, it.first))
				new_sel.selected_members[mod->name].insert(it.first);
	}

	lhs.selected_modules.swap(new_sel.selected_modules);
	lhs.selected_members.swap(new_sel.selected_members);
}

static int my_xorshift32_rng() {
	static uint32_t x32 = 314159265;
	x32 ^= x32 << 13;
	x32 ^= x32 >> 17;
	x32 ^= x32 << 5;
	return x32 & 0x0fffffff;
}

static void select_op_random(RTLIL::Design *design, RTLIL::Selection &lhs, int count)
{
	vector<pair<IdString, IdString>> objects;

	for (auto mod : design->modules())
	{
		if (!lhs.selected_module(mod->name))
			continue;

		for (auto cell : mod->cells()) {
			if (lhs.selected_member(mod->name, cell->name))
				objects.push_back(make_pair(mod->name, cell->name));
		}

		for (auto wire : mod->wires()) {
			if (lhs.selected_member(mod->name, wire->name))
				objects.push_back(make_pair(mod->name, wire->name));
		}
	}

	lhs = RTLIL::Selection(false);

	while (!objects.empty() && count-- > 0)
	{
		int idx = my_xorshift32_rng() % GetSize(objects);
		lhs.selected_members[objects[idx].first].insert(objects[idx].second);
		objects[idx] = objects.back();
		objects.pop_back();
	}

	lhs.optimize(design);
}

static void select_op_submod(RTLIL::Design *design, RTLIL::Selection &lhs)
{
	for (auto &mod_it : design->modules_)
	{
		if (lhs.selected_whole_module(mod_it.first))
		{
			for (auto &cell_it : mod_it.second->cells_)
			{
				if (design->modules_.count(cell_it.second->type) == 0)
					continue;
				lhs.selected_modules.insert(cell_it.second->type);
			}
		}
	}
}

static void select_op_cells_to_modules(RTLIL::Design *design, RTLIL::Selection &lhs)
{
	RTLIL::Selection new_sel(false);
	for (auto &mod_it : design->modules_)
		if (lhs.selected_module(mod_it.first))
			for (auto &cell_it : mod_it.second->cells_)
				if (lhs.selected_member(mod_it.first, cell_it.first) && design->modules_.count(cell_it.second->type))
					new_sel.selected_modules.insert(cell_it.second->type);
	lhs = new_sel;
}

static void select_op_module_to_cells(RTLIL::Design *design, RTLIL::Selection &lhs)
{
	RTLIL::Selection new_sel(false);
	for (auto &mod_it : design->modules_)
		for (auto &cell_it : mod_it.second->cells_)
			if (design->modules_.count(cell_it.second->type) && lhs.selected_whole_module(cell_it.second->type))
				new_sel.selected_members[mod_it.first].insert(cell_it.first);
	lhs = new_sel;
}

static void select_op_fullmod(RTLIL::Design *design, RTLIL::Selection &lhs)
{
	lhs.optimize(design);
	for (auto &it : lhs.selected_members)
		lhs.selected_modules.insert(it.first);
	lhs.selected_members.clear();
}

static void select_op_alias(RTLIL::Design *design, RTLIL::Selection &lhs)
{
	for (auto &mod_it : design->modules_)
	{
		if (lhs.selected_whole_module(mod_it.first))
			continue;
		if (!lhs.selected_module(mod_it.first))
			continue;

		SigMap sigmap(mod_it.second);
		SigPool selected_bits;

		for (auto &it : mod_it.second->wires_)
			if (lhs.selected_member(mod_it.first, it.first))
				selected_bits.add(sigmap(it.second));

		for (auto &it : mod_it.second->wires_)
			if (!lhs.selected_member(mod_it.first, it.first) && selected_bits.check_any(sigmap(it.second)))
				lhs.selected_members[mod_it.first].insert(it.first);
	}
}

static void select_op_union(RTLIL::Design*, RTLIL::Selection &lhs, const RTLIL::Selection &rhs)
{
	if (rhs.full_selection) {
		lhs.full_selection = true;
		lhs.selected_modules.clear();
		lhs.selected_members.clear();
		return;
	}

	if (lhs.full_selection)
		return;

	for (auto &it : rhs.selected_members)
		for (auto &it2 : it.second)
			lhs.selected_members[it.first].insert(it2);

	for (auto &it : rhs.selected_modules) {
		lhs.selected_modules.insert(it);
		lhs.selected_members.erase(it);
	}
}

static void select_op_diff(RTLIL::Design *design, RTLIL::Selection &lhs, const RTLIL::Selection &rhs)
{
	if (rhs.full_selection) {
		lhs.full_selection = false;
		lhs.selected_modules.clear();
		lhs.selected_members.clear();
		return;
	}

	if (lhs.full_selection) {
		if (!rhs.full_selection && rhs.selected_modules.size() == 0 && rhs.selected_members.size() == 0)
			return;
		lhs.full_selection = false;
		for (auto &it : design->modules_)
			lhs.selected_modules.insert(it.first);
	}

	for (auto &it : rhs.selected_modules) {
		lhs.selected_modules.erase(it);
		lhs.selected_members.erase(it);
	}

	for (auto &it : rhs.selected_members)
	{
		if (design->modules_.count(it.first) == 0)
			continue;

		RTLIL::Module *mod = design->modules_[it.first];

		if (lhs.selected_modules.count(mod->name) > 0)
		{
			for (auto &it : mod->wires_)
				lhs.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->memories)
				lhs.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->cells_)
				lhs.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->processes)
				lhs.selected_members[mod->name].insert(it.first);
			lhs.selected_modules.erase(mod->name);
		}

		if (lhs.selected_members.count(mod->name) == 0)
			continue;

		for (auto &it2 : it.second)
			lhs.selected_members[mod->name].erase(it2);
	}
}

static void select_op_intersect(RTLIL::Design *design, RTLIL::Selection &lhs, const RTLIL::Selection &rhs)
{
	if (rhs.full_selection)
		return;

	if (lhs.full_selection) {
		lhs.full_selection = false;
		for (auto &it : design->modules_)
			lhs.selected_modules.insert(it.first);
	}

	std::vector<RTLIL::IdString> del_list;

	for (auto &it : lhs.selected_modules)
		if (rhs.selected_modules.count(it) == 0) {
			if (rhs.selected_members.count(it) > 0)
				for (auto &it2 : rhs.selected_members.at(it))
					lhs.selected_members[it].insert(it2);
			del_list.push_back(it);
		}
	for (auto &it : del_list)
		lhs.selected_modules.erase(it);

	del_list.clear();
	for (auto &it : lhs.selected_members) {
		if (rhs.selected_modules.count(it.first) > 0)
			continue;
		if (rhs.selected_members.count(it.first) == 0) {
			del_list.push_back(it.first);
			continue;
		}
		std::vector<RTLIL::IdString> del_list2;
		for (auto &it2 : it.second)
			if (rhs.selected_members.at(it.first).count(it2) == 0)
				del_list2.push_back(it2);
		for (auto &it2 : del_list2)
			it.second.erase(it2);
		if (it.second.size() == 0)
			del_list.push_back(it.first);
	}
	for (auto &it : del_list)
		lhs.selected_members.erase(it);
}

namespace {
	struct expand_rule_t {
		char mode;
		std::set<RTLIL::IdString> cell_types, port_names;
	};
}

static int parse_comma_list(std::set<RTLIL::IdString> &tokens, std::string str, size_t pos, std::string stopchar)
{
	stopchar += ',';
	while (1) {
		size_t endpos = str.find_first_of(stopchar, pos);
		if (endpos == std::string::npos)
			endpos = str.size();
		if (endpos != pos)
			tokens.insert(RTLIL::escape_id(str.substr(pos, endpos-pos)));
		pos = endpos;
		if (pos == str.size() || str[pos] != ',')
			return pos;
		pos++;
	}
}

static int select_op_expand(RTLIL::Design *design, RTLIL::Selection &lhs, std::vector<expand_rule_t> &rules, std::set<RTLIL::IdString> &limits, int max_objects, char mode, CellTypes &ct, bool eval_only)
{
	int sel_objects = 0;
	bool is_input, is_output;
	for (auto &mod_it : design->modules_)
	{
		if (lhs.selected_whole_module(mod_it.first) || !lhs.selected_module(mod_it.first))
			continue;

		RTLIL::Module *mod = mod_it.second;
		std::set<RTLIL::Wire*> selected_wires;
		auto selected_members = lhs.selected_members[mod->name];

		for (auto &it : mod->wires_)
			if (lhs.selected_member(mod_it.first, it.first) && limits.count(it.first) == 0)
				selected_wires.insert(it.second);

		for (auto &conn : mod->connections())
		{
			std::vector<RTLIL::SigBit> conn_lhs = conn.first.to_sigbit_vector();
			std::vector<RTLIL::SigBit> conn_rhs = conn.second.to_sigbit_vector();

			for (size_t i = 0; i < conn_lhs.size(); i++) {
				if (conn_lhs[i].wire == NULL || conn_rhs[i].wire == NULL)
					continue;
				if (mode != 'i' && selected_wires.count(conn_rhs[i].wire) && selected_members.count(conn_lhs[i].wire->name) == 0)
					lhs.selected_members[mod->name].insert(conn_lhs[i].wire->name), sel_objects++, max_objects--;
				if (mode != 'o' && selected_wires.count(conn_lhs[i].wire) && selected_members.count(conn_rhs[i].wire->name) == 0)
					lhs.selected_members[mod->name].insert(conn_rhs[i].wire->name), sel_objects++, max_objects--;
			}
		}

		for (auto &cell : mod->cells_)
		for (auto &conn : cell.second->connections())
		{
			char last_mode = '-';
			if (eval_only && !yosys_celltypes.cell_evaluable(cell.second->type))
				goto exclude_match;
			for (auto &rule : rules) {
				last_mode = rule.mode;
				if (rule.cell_types.size() > 0 && rule.cell_types.count(cell.second->type) == 0)
					continue;
				if (rule.port_names.size() > 0 && rule.port_names.count(conn.first) == 0)
					continue;
				if (rule.mode == '+')
					goto include_match;
				else
					goto exclude_match;
			}
			if (last_mode == '+')
				goto exclude_match;
		include_match:
			is_input = mode == 'x' || ct.cell_input(cell.second->type, conn.first);
			is_output = mode == 'x' || ct.cell_output(cell.second->type, conn.first);
			for (auto &chunk : conn.second.chunks())
				if (chunk.wire != NULL) {
					if (max_objects != 0 && selected_wires.count(chunk.wire) > 0 && selected_members.count(cell.first) == 0)
						if (mode == 'x' || (mode == 'i' && is_output) || (mode == 'o' && is_input))
							lhs.selected_members[mod->name].insert(cell.first), sel_objects++, max_objects--;
					if (max_objects != 0 && selected_members.count(cell.first) > 0 && limits.count(cell.first) == 0 && selected_members.count(chunk.wire->name) == 0)
						if (mode == 'x' || (mode == 'i' && is_input) || (mode == 'o' && is_output))
							lhs.selected_members[mod->name].insert(chunk.wire->name), sel_objects++, max_objects--;
				}
		exclude_match:;
		}
	}

	return sel_objects;
}

static void select_op_expand(RTLIL::Design *design, std::string arg, char mode, bool eval_only)
{
	int pos = (mode == 'x' ? 2 : 3) + (eval_only ? 1 : 0);
	int levels = 1, rem_objects = -1;
	std::vector<expand_rule_t> rules;
	std::set<RTLIL::IdString> limits;

	CellTypes ct;

	if (mode != 'x')
		ct.setup(design);

	if (pos < int(arg.size()) && arg[pos] == '*') {
		levels = 1000000;
		pos++;
	} else
	if (pos < int(arg.size()) && '0' <= arg[pos] && arg[pos] <= '9') {
		size_t endpos = arg.find_first_not_of("0123456789", pos);
		if (endpos == std::string::npos)
			endpos = arg.size();
		levels = atoi(arg.substr(pos, endpos-pos).c_str());
		pos = endpos;
	}

	if (pos < int(arg.size()) && arg[pos] == '.') {
		size_t endpos = arg.find_first_not_of("0123456789", ++pos);
		if (endpos == std::string::npos)
			endpos = arg.size();
		if (int(endpos) > pos)
			rem_objects = atoi(arg.substr(pos, endpos-pos).c_str());
		pos = endpos;
	}

	while (pos < int(arg.size())) {
		if (arg[pos] != ':' || pos+1 == int(arg.size()))
			log_cmd_error("Syntax error in expand operator '%s'.\n", arg.c_str());
		pos++;
		if (arg[pos] == '+' || arg[pos] == '-') {
			expand_rule_t rule;
			rule.mode = arg[pos++];
			pos = parse_comma_list(rule.cell_types, arg, pos, "[:");
			if (pos < int(arg.size()) && arg[pos] == '[') {
				pos = parse_comma_list(rule.port_names, arg, pos+1, "]:");
				if (pos < int(arg.size()) && arg[pos] == ']')
					pos++;
			}
			rules.push_back(rule);
		} else {
			size_t endpos = arg.find(':', pos);
			if (endpos == std::string::npos)
				endpos = arg.size();
			if (int(endpos) > pos) {
				std::string str = arg.substr(pos, endpos-pos);
				if (str[0] == '@') {
					str = RTLIL::escape_id(str.substr(1));
					if (design->selection_vars.count(str) > 0) {
						for (auto i1 : design->selection_vars.at(str).selected_members)
						for (auto i2 : i1.second)
							limits.insert(i2);
					} else
						log_cmd_error("Selection %s is not defined!\n", RTLIL::unescape_id(str).c_str());
				} else
					limits.insert(RTLIL::escape_id(str));
			}
			pos = endpos;
		}
	}

#if 0
	log("expand by %d levels (max. %d objects):\n", levels, rem_objects);
	for (auto &rule : rules) {
		log("  rule (%c):\n", rule.mode);
		if (rule.cell_types.size() > 0) {
			log("    cell types:");
			for (auto &it : rule.cell_types)
				log(" %s", it.c_str());
			log("\n");
		}
		if (rule.port_names.size() > 0) {
			log("    port names:");
			for (auto &it : rule.port_names)
				log(" %s", it.c_str());
			log("\n");
		}
	}
	if (limits.size() > 0) {
		log("  limits:");
		for (auto &it : limits)
			log(" %s", it.c_str());
		log("\n");
	}
#endif

	while (levels-- > 0 && rem_objects != 0) {
		int num_objects = select_op_expand(design, work_stack.back(), rules, limits, rem_objects, mode, ct, eval_only);
		if (num_objects == 0)
			break;
		rem_objects -= num_objects;
	}

	if (rem_objects == 0)
		log_warning("reached configured limit at `%s'.\n", arg.c_str());
}

static void select_filter_active_mod(RTLIL::Design *design, RTLIL::Selection &sel)
{
	if (design->selected_active_module.empty())
		return;

	if (sel.full_selection) {
		sel.full_selection = false;
		sel.selected_modules.clear();
		sel.selected_members.clear();
		sel.selected_modules.insert(design->selected_active_module);
		return;
	}

	std::vector<RTLIL::IdString> del_list;
	for (auto mod_name : sel.selected_modules)
		if (mod_name != design->selected_active_module)
			del_list.push_back(mod_name);
	for (auto &it : sel.selected_members)
		if (it.first != design->selected_active_module)
			del_list.push_back(it.first);
	for (auto mod_name : del_list) {
		sel.selected_modules.erase(mod_name);
		sel.selected_members.erase(mod_name);
	}
}

static void select_stmt(RTLIL::Design *design, std::string arg)
{
	std::string arg_mod, arg_memb;

	if (arg.size() == 0)
		return;

	if (arg[0] == '%') {
		if (arg == "%") {
			if (design->selection_stack.size() > 0)
				work_stack.push_back(design->selection_stack.back());
		} else
		if (arg == "%%") {
			while (work_stack.size() > 1) {
				select_op_union(design, work_stack.front(), work_stack.back());
				work_stack.pop_back();
			}
		} else
		if (arg == "%n") {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%n.\n");
			select_op_neg(design, work_stack[work_stack.size()-1]);
		} else
		if (arg == "%u") {
			if (work_stack.size() < 2)
				log_cmd_error("Must have at least two elements on the stack for operator %%u.\n");
			select_op_union(design, work_stack[work_stack.size()-2], work_stack[work_stack.size()-1]);
			work_stack.pop_back();
		} else
		if (arg == "%d") {
			if (work_stack.size() < 2)
				log_cmd_error("Must have at least two elements on the stack for operator %%d.\n");
			select_op_diff(design, work_stack[work_stack.size()-2], work_stack[work_stack.size()-1]);
			work_stack.pop_back();
		} else
		if (arg == "%D") {
			if (work_stack.size() < 2)
				log_cmd_error("Must have at least two elements on the stack for operator %%d.\n");
			select_op_diff(design, work_stack[work_stack.size()-1], work_stack[work_stack.size()-2]);
			work_stack[work_stack.size()-2] = work_stack[work_stack.size()-1];
			work_stack.pop_back();
		} else
		if (arg == "%i") {
			if (work_stack.size() < 2)
				log_cmd_error("Must have at least two elements on the stack for operator %%i.\n");
			select_op_intersect(design, work_stack[work_stack.size()-2], work_stack[work_stack.size()-1]);
			work_stack.pop_back();
		} else
		if (arg.size() >= 2 && arg[0] == '%' && arg[1] == 'R') {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%R.\n");
			int count = arg.size() > 2 ? atoi(arg.c_str() + 2) : 1;
			select_op_random(design, work_stack[work_stack.size()-1], count);
		} else
		if (arg == "%s") {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%s.\n");
			select_op_submod(design, work_stack[work_stack.size()-1]);
		} else
		if (arg == "%M") {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%M.\n");
			select_op_cells_to_modules(design, work_stack[work_stack.size()-1]);
		} else
		if (arg == "%C") {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%M.\n");
			select_op_module_to_cells(design, work_stack[work_stack.size()-1]);
		} else
		if (arg == "%c") {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%c.\n");
			work_stack.push_back(work_stack.back());
		} else
		if (arg == "%m") {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%m.\n");
			select_op_fullmod(design, work_stack[work_stack.size()-1]);
		} else
		if (arg == "%a") {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%a.\n");
			select_op_alias(design, work_stack[work_stack.size()-1]);
		} else
		if (arg == "%x" || (arg.size() > 2 && arg.substr(0, 2) == "%x" && (arg[2] == ':' || arg[2] == '*' || arg[2] == '.' || ('0' <= arg[2] && arg[2] <= '9')))) {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%x.\n");
			select_op_expand(design, arg, 'x', false);
		} else
		if (arg == "%ci" || (arg.size() > 3 && arg.substr(0, 3) == "%ci" && (arg[3] == ':' || arg[3] == '*' || arg[3] == '.' || ('0' <= arg[3] && arg[3] <= '9')))) {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%ci.\n");
			select_op_expand(design, arg, 'i', false);
		} else
		if (arg == "%co" || (arg.size() > 3 && arg.substr(0, 3) == "%co" && (arg[3] == ':' || arg[3] == '*' || arg[3] == '.' || ('0' <= arg[3] && arg[3] <= '9')))) {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%co.\n");
			select_op_expand(design, arg, 'o', false);
		} else
		if (arg == "%xe" || (arg.size() > 3 && arg.substr(0, 3) == "%xe" && (arg[3] == ':' || arg[3] == '*' || arg[3] == '.' || ('0' <= arg[3] && arg[3] <= '9')))) {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%xe.\n");
			select_op_expand(design, arg, 'x', true);
		} else
		if (arg == "%cie" || (arg.size() > 4 && arg.substr(0, 4) == "%cie" && (arg[4] == ':' || arg[4] == '*' || arg[4] == '.' || ('0' <= arg[4] && arg[4] <= '9')))) {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%cie.\n");
			select_op_expand(design, arg, 'i', true);
		} else
		if (arg == "%coe" || (arg.size() > 4 && arg.substr(0, 4) == "%coe" && (arg[4] == ':' || arg[4] == '*' || arg[4] == '.' || ('0' <= arg[4] && arg[4] <= '9')))) {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on the stack for operator %%coe.\n");
			select_op_expand(design, arg, 'o', true);
		} else
			log_cmd_error("Unknown selection operator '%s'.\n", arg.c_str());
		if (work_stack.size() >= 1)
			select_filter_active_mod(design, work_stack.back());
		return;
	}

	if (arg[0] == '@') {
		std::string set_name = RTLIL::escape_id(arg.substr(1));
		if (design->selection_vars.count(set_name) > 0)
			work_stack.push_back(design->selection_vars[set_name]);
		else
			log_cmd_error("Selection @%s is not defined!\n", RTLIL::unescape_id(set_name).c_str());
		select_filter_active_mod(design, work_stack.back());
		return;
	}

	if (!design->selected_active_module.empty()) {
		arg_mod = design->selected_active_module;
		arg_memb = arg;
	} else {
		size_t pos = arg.find('/');
		if (pos == std::string::npos) {
			if (arg.find(':') == std::string::npos || arg.substr(0, 1) == "A")
				arg_mod = arg;
			else
				arg_mod = "*", arg_memb = arg;
		} else {
			arg_mod = arg.substr(0, pos);
			arg_memb = arg.substr(pos+1);
		}
	}

	work_stack.push_back(RTLIL::Selection());
	RTLIL::Selection &sel = work_stack.back();

	if (arg == "*" && arg_mod == "*") {
		select_filter_active_mod(design, work_stack.back());
		return;
	}

	sel.full_selection = false;
	for (auto &mod_it : design->modules_)
	{
		if (arg_mod.substr(0, 2) == "A:") {
			if (!match_attr(mod_it.second->attributes, arg_mod.substr(2)))
				continue;
		} else
		if (!match_ids(mod_it.first, arg_mod))
			continue;

		if (arg_memb == "") {
			sel.selected_modules.insert(mod_it.first);
			continue;
		}

		RTLIL::Module *mod = mod_it.second;
		if (arg_memb.substr(0, 2) == "w:") {
			for (auto &it : mod->wires_)
				if (match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "i:") {
			for (auto &it : mod->wires_)
				if (it.second->port_input && match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "o:") {
			for (auto &it : mod->wires_)
				if (it.second->port_output && match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "x:") {
			for (auto &it : mod->wires_)
				if ((it.second->port_input || it.second->port_output) && match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "s:") {
			size_t delim = arg_memb.substr(2).find(':');
			if (delim == std::string::npos) {
				int width = atoi(arg_memb.substr(2).c_str());
				for (auto &it : mod->wires_)
					if (it.second->width == width)
						sel.selected_members[mod->name].insert(it.first);
			} else {
				std::string min_str = arg_memb.substr(2, delim);
				std::string max_str = arg_memb.substr(2+delim+1);
				int min_width = min_str.empty() ? 0 : atoi(min_str.c_str());
				int max_width = max_str.empty() ? -1 : atoi(max_str.c_str());
				for (auto &it : mod->wires_)
					if (min_width <= it.second->width && (it.second->width <= max_width || max_width == -1))
						sel.selected_members[mod->name].insert(it.first);
			}
		} else
		if (arg_memb.substr(0, 2) == "m:") {
			for (auto &it : mod->memories)
				if (match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "c:") {
			for (auto &it : mod->cells_)
				if (match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "t:") {
			for (auto &it : mod->cells_)
				if (match_ids(it.second->type, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "p:") {
			for (auto &it : mod->processes)
				if (match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "a:") {
			for (auto &it : mod->wires_)
				if (match_attr(it.second->attributes, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->memories)
				if (match_attr(it.second->attributes, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->cells_)
				if (match_attr(it.second->attributes, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->processes)
				if (match_attr(it.second->attributes, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "r:") {
			for (auto &it : mod->cells_)
				if (match_attr(it.second->parameters, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else {
			if (arg_memb.substr(0, 2) == "n:")
				arg_memb = arg_memb.substr(2);
			for (auto &it : mod->wires_)
				if (match_ids(it.first, arg_memb))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->memories)
				if (match_ids(it.first, arg_memb))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->cells_)
				if (match_ids(it.first, arg_memb))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->processes)
				if (match_ids(it.first, arg_memb))
					sel.selected_members[mod->name].insert(it.first);
		}
	}

	select_filter_active_mod(design, work_stack.back());
}

PRIVATE_NAMESPACE_END
YOSYS_NAMESPACE_BEGIN

// used in kernel/register.cc and maybe other locations, extern decl. in register.h
void handle_extra_select_args(Pass *pass, vector<string> args, size_t argidx, size_t args_size, RTLIL::Design *design)
{
	work_stack.clear();
	for (; argidx < args_size; argidx++) {
		if (args[argidx].substr(0, 1) == "-") {
			if (pass != NULL)
				pass->cmd_error(args, argidx, "Unexpected option in selection arguments.");
			else
				log_cmd_error("Unexpected option in selection arguments.");
		}
		select_stmt(design, args[argidx]);
	}
	while (work_stack.size() > 1) {
		select_op_union(design, work_stack.front(), work_stack.back());
		work_stack.pop_back();
	}
	if (work_stack.empty())
		design->selection_stack.push_back(RTLIL::Selection(false));
	else
		design->selection_stack.push_back(work_stack.back());
}

// extern decl. in register.h
RTLIL::Selection eval_select_args(const vector<string> &args, RTLIL::Design *design)
{
	work_stack.clear();
	for (auto &arg : args)
		select_stmt(design, arg);
	while (work_stack.size() > 1) {
		select_op_union(design, work_stack.front(), work_stack.back());
		work_stack.pop_back();
	}
	if (work_stack.empty())
		return RTLIL::Selection(false);
	return work_stack.back();
}

// extern decl. in register.h
void eval_select_op(vector<RTLIL::Selection> &work, const string &op, RTLIL::Design *design)
{
	work_stack.swap(work);
	select_stmt(design, op);
	work_stack.swap(work);
}

YOSYS_NAMESPACE_END
PRIVATE_NAMESPACE_BEGIN

struct SelectPass : public Pass {
	SelectPass() : Pass("select", "modify and view the list of selected objects") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    select [ -add | -del | -set <name> ] {-read <filename> | <selection>}\n");
		log("    select [ <assert_option> ] {-read <filename> | <selection>}\n");
		log("    select [ -list | -write <filename> | -count | -clear ]\n");
		log("    select -module <modname>\n");
		log("\n");
		log("Most commands use the list of currently selected objects to determine which part\n");
		log("of the design to operate on. This command can be used to modify and view this\n");
		log("list of selected objects.\n");
		log("\n");
		log("Note that many commands support an optional [selection] argument that can be\n");
		log("used to override the global selection for the command. The syntax of this\n");
		log("optional argument is identical to the syntax of the <selection> argument\n");
		log("described here.\n");
		log("\n");
		log("    -add, -del\n");
		log("        add or remove the given objects to the current selection.\n");
		log("        without this options the current selection is replaced.\n");
		log("\n");
		log("    -set <name>\n");
		log("        do not modify the current selection. instead save the new selection\n");
		log("        under the given name (see @<name> below). to save the current selection,\n");
		log("        use \"select -set <name> %%\"\n");
		log("\n");
		log("    -assert-none\n");
		log("        do not modify the current selection. instead assert that the given\n");
		log("        selection is empty. i.e. produce an error if any object matching the\n");
		log("        selection is found.\n");
		log("\n");
		log("    -assert-any\n");
		log("        do not modify the current selection. instead assert that the given\n");
		log("        selection is non-empty. i.e. produce an error if no object matching\n");
		log("        the selection is found.\n");
		log("\n");
		log("    -assert-count N\n");
		log("        do not modify the current selection. instead assert that the given\n");
		log("        selection contains exactly N objects.\n");
		log("\n");
		log("    -assert-max N\n");
		log("        do not modify the current selection. instead assert that the given\n");
		log("        selection contains less than or exactly N objects.\n");
		log("\n");
		log("    -assert-min N\n");
		log("        do not modify the current selection. instead assert that the given\n");
		log("        selection contains at least N objects.\n");
		log("\n");
		log("    -list\n");
		log("        list all objects in the current selection\n");
		log("\n");
		log("    -write <filename>\n");
		log("        like -list but write the output to the specified file\n");
		log("\n");
		log("    -read <filename>\n");
		log("        read the specified file (written by -write)\n");
		log("\n");
		log("    -count\n");
		log("        count all objects in the current selection\n");
		log("\n");
		log("    -clear\n");
		log("        clear the current selection. this effectively selects the whole\n");
		log("        design. it also resets the selected module (see -module). use the\n");
		log("        command 'select *' to select everything but stay in the current module.\n");
		log("\n");
		log("    -none\n");
		log("        create an empty selection. the current module is unchanged.\n");
		log("\n");
		log("    -module <modname>\n");
		log("        limit the current scope to the specified module.\n");
		log("        the difference between this and simply selecting the module\n");
		log("        is that all object names are interpreted relative to this\n");
		log("        module after this command until the selection is cleared again.\n");
		log("\n");
		log("When this command is called without an argument, the current selection\n");
		log("is displayed in a compact form (i.e. only the module name when a whole module\n");
		log("is selected).\n");
		log("\n");
		log("The <selection> argument itself is a series of commands for a simple stack\n");
		log("machine. Each element on the stack represents a set of selected objects.\n");
		log("After this commands have been executed, the union of all remaining sets\n");
		log("on the stack is computed and used as selection for the command.\n");
		log("\n");
		log("Pushing (selecting) object when not in -module mode:\n");
		log("\n");
		log("    <mod_pattern>\n");
		log("        select the specified module(s)\n");
		log("\n");
		log("    <mod_pattern>/<obj_pattern>\n");
		log("        select the specified object(s) from the module(s)\n");
		log("\n");
		log("Pushing (selecting) object when in -module mode:\n");
		log("\n");
		log("    <obj_pattern>\n");
		log("        select the specified object(s) from the current module\n");
		log("\n");
		log("A <mod_pattern> can be a module name, wildcard expression (*, ?, [..])\n");
		log("matching module names, or one of the following:\n");
		log("\n");
		log("    A:<pattern>, A:<pattern>=<pattern>\n");
		log("        all modules with an attribute matching the given pattern\n");
		log("        in addition to = also <, <=, >=, and > are supported\n");
		log("\n");
		log("An <obj_pattern> can be an object name, wildcard expression, or one of\n");
		log("the following:\n");
		log("\n");
		log("    w:<pattern>\n");
		log("        all wires with a name matching the given wildcard pattern\n");
		log("\n");
		log("    i:<pattern>, o:<pattern>, x:<pattern>\n");
		log("        all inputs (i:), outputs (o:) or any ports (x:) with matching names\n");
		log("\n");
		log("    s:<size>, s:<min>:<max>\n");
		log("        all wires with a matching width\n");
		log("\n");
		log("    m:<pattern>\n");
		log("        all memories with a name matching the given pattern\n");
		log("\n");
		log("    c:<pattern>\n");
		log("        all cells with a name matching the given pattern\n");
		log("\n");
		log("    t:<pattern>\n");
		log("        all cells with a type matching the given pattern\n");
		log("\n");
		log("    p:<pattern>\n");
		log("        all processes with a name matching the given pattern\n");
		log("\n");
		log("    a:<pattern>\n");
		log("        all objects with an attribute name matching the given pattern\n");
		log("\n");
		log("    a:<pattern>=<pattern>\n");
		log("        all objects with a matching attribute name-value-pair.\n");
		log("        in addition to = also <, <=, >=, and > are supported\n");
		log("\n");
		log("    r:<pattern>, r:<pattern>=<pattern>\n");
		log("        cells with matching parameters. also with <, <=, >= and >.\n");
		log("\n");
		log("    n:<pattern>\n");
		log("        all objects with a name matching the given pattern\n");
		log("        (i.e. 'n:' is optional as it is the default matching rule)\n");
		log("\n");
		log("    @<name>\n");
		log("        push the selection saved prior with 'select -set <name> ...'\n");
		log("\n");
		log("The following actions can be performed on the top sets on the stack:\n");
		log("\n");
		log("    %%\n");
		log("        push a copy of the current selection to the stack\n");
		log("\n");
		log("    %%%%\n");
		log("        replace the stack with a union of all elements on it\n");
		log("\n");
		log("    %%n\n");
		log("        replace top set with its invert\n");
		log("\n");
		log("    %%u\n");
		log("        replace the two top sets on the stack with their union\n");
		log("\n");
		log("    %%i\n");
		log("        replace the two top sets on the stack with their intersection\n");
		log("\n");
		log("    %%d\n");
		log("        pop the top set from the stack and subtract it from the new top\n");
		log("\n");
		log("    %%D\n");
		log("        like %%d but swap the roles of two top sets on the stack\n");
		log("\n");
		log("    %%c\n");
		log("        create a copy of the top set from the stack and push it\n");
		log("\n");
		log("    %%x[<num1>|*][.<num2>][:<rule>[:<rule>..]]\n");
		log("        expand top set <num1> num times according to the specified rules.\n");
		log("        (i.e. select all cells connected to selected wires and select all\n");
		log("        wires connected to selected cells) The rules specify which cell\n");
		log("        ports to use for this. the syntax for a rule is a '-' for exclusion\n");
		log("        and a '+' for inclusion, followed by an optional comma separated\n");
		log("        list of cell types followed by an optional comma separated list of\n");
		log("        cell ports in square brackets. a rule can also be just a cell or wire\n");
		log("        name that limits the expansion (is included but does not go beyond).\n");
		log("        select at most <num2> objects. a warning message is printed when this\n");
		log("        limit is reached. When '*' is used instead of <num1> then the process\n");
		log("        is repeated until no further object are selected.\n");
		log("\n");
		log("    %%ci[<num1>|*][.<num2>][:<rule>[:<rule>..]]\n");
		log("    %%co[<num1>|*][.<num2>][:<rule>[:<rule>..]]\n");
		log("        similar to %%x, but only select input (%%ci) or output cones (%%co)\n");
		log("\n");
		log("    %%xe[...] %%cie[...] %%coe\n");
		log("        like %%x, %%ci, and %%co but only consider combinatorial cells\n");
		log("\n");
		log("    %%a\n");
		log("        expand top set by selecting all wires that are (at least in part)\n");
		log("        aliases for selected wires.\n");
		log("\n");
		log("    %%s\n");
		log("        expand top set by adding all modules that implement cells in selected\n");
		log("        modules\n");
		log("\n");
		log("    %%m\n");
		log("        expand top set by selecting all modules that contain selected objects\n");
		log("\n");
		log("    %%M\n");
		log("        select modules that implement selected cells\n");
		log("\n");
		log("    %%C\n");
		log("        select cells that implement selected modules\n");
		log("\n");
		log("    %%R[<num>]\n");
		log("        select <num> random objects from top selection (default 1)\n");
		log("\n");
		log("Example: the following command selects all wires that are connected to a\n");
		log("'GATE' input of a 'SWITCH' cell:\n");
		log("\n");
		log("    select */t:SWITCH %%x:+[GATE] */t:SWITCH %%d\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool add_mode = false;
		bool del_mode = false;
		bool clear_mode = false;
		bool none_mode = false;
		bool list_mode = false;
		bool count_mode = false;
		bool got_module = false;
		bool assert_none = false;
		bool assert_any = false;
		int assert_count = -1;
		int assert_max = -1;
		int assert_min = -1;
		std::string write_file, read_file;
		std::string set_name, sel_str;

		work_stack.clear();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-add") {
				add_mode = true;
				continue;
			}
			if (arg == "-del") {
				del_mode = true;
				continue;
			}
			if (arg == "-assert-none") {
				assert_none = true;
				continue;
			}
			if (arg == "-assert-any") {
				assert_any = true;
				continue;
			}
			if (arg == "-assert-count" && argidx+1 < args.size()) {
				assert_count = atoi(args[++argidx].c_str());
				continue;
			}
			if (arg == "-assert-max" && argidx+1 < args.size()) {
				assert_max = atoi(args[++argidx].c_str());
				continue;
			}
			if (arg == "-assert-min" && argidx+1 < args.size()) {
				assert_min = atoi(args[++argidx].c_str());
				continue;
			}
			if (arg == "-clear") {
				clear_mode = true;
				continue;
			}
			if (arg == "-none") {
				none_mode = true;
				continue;
			}
			if (arg == "-list") {
				list_mode = true;
				continue;
			}
			if (arg == "-write" && argidx+1 < args.size()) {
				write_file = args[++argidx];
				continue;
			}
			if (arg == "-read" && argidx+1 < args.size()) {
				read_file = args[++argidx];
				continue;
			}
			if (arg == "-count") {
				count_mode = true;
				continue;
			}
			if (arg == "-module" && argidx+1 < args.size()) {
				RTLIL::IdString mod_name = RTLIL::escape_id(args[++argidx]);
				if (design->modules_.count(mod_name) == 0)
					log_cmd_error("No such module: %s\n", id2cstr(mod_name));
				design->selected_active_module = mod_name.str();
				got_module = true;
				continue;
			}
			if (arg == "-set" && argidx+1 < args.size()) {
				set_name = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (arg.size() > 0 && arg[0] == '-')
				log_cmd_error("Unknown option %s.\n", arg.c_str());
			select_stmt(design, arg);
			sel_str += " " + arg;
		}

		if (!read_file.empty())
		{
			if (!sel_str.empty())
				log_cmd_error("Option -read can not be combined with a selection expression.\n");

			std::ifstream f(read_file);
			if (f.fail())
				log_error("Can't open '%s' for reading: %s\n", read_file.c_str(), strerror(errno));

			RTLIL::Selection sel(false);
			string line;

			while (std::getline(f, line)) {
				size_t slash_pos = line.find('/');
				if (slash_pos == string::npos) {
					log_warning("Ignoring line without slash in 'select -read': %s\n", line.c_str());
					continue;
				}
				IdString mod_name = RTLIL::escape_id(line.substr(0, slash_pos));
				IdString obj_name = RTLIL::escape_id(line.substr(slash_pos+1));
				sel.selected_members[mod_name].insert(obj_name);
			}

			select_filter_active_mod(design, sel);
			sel.optimize(design);
			work_stack.push_back(sel);
		}

		if (clear_mode && args.size() != 2)
			log_cmd_error("Option -clear can not be combined with any other options.\n");

		if (none_mode && args.size() != 2)
			log_cmd_error("Option -none can not be combined with any other options.\n");

		if (add_mode + del_mode + assert_none + assert_any + (assert_count >= 0) + (assert_max >= 0) + (assert_min >= 0) > 1)
			log_cmd_error("Options -add, -del, -assert-none, -assert-any, assert-count, -assert-max or -assert-min can not be combined.\n");

		if ((list_mode || !write_file.empty() || count_mode) && (add_mode || del_mode || assert_none || assert_any || assert_count >= 0 || assert_max >= 0 || assert_min >= 0))
			log_cmd_error("Options -list, -write and -count can not be combined with -add, -del, -assert-none, -assert-any, assert-count, -assert-max, or -assert-min.\n");

		if (!set_name.empty() && (list_mode || !write_file.empty() || count_mode || add_mode || del_mode || assert_none || assert_any || assert_count >= 0 || assert_max >= 0 || assert_min >= 0))
			log_cmd_error("Option -set can not be combined with -list, -write, -count, -add, -del, -assert-none, -assert-any, -assert-count, -assert-max, or -assert-min.\n");

		if (work_stack.size() == 0 && got_module) {
			RTLIL::Selection sel;
			select_filter_active_mod(design, sel);
			work_stack.push_back(sel);
		}

		while (work_stack.size() > 1) {
			select_op_union(design, work_stack.front(), work_stack.back());
			work_stack.pop_back();
		}

		log_assert(design->selection_stack.size() > 0);

		if (clear_mode) {
			design->selection_stack.back() = RTLIL::Selection(true);
			design->selected_active_module = std::string();
			return;
		}

		if (none_mode) {
			design->selection_stack.back() = RTLIL::Selection(false);
			return;
		}

		if (list_mode || count_mode || !write_file.empty())
		{
		#define LOG_OBJECT(...) { if (list_mode) log(__VA_ARGS__); if (f != NULL) fprintf(f, __VA_ARGS__); total_count++; }
			int total_count = 0;
			FILE *f = NULL;
			if (!write_file.empty()) {
				f = fopen(write_file.c_str(), "w");
				if (f == NULL)
					log_error("Can't open '%s' for writing: %s\n", write_file.c_str(), strerror(errno));
			}
			RTLIL::Selection *sel = &design->selection_stack.back();
			if (work_stack.size() > 0)
				sel = &work_stack.back();
			sel->optimize(design);
			for (auto mod_it : design->modules_)
			{
				if (sel->selected_whole_module(mod_it.first) && list_mode)
					log("%s\n", id2cstr(mod_it.first));
				if (sel->selected_module(mod_it.first)) {
					for (auto &it : mod_it.second->wires_)
						if (sel->selected_member(mod_it.first, it.first))
							LOG_OBJECT("%s/%s\n", id2cstr(mod_it.first), id2cstr(it.first))
					for (auto &it : mod_it.second->memories)
						if (sel->selected_member(mod_it.first, it.first))
							LOG_OBJECT("%s/%s\n", id2cstr(mod_it.first), id2cstr(it.first))
					for (auto &it : mod_it.second->cells_)
						if (sel->selected_member(mod_it.first, it.first))
							LOG_OBJECT("%s/%s\n", id2cstr(mod_it.first), id2cstr(it.first))
					for (auto &it : mod_it.second->processes)
						if (sel->selected_member(mod_it.first, it.first))
							LOG_OBJECT("%s/%s\n", id2cstr(mod_it.first), id2cstr(it.first))
				}
			}
			if (count_mode)
				log("%d objects.\n", total_count);
			if (f != NULL)
				fclose(f);
		#undef LOG_OBJECT
			return;
		}

		if (add_mode)
		{
			if (work_stack.size() == 0)
				log_cmd_error("Nothing to add to selection.\n");
			select_op_union(design, design->selection_stack.back(), work_stack.back());
			design->selection_stack.back().optimize(design);
			return;
		}

		if (del_mode)
		{
			if (work_stack.size() == 0)
				log_cmd_error("Nothing to delete from selection.\n");
			select_op_diff(design, design->selection_stack.back(), work_stack.back());
			design->selection_stack.back().optimize(design);
			return;
		}

		if (assert_none)
		{
			if (work_stack.size() == 0)
				log_cmd_error("No selection to check.\n");
			work_stack.back().optimize(design);
			if (!work_stack.back().empty())
				log_error("Assertion failed: selection is not empty:%s\n", sel_str.c_str());
			return;
		}

		if (assert_any)
		{
			if (work_stack.size() == 0)
				log_cmd_error("No selection to check.\n");
			work_stack.back().optimize(design);
			if (work_stack.back().empty())
				log_error("Assertion failed: selection is empty:%s\n", sel_str.c_str());
			return;
		}

		if (assert_count >= 0 || assert_max >= 0 || assert_min >= 0)
		{
			int total_count = 0;
			if (work_stack.size() == 0)
				log_cmd_error("No selection to check.\n");
			RTLIL::Selection *sel = &work_stack.back();
			sel->optimize(design);
			for (auto mod_it : design->modules_)
				if (sel->selected_module(mod_it.first)) {
					for (auto &it : mod_it.second->wires_)
						if (sel->selected_member(mod_it.first, it.first))
							total_count++;
					for (auto &it : mod_it.second->memories)
						if (sel->selected_member(mod_it.first, it.first))
							total_count++;
					for (auto &it : mod_it.second->cells_)
						if (sel->selected_member(mod_it.first, it.first))
							total_count++;
					for (auto &it : mod_it.second->processes)
						if (sel->selected_member(mod_it.first, it.first))
							total_count++;
				}
			if (assert_count >= 0 && assert_count != total_count)
				log_error("Assertion failed: selection contains %d elements instead of the asserted %d:%s\n",
						total_count, assert_count, sel_str.c_str());
			if (assert_max >= 0 && assert_max < total_count)
				log_error("Assertion failed: selection contains %d elements, more than the maximum number %d:%s\n",
						total_count, assert_max, sel_str.c_str());
			if (assert_min >= 0 && assert_min > total_count)
				log_error("Assertion failed: selection contains %d elements, less than the minimum number %d:%s\n",
						total_count, assert_min, sel_str.c_str());
			return;
		}

		if (!set_name.empty())
		{
			if (work_stack.size() == 0)
				design->selection_vars[set_name] = RTLIL::Selection(false);
			else
				design->selection_vars[set_name] = work_stack.back();
			return;
		}

		if (work_stack.size() == 0) {
			RTLIL::Selection &sel = design->selection_stack.back();
			if (sel.full_selection)
				log("*\n");
			for (auto &it : sel.selected_modules)
				log("%s\n", id2cstr(it));
			for (auto &it : sel.selected_members)
				for (auto &it2 : it.second)
					log("%s/%s\n", id2cstr(it.first), id2cstr(it2));
			return;
		}

		design->selection_stack.back() = work_stack.back();
		design->selection_stack.back().optimize(design);
	}
} SelectPass;

struct CdPass : public Pass {
	CdPass() : Pass("cd", "a shortcut for 'select -module <name>'") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    cd <modname>\n");
		log("\n");
		log("This is just a shortcut for 'select -module <modname>'.\n");
		log("\n");
		log("\n");
		log("    cd <cellname>\n");
		log("\n");
		log("When no module with the specified name is found, but there is a cell\n");
		log("with the specified name in the current module, then this is equivalent\n");
		log("to 'cd <celltype>'.\n");
		log("\n");
		log("    cd ..\n");
		log("\n");
		log("This is just a shortcut for 'select -clear'.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		if (args.size() != 2)
			log_cmd_error("Invalid number of arguments.\n");

		if (args[1] == "..") {
			design->selection_stack.back() = RTLIL::Selection(true);
			design->selected_active_module = std::string();
			return;
		}

		std::string modname = RTLIL::escape_id(args[1]);

		if (design->modules_.count(modname) == 0 && !design->selected_active_module.empty()) {
			RTLIL::Module *module = NULL;
			if (design->modules_.count(design->selected_active_module) > 0)
				module = design->modules_.at(design->selected_active_module);
			if (module != NULL && module->cells_.count(modname) > 0)
				modname = module->cells_.at(modname)->type.str();
		}

		if (design->modules_.count(modname) > 0) {
			design->selected_active_module = modname;
			design->selection_stack.back() = RTLIL::Selection();
			select_filter_active_mod(design, design->selection_stack.back());
			design->selection_stack.back().optimize(design);
			return;
		}

		log_cmd_error("No such module `%s' found!\n", RTLIL::unescape_id(modname).c_str());
	}
} CdPass;

template<typename T>
static void log_matches(const char *title, Module *module, T list)
{
	std::vector<IdString> matches;

	for (auto &it : list)
		if (module->selected(it.second))
			matches.push_back(it.first);

	if (!matches.empty()) {
		log("\n%d %s:\n", int(matches.size()), title);
		std::sort(matches.begin(), matches.end(), RTLIL::sort_by_id_str());
		for (auto id : matches)
			log("  %s\n", RTLIL::id2cstr(id));
	}
}

struct LsPass : public Pass {
	LsPass() : Pass("ls", "list modules or objects in modules") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ls [selection]\n");
		log("\n");
		log("When no active module is selected, this prints a list of modules.\n");
		log("\n");
		log("When an active module is selected, this prints a list of objects in the module.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		size_t argidx = 1;
		extra_args(args, argidx, design);

		if (design->selected_active_module.empty())
		{
			std::vector<IdString> matches;

			for (auto mod : design->selected_modules())
				matches.push_back(mod->name);

			if (!matches.empty()) {
				log("\n%d %s:\n", int(matches.size()), "modules");
				std::sort(matches.begin(), matches.end(), RTLIL::sort_by_id_str());
				for (auto id : matches)
					log("  %s%s\n", log_id(id), design->selected_whole_module(design->module(id)) ? "" : "*");
			}
		}
		else
		if (design->module(design->selected_active_module) != nullptr)
		{
			RTLIL::Module *module = design->module(design->selected_active_module);
			log_matches("wires", module, module->wires_);
			log_matches("memories", module, module->memories);
			log_matches("cells", module, module->cells_);
			log_matches("processes", module, module->processes);
		}
	}
} LsPass;

PRIVATE_NAMESPACE_END
