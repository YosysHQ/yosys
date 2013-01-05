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
#include "kernel/log.h"
#include <string.h>
#include <fnmatch.h>

static std::vector<RTLIL::Selection> work_stack;

static bool match_ids(RTLIL::IdString id, std::string pattern)
{
	if (!fnmatch(pattern.c_str(), id.c_str(), FNM_NOESCAPE))
		return true;
	if (id.size() > 0 && id[0] == '\\' && !fnmatch(pattern.c_str(), id.substr(1).c_str(), FNM_NOESCAPE))
		return true;
	return false;
}

static bool match_attr_val(const RTLIL::Const &value, std::string pattern)
{
	if (!fnmatch(pattern.c_str(), value.str.c_str(), FNM_NOESCAPE))
		return true;
	return false;
}

static bool match_attr(const std::map<RTLIL::IdString, RTLIL::Const> &attributes, std::string name_pat, std::string value_pat, bool use_value_pat)
{
	if (name_pat.find('*') != std::string::npos || name_pat.find('?') != std::string::npos || name_pat.find('[') != std::string::npos) {
		for (auto &it : attributes) {
			if (!fnmatch(name_pat.c_str(), it.first.c_str(), FNM_NOESCAPE) && (!use_value_pat || match_attr_val(it.second, value_pat)))
				return true;
			if (it.first.size() > 0 && it.first[0] == '\\' && !fnmatch(name_pat.c_str(), it.first.substr(1).c_str(), FNM_NOESCAPE) && (!use_value_pat || match_attr_val(it.second, value_pat)))
				return true;
		}
	} else {
		if (name_pat.size() > 0 && (name_pat[0] == '\\' || name_pat[0] == '$') && attributes.count(name_pat) && (!use_value_pat || match_attr_val(attributes.at(name_pat), value_pat)))
			return true;
		if (attributes.count("\\" + name_pat) && (!use_value_pat || match_attr_val(attributes.at("\\" + name_pat), value_pat)))
			return true;
	}
	return false;
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

	for (auto &mod_it : design->modules)
	{
		if (lhs.selected_whole_module(mod_it.first))
			continue;
		if (!lhs.selected_module(mod_it.first)) {
			new_sel.selected_modules.insert(mod_it.first);
			continue;
		}

		RTLIL::Module *mod = mod_it.second;
		for (auto &it : mod->wires)
			if (!lhs.selected_member(mod_it.first, it.first))
				new_sel.selected_members[mod->name].insert(it.first);
		for (auto &it : mod->memories)
			if (!lhs.selected_member(mod_it.first, it.first))
				new_sel.selected_members[mod->name].insert(it.first);
		for (auto &it : mod->cells)
			if (!lhs.selected_member(mod_it.first, it.first))
				new_sel.selected_members[mod->name].insert(it.first);
		for (auto &it : mod->processes)
			if (!lhs.selected_member(mod_it.first, it.first))
				new_sel.selected_members[mod->name].insert(it.first);
	}

	lhs.selected_modules.swap(new_sel.selected_modules);
	lhs.selected_members.swap(new_sel.selected_members);
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
		for (auto &it : design->modules)
			lhs.selected_modules.insert(it.first);
	}

	for (auto &it : rhs.selected_modules) {
		lhs.selected_modules.erase(it);
		lhs.selected_members.erase(it);
	}

	for (auto &it : rhs.selected_members)
	{
		if (design->modules.count(it.first) == 0)
			continue;

		RTLIL::Module *mod = design->modules[it.first];

		if (lhs.selected_modules.count(mod->name) > 0)
		{
			for (auto &it : mod->wires)
				lhs.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->memories)
				lhs.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->cells)
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
		for (auto &it : design->modules)
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

	std::vector<std::string> del_list;
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

	if (arg[0] == '#') {
		if (arg == "#") {
			if (design->selection_stack.size() > 0)
				work_stack.push_back(design->selection_stack.back());
		} else
		if (arg == "#n") {
			if (work_stack.size() < 1)
				log_cmd_error("Must have at least one element on stack for operator #n.\n");
			select_op_neg(design, work_stack[work_stack.size()-1]);
		} else
		if (arg == "#u") {
			if (work_stack.size() < 2)
				log_cmd_error("Must have at least two elements on stack for operator #u.\n");
			select_op_union(design, work_stack[work_stack.size()-2], work_stack[work_stack.size()-1]);
			work_stack.pop_back();
		} else
		if (arg == "#d") {
			if (work_stack.size() < 2)
				log_cmd_error("Must have at least two elements on stack for operator #d.\n");
			select_op_diff(design, work_stack[work_stack.size()-2], work_stack[work_stack.size()-1]);
			work_stack.pop_back();
		} else
		if (arg == "#i") {
			if (work_stack.size() < 2)
				log_cmd_error("Must have at least two elements on stack for operator #i.\n");
			select_op_intersect(design, work_stack[work_stack.size()-2], work_stack[work_stack.size()-1]);
			work_stack.pop_back();
		} else
			log_cmd_error("Unknown selection operator '%s'.\n", arg.c_str());
		select_filter_active_mod(design, work_stack.back());
		return;
	}

	if (!design->selected_active_module.empty()) {
		arg_mod = design->selected_active_module;
		arg_memb = arg;
	} else {
		size_t pos = arg.find('/');
		if (pos == std::string::npos) {
			arg_mod = arg;
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
	for (auto &mod_it : design->modules)
	{
		if (!match_ids(mod_it.first, arg_mod))
			continue;

		if (arg_memb == "") {
			sel.selected_modules.insert(mod_it.first);
			continue;
		}

		RTLIL::Module *mod = mod_it.second;
		if (arg_memb.substr(0, 2) == "w:") {
			for (auto &it : mod->wires)
				if (match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "m:") {
			for (auto &it : mod->memories)
				if (match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "c:") {
			for (auto &it : mod->cells)
				if (match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "t:") {
			for (auto &it : mod->cells)
				if (match_ids(it.second->type, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "p:") {
			for (auto &it : mod->processes)
				if (match_ids(it.first, arg_memb.substr(2)))
					sel.selected_members[mod->name].insert(it.first);
		} else
		if (arg_memb.substr(0, 2) == "a:") {
			bool use_value_pat = false;
			std::string name_pat = arg_memb.substr(2);
			std::string value_pat;
			if (name_pat.find('=') != std::string::npos) {
				value_pat = name_pat.substr(name_pat.find('=')+1);
				name_pat = name_pat.substr(0, name_pat.find('='));
				use_value_pat = true;
			}
			for (auto &it : mod->wires)
				if (match_attr(it.second->attributes, name_pat, value_pat, use_value_pat))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->memories)
				if (match_attr(it.second->attributes, name_pat, value_pat, use_value_pat))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->cells)
				if (match_attr(it.second->attributes, name_pat, value_pat, use_value_pat))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->processes)
				if (match_attr(it.second->attributes, name_pat, value_pat, use_value_pat))
					sel.selected_members[mod->name].insert(it.first);
		} else {
			if (arg_memb.substr(0, 2) == "n:")
				arg_memb = arg_memb.substr(2);
			for (auto &it : mod->wires)
				if (match_ids(it.first, arg_memb))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->memories)
				if (match_ids(it.first, arg_memb))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->cells)
				if (match_ids(it.first, arg_memb))
					sel.selected_members[mod->name].insert(it.first);
			for (auto &it : mod->processes)
				if (match_ids(it.first, arg_memb))
					sel.selected_members[mod->name].insert(it.first);
		}
	}

	select_filter_active_mod(design, work_stack.back());
}

struct SelectPass : public Pass {
	SelectPass() : Pass("select") { }
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool add_mode = false;
		bool del_mode = false;
		bool clear_mode = false;
		bool list_mode = false;
		bool got_module = false;

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
			if (arg == "-clear") {
				clear_mode = true;
				continue;
			}
			if (arg == "-list") {
				list_mode = true;
				continue;
			}
			if (arg == "-module" && argidx+1 < args.size()) {
				RTLIL::IdString mod_name = RTLIL::escape_id(args[++argidx]);
				if (design->modules.count(mod_name) == 0)
					log_cmd_error("No such module: %s\n", mod_name.c_str());
				design->selected_active_module = mod_name;
				got_module = true;
				continue;
			}
			if (arg.size() > 0 && arg[0] == '-')
				log_cmd_error("Unkown option %s.\n", arg.c_str());
			select_stmt(design, arg);
		}

		if (clear_mode && args.size() != 2)
			log_cmd_error("Option -clear can not be combined with other options.\n");

		if (add_mode && del_mode)
			log_cmd_error("Options -add and -del can not be combined.\n");

		if (list_mode && (add_mode || del_mode))
			log_cmd_error("Option -list can not be combined with -add or -del.\n");

		if (work_stack.size() == 0 && got_module) {
			RTLIL::Selection sel;
			select_filter_active_mod(design, sel);
			work_stack.push_back(sel);
		}

		while (work_stack.size() > 1) {
			select_op_union(design, work_stack.front(), work_stack.back());
			work_stack.pop_back();
		}

		assert(design->selection_stack.size() > 0);

		if (clear_mode)
		{
			design->selection_stack.back() = RTLIL::Selection(true);
			design->selected_active_module = std::string();
			return;
		}

		if (list_mode)
		{
			RTLIL::Selection *sel = &design->selection_stack.back();
			if (work_stack.size() > 0)
				sel = &work_stack.back();
			sel->optimize(design);
			for (auto mod_it : design->modules)
			{
				if (design->selected_whole_module(mod_it.first))
					log("%s\n", mod_it.first.c_str());
				if (design->selected_module(mod_it.first)) {
					for (auto &it : mod_it.second->wires)
						if (design->selected_member(mod_it.first, it.first))
							log("%s/%s\n", mod_it.first.c_str(), it.first.c_str());
					for (auto &it : mod_it.second->memories)
						if (design->selected_member(mod_it.first, it.first))
							log("%s/%s\n", mod_it.first.c_str(), it.first.c_str());
					for (auto &it : mod_it.second->cells)
						if (design->selected_member(mod_it.first, it.first))
							log("%s/%s\n", mod_it.first.c_str(), it.first.c_str());
					for (auto &it : mod_it.second->processes)
						if (design->selected_member(mod_it.first, it.first))
							log("%s/%s\n", mod_it.first.c_str(), it.first.c_str());
				}
			}
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

		if (work_stack.size() == 0) {
			RTLIL::Selection &sel = design->selection_stack.back();
			if (sel.full_selection)
				log("*\n");
			for (auto &it : sel.selected_modules)
				log("%s\n", it.c_str());
			for (auto &it : sel.selected_members)
				for (auto &it2 : it.second)
					log("%s/%s\n", it.first.c_str(), it2.c_str());
			return;
		}

		design->selection_stack.back() = work_stack.back();
		design->selection_stack.back().optimize(design);
	}
} SelectPass;
 
