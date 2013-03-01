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

	if (arg[0] == '@') {
		std::string set_name = RTLIL::escape_id(arg.substr(1));
		if (design->selection_vars.count(set_name) > 0)
			work_stack.push_back(design->selection_vars[set_name]);
		else
			work_stack.push_back(RTLIL::Selection(false));
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
	SelectPass() : Pass("select", "modify and view the list of selected objects") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    select [ -add | -del | -set <name> ] <selection>\n");
		log("    select [ -list | -clear ]\n");
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
		log("        under the given name (see @<name> below).\n");
		log("\n");
		log("    -list\n");
		log("        list all objects in the current selection\n");
		log("\n");
		log("    -clear\n");
		log("        clear the current selection. this effectively selects the\n");
		log("        whole design.\n");
		log("\n");
		log("    -module <modname>\n");
		log("        limit the current scope to the specified module\n");
		log("        the difference between this and simply selecting the module\n");
		log("        is that all object names are interpreted relative to this\n");
		log("        module after this command until the selection is cleared again.\n");
		log("\n");
		log("When this command is called without an argument, the current selection\n");
		log("is displayed in a compact form (i.e.. only the module name when a whole module\n");
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
		log("A <mod_pattern> can be a module name or wildcard expression (*, ?, [..])\n");
		log("matching module names.\n");
		log("\n");
		log("An <obj_pattern> can be an object name, wildcard expression, or one of\n");
		log("the following:\n");
		log("\n");
		log("    w:<pattern>\n");
		log("        all wires with a name matching the given wildcard pattern\n");
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
		log("        all objects with a matching attribute name-value-pair\n");
		log("\n");
		log("    n:<pattern>\n");
		log("        all object with a name matching the given pattern\n");
		log("        (i.e. the n: is optional as it is the default matching rule)\n");
		log("\n");
		log("    @<name>\n");
		log("        push the selection saved prior with 'select -set <name> ...'\n");
		log("\n");
		log("The following actions can be performed on the top sets on the stack:\n");
		log("\n");
		log("    #\n");
		log("        push a copy of the current selection to the stack\n");
		log("\n");
		log("    #n\n");
		log("        replace top set with its invert\n");
		log("\n");
		log("    #u\n");
		log("        replace the two top sets on the stack with their union\n");
		log("\n");
		log("    #i\n");
		log("        replace the two top sets on the stack with their intersection\n");
		log("\n");
		log("    #d\n");
		log("        pop the top set from the stack and subtract it from the new top\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool add_mode = false;
		bool del_mode = false;
		bool clear_mode = false;
		bool list_mode = false;
		bool got_module = false;
		std::string set_name;

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
					log_cmd_error("No such module: %s\n", id2cstr(mod_name));
				design->selected_active_module = mod_name;
				got_module = true;
				continue;
			}
			if (arg == "-set" && argidx+1 < args.size()) {
				set_name = RTLIL::escape_id(args[++argidx]);
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

		if (!set_name.empty() && (list_mode || add_mode || del_mode))
			log_cmd_error("Option -set can not be combined with -list, -add or -del.\n");

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
				if (sel->selected_whole_module(mod_it.first))
					log("%s\n", id2cstr(mod_it.first));
				if (sel->selected_module(mod_it.first)) {
					for (auto &it : mod_it.second->wires)
						if (sel->selected_member(mod_it.first, it.first))
							log("%s/%s\n", id2cstr(mod_it.first), id2cstr(it.first));
					for (auto &it : mod_it.second->memories)
						if (sel->selected_member(mod_it.first, it.first))
							log("%s/%s\n", id2cstr(mod_it.first), id2cstr(it.first));
					for (auto &it : mod_it.second->cells)
						if (sel->selected_member(mod_it.first, it.first))
							log("%s/%s\n", id2cstr(mod_it.first), id2cstr(it.first));
					for (auto &it : mod_it.second->processes)
						if (sel->selected_member(mod_it.first, it.first))
							log("%s/%s\n", id2cstr(mod_it.first), id2cstr(it.first));
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

		if (!set_name.empty())
		{
			if (work_stack.size() == 0)
				design->selection_vars.erase(set_name);
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
 
