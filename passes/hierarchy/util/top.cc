/*
*  yosys -- Yosys Open SYnthesis Suite
*
*  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
*  Copyright (C) 2018  Ruben Undheim <ruben.undheim@gmail.com>
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
#include "frontends/verific/verific.h"
#include "passes/hierarchy/util/top.h"
#include "passes/hierarchy/util/misc.h"

YOSYS_NAMESPACE_BEGIN
namespace Hierarchy {

Module* TopModulePrepare::load_top(const string& name, bool auto_top) {
	Module* top_mod = nullptr;
	if (!name.empty())
		top_mod = load_top_module_regular(name);

	top_mod = load_top_module_verific(is_from_verific, name, top_mod);

	if (top_mod == nullptr)
		top_mod = load_top_module_attribute();

	if (top_mod == nullptr)
		derive_all();

	if (top_mod == nullptr && auto_top)
		top_mod = load_top_module_auto();

	if (top_mod != nullptr && top_mod->name.begins_with("$abstract")) {
		top_mod = rederived_top(top_mod);
	}

	if (top_mod != NULL)
		clear_initial_top_attribute(top_mod);

	return top_mod;
}

Module* TopModulePrepare::load_top_module_regular(const string& name) {
	Module* top_mod = nullptr;
	IdString top_name = RTLIL::escape_id(name);
	IdString abstract_id = "$abstract" + RTLIL::escape_id(name);
	top_mod = design->module(top_name);

	dict<RTLIL::IdString, RTLIL::Const> top_parameters;
	if ((top_mod == nullptr && design->module(abstract_id)) || top_mod != nullptr) {
		for (auto &para : params) {
			SigSpec sig_value;
			if (!RTLIL::SigSpec::parse(sig_value, NULL, para.second))
				log_cmd_error("Can't decode value '%s'!\n", para.second);
			top_parameters[RTLIL::escape_id(para.first)] = sig_value.as_const();
		}
	}

	if (top_mod == nullptr && design->module(abstract_id))
		top_mod = design->module(design->module(abstract_id)->derive(design, top_parameters));
	else if (top_mod != nullptr && !top_parameters.empty())
		top_mod = design->module(top_mod->derive(design, top_parameters));

	// Delete template of derived top module or something idk
	if (top_mod != nullptr && top_mod->name != top_name) {
		Module *m = top_mod->clone();
		m->name = top_name;
		Module *old_mod = design->module(top_name);
		if (old_mod)
			design->remove(old_mod);
		design->add(m);
		top_mod = m;
	}
	return top_mod;
}

Module* TopModulePrepare::load_top_module_verific(bool& is_from_verific, string name, Module* top_mod) {
	// Unused if not YOSYS_ENABLE_VERIFIC
	(void)is_from_verific;
	(void)params;
	(void)design;
	Module* new_top_mod = top_mod;
#ifdef YOSYS_ENABLE_VERIFIC
	is_from_verific = verific_import_pending;
#endif

	if (top_mod == nullptr && !name.empty()) {
#ifdef YOSYS_ENABLE_VERIFIC
		if (verific_import_pending) {
			name = verific_import(design, params, name);
			log("verific name: %s\n", name);
			new_top_mod = design->module(RTLIL::escape_id(name));
		}
#endif
		if (new_top_mod == NULL)
			log_cmd_error("Module `%s' not found!\n", name);
	} else {
#ifdef YOSYS_ENABLE_VERIFIC
		if (verific_import_pending)
			verific_import(design, params);
#endif
	}
	return new_top_mod;
}

void TopModulePrepare::derive_all() {
	std::vector<IdString> abstract_ids;
	for (auto module : design->modules())
		if (module->name.begins_with("$abstract"))
			abstract_ids.push_back(module->name);
	for (auto abstract_id : abstract_ids)
		design->module(abstract_id)->derive(design, {});
	for (auto abstract_id : abstract_ids)
		design->remove(design->module(abstract_id));
}

Module* TopModulePrepare::load_top_module_attribute() {
	Module* top_mod = nullptr;
	for (auto mod : design->modules())
		if (mod->get_bool_attribute(ID::top)) {
			log("Attribute `top' found on module `%s'. Setting top module to %s.\n", log_id(mod), log_id(mod));
			top_mod = mod;
		}
	return top_mod;
}

static int find_top_mod_score(Design *design, Module *module, dict<Module*, int> &db)
{
	if (db.count(module) == 0) {
		int score = 0;
		db[module] = 0;
		for (auto cell : module->cells()) {
			std::string celltype = cell->type.str();
			// Is this an array instance
			if (auto array_type = try_make_array(celltype))
				celltype = array_type->name;
			// Is this cell a module instance?
			auto instModule = design->module(celltype);
			// If there is no instance for this, issue a warning.
			if (instModule != nullptr) {
				score = max(score, find_top_mod_score(design, instModule, db) + 1);
			}
		}
		db[module] = score;
	}
	return db.at(module);
}

Module* TopModulePrepare::load_top_module_auto() {
	Module* top_mod = nullptr;
	log_header(design, "Finding top of design hierarchy..\n");
	dict<Module*, int> db;
	for (Module *mod : design->selected_modules()) {
		int score = find_top_mod_score(design, mod, db);
		log("root of %3d design levels: %-20s\n", score, log_id(mod));
		if (!top_mod || score > db[top_mod])
			top_mod = mod;
	}
	if (top_mod != nullptr)
		log("Automatically selected %s as design top module.\n", log_id(top_mod));
	return top_mod;
}

Module* TopModulePrepare::rederived_top(Module* top_mod) {
	IdString top_name = top_mod->name.substr(strlen("$abstract"));

	dict<RTLIL::IdString, RTLIL::Const> top_parameters;
	for (auto &para : params) {
		SigSpec sig_value;
		if (!RTLIL::SigSpec::parse(sig_value, NULL, para.second))
			log_cmd_error("Can't decode value '%s'!\n", para.second);
		top_parameters[RTLIL::escape_id(para.first)] = sig_value.as_const();
	}

	top_mod = design->module(top_mod->derive(design, top_parameters));

	if (top_mod != nullptr && top_mod->name != top_name) {
		Module *m = top_mod->clone();
		m->name = top_name;
		Module *old_mod = design->module(top_name);
		if (old_mod)
			design->remove(old_mod);
		design->add(m);
		top_mod = m;
	}
	return top_mod;
}

void TopModulePrepare::clear_initial_top_attribute(Module* top_mod) {
	for (auto mod : design->modules())
		if (mod == top_mod)
			mod->attributes[ID::initial_top] = RTLIL::Const(1);
		else
			mod->attributes.erase(ID::initial_top);
}

void ensure_unique_top_attribute(Module* top_mod, Design* design) {
	for (auto mod : design->modules()) {
		if (mod == top_mod)
			mod->attributes[ID::top] = RTLIL::Const(1);
		else
			mod->attributes.erase(ID::top);
		mod->attributes.erase(ID::initial_top);
	}
}

};
YOSYS_NAMESPACE_END
