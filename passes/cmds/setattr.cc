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
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct setunset_t
{
	RTLIL::IdString name;
	RTLIL::Const value;
	bool unset;

	setunset_t(std::string unset_name) : name(RTLIL::escape_id(unset_name)), value(), unset(true) { }

	setunset_t(std::string set_name, std::string set_value) : name(RTLIL::escape_id(set_name)), value(), unset(false)
	{
		if (set_value.compare(0, 1, "\"") == 0 && set_value.compare(GetSize(set_value)-1, std::string::npos, "\"") == 0) {
			value = RTLIL::Const(set_value.substr(1, GetSize(set_value)-2));
		} else {
			RTLIL::SigSpec sig_value;
			if (!RTLIL::SigSpec::parse(sig_value, NULL, set_value))
				log_cmd_error("Can't decode value '%s'!\n", set_value.c_str());
			value = sig_value.as_const();
		}
	}
};

static void do_setunset(dict<RTLIL::IdString, RTLIL::Const> &attrs, const std::vector<setunset_t> &list)
{
	for (auto &item : list)
		if (item.unset)
			attrs.erase(item.name);
		else
			attrs[item.name] = item.value;
}

struct SetattrPass : public Pass {
	SetattrPass() : Pass("setattr", "set/unset attributes on objects") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    setattr [ -mod ] [ -set name value | -unset name ]... [selection]\n");
		log("\n");
		log("Set/unset the given attributes on the selected objects. String values must be\n");
		log("passed in double quotes (\").\n");
		log("\n");
		log("When called with -mod, this command will set and unset attributes on modules\n");
		log("instead of objects within modules.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::vector<setunset_t> setunset_list;
		bool flag_mod = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-set" && argidx+2 < args.size()) {
				string set_key = args[++argidx];
				string set_val = args[++argidx];
				setunset_list.push_back(setunset_t(set_key, set_val));
				continue;
			}
			if (arg == "-unset" && argidx+1 < args.size()) {
				setunset_list.push_back(setunset_t(args[++argidx]));
				continue;
			}
			if (arg == "-mod") {
				flag_mod = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod : design->modules_)
		{
			RTLIL::Module *module = mod.second;

			if (flag_mod) {
				if (design->selected_whole_module(module->name))
					do_setunset(module->attributes, setunset_list);
				continue;
			}

			if (!design->selected(module))
				continue;

			for (auto &it : module->wires_)
				if (design->selected(module, it.second))
					do_setunset(it.second->attributes, setunset_list);

			for (auto &it : module->memories)
				if (design->selected(module, it.second))
					do_setunset(it.second->attributes, setunset_list);

			for (auto &it : module->cells_)
				if (design->selected(module, it.second))
					do_setunset(it.second->attributes, setunset_list);

			for (auto &it : module->processes)
				if (design->selected(module, it.second))
					do_setunset(it.second->attributes, setunset_list);
		}
	}
} SetattrPass;

struct WbflipPass : public Pass {
	WbflipPass() : Pass("wbflip", "flip the whitebox attribute") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    wbflip [selection]\n");
		log("\n");
		log("Flip the whitebox attribute on selected cells. I.e. if it's set, unset it, and\n");
		log("vice-versa. Blackbox cells are not effected by this command.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			// if (arg == "-mod") {
			// 	flag_mod = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (Module *module : design->modules())
		{
			if (!design->selected(module))
				continue;

			if (module->get_bool_attribute("\\blackbox"))
				continue;

			module->set_bool_attribute("\\whitebox", !module->get_bool_attribute("\\whitebox"));
		}
	}
} WbflipPass;

struct SetparamPass : public Pass {
	SetparamPass() : Pass("setparam", "set/unset parameters on objects") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    setparam [ -type cell_type ] [ -set name value | -unset name ]... [selection]\n");
		log("\n");
		log("Set/unset the given parameters on the selected cells. String values must be\n");
		log("passed in double quotes (\").\n");
		log("\n");
		log("The -type option can be used to change the cell type of the selected cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		vector<setunset_t> setunset_list;
		string new_cell_type;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-set" && argidx+2 < args.size()) {
				string set_key = args[++argidx];
				string set_val = args[++argidx];
				setunset_list.push_back(setunset_t(set_key, set_val));
				continue;
			}
			if (arg == "-unset" && argidx+1 < args.size()) {
				setunset_list.push_back(setunset_t(args[++argidx]));
				continue;
			}
			if (arg == "-type" && argidx+1 < args.size()) {
				new_cell_type = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod : design->modules_)
		{
			RTLIL::Module *module = mod.second;

			if (!design->selected(module))
				continue;

			for (auto &it : module->cells_)
				if (design->selected(module, it.second)) {
					if (!new_cell_type.empty())
						it.second->type = new_cell_type;
					do_setunset(it.second->parameters, setunset_list);
				}
		}
	}
} SetparamPass;

struct ChparamPass : public Pass {
	ChparamPass() : Pass("chparam", "re-evaluate modules with new parameters") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    chparam [ -set name value ]... [selection]\n");
		log("\n");
		log("Re-evaluate the selected modules with new parameters. String values must be\n");
		log("passed in double quotes (\").\n");
		log("\n");
		log("\n");
		log("    chparam -list [selection]\n");
		log("\n");
		log("List the available parameters of the selected modules.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::vector<setunset_t> setunset_list;
		dict<RTLIL::IdString, RTLIL::Const> new_parameters;
		bool list_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-set" && argidx+2 < args.size()) {
				string set_key = args[++argidx];
				string set_val = args[++argidx];
				setunset_list.push_back(setunset_t(set_key, set_val));
				continue;
			}
			if (arg == "-list") {
				list_mode = true;
				continue;
			}
			break;
		}

		for (int i = argidx; i < GetSize(args); i++)
			if (design->module("$abstract\\" + args[i]) != nullptr &&
					design->module(RTLIL::escape_id(args[i])) == nullptr)
				args[i] = "$abstract\\" + args[i];

		extra_args(args, argidx, design);

		do_setunset(new_parameters, setunset_list);

		if (list_mode) {
			if (!new_parameters.empty())
				log_cmd_error("The options -set and -list cannot be used together.\n");
			for (auto module : design->selected_modules()) {
				log("%s:\n", log_id(module));
				for (auto param : module->avail_parameters)
					log("  %s\n", log_id(param));
			}
			return;
		}

		pool<IdString> modnames, old_modnames;
		for (auto module : design->selected_whole_modules_warn()) {
			modnames.insert(module->name);
			old_modnames.insert(module->name);
		}
		modnames.sort();

		for (auto modname : modnames) {
			Module *module = design->module(modname);
			Module *new_module = design->module(module->derive(design, new_parameters));
			if (module != new_module) {
				Module *m = new_module->clone();
				m->name = module->name;
				design->remove(module);
				design->add(m);
			}
			if (old_modnames.count(new_module->name) == 0)
				design->remove(new_module);
		}
	}
} ChparamPass;

PRIVATE_NAMESPACE_END
