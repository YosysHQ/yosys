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

	setunset_t(std::string set_name, std::vector<std::string> args, size_t &argidx) : name(RTLIL::escape_id(set_name)), value(), unset(false)
	{
		if (!args[argidx].empty() && args[argidx][0] == '"') {
			std::string str = args[argidx++].substr(1);
			while (str.size() != 0 && str[str.size()-1] != '"' && argidx < args.size())
				str += args[argidx++];
			if (str.size() != 0 && str[str.size()-1] == '"')
				str = str.substr(0, str.size()-1);
			value = RTLIL::Const(str);
		} else {
			RTLIL::SigSpec sig_value;
			if (!RTLIL::SigSpec::parse(sig_value, NULL, args[argidx++]))
				log_cmd_error("Can't decode value '%s'!\n", args[argidx-1].c_str());
			value = sig_value.as_const();
		}
	}
};

static void do_setunset(dict<RTLIL::IdString, RTLIL::Const> &attrs, std::vector<setunset_t> &list)
{
	for (auto &item : list)
		if (item.unset)
			attrs.erase(item.name);
		else
			attrs[item.name] = item.value;
}

struct SetattrPass : public Pass {
	SetattrPass() : Pass("setattr", "set/unset attributes on objects") { }
	virtual void help()
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
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::vector<setunset_t> setunset_list;
		bool flag_mod = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-set" && argidx+2 < args.size()) {
				argidx += 2;
				setunset_list.push_back(setunset_t(args[argidx-1], args, argidx));
				argidx--;
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
 
struct SetparamPass : public Pass {
	SetparamPass() : Pass("setparam", "set/unset parameters on objects") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    setparam [ -set name value | -unset name ]... [selection]\n");
		log("\n");
		log("Set/unset the given parameters on the selected cells. String values must be\n");
		log("passed in double quotes (\").\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::vector<setunset_t> setunset_list;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-set" && argidx+2 < args.size()) {
				argidx += 2;
				setunset_list.push_back(setunset_t(args[argidx-1], args, argidx));
				argidx--;
				continue;
			}
			if (arg == "-unset" && argidx+1 < args.size()) {
				setunset_list.push_back(setunset_t(args[++argidx]));
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
				if (design->selected(module, it.second))
					do_setunset(it.second->parameters, setunset_list);
		}
	}
} SetparamPass;
 
PRIVATE_NAMESPACE_END
