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
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

Const make_value(string &value)
{
	if (GetSize(value) >= 2 && value.front() == '"' && value.back() == '"')
		return Const(value.substr(1, GetSize(value)-2));

	SigSpec sig;
	SigSpec::parse(sig, nullptr, value);
	return sig.as_const();
}

bool string_compare_nocase(const string &str1, const string &str2)
{
	if (str1.size() != str2.size())
		return false;

	for (size_t i = 0; i < str1.size(); i++)
	{
		char ch1 = str1[i], ch2 = str2[i];
		if ('a' <= ch1 && ch1 <= 'z')
			ch1 -= 'a' - 'A';
		if ('a' <= ch2 && ch2 <= 'z')
			ch2 -= 'a' - 'A';
		if (ch1 != ch2)
			return false;
	}

	return true;
}

bool match_name(string &name, IdString &id, bool ignore_case=false)
{
	string str1 = RTLIL::escape_id(name);
	string str2 = id.str();

	if (ignore_case)
		return string_compare_nocase(str1, str2);

	return str1 == str2;
}

bool match_value(string &value, Const &val, bool ignore_case=false)
{
	if (ignore_case && ((val.flags & RTLIL::CONST_FLAG_STRING) != 0) && GetSize(value) && value.front() == '"' && value.back() == '"') {
		string str1 = value.substr(1, GetSize(value)-2);
		string str2 = val.decode_string();
		return string_compare_nocase(str1, str2);
	}

	return make_value(value) == val;
}

struct AttrmapAction {
	virtual ~AttrmapAction() { }
	virtual bool apply(IdString &id, Const &val) = 0;
};

struct AttrmapTocase : AttrmapAction {
	string name;
	bool apply(IdString &id, Const&) YS_OVERRIDE {
		if (match_name(name, id, true))
			id = RTLIL::escape_id(name);
		return true;
	}
};

struct AttrmapRename : AttrmapAction {
	string old_name, new_name;
	bool apply(IdString &id, Const&) YS_OVERRIDE {
		if (match_name(old_name, id))
			id = RTLIL::escape_id(new_name);
		return true;
	}
};

struct AttrmapMap : AttrmapAction {
	bool imap;
	string old_name, new_name;
	string old_value, new_value;
	bool apply(IdString &id, Const &val) YS_OVERRIDE {
		if (match_name(old_name, id) && match_value(old_value, val, true)) {
			id = RTLIL::escape_id(new_name);
			val = make_value(new_value);
		}
		return true;
	}
};

struct AttrmapRemove : AttrmapAction {
	bool has_value;
	string name, value;
	bool apply(IdString &id, Const &val) YS_OVERRIDE {
		return !(match_name(name, id) && (!has_value || match_value(value, val)));
	}
};

void attrmap_apply(string objname, vector<std::unique_ptr<AttrmapAction>> &actions, dict<RTLIL::IdString, RTLIL::Const> &attributes)
{
	dict<RTLIL::IdString, RTLIL::Const> new_attributes;

	for (auto attr : attributes)
	{
		auto new_attr = attr;
		for (auto &action : actions)
			if (!action->apply(new_attr.first, new_attr.second))
				goto delete_this_attr;

		if (new_attr != attr)
			log("Changed attribute on %s: %s=%s -> %s=%s\n", objname.c_str(),
					log_id(attr.first), log_const(attr.second), log_id(new_attr.first), log_const(new_attr.second));

		new_attributes[new_attr.first] = new_attr.second;

		if (0)
	delete_this_attr:
			log("Removed attribute on %s: %s=%s\n", objname.c_str(), log_id(attr.first), log_const(attr.second));
	}

	attributes.swap(new_attributes);
}

void log_attrmap_paramap_options()
{
	log("    -tocase <name>\n");
	log("        Match attribute names case-insensitively and set it to the specified\n");
	log("        name.\n");
	log("\n");
	log("    -rename <old_name> <new_name>\n");
	log("        Rename attributes as specified\n");
	log("\n");
	log("    -map <old_name>=<old_value> <new_name>=<new_value>\n");
	log("        Map key/value pairs as indicated.\n");
	log("\n");
	log("    -imap <old_name>=<old_value> <new_name>=<new_value>\n");
	log("        Like -map, but use case-insensitive match for <old_value> when\n");
	log("        it is a string value.\n");
	log("\n");
	log("    -remove <name>=<value>\n");
	log("        Remove attributes matching this pattern.\n");
}

bool parse_attrmap_paramap_options(size_t &argidx, std::vector<std::string> &args, vector<std::unique_ptr<AttrmapAction>> &actions)
{
	std::string arg = args[argidx];
	if (arg == "-tocase" && argidx+1 < args.size()) {
		auto action = new AttrmapTocase;
		action->name = args[++argidx];
		actions.push_back(std::unique_ptr<AttrmapAction>(action));
		return true;
	}
	if (arg == "-rename" && argidx+2 < args.size()) {
		auto action = new AttrmapRename;
		action->old_name = args[++argidx];
		action->new_name = args[++argidx];
		actions.push_back(std::unique_ptr<AttrmapAction>(action));
		return true;
	}
	if ((arg == "-map" || arg == "-imap") && argidx+2 < args.size()) {
		string arg1 = args[++argidx];
		string arg2 = args[++argidx];
		string val1, val2;
		size_t p = arg1.find("=");
		if (p != string::npos) {
			val1 = arg1.substr(p+1);
			arg1 = arg1.substr(0, p);
		}
		p = arg2.find("=");
		if (p != string::npos) {
			val2 = arg2.substr(p+1);
			arg2 = arg2.substr(0, p);
		}
		auto action = new AttrmapMap;
		action->imap = (arg == "-map");
		action->old_name = arg1;
		action->new_name = arg2;
		action->old_value = val1;
		action->new_value = val2;
		actions.push_back(std::unique_ptr<AttrmapAction>(action));
		return true;
	}
	if (arg == "-remove" && argidx+1 < args.size()) {
		string arg1 = args[++argidx], val1;
		size_t p = arg1.find("=");
		if (p != string::npos) {
			val1 = arg1.substr(p+1);
			arg1 = arg1.substr(0, p);
		}
		auto action = new AttrmapRemove;
		action->name = arg1;
		action->has_value = (p != string::npos);
		action->value = val1;
		actions.push_back(std::unique_ptr<AttrmapAction>(action));
		return true;
	}
	return false;
}

struct AttrmapPass : public Pass {
	AttrmapPass() : Pass("attrmap", "renaming attributes") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    attrmap [options] [selection]\n");
		log("\n");
		log("This command renames attributes and/or maps key/value pairs to\n");
		log("other key/value pairs.\n");
		log("\n");
		log_attrmap_paramap_options();
		log("\n");
		log("    -modattr\n");
		log("        Operate on module attributes instead of attributes on wires and cells.\n");
		log("\n");
		log("For example, mapping Xilinx-style \"keep\" attributes to Yosys-style:\n");
		log("\n");
		log("    attrmap -tocase keep -imap keep=\"true\" keep=1 \\\n");
		log("            -imap keep=\"false\" keep=0 -remove keep=0\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ATTRMAP pass (move or copy attributes).\n");

		bool modattr_mode = false;
		vector<std::unique_ptr<AttrmapAction>> actions;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (parse_attrmap_paramap_options(argidx, args, actions))
				continue;
			if (args[argidx] == "-modattr") {
				modattr_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (modattr_mode)
		{
			for (auto module : design->selected_whole_modules())
				attrmap_apply(stringf("%s", log_id(module)), actions, module->attributes);
		}
		else
		{
			for (auto module : design->selected_modules())
			{
				for (auto wire : module->selected_wires())
					attrmap_apply(stringf("%s.%s", log_id(module), log_id(wire)), actions, wire->attributes);

				for (auto cell : module->selected_cells())
					attrmap_apply(stringf("%s.%s", log_id(module), log_id(cell)), actions, cell->attributes);

				for (auto proc : module->processes)
				{
					if (!design->selected(module, proc.second))
						continue;
					attrmap_apply(stringf("%s.%s", log_id(module), log_id(proc.first)), actions, proc.second->attributes);

					std::vector<RTLIL::CaseRule*> all_cases = {&proc.second->root_case};
					while (!all_cases.empty()) {
						RTLIL::CaseRule *cs = all_cases.back();
						all_cases.pop_back();
						attrmap_apply(stringf("%s.%s (case)", log_id(module), log_id(proc.first)), actions, cs->attributes);

						for (auto &sw : cs->switches) {
							attrmap_apply(stringf("%s.%s (switch)", log_id(module), log_id(proc.first)), actions, sw->attributes);
							all_cases.insert(all_cases.end(), sw->cases.begin(), sw->cases.end());
						}
					}
				}
			}
		}
	}
} AttrmapPass;

struct ParamapPass : public Pass {
	ParamapPass() : Pass("paramap", "renaming cell parameters") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    paramap [options] [selection]\n");
		log("\n");
		log("This command renames cell parameters and/or maps key/value pairs to\n");
		log("other key/value pairs.\n");
		log("\n");
		log_attrmap_paramap_options();
		log("\n");
		log("For example, mapping Diamond-style ECP5 \"init\" attributes to Yosys-style:\n");
		log("\n");
		log("    paramap -tocase INIT t:LUT4\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing PARAMAP pass (move or copy cell parameters).\n");

		vector<std::unique_ptr<AttrmapAction>> actions;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (parse_attrmap_paramap_options(argidx, args, actions))
				continue;
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		for (auto cell : module->selected_cells())
			attrmap_apply(stringf("%s.%s", log_id(module), log_id(cell)), actions, cell->parameters);
	}
} ParamapPass;

PRIVATE_NAMESPACE_END
