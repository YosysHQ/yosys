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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static void add_wire(RTLIL::Design *design, RTLIL::Module *module, std::string name, int width, bool flag_input, bool flag_output, bool flag_global)
{
	RTLIL::Wire *wire = nullptr;
	name = RTLIL::escape_id(name);

	if (module->count_id(name) != 0)
	{
		wire = module->wire(name);

		if (wire != nullptr && wire->width != width)
			wire = nullptr;

		if (wire != nullptr && wire->port_input != flag_input)
			wire = nullptr;

		if (wire != nullptr && wire->port_output != flag_output)
			wire = nullptr;

		if (wire == nullptr)
			log_cmd_error("Found incompatible object with same name in module %s!\n", module->name.c_str());

		log("Module %s already has such an object.\n", module->name.c_str());
	}
	else
	{
		wire = module->addWire(name, width);
		wire->port_input = flag_input;
		wire->port_output = flag_output;

		if (flag_input || flag_output) {
			module->fixup_ports();
		}

		log("Added wire %s to module %s.\n", name.c_str(), module->name.c_str());
	}

	if (!flag_global)
		return;

	for (auto cell : module->cells())
	{
		RTLIL::Module *mod = design->module(cell->type);
		if (mod == nullptr)
			continue;
		if (!design->selected_whole_module(mod->name))
			continue;
		if (mod->get_blackbox_attribute())
			continue;
		if (cell->hasPort(name))
			continue;

		cell->setPort(name, wire);
		log("Added connection %s to cell %s.%s (%s).\n", name.c_str(), module->name.c_str(), cell->name.c_str(), cell->type.c_str());
	}
}

struct AddPass : public Pass {
	AddPass() : Pass("add", "add objects to the design") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    add <command> [selection]\n");
		log("\n");
		log("This command adds objects to the design. It operates on all fully selected\n");
		log("modules. So e.g. 'add -wire foo' will add a wire foo to all selected modules.\n");
		log("\n");
		log("\n");
		log("    add {-wire|-input|-inout|-output} <name> <width> [selection]\n");
		log("\n");
		log("Add a wire (input, inout, output port) with the given name and width. The\n");
		log("command will fail if the object exists already and has different properties\n");
		log("than the object to be created.\n");
		log("\n");
		log("\n");
		log("    add -global_input <name> <width> [selection]\n");
		log("\n");
		log("Like 'add -input', but also connect the signal between instances of the\n");
		log("selected modules.\n");
		log("\n");
		log("\n");
		log("    add -mod <name[s]>\n");
		log("\n");
		log("Add module[s] with the specified name[s].\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string command;
		std::string arg_name;
		bool arg_flag_input = false;
		bool arg_flag_output = false;
		bool arg_flag_global = false;
		bool mod_mode = false;
		int arg_width = 0;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-wire" || arg == "-input" || arg == "-inout" || arg == "-output" || arg == "-global_input") {
				if (argidx+2 >= args.size())
					break;
				command = "wire";
				if (arg == "-input" || arg == "-inout" || arg == "-global_input")
					arg_flag_input = true;
				if (arg == "-output" || arg == "-inout")
					arg_flag_output = true;
				if (arg == "-global_input")
					arg_flag_global = true;
				arg_name = args[++argidx];
				arg_width = atoi(args[++argidx].c_str());
				continue;
			}
			if (arg == "-mod") {
				mod_mode = true;
				argidx++;
				break;
			}
			break;
		}

		if (mod_mode) {
			for (; argidx < args.size(); argidx++)
				design->addModule(RTLIL::escape_id(args[argidx]));
			return;
		}

		extra_args(args, argidx, design, false);

		for (auto module : design->modules())
		{
			log_assert(module != nullptr);
			if (!design->selected_whole_module(module->name))
				continue;
			if (module->get_bool_attribute("\\blackbox"))
				continue;

			if (command == "wire")
				add_wire(design, module, arg_name, arg_width, arg_flag_input, arg_flag_output, arg_flag_global);
		}
	}
} AddPass;

PRIVATE_NAMESPACE_END
