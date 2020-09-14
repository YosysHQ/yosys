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

static void rename_in_module(RTLIL::Module *module, std::string from_name, std::string to_name, bool flag_output)
{
	from_name = RTLIL::escape_id(from_name);
	to_name = RTLIL::escape_id(to_name);

	if (module->count_id(to_name))
		log_cmd_error("There is already an object `%s' in module `%s'.\n", to_name.c_str(), module->name.c_str());

	RTLIL::Wire *wire_to_rename = module->wire(from_name);
	RTLIL::Cell *cell_to_rename = module->cell(from_name);

	if (wire_to_rename != nullptr) {
		log("Renaming wire %s to %s in module %s.\n", log_id(wire_to_rename), log_id(to_name), log_id(module));
		module->rename(wire_to_rename, to_name);
		if (wire_to_rename->port_id || flag_output) {
			if (flag_output)
				wire_to_rename->port_output = true;
			module->fixup_ports();
		}
		return;
	}

	if (cell_to_rename != nullptr) {
		if (flag_output)
			log_cmd_error("Called with -output but the specified object is a cell.\n");
		log("Renaming cell %s to %s in module %s.\n", log_id(cell_to_rename), log_id(to_name), log_id(module));
		module->rename(cell_to_rename, to_name);
		return;
	}

	log_cmd_error("Object `%s' not found!\n", from_name.c_str());
}

static std::string derive_name_from_src(const std::string &src, int counter)
{
	std::string src_base = src.substr(0, src.find('|'));
	if (src_base.empty())
		return stringf("$%d", counter);
	else
		return stringf("\\%s$%d", src_base.c_str(), counter);
}

static IdString derive_name_from_cell_output_wire(const RTLIL::Cell *cell)
{
	// Find output
	const SigSpec *output = nullptr;
	int num_outputs = 0;
	for (auto &connection : cell->connections()) {
		if (cell->output(connection.first)) {
			output = &connection.second;
			num_outputs++;
		}
	}

	if (num_outputs != 1) // Skip cells thad drive multiple outputs
		return cell->name;

	std::string name = "";
	for (auto &chunk : output->chunks()) {
		// Skip cells that drive privately named wires
		if (!chunk.wire || chunk.wire->name.str()[0] == '$')
			return cell->name;

		if (name != "")
			name += "$";

		name += chunk.wire->name.str();
		if (chunk.wire->width != chunk.width) {
			name += "[";
			if (chunk.width != 1)
				name += std::to_string(chunk.offset + chunk.width) + ":";
			name += std::to_string(chunk.offset) + "]";
		}
	}

	return name + cell->type.str();
}

struct RenamePass : public Pass {
	RenamePass() : Pass("rename", "rename object in the design") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    rename old_name new_name\n");
		log("\n");
		log("Rename the specified object. Note that selection patterns are not supported\n");
		log("by this command.\n");
		log("\n");
		log("\n");
		log("\n");
		log("    rename -output old_name new_name\n");
		log("\n");
		log("Like above, but also make the wire an output. This will fail if the object is\n");
		log("not a wire.\n");
		log("\n");
		log("\n");
		log("    rename -src [selection]\n");
		log("\n");
		log("Assign names auto-generated from the src attribute to all selected wires and\n");
		log("cells with private names.\n");
		log("\n");
		log("\n");
		log("    rename -wire [selection]\n");
		log("\n");
		log("Assign auto-generated names based on the wires they drive to all selected\n");
		log("cells with private names. Ignores cells driving privatly named wires.\n");
		log("\n");
		log("\n");
		log("    rename -enumerate [-pattern <pattern>] [selection]\n");
		log("\n");
		log("Assign short auto-generated names to all selected wires and cells with private\n");
		log("names. The -pattern option can be used to set the pattern for the new names.\n");
		log("The character %% in the pattern is replaced with a integer number. The default\n");
		log("pattern is '_%%_'.\n");
		log("\n");
		log("\n");
		log("    rename -hide [selection]\n");
		log("\n");
		log("Assign private names (the ones with $-prefix) to all selected wires and cells\n");
		log("with public names. This ignores all selected ports.\n");
		log("\n");
		log("\n");
		log("    rename -top new_name\n");
		log("\n");
		log("Rename top module.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string pattern_prefix = "_", pattern_suffix = "_";
		bool flag_src = false;
		bool flag_wire = false;
		bool flag_enumerate = false;
		bool flag_hide = false;
		bool flag_top = false;
		bool flag_output = false;
		bool got_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-src" && !got_mode) {
				flag_src = true;
				got_mode = true;
				continue;
			}
			if (arg == "-output" && !got_mode) {
				flag_output = true;
				got_mode = true;
				continue;
			}
			if (arg == "-wire" && !got_mode) {
				flag_wire = true;
				got_mode = true;
				continue;
			}
			if (arg == "-enumerate" && !got_mode) {
				flag_enumerate = true;
				got_mode = true;
				continue;
			}
			if (arg == "-hide" && !got_mode) {
				flag_hide = true;
				got_mode = true;
				continue;
			}
			if (arg == "-top" && !got_mode) {
				flag_top = true;
				got_mode = true;
				continue;
			}
			if (arg == "-pattern" && argidx+1 < args.size() && args[argidx+1].find('%') != std::string::npos) {
				int pos = args[++argidx].find('%');
				pattern_prefix = args[argidx].substr(0, pos);
				pattern_suffix = args[argidx].substr(pos+1);
				continue;
			}
			break;
		}

		if (flag_src)
		{
			extra_args(args, argidx, design);

			for (auto module : design->selected_modules())
			{
				int counter = 0;
				dict<RTLIL::Wire *, IdString> new_wire_names;
				dict<RTLIL::Cell *, IdString> new_cell_names;

				for (auto wire : module->selected_wires())
					if (wire->name[0] == '$')
						new_wire_names.emplace(wire, derive_name_from_src(wire->get_src_attribute(), counter++));

				for (auto cell : module->selected_cells())
					if (cell->name[0] == '$')
						new_cell_names.emplace(cell, derive_name_from_src(cell->get_src_attribute(), counter++));

				for (auto &it : new_wire_names)
					module->rename(it.first, it.second);

				for (auto &it : new_cell_names)
					module->rename(it.first, it.second);
			}
		}
		else
		if (flag_wire)
		{
			extra_args(args, argidx, design);

			for (auto module : design->selected_modules()) {
				dict<RTLIL::Cell *, IdString> new_cell_names;
				for (auto cell : module->selected_cells())
					if (cell->name[0] == '$')
						new_cell_names[cell] = derive_name_from_cell_output_wire(cell);
				for (auto &it : new_cell_names)
					module->rename(it.first, it.second);
			}
		}
		else
		if (flag_enumerate)
		{
			extra_args(args, argidx, design);

			for (auto module : design->selected_modules())
			{
				int counter = 0;
				dict<RTLIL::Wire *, IdString> new_wire_names;
				dict<RTLIL::Cell *, IdString> new_cell_names;

				for (auto wire : module->selected_wires())
					if (wire->name[0] == '$') {
						RTLIL::IdString buf;
						do buf = stringf("\\%s%d%s", pattern_prefix.c_str(), counter++, pattern_suffix.c_str());
						while (module->wire(buf) != nullptr);
						new_wire_names[wire] = buf;
					}

				for (auto cell : module->selected_cells())
					if (cell->name[0] == '$') {
						RTLIL::IdString buf;
						do buf = stringf("\\%s%d%s", pattern_prefix.c_str(), counter++, pattern_suffix.c_str());
						while (module->cell(buf) != nullptr);
						new_cell_names[cell] = buf;
					}

				for (auto &it : new_wire_names)
					module->rename(it.first, it.second);

				for (auto &it : new_cell_names)
					module->rename(it.first, it.second);
			}
		}
		else
		if (flag_hide)
		{
			extra_args(args, argidx, design);

			for (auto module : design->selected_modules())
			{
				dict<RTLIL::Wire *, IdString> new_wire_names;
				dict<RTLIL::Cell *, IdString> new_cell_names;

				for (auto wire : module->selected_wires())
					if (wire->name.isPublic() && wire->port_id == 0)
						new_wire_names[wire] = NEW_ID;

				for (auto cell : module->selected_cells())
					if (cell->name.isPublic())
						new_cell_names[cell] = NEW_ID;

				for (auto &it : new_wire_names)
					module->rename(it.first, it.second);

				for (auto &it : new_cell_names)
					module->rename(it.first, it.second);
			}
		}
		else
		if (flag_top)
		{
			if (argidx+1 != args.size())
				log_cmd_error("Invalid number of arguments!\n");

			IdString new_name = RTLIL::escape_id(args[argidx]);
			RTLIL::Module *module = design->top_module();

			if (module == nullptr)
				log_cmd_error("No top module found!\n");

			log("Renaming module %s to %s.\n", log_id(module), log_id(new_name));
			design->rename(module, new_name);
		}
		else
		{
			if (argidx+2 != args.size())
				log_cmd_error("Invalid number of arguments!\n");

			std::string from_name = args[argidx++];
			std::string to_name = args[argidx++];

			if (!design->selected_active_module.empty())
			{
				if (design->module(design->selected_active_module) != nullptr)
					rename_in_module(design->module(design->selected_active_module), from_name, to_name, flag_output);
			}
			else
			{
				if (flag_output)
					log_cmd_error("Mode -output requires that there is an active module selected.\n");

				RTLIL::Module *module_to_rename = nullptr;
				for (auto module : design->modules())
					if (module->name == from_name || RTLIL::unescape_id(module->name) == from_name) {
						module_to_rename = module;
						break;
					}

				if (module_to_rename != nullptr) {
					to_name = RTLIL::escape_id(to_name);
					log("Renaming module %s to %s.\n", module_to_rename->name.c_str(), to_name.c_str());
					design->rename(module_to_rename, to_name);
				} else
					log_cmd_error("Object `%s' not found!\n", from_name.c_str());
			}
		}
	}
} RenamePass;

PRIVATE_NAMESPACE_END
