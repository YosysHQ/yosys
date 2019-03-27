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

	for (auto &it : module->wires_)
		if (it.first == from_name) {
			Wire *w = it.second;
			log("Renaming wire %s to %s in module %s.\n", log_id(w), log_id(to_name), log_id(module));
			module->rename(w, to_name);
			if (w->port_id || flag_output) {
				if (flag_output)
					w->port_output = true;
				module->fixup_ports();
			}
			return;
		}

	for (auto &it : module->cells_)
		if (it.first == from_name) {
			if (flag_output)
				log_cmd_error("Called with -output but the specified object is a cell.\n");
			log("Renaming cell %s to %s in module %s.\n", log_id(it.second), log_id(to_name), log_id(module));
			module->rename(it.second, to_name);
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

static IdString derive_name_from_wire(const RTLIL::Cell &cell)
{
	// Find output
	const SigSpec *output = nullptr;
	int num_outputs = 0;
	for (auto &connection : cell.connections()) {
		if (cell.output(connection.first)) {
			output = &connection.second;
			num_outputs++;
		}
	}

	if (num_outputs != 1) // Skip cells thad drive multiple outputs
		return cell.name;

	std::string name = "";
	for (auto &chunk : output->chunks()) {
		// Skip cells that drive privately named wires
		if (!chunk.wire || chunk.wire->name.str()[0] == '$')
			return cell.name;

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

	return name + cell.type.str();
}

struct RenamePass : public Pass {
	RenamePass() : Pass("rename", "rename object in the design") { }
	void help() YS_OVERRIDE
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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

			for (auto &mod : design->modules_)
			{
				int counter = 0;

				RTLIL::Module *module = mod.second;
				if (!design->selected(module))
					continue;

				dict<RTLIL::IdString, RTLIL::Wire*> new_wires;
				for (auto &it : module->wires_) {
					if (it.first[0] == '$' && design->selected(module, it.second))
						it.second->name = derive_name_from_src(it.second->get_src_attribute(), counter++);
					new_wires[it.second->name] = it.second;
				}
				module->wires_.swap(new_wires);
				module->fixup_ports();

				dict<RTLIL::IdString, RTLIL::Cell*> new_cells;
				for (auto &it : module->cells_) {
					if (it.first[0] == '$' && design->selected(module, it.second))
						it.second->name = derive_name_from_src(it.second->get_src_attribute(), counter++);
					new_cells[it.second->name] = it.second;
				}
				module->cells_.swap(new_cells);
			}
		}
		else
		if (flag_wire)
		{
			extra_args(args, argidx, design);

			for (auto &mod : design->modules_)
			{
				RTLIL::Module *module = mod.second;
				if (!design->selected(module))
					continue;

				dict<RTLIL::IdString, RTLIL::Cell*> new_cells;
				for (auto &it : module->cells_) {
					if (it.first[0] == '$' && design->selected(module, it.second))
						it.second->name = derive_name_from_wire(*it.second);
					new_cells[it.second->name] = it.second;
				}
				module->cells_.swap(new_cells);
			}
		}
		else
		if (flag_enumerate)
		{
			extra_args(args, argidx, design);

			for (auto &mod : design->modules_)
			{
				int counter = 0;

				RTLIL::Module *module = mod.second;
				if (!design->selected(module))
					continue;

				dict<RTLIL::IdString, RTLIL::Wire*> new_wires;
				for (auto &it : module->wires_) {
					if (it.first[0] == '$' && design->selected(module, it.second))
						do it.second->name = stringf("\\%s%d%s", pattern_prefix.c_str(), counter++, pattern_suffix.c_str());
						while (module->count_id(it.second->name) > 0);
					new_wires[it.second->name] = it.second;
				}
				module->wires_.swap(new_wires);
				module->fixup_ports();

				dict<RTLIL::IdString, RTLIL::Cell*> new_cells;
				for (auto &it : module->cells_) {
					if (it.first[0] == '$' && design->selected(module, it.second))
						do it.second->name = stringf("\\%s%d%s", pattern_prefix.c_str(), counter++, pattern_suffix.c_str());
						while (module->count_id(it.second->name) > 0);
					new_cells[it.second->name] = it.second;
				}
				module->cells_.swap(new_cells);
			}
		}
		else
		if (flag_hide)
		{
			extra_args(args, argidx, design);

			for (auto &mod : design->modules_)
			{
				RTLIL::Module *module = mod.second;
				if (!design->selected(module))
					continue;

				dict<RTLIL::IdString, RTLIL::Wire*> new_wires;
				for (auto &it : module->wires_) {
					if (design->selected(module, it.second))
						if (it.first[0] == '\\' && it.second->port_id == 0)
							it.second->name = NEW_ID;
					new_wires[it.second->name] = it.second;
				}
				module->wires_.swap(new_wires);
				module->fixup_ports();

				dict<RTLIL::IdString, RTLIL::Cell*> new_cells;
				for (auto &it : module->cells_) {
					if (design->selected(module, it.second))
						if (it.first[0] == '\\')
							it.second->name = NEW_ID;
					new_cells[it.second->name] = it.second;
				}
				module->cells_.swap(new_cells);
			}
		}
		else
		if (flag_top)
		{
			if (argidx+1 != args.size())
				log_cmd_error("Invalid number of arguments!\n");

			IdString new_name = RTLIL::escape_id(args[argidx]);
			RTLIL::Module *module = design->top_module();

			if (module == NULL)
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
				if (design->modules_.count(design->selected_active_module) > 0)
					rename_in_module(design->modules_.at(design->selected_active_module), from_name, to_name, flag_output);
			}
			else
			{
				if (flag_output)
					log_cmd_error("Mode -output requires that there is an active module selected.\n");
				for (auto &mod : design->modules_) {
					if (mod.first == from_name || RTLIL::unescape_id(mod.first) == from_name) {
						to_name = RTLIL::escape_id(to_name);
						log("Renaming module %s to %s.\n", mod.first.c_str(), to_name.c_str());
						RTLIL::Module *module = mod.second;
						design->modules_.erase(module->name);
						module->name = to_name;
						design->modules_[module->name] = module;
						goto rename_ok;
					}
				}

				log_cmd_error("Object `%s' not found!\n", from_name.c_str());
			rename_ok:;
			}
		}
	}
} RenamePass;

PRIVATE_NAMESPACE_END
