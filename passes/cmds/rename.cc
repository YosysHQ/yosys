/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/hashlib.h"

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

static IdString derive_name_from_cell_output_wire(const RTLIL::Cell *cell, string suffix)
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

	if (suffix.empty()) {
		suffix = cell->type.str();
	}
	return name + suffix;
}

static bool rename_witness(RTLIL::Design *design, dict<RTLIL::Module *, int> &cache, RTLIL::Module *module)
{
	auto cached = cache.find(module);
	if (cached != cache.end()) {
		if (cached->second == -1)
			log_error("Cannot rename witness signals in a design containing recursive instantiations.\n");
		return cached->second;
	}
	cache.emplace(module, -1);

	std::vector<std::pair<Cell *, IdString>> renames;

	bool has_witness_signals = false;
	for (auto cell : module->cells())
	{
		RTLIL::Module *impl = design->module(cell->type);
		if (impl != nullptr) {
			bool witness_in_cell = rename_witness(design, cache, impl);
			has_witness_signals |= witness_in_cell;
			if (witness_in_cell && !cell->name.isPublic()) {
				std::string name = cell->name.c_str() + 1;
				for (auto &c : name)
					if ((c < 'a' || c > 'z') && (c < 'A' || c > 'Z') && (c < '0' || c > '9') && c != '_')
						c = '_';
				auto new_id = module->uniquify("\\_witness_." + name);
				cell->set_hdlname_attribute({ "_witness_", strstr(new_id.c_str(), ".") + 1 });
				renames.emplace_back(cell, new_id);
			}
		}

		if (cell->type.in(ID($anyconst), ID($anyseq), ID($anyinit), ID($allconst), ID($allseq))) {
			has_witness_signals = true;
			IdString QY;
			bool clk2fflogic = false;
			if (cell->type == ID($anyinit))
				QY = (clk2fflogic = cell->get_bool_attribute(ID(clk2fflogic))) ? ID::D : ID::Q;
			else
				QY = ID::Y;
			auto sig_out = cell->getPort(QY);

			for (auto chunk : sig_out.chunks()) {
				if (chunk.is_wire() && !chunk.wire->name.isPublic()) {
					std::string name = stringf("%s_%s", cell->type.c_str() + 1, cell->name.c_str() + 1);
					for (auto &c : name)
						if ((c < 'a' || c > 'z') && (c < 'A' || c > 'Z') && (c < '0' || c > '9') && c != '_')
							c = '_';
					auto new_id = module->uniquify("\\_witness_." + name);
					auto new_wire = module->addWire(new_id, GetSize(sig_out));
					new_wire->set_hdlname_attribute({ "_witness_", strstr(new_id.c_str(), ".") + 1 });
					if (clk2fflogic)
						module->connect({new_wire, sig_out});
					else
						module->connect({sig_out, new_wire});
					cell->setPort(QY, new_wire);
					break;
				}
			}
		}


		if (cell->type.in(ID($assert), ID($assume), ID($cover), ID($live), ID($fair), ID($check))) {
			has_witness_signals = true;
			if (cell->name.isPublic())
				continue;
			std::string name = stringf("%s_%s", cell->type.c_str() + 1, cell->name.c_str() + 1);
			for (auto &c : name)
				if ((c < 'a' || c > 'z') && (c < 'A' || c > 'Z') && (c < '0' || c > '9') && c != '_')
					c = '_';
			auto new_id = module->uniquify("\\_witness_." + name);
			renames.emplace_back(cell, new_id);
			cell->set_hdlname_attribute({ "_witness_", strstr(new_id.c_str(), ".") + 1 });
		}
	}
	for (auto rename : renames) {
		module->rename(rename.first, rename.second);
	}

	cache[module] = has_witness_signals;
	return has_witness_signals;
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
		log("    rename -wire [selection] [-suffix <suffix>]\n");
		log("\n");
		log("Assign auto-generated names based on the wires they drive to all selected\n");
		log("cells with private names. Ignores cells driving privatly named wires.\n");
		log("By default, the cell is named after the wire with the cell type as suffix.\n");
		log("The -suffix option can be used to set the suffix to the given string instead.\n");
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
		log("    rename -witness\n");
		log("\n");
		log("Assigns auto-generated names to all $any*/$all* output wires and containing\n");
		log("cells that do not have a public name. This ensures that, during formal\n");
		log("verification, a solver-found trace can be fully specified using a public\n");
		log("hierarchical names.\n");
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
		log("\n");
		log("    rename -scramble-name [-seed <seed>] [selection]\n");
		log("\n");
		log("Assign randomly-generated names to all selected wires and cells. The seed option\n");
		log("can be used to change the random number generator seed from the default, but it\n");
		log("must be non-zero.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string pattern_prefix = "_", pattern_suffix = "_";
		std::string cell_suffix = "";
		bool flag_src = false;
		bool flag_wire = false;
		bool flag_enumerate = false;
		bool flag_witness = false;
		bool flag_hide = false;
		bool flag_top = false;
		bool flag_output = false;
		bool flag_scramble_name = false;
		bool got_mode = false;
		unsigned int seed = 1;

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
			if (arg == "-witness" && !got_mode) {
				flag_witness = true;
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
			if (arg == "-scramble-name" && !got_mode) {
				flag_scramble_name = true;
				got_mode = true;
				continue;
			}
			if (arg == "-pattern" && argidx+1 < args.size() && args[argidx+1].find('%') != std::string::npos) {
				int pos = args[++argidx].find('%');
				pattern_prefix = args[argidx].substr(0, pos);
				pattern_suffix = args[argidx].substr(pos+1);
				continue;
			}
			if (arg == "-suffix" && argidx + 1 < args.size()) {
				cell_suffix = args[++argidx];
				continue;
			}
			if (arg == "-seed" && argidx+1 < args.size()) {
				seed = std::stoi(args[++argidx]);
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
						new_cell_names[cell] = derive_name_from_cell_output_wire(cell, cell_suffix);
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
		if (flag_witness)
		{
			extra_args(args, argidx, design, false);

			RTLIL::Module *module = design->top_module();

			if (module == nullptr)
				log_cmd_error("No top module found!\n");

			dict<RTLIL::Module *, int> cache;
			rename_witness(design, cache, module);
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
		if (flag_scramble_name)
		{
			extra_args(args, argidx, design);

			if (seed == 0)
				log_error("Seed for -scramble-name cannot be zero.\n");

			for (auto module : design->selected_modules())
			{
				if (module->memories.size() != 0 || module->processes.size() != 0) {
					log_warning("Skipping module %s with unprocessed memories or processes\n", log_id(module));
					continue;
				}

				dict<RTLIL::Wire *, IdString> new_wire_names;
				dict<RTLIL::Cell *, IdString> new_cell_names;

				for (auto wire : module->selected_wires())
					if (wire->port_id == 0) {
						seed = mkhash_xorshift(seed);
						new_wire_names[wire] = stringf("$_%u_", seed);
					}

				for (auto cell : module->selected_cells()) {
					seed = mkhash_xorshift(seed);
					new_cell_names[cell] = stringf("$_%u_", seed);
				}

				for (auto &it : new_wire_names)
					module->rename(it.first, it.second);

				for (auto &it : new_cell_names)
					module->rename(it.first, it.second);
			}
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
