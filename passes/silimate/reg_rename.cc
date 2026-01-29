/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2026  Stan Lee          <stan@silimate.com>
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

#include "kernel/fstdata.h"
#include "kernel/yosys.h"
#include <regex>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RegRenameInstance {
	std::string vcd_scope;
	Module *module;
	dict<Cell *, RegRenameInstance *> children;

	// Constructor
	// When constructing, it will recursively build the module hierarchy with correct VCD scope mapping
	RegRenameInstance(std::string scope, Module *mod) : vcd_scope(scope), module(mod)
	{
		// Loop through all cells in the module
		for (auto cell : module->cells()) {
			Module *child = module->design->module(cell->type);
			if (child == nullptr) {
				continue; // skip non-module cells
			}
			// Construct the child's scope in VCD format, which is the parent scope plus the instance name
			std::string child_scope = vcd_scope + "." + RTLIL::unescape_id(cell->name);
			children[cell] = new RegRenameInstance(child_scope, child);
		}
	}

	// Deconstructor
	~RegRenameInstance()
	{
		for (auto &it : children)
			delete it.second;
	}

	// Processes registers in a given module hierarchy and renames to allow for correct register annotation
	void process_registers(dict<std::pair<std::string, std::string>, int> &vcd_reg_widths)
	{
		std::regex reg_regex("(.*)_reg(?:\\[(\\d+)\\])?$");
		pool<Wire *> wiresToRemove;

		// Loop through all cells in the module
		for (auto cell : module->cells()) {

			// Skip non-register cells
			if (!RTLIL::builtin_ff_cell_types().count(cell->type)) {
				continue;
			}

			// Extract the register name from the cell name
			std::smatch match;
			std::string name = cell->name.c_str();
			if (!std::regex_match(name, match, reg_regex)) {
				log_warning("Unable to extract register name from cell %s\n", name.c_str());
				continue;
			}

			// Register name
			std::string baseName = RTLIL::unescape_id(match[1].str());
			bool isMultiBit = match.size() > 2 && match[2].matched;

			for (auto conn : cell->connections()) {

				// Rename wires from the register output
				if (conn.first == ID::Q && conn.second.is_wire()) {
					Wire *oldWire = conn.second.as_wire();

					// Skip wires that are inputs or outputs
					if (oldWire->port_input || oldWire->port_output)
						continue;

					// If the register is multi-bit, we must create a new wire
					if (isMultiBit) {
						int index = std::stoi(match[2].str());

						// Lookup the original register width using the VCD scope and netlist-extracted register name
						int origRegWidth = vcd_reg_widths[{vcd_scope, baseName}];
						if (origRegWidth == 0) { // if not found, log a warning and skip
							log_warning("Register '%s' with extracted name '%s' in scope '%s' not found in VCD\n",
								    cell->name.c_str(), baseName.c_str(), vcd_scope.c_str());
							continue;
						}

						// Create a new wire for the multi-bit register if it doesn't exist already
						Wire *newWire = module->wire(RTLIL::escape_id(baseName));
						if (newWire == nullptr) {
							log("Creating wire %s[%d:0] in scope %s\n", baseName.c_str(), origRegWidth - 1,
							    vcd_scope.c_str());
							newWire = module->addWire(RTLIL::escape_id(baseName), origRegWidth);
						}

						// Log the connection of the new wire to the register
						log("Connecting register wire %s[%d] to bit %d of %s in module %s\n", newWire->name.c_str(), index,
						    index, log_id(newWire), log_id(module));

						// Replace old connection with a new one even at the input ports of subsequent cells from the register
						// output
						auto rewriter = [&](SigSpec &sig) { sig.replace(SigBit(oldWire), SigSpec(newWire, index, 1)); };
						module->rewrite_sigspecs(rewriter);

						// Add the old wires to the list of wires to delete after processing
						wiresToRemove.insert(oldWire);
					} else {
						// Single-bit register rename
						IdString target_name = RTLIL::escape_id(baseName);
						if (oldWire->name != target_name && !module->wire(target_name)) {
							log("Renaming %s to %s in scope %s\n", oldWire->name.c_str(), target_name.c_str(),
							    vcd_scope.c_str());
							module->rename(oldWire, target_name);
						}
					}
				}
			}
		}
		// Delete the old unused wires
		module->remove(wiresToRemove);
	}

	void process_all(dict<std::pair<std::string, std::string>, int> &vcd_reg_widths)
	{
		process_registers(vcd_reg_widths);
		for (auto &it : children)
			it.second->process_all(vcd_reg_widths);
	}
};

struct RegRenamePass : public Pass {
	RegRenamePass()
	    : Pass("reg_rename", "renames register output wires to the correct register name and creates new wires for multi-bit registers for "
				 "correct VCD register annotations.")
	{
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    reg_rename [options]\n");
		log("\n");
		log("    -vcd <filename>\n");
		log("        vcd file to extract original register width from\n");
		log("    -scope <scope>\n");
		log("        scope to process in vcd file\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing reg_rename pass\n");

		// Argument parsing
		std::string vcd_filename;
		std::string scope;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-vcd" && argidx + 1 < args.size()) {
				vcd_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-scope" && argidx + 1 < args.size()) {
				scope = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Extract pre-optimization register widths from VCD file
		dict<std::pair<std::string, std::string>, int> vcd_reg_widths;
		if (!vcd_filename.empty()) {
			if (scope.empty()) {
				log_error("No scope provided. Use -scope option.\n");
			}
			log("Reading VCD file: %s\n", vcd_filename.c_str());
			try {
				FstData fst(vcd_filename);
				for (auto &var : fst.getVars()) {
					if (var.is_reg) {
						std::string reg_vcd_scope = var.scope;
						std::string reg_name = var.name;

						// Remove bracket notation if present to preserve register name
						if (auto pos = reg_name.find('['); pos != std::string::npos)
							reg_name.erase(pos);

						// Map the register's vcd scope and name to its original width for later lookup
						vcd_reg_widths[{reg_vcd_scope, reg_name}] = var.width;
						log("Found register '%s' in scope '%s' with width %d\n", reg_name.c_str(), reg_vcd_scope.c_str(),
						    var.width);
					}
				}
				log("Extracted %d register widths from VCD\n", GetSize(vcd_reg_widths));
			} catch (const std::exception &e) {
				log_error("Failed to read VCD file '%s': %s\n", vcd_filename.c_str(), e.what());
			}
		} else {
			log_error("No VCD file provided. Use -vcd option.\n");
		}

		// STEP 2: Build hierarchy and process
		Module *topmod = design->top_module();
		if (!topmod)
			log_error("No top module found!\n");
		log("Building hierarchy from scope: %s\n", scope.c_str());

		// Build hierarchy and process register renamings
		RegRenameInstance *root = new RegRenameInstance(scope, topmod);
		root->process_all(vcd_reg_widths);
		delete root;

		log_flush();
	}
} RegRenamePass;

PRIVATE_NAMESPACE_END
