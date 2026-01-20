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

#include "kernel/yosys.h"
#include <regex>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RegWires {
	std::vector<std::pair<Wire*, int>> oldWires;
	int origRegWidth;
};

struct RegRenamePass : public Pass {
	RegRenamePass() : Pass("reg_rename", "renames register output wires to the correct register name and creates new wires for multi-bit registers for correct VCD register annotations.") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    reg_rename\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing reg_rename pass\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// No options currently. When adding in the future make sure to update docstring with [options]
			break;
		}
		extra_args(args, argidx, design);

		uint32_t count = 0;
		uint32_t moduleCount = design->selected_modules().size();

		// Data structure used to keep track of multi-bit registers.
		// Relevant for correct register annotation.
		// Key is (Module*, baseName) to handle hierarchical designs where multiple modules may have same register names
		// Value is a vector of (Wire*, index) pairs to connect the renamed registers to the corresponding index of the new wire
		std::map<std::pair<Module*, std::string>, RegWires> regWireMap;

		// Regex to match register output wires
		// .*_reg[NUMBER] or .*_reg, can match NUMBER and part before _reg
		std::regex reg_regex("(.*)_reg(?:\\[(\\d+)\\])?$");
		for (auto module : design->selected_modules()) {
			pool<Wire *> wiresToRemove; // pool of wires to remove from the netlist
			for (auto cell : module->selected_cells()) {

				// Rename register output wires to corresponding testbench names
				std::smatch match;
				std::string name = cell->name.c_str();
				if (std::regex_match(name, match, reg_regex)) {

					// baseName is the part before _reg
					std::string baseName = match[1].str();

					// Check if the register is a multi-bit register (look for [NUMBER] match in regex)
					bool isMultiBit = match.size() > 2 && match[2].matched;
					std::string indexStr;
					for (auto conn : cell->connections()) {
						if (conn.first == ID::Q && conn.second.is_wire()) {
							Wire *oldWire = conn.second.as_wire();

							// Skip if this wire is a module port (input/output)
							if (oldWire->port_input || oldWire->port_output) {
								log("Skipping port wire %s in register renaming for cell %s in module %s\n", 
									oldWire->name.c_str(), log_id(cell), log_id(module));
								continue;
							}

							// Different cases for multi-bit and single-bit registers
							if (isMultiBit) {

								// Index of the register
								int index = std::stoi(match[2].str());

								// Get or create the multi-bit wire
								Wire *newWire = module->wire(RTLIL::escape_id(baseName));
								if (newWire == nullptr) {
									// Wire doesn't exist, create it with the original register width
									int origRegWidth = std::stoi(cell->get_string_attribute("$ORIG_REG_WIDTH"));
									log("Creating multi-bit wire %s with width %d in module %s\n",
										baseName.c_str(), origRegWidth, log_id(module));
									newWire = module->addWire(RTLIL::escape_id(baseName), origRegWidth);
								}

								// Log that the new wire is being connected to the register
								log("Connecting register wire %s to bit %d of %s in module %s\n",
									newWire->name.c_str(), index, baseName.c_str(), log_id(module));
								
								// Replace all uses of oldWire with newWire[index]
								auto rewriter = [&](SigSpec &sig) {
									sig.replace(SigBit(oldWire), SigSpec(newWire, index, 1));
								};
								module->rewrite_sigspecs(rewriter);
								
								// Mark old wire for deletion
								log("Marking old wire %s for deletion in module %s\n",
									oldWire->name.c_str(), log_id(module));
								wiresToRemove.insert(oldWire);
								count++;
							} else {
								if (oldWire->name != baseName) {
									// Rename single-bit register to correct name from RTL
									log("Renaming register wire %s to %s for cell %s in module %s\n", 
										oldWire->name.c_str(), baseName, log_id(cell), log_id(module));
									module->rename(oldWire, baseName);
									count++;
								}
							}
						}
					}
				}
			}
			module->remove(wiresToRemove);
		}

		// End
		log("Renamed %d registers in %d modules\n", count, moduleCount);
		log_flush();
	}
} RegRenamePass;

PRIVATE_NAMESPACE_END
