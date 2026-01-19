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

struct CellTracker {
	Cell *cell;
	int index;
};

struct RegTracker {
	std::map<std::string, CellTracker> renamedRegs;
	std::string origRegWidth;
	Module *module;
};

struct RegRenamePass : public Pass {
	RegRenamePass() : Pass("reg_rename", "renames register output wires to the correct register name") { }
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
		std::map<std::string, RegTracker> regTrackers;

		// Regex to match register output wires
		// .*_reg[NUMBER] or .*_reg, can match NUMBER and part before _reg
		std::regex reg_regex("(.*)_reg(?:\\[(\\d+)\\])?$");
		for (auto module : design->selected_modules()) {
			for (auto cell : module->selected_cells()) {

				// Rename register output wires to corresponding testbench names
				std::smatch match;
				std::string name = cell->name.c_str();
				if (std::regex_match(name, match, reg_regex)) {

					// baseName is the part before _reg
					std::string baseName = match[1].str();
					std::string registerName = baseName;

					// Check if the register is a multi-bit register
					bool isMultiBit = match.size() > 2 && match[2].matched;
					std::string indexStr;
					if (isMultiBit) {
						// indexStr is the NUMBER in .*_reg[NUMBER]
						indexStr = match[2].str();
						registerName += "_" + indexStr;
					}

					for (auto conn : cell->connections()) {
						if (conn.first == ID::Q && conn.second.is_wire()) {
							Wire *wire = conn.second.as_wire();

							// Skip if this wire is a module port (input/output)
							if (wire->port_input || wire->port_output) {
								log("Skipping port wire %s in register renaming for cell %s in module %s\n", 
									wire->name.c_str(), log_id(cell), log_id(module));
								continue;
							}

							// Skip if we already renamed the wire
							if (wire->name == registerName) {
								continue;
							}

							// Rename register
							log("Renaming register wire %s to %s for cell %s in module %s\n", 
								wire->name.c_str(), registerName, log_id(cell), log_id(module));

							// Log relevant information for multi-bit registers for wire reconstruction
							if (isMultiBit) {
								std::string origRegWidth = cell->get_string_attribute("$ORIG_REG_WIDTH");
								regTrackers[baseName].origRegWidth = origRegWidth;
								regTrackers[baseName].renamedRegs[registerName] = CellTracker{cell, std::stoi(indexStr)};
								regTrackers[baseName].module = module;
							}
								
							module->rename(wire, registerName);
							count++;
						}
					}
				}
			}
		}

	for (const auto &[baseName, regTracker] : regTrackers) {

		// Get the module for this register
		Module *mod = regTracker.module;

		// Create a new wire for the multi-bit register
		int width = std::stoi(regTracker.origRegWidth);
		log("Creating new wire %s for register %s with width %d\n", baseName.c_str(), baseName.c_str(), width);
		Wire *newWire = mod->addWire(baseName, width);

		pool<Wire *> oldWires;

		// Connect the renamed registers to the corresponding index of the new wire
		for (const auto &[renamedRegName, cellTracker] : regTracker.renamedRegs) {

			// Get the old wire (the Q output that was renamed)
			Wire *oldWire = cellTracker.cell->getPort(ID::Q).as_wire();

			// Get the index of the renamed register
			int index = cellTracker.index;
			log("Connecting renamed register %s to index %d\n", renamedRegName.c_str(), index);

			// Connect the renamed register to the corresponding index of the new wire
			mod->connect(SigSpec(newWire, index, 1), cellTracker.cell->getPort(ID::Q));

			// Replace all uses of oldWire with newWire[index] throughout the module
			auto rewriter = [&](SigSpec &sig) {
				sig.replace(SigBit(oldWire), SigSpec(newWire, index, 1));
			};
			mod->rewrite_sigspecs(rewriter);

			// Add the old wire to the list of old wires to delete
			oldWires.insert(oldWire);
		}

		// Delete the old wires
		mod->remove(oldWires);
	}


		log("Renamed %d registers in %d modules\n", count, moduleCount);
		log_flush();
	}
} RegRenamePass;

PRIVATE_NAMESPACE_END
