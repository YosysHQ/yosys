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


		// Regex to match register output wires
		// .*_reg[NUMBER] or .*_reg, can match NUMBER and part before _reg
		std::regex reg_regex("(.*)_reg(?:\\[(\\d+)\\])?$");
		for (auto module : design->selected_modules()) {
			for (auto cell : module->selected_cells()) {

				// Rename register output wires to corresponding testbench names
				std::smatch match;
				std::string name = cell->name.c_str();
				if (std::regex_match(name, match, reg_regex)) {


					std::string origRegWidth = cell->get_string_attribute("$ORIG_REG_WIDTH");
					log("Original register width for cell %s: %s\n", cell->name.c_str(), origRegWidth.c_str());

					// baseName is the part before _reg
					std::string baseName = match[1].str();
					std::string registerName = baseName;
					if (match.size() > 2 && match[2].matched) {
						// indexStr is the NUMBER in .*_reg[NUMBER]
						std::string indexStr = match[2].str();
						registerName += indexStr;
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
							module->rename(wire, registerName);
							count++;
						}
					}
				}
			}
		}
		log("Renamed %d registers in %d modules\n", count, moduleCount);
		log_flush();
	}
} RegRenamePass;

PRIVATE_NAMESPACE_END
