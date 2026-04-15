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
#include "passes/silimate/reg_rename.h"
#include <regex>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RegRenameInstance {
	std::string vcd_scope;
	Module *module;
	bool debug;
	dict<Cell*, RegRenameInstance *> children;

	// Constructor
	// When constructing, it will recursively build the
	// module hierarchy with correct VCD scope mapping
	RegRenameInstance(std::string scope, Module *mod, bool dbg = false) : vcd_scope(scope), module(mod), debug(dbg)
	{
		// Loop through all cells in the module
		for (auto cell : module->cells()) {
			Module *child = module->design->module(cell->type);
			if (child == nullptr) {
				continue; // skip non-module cells
			}
			// Construct the child's scope in VCD format,
			// which is the parent scope plus the instance name
			std::string child_scope = vcd_scope + "." + RTLIL::unescape_id(cell->name);
			children[cell] = new RegRenameInstance(child_scope, child, debug);
		}
	}

	// Destructor
	~RegRenameInstance()
	{
		for (auto &it : children)
			delete it.second;
	}

	// Processes registers in a given module hierarchy
	// and renames to allow for correct register annotation
	void process_registers(dict<std::pair<std::string, std::string>, int> &vcd_reg_widths)
	{
		if (debug)
			log("Processing registers in scope: %s (module: %s)\n", 
					vcd_scope.c_str(), log_id(module->name));

		pool<Wire *> wiresToRemove;

		// Loop through all cells in the module
		for (auto cell : module->cells()) {

			// Skip non-register cells
			if (!RTLIL::builtin_ff_cell_types().count(cell->type)) {
				continue;
			}

			// We know it is a reg with _reg suffix with all brackets removed
			std::string searchName = cell->name.c_str();
			if (auto pos = searchName.find('['); pos != std::string::npos)
				searchName.erase(pos);

			// If register name with no brackets ends with _reg, we can process it
			size_t reg_pos = searchName.rfind("_reg");
			if (reg_pos != std::string::npos && reg_pos == searchName.size() - 4) {

				// Remove "_reg" to get the target wire specification
				std::string cellName = cell->name.c_str();
				cellName.erase(reg_pos, 4);

				// Index comes from the right-most brackets
				std::string wireName;
				int bitIndex = 0;
				size_t last_open = cellName.rfind('[');
				size_t last_close = cellName.rfind(']');
				if (last_open != std::string::npos && last_close != std::string::npos && last_close > last_open) {
						wireName = cellName.substr(0, last_open);
						bitIndex = std::stoi(cellName.substr(last_open + 1, last_close - last_open - 1));
				} else {
						wireName = cellName;
						bitIndex = 0;
				}

				// Process Q output connection for the cell
				for (auto &conn : cell->connections()) {
					if (conn.first != ID::Q || !conn.second.is_wire()) continue;

					Wire *oldWire = conn.second.as_wire();
					if (oldWire->port_input || oldWire->port_output) continue;

					// Lookup wire width from VCD
					std::string regName = RTLIL::unescape_id(wireName);
					int wireWidth = vcd_reg_widths[{vcd_scope, regName}];
					if (wireWidth == 0) {
						if (debug)
							log("Register '%s' not found in VCD scope '%s' (cell: %s)\n",
								regName.c_str(), vcd_scope.c_str(), cellName.c_str());
						continue;
					}

					// Validate bit index
					if (bitIndex >= wireWidth) {
							log_warning("Bit index %d exceeds wire width %d for '%s'\n",
													bitIndex, wireWidth, wireName.c_str());
							continue;
					}

					IdString wireId = RTLIL::escape_id(wireName);

					// Single-bit wire requires only simple renaming
					if (wireWidth == 1 && bitIndex == 0) {
							if (oldWire->name != wireId && !module->wire(wireId)) {
									if (debug)
										log("Renaming %s to %s\n", log_id(oldWire), wireName.c_str());
									module->rename(oldWire, wireId);
							}
							continue;
					}

					// Multi-bit wire requires creating a new wire and rewiring connections
					Wire *targetWire = module->wire(wireId);
				
					if (!targetWire) {
						if (debug)
							log("Creating wire %s[%d:0] in scope %s\n", 
									wireName.c_str(), wireWidth - 1, vcd_scope.c_str());
						targetWire = module->addWire(wireId, wireWidth);
					}
				
					if (debug)
						log("Connecting %s to %s[%d]\n", 
								log_id(oldWire), wireName.c_str(), bitIndex);
				
					auto rewriter = [&](SigSpec &sig) { 
						sig.replace(SigBit(oldWire), SigSpec(targetWire, bitIndex, 1)); 
					};
					module->rewrite_sigspecs(rewriter);
					
					wiresToRemove.insert(oldWire);
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
	    : Pass("reg_rename", "renames register output wires to the correct "
				"register name and creates new wires for multi-bit registers for "
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
		log("    -d\n");
		log("        enable debug output\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing reg_rename pass\n");

		// Argument parsing
		std::string vcd_filename;
		std::string scope;
		bool debug = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-vcd" && argidx + 1 < args.size()) {
				vcd_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-scope" && argidx + 1 < args.size()) {
				scope = normalize_scope(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-d") {
				debug = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// Extract top module
		Module *topmod = design->top_module();
		if (!topmod)
			log_error("No top module found!\n");

		// Extract pre-optimization register widths from VCD file
		dict<std::pair<std::string, std::string>, int> vcd_reg_widths;
		if (!vcd_filename.empty()) {
			log("Reading VCD file: %s\n", vcd_filename.c_str());
			try {
				FstData fst(vcd_filename);
				if (scope.empty()) {
					scope = fst.autoScope(topmod);
					if (scope.empty()) {
						log_error("No scope found for module '%s'. Please specify -scope explicitly.\n", 
							RTLIL::unescape_id(topmod->name).c_str());
					}
				}
				log("Using scope: \"%s\"\n", scope.c_str());
				for (auto &var : fst.getVars()) {
					if (var.is_reg) {
						std::string reg_vcd_scope = var.scope;
						std::string reg_name = var.name;

						// Remove bracket notation if present to preserve register name
						if (auto pos = reg_name.rfind('['); pos != std::string::npos)
							reg_name.erase(pos);

						// Map the register's vcd scope and name to
						// its original width for later lookup.
						reg_name = RTLIL::unescape_id(reg_name);
						vcd_reg_widths[{reg_vcd_scope, reg_name}] = var.width;
						if (debug)
							log("Found register '%s' in scope '%s' with width %d\n",
								reg_name.c_str(), reg_vcd_scope.c_str(), var.width);
					}
				}
				log("Extracted %d register widths from VCD\n", GetSize(vcd_reg_widths));
			} catch (const std::exception &e) {
				log_error("Failed to read VCD file '%s': %s\n", 
					vcd_filename.c_str(), e.what());
			}
		} else {
			log_error("No VCD file provided. Use -vcd option.\n");
		}

		// STEP 2: Build hierarchy and process
		log("Building hierarchy from scope: %s\n", scope.c_str());

		// Build hierarchy and process register renamings
		RegRenameInstance *root = new RegRenameInstance(scope, topmod, debug);
		root->process_all(vcd_reg_widths);
		delete root;

		log_flush();
	}
} RegRenamePass;

PRIVATE_NAMESPACE_END
