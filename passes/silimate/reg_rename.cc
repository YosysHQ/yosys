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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Struct stores the width and index offset of a register in VCD file.
struct RegInfo {
	int width = 0;
	int offset = 0;
};

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
	void process_registers(dict<std::string, RegInfo> &vcd_reg_widths)
	{
		if (debug)
			log("Processing registers in scope: %s (module: %s)\n", 
					vcd_scope.c_str(), log_id(module->name));
		else
			log("Processing registers in %s\n", 
					log_id(module->name));
		
		// Map of old bits to new bits of a renamed reg wire
		dict<SigBit, SigBit> bit_map;
		pool<SigBit> claimed_bits;

		// Caches of target wires and wires to remove
		dict<IdString, Wire*> targetWireCache;
		pool<Wire *> wireRemoveCache;
		
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
				std::string wireName = cellName;
				int bitIndex = 0;
				size_t last_open = cellName.rfind('[');
				size_t last_close = cellName.rfind(']');
				if (last_open != std::string::npos && last_close != std::string::npos && last_close > last_open) {
					// Validate bracket content is just a single bit slice
					std::string inner = cellName.substr(last_open + 1, last_close - last_open - 1);
					if (!inner.empty() && inner.find_first_not_of("0123456789") == std::string::npos) {
						wireName = cellName.substr(0, last_open);
						bitIndex = std::stoi(inner);
					}
				}

				// Process Q output connection for the cell
				for (auto &conn : cell->connections()) {
					if (conn.first != ID::Q || !conn.second.is_wire()) continue;

					Wire *oldWire = conn.second.as_wire();
					if (oldWire->port_input || oldWire->port_output) continue;

					// Lookup wire information from VCD
					std::string regName = RTLIL::unescape_id(wireName);
					RegInfo regInfo = vcd_reg_widths[vcd_scope + "." + regName];

					int wireWidth = regInfo.width;
					int wireOffset = regInfo.offset;
					if (wireWidth == 0) {
						log_warning("Unable to find matching register %s in VCD for cell %s in scope %s\n",
							regName.c_str(), cellName.c_str(), vcd_scope.c_str());
						continue;
					}

					// Validate bit index
					int maxIndex = wireOffset + wireWidth - 1;
					int minIndex = wireOffset;
					if (bitIndex < minIndex || bitIndex > maxIndex) {
						log_warning("Bit index %d is invalid for wire indices [%d:%d] for '%s'\n",
												bitIndex, maxIndex, minIndex, wireName.c_str());
						continue;
					}

					IdString wireId = RTLIL::escape_id(wireName);

					// Find or create the target wire of the correct VCD-derived width
					Wire *targetWire = nullptr;

					// Check if the target wire was already created
					auto cache_it = targetWireCache.find(wireId);
					if (cache_it != targetWireCache.end()) {
						targetWire = cache_it->second;
					} else {

						// If the cache misses, create the target wire
						targetWire = module->wire(wireId);
						if (!targetWire) {
							if (debug)
								log("Creating wire %s[%d:%d] in scope %s\n", 
										wireName.c_str(), maxIndex, minIndex, vcd_scope.c_str());
							targetWire = module->addWire(wireId, wireWidth);
							targetWire->start_offset = wireOffset;
						}
						targetWireCache[wireId] = targetWire;
					}

					// Skip self-mapping (e.g. oldWire is already the target wire)
					if (targetWire == oldWire)
						continue;

					int normalizedIndex = bitIndex - wireOffset;

					// Check for conflicts with other cells (multiple drivers guard)
					bool conflict = false;
					for (int i = 0; i < GetSize(oldWire); i++) {
						if (claimed_bits.count(SigBit(targetWire, normalizedIndex + i))) {
							conflict = true;
							break;
						}
					}
					if (conflict) {
						log_warning("Skipping cell %s: target %s[%d] already driven by another cell\n",
							log_id(cell->name), wireName.c_str(), bitIndex);
						continue;
					}

					// Create the new connection.
					if (debug)
						log("Connecting %s to %s[%d]\n", 
								log_id(oldWire), wireName.c_str(), bitIndex);

					// Record the mapping for each bit of the old wire to the target wire.
					for (int i = 0; i < GetSize(oldWire); i++) {
						SigBit target(targetWire, normalizedIndex + i);
						bit_map[SigBit(oldWire, i)] = target;
						claimed_bits.insert(target);
					}
					wireRemoveCache.insert(oldWire);
				}
			}
		}

		// Apply all bit-level rewrites in a single pass over the module.
		if (!bit_map.empty()) {
			auto rewriter = [&](SigSpec &sig) {
				for (int i = 0; i < GetSize(sig); i++) {
					auto it = bit_map.find(sig[i]);
					if (it != bit_map.end())
						sig.replace(i, SigSpec(it->second));
				}
			};
			module->rewrite_sigspecs(rewriter);
		}

		// Delete the old unused wires
		module->remove(wireRemoveCache);
	}

	void process_all(dict<std::string, RegInfo> &vcd_reg_widths)
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

		// Extract pre-optimization signal widths from VCD file
		dict<std::string, RegInfo> vcd_reg_widths;
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

				// Extract all signals from the VCD file (registers can be 'reg' or 'wire' in VCDs)
				for (auto &var : fst.getVars()) {
					std::string vcd_scope = var.scope;
					std::string signal_name = var.name;
					std::string signal_bits = "";

					// Use the bracket notation to extract the bit range and construct true reg name.
					if (!signal_name.empty() && signal_name.back() == ']') {
						size_t open = signal_name.rfind('[');
						if (open != std::string::npos) {
							signal_bits = signal_name.substr(open);
							signal_name.erase(open);
						}
					}

					// Extract the LSB and MSB indices if present.
					int msb = 0;
					int lsb = 0;
					size_t colon_pos = signal_bits.find(':');
					if (colon_pos != std::string::npos) { // range case
							msb = std::stoi(signal_bits.substr(1, colon_pos - 1));
							lsb = std::stoi(signal_bits.substr(colon_pos + 1));
					} else if (!signal_bits.empty()) { // single index case
						msb = lsb = std::stoi(signal_bits.substr(1));
					}
					int width  = var.width;
					int offset = std::min(msb, lsb);

					// Map the register's vcd scope and name to
					// its original width and offset for later lookup.
					signal_name = RTLIL::unescape_id(signal_name);
					vcd_reg_widths[vcd_scope + "." + signal_name] = {width, offset};
					if (debug)
						log("Found signal '%s' in scope '%s' with range [%d:%d] (width %d)\n",
							signal_name.c_str(), vcd_scope.c_str(),
							offset + width - 1, offset, width);
				}
				log("Extracted %d signal widths from VCD\n", GetSize(vcd_reg_widths));
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
