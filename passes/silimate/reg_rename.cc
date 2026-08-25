/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Stan Lee          <stan@silimate.com>
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

#include <algorithm>

#include "kernel/fstdata.h"
#include "kernel/yosys.h"
#include "passes/silimate/reg_rename.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// One dumped element of a register: the waveform name minus its bit range, the word indices
// parsed out of that name, its RTL bit range, and where its lsb sits in the register's flat
// bit vector.
struct RegElem {
	std::string name;
	std::vector<int> idx;
	int width = 0;
	int offset = 0;
	int flat = 0;
};

// Every dumped element of one register, ordered least-significant first.
struct RegLayout {
	int total_width = 0;
	std::vector<RegElem> elems;

	// How many index groups the waveform spells each element with
	int rank() const { return elems.empty() ? 0 : GetSize(elems[0].idx); }

	// Element the waveform spells with exactly these word indices.
	const RegElem *at_idx(const std::vector<int> &idx) const
	{
		for (auto &e : elems)
			if (e.idx == idx)
				return &e;
		return nullptr;
	}

	// Element covering a flat bit position, or nullptr when out of range.
	const RegElem *at_flat(int bit) const
	{
		size_t lo = 0, hi = elems.size(); // elems is sorted by flat
		while (lo < hi) {
			size_t mid = (lo + hi) / 2;
			if (bit < elems[mid].flat)
				hi = mid;
			else if (bit >= elems[mid].flat + elems[mid].width)
				lo = mid + 1;
			else
				return &elems[mid];
		}
		return nullptr;
	}
};

// Peel trailing "[digits]" groups: "q[3][7]" -> base "q", idx {3, 7}.
static std::string split_word_indices(const std::string &name, std::vector<int> &idx)
{
	size_t end = name.size();
	std::vector<int> rev;
	while (end && name[end - 1] == ']') {
		size_t open = name.rfind('[', end - 1);
		if (open == std::string::npos)
			break;
		std::string inner = name.substr(open + 1, end - open - 2);
		if (inner.empty() || inner.find_first_not_of("0123456789") != std::string::npos)
			break;
		rev.push_back(std::stoi(inner));
		end = open;
	}
	idx.assign(rev.rbegin(), rev.rend());
	return name.substr(0, end);
}

// Split a register cell name, spelled \name[word]_reg[bit] or \name_reg[word][bit], into the
// register, the word indices selecting a dumped element, and the bit inside it. False when the
// cell is not a named register.
static bool split_reg_cell(IdString cell_name, std::string &reg, std::vector<int> &word, int &bit)
{
	std::vector<int> post, pre;
	std::string stem = split_word_indices(cell_name.str(), post);
	if (GetSize(stem) < 4 || stem.compare(GetSize(stem) - 4, 4, "_reg") != 0)
		return false;
	reg = RTLIL::unescape_id(split_word_indices(stem.substr(0, GetSize(stem) - 4), pre));

	// Trailing groups are the bit index preceded by more word indices
	word = pre;
	bit = 0;
	if (!post.empty()) {
		word.insert(word.end(), post.begin(), post.end() - 1);
		bit = post.back();
	}
	return true;
}

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
	void process_registers(dict<std::string, RegLayout> &reg_layouts)
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

		// Word grid of every register as the netlist spells it: one past the largest index at
		// each position. A reshaping alias makes this differ from the dumped shape.
		dict<std::string, std::vector<int>> word_grids;
		for (auto cell : module->cells()) {
			std::string reg;
			std::vector<int> word;
			int bit = 0;
			if (!RTLIL::builtin_ff_cell_types().count(cell->type) ||
					!split_reg_cell(cell->name, reg, word, bit))
				continue;
			auto &grid = word_grids[reg];
			grid.resize(std::max(GetSize(grid), GetSize(word)), 0);
			for (int i = 0; i < GetSize(word); i++)
				grid[i] = std::max(grid[i], word[i] + 1);
		}

		// Loop through all cells in the module
		for (auto cell : module->cells()) {

			// Skip non-register cells
			if (!RTLIL::builtin_ff_cell_types().count(cell->type)) {
				continue;
			}

			// Which register this cell belongs to, and which bit of it it holds
			std::string reg;
			std::vector<int> word;
			int bit = 0;
			if (!split_reg_cell(cell->name, reg, word, bit))
				continue;

			// Process Q output connection for the cell
			for (auto &conn : cell->connections()) {
				if (conn.first != ID::Q || !conn.second.is_wire()) continue;

				Wire *oldWire = conn.second.as_wire();
				if (oldWire->port_input || oldWire->port_output) continue;

				auto layout_it = reg_layouts.find(vcd_scope + "." + reg);
				if (layout_it == reg_layouts.end()) {
					log_warning("Unable to find matching register %s in VCD for cell %s in scope %s\n",
						reg.c_str(), log_id(cell->name), vcd_scope.c_str());
					continue;
				}
				const RegLayout &layout = layout_it->second;
				const std::vector<int> &grid = word_grids.at(reg);

				const RegElem *elem = nullptr;
				int bitIndex = bit;
				if (GetSize(word) == layout.rank()) {
					// Netlist and waveform spell the register the same way
					elem = layout.at_idx(word);
				} else {
					// The netlist reaches the register through an alias of a different rank,
					// so place the word by its row-major position instead of by name.
					int slots = 1, slot = 0;
					for (int i = 0; i < GetSize(word); i++) {
						slot = slot * grid[i] + word[i];
						slots *= grid[i];
					}
					if (layout.total_width % slots == 0) {
						int flat = slot * (layout.total_width / slots) + bit;
						elem = layout.at_flat(flat);
						if (elem)
							bitIndex = elem->offset + (flat - elem->flat);
					}
				}
				if (elem == nullptr) {
					log_warning("Cannot place cell %s in register %s, dumped as %d bits in %d "
						"elements, in scope %s\n", log_id(cell->name), reg.c_str(),
						layout.total_width, GetSize(layout.elems), vcd_scope.c_str());
					continue;
				}

				std::string wireName = elem->name;
				int wireWidth = elem->width;
				int wireOffset = elem->offset;
				int maxIndex = wireOffset + wireWidth - 1;
				int minIndex = wireOffset;

				// Validate bit index, and that an unsplit cell fits in one dumped element
				if (bitIndex < minIndex || bitIndex + GetSize(oldWire) - 1 > maxIndex) {
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

		// Drop leftover alias/X assigns onto claimed bits.
		if (!claimed_bits.empty()) {
			std::vector<RTLIL::SigSig> kept;
			bool changed = false;
			// Rebuild connection list, omitting bits that flops now own.
			for (auto &conn : module->connections()) {
				RTLIL::SigSpec lhs, rhs; // lhs = driven, rhs = driver
				for (int i = 0; i < GetSize(conn.first); i++) {
					// Alias/opt left an assign (often to X) on the restored Q bit.
					if (claimed_bits.count(conn.first[i])) {
						changed = true;
						continue;
					}
					lhs.append(conn.first[i]);
					rhs.append(conn.second[i]);
				}
				// Keep any remaining (non-claimed) slice of this assign.
				if (GetSize(lhs))
					kept.emplace_back(lhs, rhs);
			}
			// Only rewrite the module if we actually removed something.
			if (changed)
				module->new_connections(kept);
		}
	}

	void process_all(dict<std::string, RegLayout> &reg_layouts)
	{
		process_registers(reg_layouts);
		for (auto &it : children)
			it.second->process_all(reg_layouts);
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
		log("    -waveform <filename>\n");
		log("        waveform file (VCD or FST) to extract original register widths from.\n");
		log("        VCD inputs are converted via the external vcd2fst tool.\n");
		log("    -scope <scope>\n");
		log("        scope to process in the waveform\n");
		log("\n");
		log("    -d\n");
		log("        enable debug output\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing reg_rename pass\n");

		// Argument parsing
		std::string waveform_filename;
		std::string scope;
		bool debug = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-waveform" && argidx + 1 < args.size()) {
				waveform_filename = args[++argidx];
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

		// Extract pre-optimization signal widths from waveform file
		dict<std::string, RegLayout> reg_layouts;
		if (!waveform_filename.empty()) {
			log("Reading waveform file: %s\n", waveform_filename.c_str());
			try {
				FstData fst(waveform_filename);
				if (scope.empty()) {
					scope = fst.autoScope(topmod);
					if (scope.empty()) {
						log_error("No scope found for module '%s'. Please specify -scope explicitly.\n", 
							RTLIL::unescape_id(topmod->name).c_str());
					}
				}
				log("Using scope: \"%s\"\n", scope.c_str());

				// Extract all signals from the waveform (registers can be 'reg' or 'wire' in VCDs)
				for (auto &var : fst.getVars()) {
					std::string vcd_scope = var.scope;
					std::string signal_name = var.name;
					std::string signal_bits = "";

					// Use the bracket notation to extract the bit range and construct true reg name.
					if (!signal_name.empty() && signal_name.back() == ']') {
						size_t open = signal_name.rfind('[');
						if (open != std::string::npos) {
							std::string inner = signal_name.substr(open + 1, signal_name.size() - open - 2);
							// Ensure that signal_bits is not populated with non-indexed characters.
							if (!inner.empty() && inner.find_first_not_of("0123456789:") == std::string::npos) {
								signal_bits = signal_name.substr(open);
								signal_name.erase(open);
							}
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

					// Group each element under its register, so a register dumped word by
					// word is one layout rather than several unrelated signals.
					signal_name = RTLIL::unescape_id(signal_name);
					RegElem elem;
					elem.name = signal_name;
					elem.width = width;
					elem.offset = offset;
					std::string base = split_word_indices(signal_name, elem.idx);
					reg_layouts[vcd_scope + "." + base].elems.push_back(elem);
					if (debug)
						log("Found signal '%s' in scope '%s' with range [%d:%d] (width %d)\n",
							signal_name.c_str(), vcd_scope.c_str(),
							offset + width - 1, offset, width);
				}

				// Order each register least-significant element first and assign flat bit
				// positions. Word index 0 is the lsb, matching [N-1:0] declarations.
				for (auto &it : reg_layouts) {
					auto &elems = it.second.elems;
					std::sort(elems.begin(), elems.end(), [](const RegElem &a, const RegElem &b) {
						return a.idx != b.idx ? a.idx < b.idx : a.offset < b.offset;
					});
					int flat = 0;
					for (auto &e : elems) {
						e.flat = flat;
						flat += e.width;
					}
					it.second.total_width = flat;
				}
				log("Extracted %d registers from waveform\n", GetSize(reg_layouts));
			} catch (const std::exception &e) {
				log_error("Failed to read waveform file '%s': %s\n", 
					waveform_filename.c_str(), e.what());
			}
		} else {
			log_error("No waveform file provided. Use -waveform option.\n");
		}

		// STEP 2: Build hierarchy and process
		log("Building hierarchy from scope: %s\n", scope.c_str());

		// Build hierarchy and process register renamings
		RegRenameInstance *root = new RegRenameInstance(scope, topmod, debug);
		root->process_all(reg_layouts);
		delete root;

		log_flush();
	}
} RegRenamePass;

PRIVATE_NAMESPACE_END
