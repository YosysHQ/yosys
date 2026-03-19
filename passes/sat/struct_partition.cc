/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Structural-isomorphism partitioning for equivalence checking.
 *
 *  Given two modules (typically named "gold" and "gate") with matching
 *  port signatures, this pass:
 *
 *    1. Builds a bottom-up structural hash for every cell in each module.
 *       The hash captures cell type, parameters, and the recursive structure
 *       of each input driver chain back to primary inputs.  Wire and cell
 *       names are deliberately ignored — only connectivity and function
 *       matter.
 *
 *    2. Finds hash groups where cells from BOTH modules appear.  Every cell
 *       in such a group computes the same Boolean function of the same
 *       primary inputs, so they are structurally equivalent.
 *
 *    3. For each matched group, replaces every cell's output in both
 *       modules with a shared new primary-input port (a "cutpoint").
 *       The matched cells and all transitively dead fanin logic are then
 *       removed.
 *
 *  The result is a pair of simplified modules whose remaining logic is
 *  exactly the part that differs — or that could not be structurally
 *  matched — ready to be fed into `miter -equiv` and a SAT/PDR solver.
 *
 *  The key insight is that structurally identical subcircuits do not need
 *  to be proved equivalent by the solver; replacing them with free inputs
 *  shrinks the problem while preserving soundness.
 *
 *  Algorithm notes
 *  ---------------
 *  - Primary inputs hash by their port name (shared between gold/gate).
 *  - Constants hash by their value.
 *  - Flip-flop Q outputs break feedback loops: when computing the hash
 *    of a FF, we do NOT recurse through Q.  Instead, Q is treated as a
 *    fresh leaf ("secondary PI") in the downstream combinational cone.
 *    The FF itself IS hashed (by type + params + input drivers), so two
 *    structurally identical FFs will match.
 *  - The hash is a tuple-like structure (not a numeric hash), so there
 *    are no collisions — matching is exact.
 *
 *  Copyright (C) 2025  Silimate Inc.
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
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <cstdarg>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// ---------------------------------------------------------------------------
// StructuralHash — collision-free structural identity
// ---------------------------------------------------------------------------
//
// Each cell's "structural hash" is a tree-shaped value that encodes:
//   (cell_type, {parameters}, {port -> driver_hash, ...})
//
// We serialise these trees into interned integer IDs so that comparison
// is O(1) after the initial bottom-up pass.  Two cells get the same ID
// if and only if they are structurally identical.

struct StructuralHasher {
	// Intern table: canonical representation -> unique ID
	dict<std::vector<int>, int> intern_table;
	int next_id = 1;

	// Sentinel IDs for leaves
	enum { CONST_BASE = -1000000, PI_BASE = -2000000, CYCLE_GUARD = 0 };

	int intern(const std::vector<int> &key) {
		auto it = intern_table.find(key);
		if (it != intern_table.end())
			return it->second;
		int id = next_id++;
		intern_table[key] = id;
		return id;
	}

	// Intern a primary-input identity.  We use the port name's hash to
	// generate a stable integer that is the same in both gold and gate.
	dict<IdString, int> pi_ids;
	int intern_pi(IdString port_name) {
		auto it = pi_ids.find(port_name);
		if (it != pi_ids.end())
			return it->second;
		int id = PI_BASE - (int)pi_ids.size();
		pi_ids[port_name] = id;
		return id;
	}

	// Intern a constant value.
	dict<Const, int> const_ids;
	int intern_const(const Const &val) {
		auto it = const_ids.find(val);
		if (it != const_ids.end())
			return it->second;
		int id = CONST_BASE - (int)const_ids.size();
		const_ids[val] = id;
		return id;
	}
};

// ---------------------------------------------------------------------------
// Per-module analysis state
// ---------------------------------------------------------------------------

struct ModuleAnalysis {
	RTLIL::Module *module;
	SigMap sigmap;
	CellTypes ct;

	// bit -> (cell, port) that drives it
	dict<SigBit, std::pair<Cell*, IdString>> bit_driver;

	// cell -> structural hash ID
	dict<Cell*, int> cell_hash;

	// Which SigBits are primary inputs (module input ports)
	dict<SigBit, IdString> pi_bits; // bit -> port_name

	// Set of cells being visited (cycle detection)
	pool<Cell*> visiting;

	// Set of cells that are flip-flops / sequential
	pool<Cell*> ff_cells;

	ModuleAnalysis(RTLIL::Module *mod, Design *design) : module(mod), sigmap(mod) {
		ct.setup(design);

		// Record primary-input bits
		for (auto wire : module->wires()) {
			if (wire->port_input) {
				SigSpec sig = sigmap(wire);
				for (int i = 0; i < GetSize(sig); i++)
					pi_bits[sig[i]] = wire->name;
			}
		}

		// Build bit -> driver map
		for (auto cell : module->cells()) {
			if (cell->is_builtin_ff() || cell->type.in(
					ID($sr), ID($ff), ID($dff), ID($dffe),
					ID($dffsr), ID($dffsre), ID($adff), ID($adffe),
					ID($aldff), ID($aldffe), ID($sdff), ID($sdffe),
					ID($sdffce), ID($dlatch), ID($adlatch), ID($dlatchsr),
					ID($anyinit)))
				ff_cells.insert(cell);

			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first)) {
					SigSpec sig = sigmap(conn.second);
					for (int i = 0; i < GetSize(sig); i++)
						if (sig[i].wire)
							bit_driver[sig[i]] = {cell, conn.first};
				}
			}
		}
	}

	// Compute structural hash for a single SigBit
	int hash_bit(SigBit bit, StructuralHasher &hasher) {
		bit = sigmap(bit);

		// Constant
		if (bit.wire == nullptr)
			return hasher.intern_const(Const(bit.data));

		// Primary input
		auto pi_it = pi_bits.find(bit);
		if (pi_it != pi_bits.end())
			return hasher.intern_pi(pi_it->second);

		// Driven by a cell
		auto drv_it = bit_driver.find(bit);
		if (drv_it != bit_driver.end()) {
			Cell *drv_cell = drv_it->second.first;
			IdString drv_port = drv_it->second.second;

			// For FFs, treat Q as a secondary PI (to break cycles).
			// The FF itself will get its own hash via hash_cell.
			if (ff_cells.count(drv_cell) && drv_port == ID::Q) {
				int ff_hash = hash_cell(drv_cell, hasher);
				// Encode "output bit i of ff with hash ff_hash"
				SigSpec q_sig = sigmap(drv_cell->getPort(ID::Q));
				int bit_idx = 0;
				for (int i = 0; i < GetSize(q_sig); i++)
					if (q_sig[i] == bit) { bit_idx = i; break; }
				std::vector<int> key = {ff_hash, bit_idx, -99};
				return hasher.intern(key);
			}

			int ch = hash_cell(drv_cell, hasher);
			// Multi-bit output: encode which bit of the output we're reading
			SigSpec port_sig = sigmap(drv_cell->getPort(drv_port));
			int bit_idx = 0;
			for (int i = 0; i < GetSize(port_sig); i++)
				if (port_sig[i] == bit) { bit_idx = i; break; }
			std::vector<int> key = {ch, bit_idx, (int)drv_port.index_};
			return hasher.intern(key);
		}

		// Undriven wire — treat as a unique unknown
		return hasher.intern_const(Const(State::Sx));
	}

	// Compute structural hash for a SigSpec (multi-bit signal)
	int hash_sig(const SigSpec &sig, StructuralHasher &hasher) {
		SigSpec mapped = sigmap(sig);
		if (GetSize(mapped) == 1)
			return hash_bit(mapped[0], hasher);

		std::vector<int> key;
		key.reserve(GetSize(mapped) + 1);
		key.push_back(-77); // tag for "concatenated signal"
		for (auto &bit : mapped)
			key.push_back(hash_bit(bit, hasher));
		return hasher.intern(key);
	}

	// Compute structural hash for a cell
	int hash_cell(Cell *cell, StructuralHasher &hasher) {
		auto it = cell_hash.find(cell);
		if (it != cell_hash.end())
			return it->second;

		// Cycle guard
		if (visiting.count(cell)) {
			cell_hash[cell] = StructuralHasher::CYCLE_GUARD;
			return StructuralHasher::CYCLE_GUARD;
		}
		visiting.insert(cell);

		// Build the key: cell_type, sorted parameters, sorted input hashes
		std::vector<int> key;

		// Cell type
		key.push_back((int)cell->type.index_);

		// Parameters (sorted by name for determinism)
		std::vector<std::pair<IdString, Const>> sorted_params(
			cell->parameters.begin(), cell->parameters.end());
		std::sort(sorted_params.begin(), sorted_params.end(),
			[](const auto &a, const auto &b) { return a.first < b.first; });

		key.push_back(-88); // separator
		for (auto &[pname, pval] : sorted_params) {
			key.push_back((int)pname.index_);
			key.push_back(hasher.intern_const(pval));
		}

		// Input connections (sorted by port name)
		key.push_back(-99); // separator
		std::vector<std::pair<IdString, SigSpec>> inputs;
		for (auto &conn : cell->connections()) {
			if (cell->output(conn.first))
				continue;
			inputs.push_back({conn.first, conn.second});
		}
		std::sort(inputs.begin(), inputs.end(),
			[](const auto &a, const auto &b) { return a.first < b.first; });

		for (auto &[port, sig] : inputs) {
			key.push_back((int)port.index_);
			key.push_back(hash_sig(sig, hasher));
		}

		int id = hasher.intern(key);
		cell_hash[cell] = id;
		visiting.erase(cell);
		return id;
	}

	// Hash all cells in the module
	void hash_all_cells(StructuralHasher &hasher) {
		for (auto cell : module->cells())
			hash_cell(cell, hasher);
	}
};

// ---------------------------------------------------------------------------
// Core: find matches and apply cutpoints
// ---------------------------------------------------------------------------

struct StructPartitionWorker {
	Design *design;
	Module *gold_mod;
	Module *gate_mod;
	bool verbose;
	FILE *log_file;

	int total_cutpoints = 0;
	int total_cells_removed = 0;

	StructPartitionWorker(Design *d, Module *gold, Module *gate, bool v, FILE *lf = nullptr)
		: design(d), gold_mod(gold), gate_mod(gate), verbose(v), log_file(lf) {}

	void vlog(const char *fmt, ...) __attribute__((format(printf, 2, 3))) {
		va_list ap;
		va_start(ap, fmt);
		char buf[4096];
		vsnprintf(buf, sizeof(buf), fmt, ap);
		va_end(ap);
		if (log_file)
			fputs(buf, log_file);
		else
			log("%s", buf);
	}

	void run() {
		// A single shared hasher ensures the same intern IDs across both modules
		StructuralHasher hasher;

		vlog("Structural partitioning: analyzing module `%s'.\n", gold_mod->name.c_str());
		ModuleAnalysis gold_analysis(gold_mod, design);
		gold_analysis.hash_all_cells(hasher);

		vlog("Structural partitioning: analyzing module `%s'.\n", gate_mod->name.c_str());
		ModuleAnalysis gate_analysis(gate_mod, design);
		gate_analysis.hash_all_cells(hasher);

		// Group cells by structural hash across both modules
		dict<int, std::vector<Cell*>> gold_by_hash, gate_by_hash;
		for (auto &[cell, h] : gold_analysis.cell_hash)
			if (h != StructuralHasher::CYCLE_GUARD)
				gold_by_hash[h].push_back(cell);
		for (auto &[cell, h] : gate_analysis.cell_hash)
			if (h != StructuralHasher::CYCLE_GUARD)
				gate_by_hash[h].push_back(cell);

		// Find hashes present in BOTH modules — these are the structural matches.
		// ALL cells with a matching hash (in both modules) get the same cutpoint.
		struct CutpointGroup {
			std::vector<Cell*> gold_cells;
			std::vector<Cell*> gate_cells;
		};
		std::vector<CutpointGroup> groups;

		for (auto &[h, gold_cells] : gold_by_hash) {
			auto it = gate_by_hash.find(h);
			if (it == gate_by_hash.end())
				continue;
			groups.push_back({gold_cells, it->second});
		}

		if (groups.empty()) {
			vlog("No structural matches found between `%s' and `%s'.\n",
				gold_mod->name.c_str(), gate_mod->name.c_str());
			return;
		}

		vlog("Found %d structurally matched groups.\n", (int)groups.size());

		// For each group, create cutpoint PIs and rewire
		for (auto &group : groups)
			apply_cutpoint_group(group.gold_cells, group.gate_cells,
				gold_analysis, gate_analysis);

		// Remove transitively dead cells from both modules
		remove_dead_cells(gold_mod);
		remove_dead_cells(gate_mod);

		gold_mod->fixup_ports();
		gate_mod->fixup_ports();

		vlog("Structural partitioning: created %d cutpoints, removed %d cells.\n",
			total_cutpoints, total_cells_removed);
	}

private:
	// Create a cutpoint for one matched group.
	//
	// Every cell in gold_cells and gate_cells computes the same function.
	// We pick the output port(s) of the cell type, create a fresh input
	// port with the same width on BOTH modules (same name), and rewire
	// all the cells' outputs to that port.  Then we remove the cells.
	void apply_cutpoint_group(
		const std::vector<Cell*> &gold_cells,
		const std::vector<Cell*> &gate_cells,
		ModuleAnalysis &/*gold_an*/,
		ModuleAnalysis &/*gate_an*/)
	{
		if (gold_cells.empty() || gate_cells.empty())
			return;

		Cell *representative = gold_cells[0];

		// Determine output ports for this cell type
		std::vector<IdString> out_ports;
		for (auto &conn : representative->connections())
			if (representative->output(conn.first))
				out_ports.push_back(conn.first);

		if (out_ports.empty())
			return;

		for (auto out_port : out_ports) {
			SigSpec rep_sig = representative->getPort(out_port);
			int width = GetSize(rep_sig);
			if (width == 0)
				continue;

			// Create a unique cutpoint name
			std::string cut_name = stringf("\\cut_%d", total_cutpoints);
			total_cutpoints++;

			if (verbose)
				vlog("  Cutpoint %s (width %d) for %d+%d cells of type %s.\n",
					cut_name.c_str(), width,
					(int)gold_cells.size(), (int)gate_cells.size(),
					representative->type.c_str());

			// Create the new input port on both modules
			Wire *gold_cut = gold_mod->addWire(cut_name, width);
			gold_cut->port_input = true;

			Wire *gate_cut = gate_mod->addWire(cut_name, width);
			gate_cut->port_input = true;

			// Rewire all gold cells: connect their output to the cutpoint wire
			for (auto cell : gold_cells) {
				SigSpec old_sig = cell->getPort(out_port);
				if (GetSize(old_sig) != width) continue;
				gold_mod->connect(old_sig, gold_cut);
			}

			// Rewire all gate cells: connect their output to the cutpoint wire
			for (auto cell : gate_cells) {
				SigSpec old_sig = cell->getPort(out_port);
				if (GetSize(old_sig) != width) continue;
				gate_mod->connect(old_sig, gate_cut);
			}
		}

		// Remove the matched cells
		for (auto cell : gold_cells) {
			if (verbose)
				vlog("    Removing gold cell `%s'.\n", cell->name.c_str());
			gold_mod->remove(cell);
			total_cells_removed++;
		}
		for (auto cell : gate_cells) {
			if (verbose)
				vlog("    Removing gate cell `%s'.\n", cell->name.c_str());
			gate_mod->remove(cell);
			total_cells_removed++;
		}
	}

	// Remove cells whose outputs are entirely unconnected.
	// Iterate to fixpoint since removing one cell may make its drivers dead.
	void remove_dead_cells(Module *mod) {
		SigMap sigmap(mod);

		bool changed = true;
		while (changed) {
			changed = false;

			// Collect all bits that are used as inputs somewhere
			pool<SigBit> used_bits;
			for (auto cell : mod->cells())
				for (auto &conn : cell->connections())
					if (cell->input(conn.first))
						for (auto bit : sigmap(conn.second))
							if (bit.wire)
								used_bits.insert(bit);

			// Module output ports are "used"
			for (auto wire : mod->wires())
				if (wire->port_output)
					for (auto bit : sigmap(wire))
						used_bits.insert(bit);

			// Also count bits used in module-level connections (LHS = driven)
			for (auto &conn : mod->connections()) {
				for (auto bit : sigmap(conn.first))
					if (bit.wire)
						used_bits.insert(bit);
				for (auto bit : sigmap(conn.second))
					if (bit.wire)
						used_bits.insert(bit);
			}

			// Remove cells whose outputs are entirely unused
			std::vector<Cell*> to_remove;
			for (auto cell : mod->cells()) {
				bool any_output_used = false;
				bool has_output = false;
				for (auto &conn : cell->connections()) {
					if (!cell->output(conn.first))
						continue;
					has_output = true;
					for (auto bit : sigmap(conn.second)) {
						if (used_bits.count(bit)) {
							any_output_used = true;
							break;
						}
					}
					if (any_output_used) break;
				}
				// Only remove cells that have outputs but none are used.
				// Keep cells with no outputs (side effects like $assert).
				if (has_output && !any_output_used && !cell->has_keep_attr())
					to_remove.push_back(cell);
			}

			for (auto cell : to_remove) {
				if (verbose)
					vlog("    Dead cell removal: `%s' (%s).\n",
						cell->name.c_str(), cell->type.c_str());
				mod->remove(cell);
				total_cells_removed++;
				changed = true;
			}

			if (changed)
				sigmap.set(mod);
		}
	}
};

// ---------------------------------------------------------------------------
// Pass registration
// ---------------------------------------------------------------------------

struct StructPartitionPass : public Pass {
	StructPartitionPass() : Pass("struct_partition",
		"partition equivalent subcircuits between two modules") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    struct_partition [options] gold_module gate_module\n");
		log("\n");
		log("This pass identifies structurally identical subcircuits between two modules\n");
		log("(typically a gold and gate design for equivalence checking) and replaces\n");
		log("matched logic with shared primary-input cutpoints.\n");
		log("\n");
		log("The structural matching is purely based on cell types, parameters, and\n");
		log("input connectivity — cell and wire names are ignored entirely.\n");
		log("\n");
		log("For each group of cells that are structurally identical across both modules,\n");
		log("ALL cells in the group are removed and their outputs are replaced by a new\n");
		log("input port with the same name in both modules.  Transitively dead fanin\n");
		log("logic is also removed.\n");
		log("\n");
		log("This shrinks the subsequent `miter -equiv` + SAT/PDR problem by eliminating\n");
		log("logic that is provably identical by construction.\n");
		log("\n");
		log("    -v\n");
		log("        verbose output: log each cutpoint and removed cell\n");
		log("\n");
		log("    -o <file>\n");
		log("        write verbose log output to <file> instead of standard log\n");
		log("\n");
		log("Typical usage:\n");
		log("\n");
		log("    read_rtlil gold.il\n");
		log("    read_rtlil gate.il\n");
		log("    struct_partition gold gate\n");
		log("    miter -equiv gold gate miter\n");
		log("    ...\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool verbose = false;
		std::string log_file_path;

		log_header(design, "Executing STRUCT_PARTITION pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-v") {
				verbose = true;
				continue;
			}
			if (args[argidx] == "-o" && argidx + 1 < args.size()) {
				log_file_path = args[++argidx];
				continue;
			}
			break;
		}

		if (argidx + 2 != args.size())
			cmd_error(args, argidx, "Expected exactly two module name arguments.");

		IdString gold_name = RTLIL::escape_id(args[argidx]);
		IdString gate_name = RTLIL::escape_id(args[argidx + 1]);

		Module *gold_mod = design->module(gold_name);
		if (!gold_mod)
			log_cmd_error("Module `%s' not found.\n", gold_name.c_str());

		Module *gate_mod = design->module(gate_name);
		if (!gate_mod)
			log_cmd_error("Module `%s' not found.\n", gate_name.c_str());

		// Verify port compatibility
		for (auto gold_wire : gold_mod->wires()) {
			if (!gold_wire->port_input)
				continue;
			Wire *gate_wire = gate_mod->wire(gold_wire->name);
			if (!gate_wire || !gate_wire->port_input)
				log_cmd_error("Input port `%s' in `%s' has no match in `%s'.\n",
					gold_wire->name.c_str(), gold_name.c_str(), gate_name.c_str());
			if (gold_wire->width != gate_wire->width)
				log_cmd_error("Port `%s' width mismatch: %d vs %d.\n",
					gold_wire->name.c_str(), gold_wire->width, gate_wire->width);
		}

		FILE *log_file = nullptr;
		if (!log_file_path.empty()) {
			log_file = fopen(log_file_path.c_str(), "w");
			if (!log_file)
				log_cmd_error("Cannot open output file `%s'.\n", log_file_path.c_str());
		}

		StructPartitionWorker worker(design, gold_mod, gate_mod, verbose, log_file);
		worker.run();

		if (log_file)
			fclose(log_file);
	}
} StructPartitionPass;

PRIVATE_NAMESPACE_END
