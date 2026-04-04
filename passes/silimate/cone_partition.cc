/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Cone partitioning for equivalence checking.
 *
 *  Given two modules (typically "gold" and "gate") with matching port
 *  signatures, this pass:
 *
 *    1. Builds bottom-up structural hashes for every cell in each module
 *       (identical algorithm to struct_partition).
 *
 *    2. Finds hash groups where FF cells from BOTH modules match — these
 *       are structurally equivalent sequential boundaries.
 *
 *    3. For each matched FF group:
 *       - The FF's Q output is disconnected from the rest of the circuit
 *         and exposed as a new output port (PO).
 *       - A new input port (PI) is created to replace the FF's Q output
 *         for any downstream logic that was consuming it.
 *       - The cone's transitive fanin is traced backwards, stopping at
 *         existing module PIs or at other matched FFs (whose PIs are
 *         reused). Any other leaf signals become new PIs.
 *
 *    4. Multi-clock-domain handling:
 *       - If both gold and gate have multiple clock domains, unmatched
 *         FFs (those not in any structural cone) are grouped by clock
 *         domain. Each group's Q outputs are XOR-reduced into a single
 *         bit, ANDed with the 1-bit clock guard PI for that domain,
 *         and driven out as one shared PO. This makes the comparison
 *         logic-based rather than name-based.
 *       - If only one module has multiple clock domains while the other
 *         has one, the pass errors out declaring the designs inequivalent.
 *       - Each unique (clock_signal, polarity) pair gets one guard PI
 *         (\clkguard_N). The guard ensures the SAT solver treats FFs in
 *         different domains as distinguishable even after clkmerge.
 *
 *  The result is a pair of modules where every structurally matched
 *  FF cone is individually observable through its own PI/PO pair, ready
 *  for per-cone equivalence checking.
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
#include "kernel/ff.h"
#include "kernel/log.h"
#include <cstdarg>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// ---------------------------------------------------------------------------
// StructuralHash — collision-free structural identity (same as struct_partition)
// ---------------------------------------------------------------------------

struct StructuralHasher {
	dict<std::vector<int>, int> intern_table;
	int next_id = 1;

	enum { CONST_BASE = -1000000, PI_BASE = -2000000, CYCLE_GUARD = 0 };

	int intern(const std::vector<int> &key) {
		auto it = intern_table.find(key);
		if (it != intern_table.end())
			return it->second;
		int id = next_id++;
		intern_table[key] = id;
		return id;
	}

	dict<std::pair<IdString, int>, int> pi_ids;
	int intern_pi(IdString port_name, int bit_idx) {
		auto key = std::make_pair(port_name, bit_idx);
		auto it = pi_ids.find(key);
		if (it != pi_ids.end())
			return it->second;
		int id = PI_BASE - (int)pi_ids.size();
		pi_ids[key] = id;
		return id;
	}

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
// Per-module analysis state (same as struct_partition)
// ---------------------------------------------------------------------------

struct ModuleAnalysis {
	RTLIL::Module *module;
	SigMap sigmap;
	CellTypes ct;

	dict<SigBit, std::pair<Cell*, IdString>> bit_driver;
	dict<Cell*, int> cell_hash;
	dict<SigBit, std::pair<IdString, int>> pi_bits;
	pool<Cell*> visiting;
	pool<Cell*> ff_cells;

	ModuleAnalysis(RTLIL::Module *mod, Design *design) : module(mod), sigmap(mod) {
		ct.setup(design);

		for (auto wire : module->wires()) {
			if (wire->port_input) {
				SigSpec sig = sigmap(wire);
				for (int i = 0; i < GetSize(sig); i++)
					pi_bits[sig[i]] = {wire->name, i};
			}
		}

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

	int hash_bit(SigBit bit, StructuralHasher &hasher) {
		bit = sigmap(bit);

		if (bit.wire == nullptr)
			return hasher.intern_const(Const(bit.data));

		auto pi_it = pi_bits.find(bit);
		if (pi_it != pi_bits.end())
			return hasher.intern_pi(pi_it->second.first, pi_it->second.second);

		auto drv_it = bit_driver.find(bit);
		if (drv_it != bit_driver.end()) {
			Cell *drv_cell = drv_it->second.first;
			IdString drv_port = drv_it->second.second;

			if (ff_cells.count(drv_cell) && drv_port == ID::Q) {
				int ff_hash = hash_cell(drv_cell, hasher);
				SigSpec q_sig = sigmap(drv_cell->getPort(ID::Q));
				int bit_idx = 0;
				for (int i = 0; i < GetSize(q_sig); i++)
					if (q_sig[i] == bit) { bit_idx = i; break; }
				std::vector<int> key = {ff_hash, bit_idx, -99};
				return hasher.intern(key);
			}

			int ch = hash_cell(drv_cell, hasher);
			SigSpec port_sig = sigmap(drv_cell->getPort(drv_port));
			int bit_idx = 0;
			for (int i = 0; i < GetSize(port_sig); i++)
				if (port_sig[i] == bit) { bit_idx = i; break; }
			std::vector<int> key = {ch, bit_idx, (int)drv_port.index_};
			return hasher.intern(key);
		}

		return hasher.intern_const(Const(State::Sx));
	}

	int hash_sig(const SigSpec &sig, StructuralHasher &hasher) {
		SigSpec mapped = sigmap(sig);
		if (GetSize(mapped) == 1)
			return hash_bit(mapped[0], hasher);

		std::vector<int> key;
		key.reserve(GetSize(mapped) + 1);
		key.push_back(-77);
		for (auto &bit : mapped)
			key.push_back(hash_bit(bit, hasher));
		return hasher.intern(key);
	}

	int hash_cell(Cell *cell, StructuralHasher &hasher) {
		auto it = cell_hash.find(cell);
		if (it != cell_hash.end())
			return it->second;

		if (visiting.count(cell)) {
			cell_hash[cell] = StructuralHasher::CYCLE_GUARD;
			return StructuralHasher::CYCLE_GUARD;
		}
		visiting.insert(cell);

		std::vector<int> key;
		key.push_back((int)cell->type.index_);

		std::vector<std::pair<IdString, Const>> sorted_params(
			cell->parameters.begin(), cell->parameters.end());
		std::sort(sorted_params.begin(), sorted_params.end(),
			[](const auto &a, const auto &b) { return a.first < b.first; });

		key.push_back(-88);
		for (auto &[pname, pval] : sorted_params) {
			key.push_back((int)pname.index_);
			key.push_back(hasher.intern_const(pval));
		}

		key.push_back(-99);
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

	void hash_all_cells(StructuralHasher &hasher) {
		for (auto cell : module->cells())
			hash_cell(cell, hasher);
	}
};

// ---------------------------------------------------------------------------
// Core worker
// ---------------------------------------------------------------------------

struct ConePartitionWorker {
	Design *design;
	Module *gold_mod;
	Module *gate_mod;
	bool verbose;
	FILE *log_file;

	int total_pos = 0;
	int total_pis = 0;
	int total_guards = 0;

	// Clock domain guard tracking:
	// Each unique (clk_signal_string, polarity) pair gets a unique guard index.
	// A guard PI wire named \clkguard_<idx> is created in each module for each
	// clock domain that appears in its FFs. The PO for a cone is ANDed with
	// the guard so that FFs in different clock domains remain structurally
	// distinguishable even after clkmerge unifies the actual clock signals.
	dict<std::pair<std::string, bool>, int> clk_domain_to_guard;
	int next_guard_idx = 0;
	dict<std::pair<Module*, int>, Wire*> guard_pi_cache;

	ConePartitionWorker(Design *d, Module *gold, Module *gate, bool v, FILE *lf = nullptr)
		: design(d), gold_mod(gold), gate_mod(gate), verbose(v), log_file(lf) {}

	int get_or_create_guard_idx(const SigSpec &clk, bool pol, SigMap &sigmap) {
		SigSpec mapped = sigmap(clk);
		std::string clk_str = log_signal(mapped);
		auto key = std::make_pair(clk_str, pol);
		auto it = clk_domain_to_guard.find(key);
		if (it != clk_domain_to_guard.end())
			return it->second;
		int idx = next_guard_idx++;
		clk_domain_to_guard[key] = idx;
		return idx;
	}

	Wire* get_or_create_guard_pi(Module *mod, int guard_idx) {
		auto key = std::make_pair(mod, guard_idx);
		auto it = guard_pi_cache.find(key);
		if (it != guard_pi_cache.end())
			return it->second;
		std::string name = stringf("\\clkguard_%d", guard_idx);
		Wire *w = mod->addWire(name, 1);
		w->port_input = true;
		guard_pi_cache[key] = w;
		total_guards++;
		return w;
	}

	// Returns guard index for an FF cell, or -1 if the FF has no clock.
	int get_ff_guard_idx(Cell *cell, SigMap &sigmap) {
		FfData ff(nullptr, cell);
		if (!ff.has_clk)
			return -1;
		return get_or_create_guard_idx(ff.sig_clk, ff.pol_clk, sigmap);
	}

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

	// Collect the set of clock domains (clk_signal, polarity) for all FFs in a module.
	pool<std::pair<std::string, bool>> collect_clock_domains(ModuleAnalysis &analysis, SigMap &sigmap) {
		pool<std::pair<std::string, bool>> domains;
		for (auto cell : analysis.ff_cells) {
			FfData ff(nullptr, cell);
			if (!ff.has_clk)
				continue;
			SigSpec mapped = sigmap(ff.sig_clk);
			std::string clk_str = log_signal(mapped);
			domains.insert({clk_str, ff.pol_clk});
		}
		return domains;
	}

	void run() {
		StructuralHasher hasher;

		vlog("Cone partitioning: analyzing module `%s'.\n", gold_mod->name.c_str());
		ModuleAnalysis gold_analysis(gold_mod, design);
		gold_analysis.hash_all_cells(hasher);

		vlog("Cone partitioning: analyzing module `%s'.\n", gate_mod->name.c_str());
		ModuleAnalysis gate_analysis(gate_mod, design);
		gate_analysis.hash_all_cells(hasher);

		SigMap gold_sigmap(gold_mod);
		SigMap gate_sigmap(gate_mod);

		// Collect clock domains from each module
		auto gold_domains = collect_clock_domains(gold_analysis, gold_sigmap);
		auto gate_domains = collect_clock_domains(gate_analysis, gate_sigmap);

		bool gold_multi = gold_domains.size() > 1;
		bool gate_multi = gate_domains.size() > 1;

		vlog("Gold module has %d clock domain(s), gate module has %d clock domain(s).\n",
			(int)gold_domains.size(), (int)gate_domains.size());

		if (gold_multi != gate_multi) {
			vlog("ERROR: Clock domain count mismatch — gold has %d, gate has %d.\n",
				(int)gold_domains.size(), (int)gate_domains.size());
			vlog("One module has multiple clock domains while the other does not.\n");
			vlog("The designs are NOT equivalent.\n");
			log_cmd_error("Designs are inequivalent: clock domain count mismatch "
				"(gold=%d, gate=%d). One module has multiple clock domains "
				"while the other does not.\n",
				(int)gold_domains.size(), (int)gate_domains.size());
			return;
		}

		bool multi_clock = gold_multi && gate_multi;
		if (multi_clock) {
			if (gold_domains != gate_domains) {
				vlog("WARNING: Gold and gate have different clock domain sets.\n");
				for (auto &d : gold_domains)
					vlog("  gold domain: %s%s\n", d.second ? "" : "!", d.first.c_str());
				for (auto &d : gate_domains)
					vlog("  gate domain: %s%s\n", d.second ? "" : "!", d.first.c_str());
			}
			vlog("Multi-clock mode: unmatched FFs will be guarded with clock domain PIs.\n");
		}

		// Only consider FF cells for matching
		dict<int, std::vector<Cell*>> gold_ff_by_hash, gate_ff_by_hash;
		for (auto &[cell, h] : gold_analysis.cell_hash)
			if (h != StructuralHasher::CYCLE_GUARD && gold_analysis.ff_cells.count(cell))
				gold_ff_by_hash[h].push_back(cell);
		for (auto &[cell, h] : gate_analysis.cell_hash)
			if (h != StructuralHasher::CYCLE_GUARD && gate_analysis.ff_cells.count(cell))
				gate_ff_by_hash[h].push_back(cell);

		struct ConeGroup {
			std::vector<Cell*> gold_cells;
			std::vector<Cell*> gate_cells;
		};
		std::vector<ConeGroup> groups;

		pool<Cell*> matched_gold_ffs, matched_gate_ffs;

		for (auto &[h, gold_cells] : gold_ff_by_hash) {
			auto it = gate_ff_by_hash.find(h);
			if (it == gate_ff_by_hash.end())
				continue;
			groups.push_back({gold_cells, it->second});
			for (auto c : gold_cells) matched_gold_ffs.insert(c);
			for (auto c : it->second) matched_gate_ffs.insert(c);
		}

		if (groups.empty()) {
			vlog("No structural FF matches found between `%s' and `%s'.\n",
				gold_mod->name.c_str(), gate_mod->name.c_str());
		} else {
			vlog("Found %d structurally matched FF groups.\n", (int)groups.size());
		}

		int cone_idx = 0;
		for (auto &group : groups) {
			expose_matched_ff_group(group.gold_cells, group.gate_cells,
						cone_idx, gold_sigmap, gate_sigmap);
			cone_idx++;
		}

		// In multi-clock mode, expose unmatched FFs with clock-domain guard ANDs.
		// Instead of exposing each unmatched FF individually (which would make
		// matching name-based), we group all unmatched FFs by clock domain and
		// XOR-reduce their Q outputs into a single aggregate PO per domain,
		// ANDed with the clock guard PI. This way the SAT solver compares
		// unmatched FFs by their logic content, not by name.
		if (multi_clock) {
			dict<int, std::vector<Cell*>> gold_unmatched_by_guard, gate_unmatched_by_guard;
			for (auto cell : gold_analysis.ff_cells) {
				if (matched_gold_ffs.count(cell))
					continue;
				int guard_idx = get_ff_guard_idx(cell, gold_sigmap);
				gold_unmatched_by_guard[guard_idx].push_back(cell);
			}
			for (auto cell : gate_analysis.ff_cells) {
				if (matched_gate_ffs.count(cell))
					continue;
				int guard_idx = get_ff_guard_idx(cell, gate_sigmap);
				gate_unmatched_by_guard[guard_idx].push_back(cell);
			}

			int unmatched_gold = 0, unmatched_gate = 0;
			for (auto &[guard_idx, cells] : gold_unmatched_by_guard) {
				expose_unmatched_ff_group(gold_mod, cells, guard_idx);
				unmatched_gold += (int)cells.size();
			}
			for (auto &[guard_idx, cells] : gate_unmatched_by_guard) {
				expose_unmatched_ff_group(gate_mod, cells, guard_idx);
				unmatched_gate += (int)cells.size();
			}
			vlog("Multi-clock: guarded %d unmatched gold FFs, %d unmatched gate FFs.\n",
				unmatched_gold, unmatched_gate);
		}

		gold_mod->fixup_ports();
		gate_mod->fixup_ports();

		vlog("Cone partitioning: created %d POs, %d PIs, %d clock guard PIs.\n",
			total_pos, total_pis, total_guards);
	}

private:
	// For a single matched FF group:
	//   1. Create a PI wire (same name in both modules) to replace the FF's Q
	//      for all downstream consumers.
	//   2. Create a PO wire (same name in both modules) that observes the FF's
	//      actual Q output.
	//   3. Redirect each FF's Q port to a fresh internal wire so the FF is fully
	//      severed from the rest of the circuit. The internal wire drives only
	//      the PO. The old Q wire is now driven by the PI.
	void expose_matched_ff_group(
		const std::vector<Cell*> &gold_cells,
		const std::vector<Cell*> &gate_cells,
		int cone_idx,
		SigMap &/*gold_sigmap*/,
		SigMap &/*gate_sigmap*/)
	{
		if (gold_cells.empty() || gate_cells.empty())
			return;

		Cell *gold_rep = gold_cells[0];
		int q_width = GetSize(gold_rep->getPort(ID::Q));
		if (q_width == 0)
			return;

		std::string pi_name = stringf("\\cone_%d_ff_pi", cone_idx);
		std::string po_name = stringf("\\cone_%d_po", cone_idx);

		if (verbose) {
			vlog("  Cone %d: PI %s, PO %s (width %d) for %d+%d FFs.\n",
				cone_idx, pi_name.c_str(), po_name.c_str(), q_width,
				(int)gold_cells.size(), (int)gate_cells.size());
		}

		rewire_ff_group(gold_mod, gold_cells, pi_name, po_name, q_width, cone_idx);
		rewire_ff_group(gate_mod, gate_cells, pi_name, po_name, q_width, cone_idx);

		total_pis++;
		total_pos++;
	}

	void rewire_ff_group(Module *mod, const std::vector<Cell*> &ff_cells,
			     const std::string &pi_name, const std::string &po_name,
			     int q_width, int cone_idx)
	{
		if (mod->wire(pi_name) || mod->wire(po_name))
			return;

		Wire *pi_wire = mod->addWire(pi_name, q_width);
		pi_wire->port_input = true;

		Wire *po_wire = mod->addWire(po_name, q_width);
		po_wire->port_output = true;

		bool po_connected = false;
		int ff_idx = 0;
		for (auto cell : ff_cells) {
			SigSpec old_q = cell->getPort(ID::Q);
			if (GetSize(old_q) != q_width)
				continue;

			std::string q_int_name = stringf("\\cone_%d_q_%d", cone_idx, ff_idx);
			Wire *q_int = mod->addWire(q_int_name, q_width);

			cell->setPort(ID::Q, SigSpec(q_int));

			mod->connect(old_q, SigSpec(pi_wire));

			if (!po_connected) {
				mod->connect(SigSpec(po_wire), SigSpec(q_int));
				po_connected = true;
			}

			ff_idx++;
		}
	}

	// Expose all unmatched FFs in a single clock domain as one aggregate PO.
	// Each FF's Q is redirected to an internal wire and a PI replaces it for
	// downstream consumers. All the internal Q wires are XOR-reduced into a
	// single 1-bit signal, ANDed with the clock guard PI, and driven out as
	// one shared PO. This makes the comparison logic-based rather than
	// name-based across gold/gate.
	void expose_unmatched_ff_group(Module *mod, const std::vector<Cell*> &cells, int guard_idx)
	{
		if (cells.empty())
			return;

		std::string prefix = guard_idx >= 0
			? stringf("\\uff_domain_%d", guard_idx)
			: std::string("\\uff_domain_unclocked");
		std::string po_name = prefix + "_po";

		if (mod->wire(po_name))
			return;

		// Disconnect each FF's Q, create a PI replacement, and collect
		// internal Q wires for the reduction.
		std::vector<Wire*> q_internals;
		int ff_idx = 0;
		for (auto cell : cells) {
			SigSpec old_q = cell->getPort(ID::Q);
			int q_width = GetSize(old_q);
			if (q_width == 0) {
				ff_idx++;
				continue;
			}

			std::string pi_name = stringf("%s_ff%d_pi", prefix.c_str(), ff_idx);
			std::string q_int_name = stringf("%s_ff%d_q", prefix.c_str(), ff_idx);

			if (mod->wire(pi_name)) {
				ff_idx++;
				continue;
			}

			Wire *pi_wire = mod->addWire(pi_name, q_width);
			pi_wire->port_input = true;

			Wire *q_int = mod->addWire(q_int_name, q_width);

			cell->setPort(ID::Q, SigSpec(q_int));
			mod->connect(old_q, SigSpec(pi_wire));

			q_internals.push_back(q_int);
			total_pis++;

			if (verbose) {
				vlog("  Unmatched FF %s in %s: PI %s (width %d) [guard=%d].\n",
					cell->name.c_str(), mod->name.c_str(),
					pi_name.c_str(), q_width, guard_idx);
			}
			ff_idx++;
		}

		if (q_internals.empty())
			return;

		// XOR-reduce all internal Q bits down to a single bit.
		SigSpec all_bits;
		for (auto w : q_internals)
			for (int i = 0; i < w->width; i++)
				all_bits.append(SigBit(w, i));

		SigBit reduced;
		if (GetSize(all_bits) == 1) {
			reduced = all_bits[0];
		} else {
			SigBit acc = all_bits[0];
			for (int i = 1; i < GetSize(all_bits); i++) {
				Wire *tmp = mod->addWire(
					stringf("%s_xor_%d", prefix.c_str(), i), 1);
				mod->addXor(stringf("%s_xor_%d_cell", prefix.c_str(), i),
					    acc, all_bits[i], SigBit(tmp, 0));
				acc = SigBit(tmp, 0);
			}
			reduced = acc;
		}

		Wire *po_wire = mod->addWire(po_name, 1);
		po_wire->port_output = true;

		if (guard_idx >= 0) {
			Wire *guard_pi = get_or_create_guard_pi(mod, guard_idx);
			Wire *guarded = mod->addWire(prefix + "_guarded", 1);
			mod->addAnd(prefix + "_clkand",
				    reduced, SigBit(guard_pi, 0), SigBit(guarded, 0));
			mod->connect(SigSpec(po_wire), SigSpec(guarded));
		} else {
			mod->connect(SigBit(po_wire, 0), reduced);
		}

		total_pos++;

		if (verbose) {
			vlog("  Unmatched FF group [guard=%d] in %s: %d FFs -> PO %s (1-bit XOR-reduced).\n",
				guard_idx, mod->name.c_str(), (int)cells.size(), po_name.c_str());
		}
	}

};

// ---------------------------------------------------------------------------
// Pass registration
// ---------------------------------------------------------------------------

struct ConePartitionPass : public Pass {
	ConePartitionPass() : Pass("cone_partition",
		"expose matched structural cones as PI/PO pairs") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    cone_partition [options] gold_module gate_module\n");
		log("\n");
		log("This pass identifies structurally identical flip-flop cones between two\n");
		log("modules (typically a gold and gate design) using the same hashing algorithm\n");
		log("as struct_partition, then exposes each matched cone's boundary as ports:\n");
		log("\n");
		log("  - Each matched FF's Q output is disconnected from the circuit and\n");
		log("    exposed as a new output port (PO).\n");
		log("  - A new input port (PI) replaces the FF's Q output for any downstream\n");
		log("    consumers.\n");
		log("  - The cone's transitive fanin (back through combinational logic) is\n");
		log("    traced until it reaches a module PI, an unmatched FF boundary, or\n");
		log("    another matched FF (whose replacement PI is reused). Leaf signals\n");
		log("    at the cone boundary become new input ports.\n");
		log("\n");
		log("Multi-clock-domain handling:\n");
		log("\n");
		log("  The pass collects the set of clock domains (signal + polarity) from\n");
		log("  all FFs in each module. Three cases:\n");
		log("\n");
		log("    1. Both modules have a single clock domain (or no clocked FFs):\n");
		log("       no special handling; cones are created as above.\n");
		log("\n");
		log("    2. Only ONE module has multiple clock domains while the other has\n");
		log("       one: the pass errors out, declaring the designs inequivalent.\n");
		log("       A design cannot gain/lose clock domains and still be equivalent.\n");
		log("\n");
		log("    3. Both modules have multiple clock domains: after creating cones\n");
		log("       for structurally matched FFs (as above), unmatched FFs are\n");
		log("       grouped by clock domain. Each group's Q outputs are XOR-\n");
		log("       reduced into a single bit, ANDed with the 1-bit clock-domain\n");
		log("       guard PI (clkguard_N), and driven out as one shared PO per\n");
		log("       domain. This makes the comparison logic-based rather than\n");
		log("       name-based across gold/gate.\n");
		log("\n");
		log("    -v\n");
		log("        verbose output: log each created port\n");
		log("\n");
		log("    -o <file>\n");
		log("        write verbose log output to <file> instead of standard log\n");
		log("\n");
		log("Typical usage:\n");
		log("\n");
		log("    read_rtlil gold.il\n");
		log("    read_rtlil gate.il\n");
		log("    cone_partition gold gate\n");
		log("    # Each cone now has its own PI/PO ports for targeted checking.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool verbose = false;
		std::string log_file_path;

		log_header(design, "Executing CONE_PARTITION pass.\n");

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

		ConePartitionWorker worker(design, gold_mod, gate_mod, verbose, log_file);
		worker.run();

		if (log_file)
			fclose(log_file);
	}
} ConePartitionPass;

PRIVATE_NAMESPACE_END
