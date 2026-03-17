/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Silimate Inc.
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
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ff.h"
#include "kernel/satgen.h"
#include <queue>
#include <algorithm>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Configuration
static const int DEFAULT_MAX_COVER = 100;      // Max candidate signals to consider
static const int DEFAULT_MIN_NET_SIZE = 10;         // Min registers per clock gate

struct InferCeWorker
{
	Module *module;
	SigMap sigmap;
	
	// Configuration
	int max_cover;
	int min_net_size;
	
	// Maps output signal bits to their driver cells
	dict<SigBit, Cell*> sig_to_driver;
	
	// Maps cell input pins to their source signals  
	dict<SigBit, pool<Cell*>> sig_to_sinks;
	
	// Pre-computed list of combinational cells (for SAT import)
	std::vector<Cell*> comb_cells;
	
	// Statistics
	int accepted_count = 0;
	int rejected_sat_count = 0;
	int sat_solves = 0;
	
	InferCeWorker(Module *module, int max_cover, int min_net_size)
		: module(module), sigmap(module), 
		  max_cover(max_cover), min_net_size(min_net_size)
	{
		// Build driver and sink maps
		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first)) {
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							sig_to_driver[bit] = cell;
				}
				if (cell->input(conn.first)) {
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							sig_to_sinks[bit].insert(cell);
				}
			}
			
			// Collect combinational cells for SAT
			if (!cell->type.in(ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
			                   ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr), 
			                   ID($dffsre), ID($_DFF_P_), ID($_DFF_N_), ID($_DFFE_PP_),
			                   ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_))) {
				comb_cells.push_back(cell);
			}
		}
	}
	
	
	// Get upstream signals feeding into given signals (BFS backward)
	pool<SigBit> getUpstreamSignals(const pool<SigBit> &start_signals, int limit)
	{
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		
		for (auto bit : start_signals) {
			worklist.push(bit);
			visited.insert(bit);
		}
		
		while (!worklist.empty() && (int)visited.size() < limit) {
			SigBit bit = worklist.front();
			worklist.pop();
			
			if (!sig_to_driver.count(bit))
				continue;
			
			Cell *driver = sig_to_driver[bit];
			
		if (driver->type.in(ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
		                    ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr),
		                    ID($dffsre), ID($_DFF_P_), ID($_DFF_N_), ID($_DFFE_PP_),
		                    ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_)))
				continue;
			
			for (auto &conn : driver->connections())
				if (driver->input(conn.first))
					for (auto in_bit : sigmap(conn.second))
						if (in_bit.wire && !visited.count(in_bit)) {
							visited.insert(in_bit);
							worklist.push(in_bit);
						}
		}
		return visited;
	}
	
	// Get cells in the transitive fanin cone of given signals (for SAT import)
	// This is much faster than importing ALL cells
	pool<Cell*> getConeOfLogic(SigSpec sig)
	{
		pool<Cell*> cone_cells;
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		
		// Start from all bits in sig
		for (auto bit : sigmap(sig)) {
			if (bit.wire && !visited.count(bit)) {
				visited.insert(bit);
				worklist.push(bit);
			}
		}
		
		// BFS backward through drivers
		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();
			
			if (!sig_to_driver.count(bit))
				continue;
			
			Cell *driver = sig_to_driver[bit];
			
			// Skip registers
			if (driver->type.in(ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
			                    ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr),
			                    ID($dffsre), ID($_DFF_P_), ID($_DFF_N_), ID($_DFFE_PP_),
			                    ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_)))
				continue;
			
			// Add this cell to cone
			if (cone_cells.count(driver))
				continue;  // Already processed
			cone_cells.insert(driver);
			
			// Add inputs of driver to worklist
			for (auto &conn : driver->connections()) {
				if (driver->input(conn.first)) {
					for (auto in_bit : sigmap(conn.second)) {
						if (in_bit.wire && !visited.count(in_bit)) {
							visited.insert(in_bit);
							worklist.push(in_bit);
						}
					}
				}
			}
		}
		
		return cone_cells;
	}
	
	// Check if OR/AND of signals forms a valid gating condition using SAT
	// Uses a PRE-CREATED SAT solver (passed in) to avoid recreating for each check
	bool isValidGatingSetWithSolver(ezSatPtr &ez, SatGen &satgen, 
	                                 const std::vector<SigBit> &conds, 
	                                 SigSpec sig_d, SigSpec sig_q, bool as_enable)
	{
		if (conds.empty())
			return false;
		
		sat_solves++;
		
		std::vector<int> d_vec = satgen.importSigSpec(sig_d);
		std::vector<int> q_vec = satgen.importSigSpec(sig_q);
		
		// Build OR (for enable) or AND (for disable) of condition signals
		std::vector<int> cond_vars;
		for (auto bit : conds)
			cond_vars.push_back(satgen.importSigSpec(SigSpec(bit))[0]);
		
		int combined_cond;
		if (as_enable) {
			// Clock enable: OR of signals (any signal high = enable)
			combined_cond = ez->expression(ezSAT::OpOr, cond_vars);
		} else {
			// Clock disable: AND of signals (all signals high = disable)
			combined_cond = ez->expression(ezSAT::OpAnd, cond_vars);
		}
		
		int d_ne_q = ez->vec_ne(d_vec, q_vec);
		
		// Safe gating: when gating is active (enable=0 or disable=1), D must equal Q
		int gating_active = as_enable ? ez->NOT(combined_cond) : combined_cond;
		int query = ez->AND(gating_active, d_ne_q);
		
		std::vector<int> assumptions = {query};
		std::vector<int> dummy_exprs;
		std::vector<bool> dummy_vals;
		
		bool is_valid = !ez->solve(dummy_exprs, dummy_vals, assumptions);
		if (!is_valid)
			rejected_sat_count++;
		return is_valid;
	}
	
	// Wrapper that creates a fresh SAT solver (used for standalone checks)
	bool isValidGatingSet(const std::vector<SigBit> &conds, SigSpec sig_d, SigSpec sig_q, bool as_enable)
	{
		if (conds.empty())
			return false;
		
		pool<Cell*> cone = getConeOfLogic(sig_d);
		ezSatPtr ez;
		SatGen satgen(ez.get(), &sigmap);
		for (auto cell : cone)
			satgen.importCell(cell);
		
		return isValidGatingSetWithSolver(ez, satgen, conds, sig_d, sig_q, as_enable);
	}
	
	// Binary search to minimize the gating condition set
	// Tries to remove half of the signals at a time
	// Uses pre-created SAT solver to avoid recreating for each check
	void minimizeGatingConditionWithSolver(
		ezSatPtr &ez, SatGen &satgen,
		std::vector<SigBit> &good_conds,
		std::vector<SigBit>::iterator begin,
		std::vector<SigBit>::iterator end,
		SigSpec sig_d, SigSpec sig_q, bool as_enable)
	{
		int half_len = (end - begin) / 2;
		
		if (half_len == 0)
			return;
		
		auto mid = begin + half_len;
		
		// Try removing [mid, end) from the condition
		std::vector<SigBit> test_conds;
		test_conds.insert(test_conds.end(), good_conds.begin(), begin);
		test_conds.insert(test_conds.end(), begin, mid);
		test_conds.insert(test_conds.end(), end, good_conds.end());
		
		if (!test_conds.empty() && isValidGatingSetWithSolver(ez, satgen, test_conds, sig_d, sig_q, as_enable)) {
			// Can remove [mid, end)
			good_conds.erase(mid, end);
			// Recurse on remaining half
			minimizeGatingConditionWithSolver(ez, satgen, good_conds, begin, begin + half_len, sig_d, sig_q, as_enable);
		} else {
			// Cannot remove all of [mid, end), try to minimize each half
			if (end - mid > 1)
				minimizeGatingConditionWithSolver(ez, satgen, good_conds, mid, end, sig_d, sig_q, as_enable);
			minimizeGatingConditionWithSolver(ez, satgen, good_conds, begin, mid, sig_d, sig_q, as_enable);
		}
	}
	
	// Wrapper for standalone use (creates fresh solver)
	void minimizeGatingCondition(
		std::vector<SigBit> &good_conds,
		std::vector<SigBit>::iterator begin,
		std::vector<SigBit>::iterator end,
		SigSpec sig_d, SigSpec sig_q, bool as_enable)
	{
		pool<Cell*> cone = getConeOfLogic(sig_d);
		ezSatPtr ez;
		SatGen satgen(ez.get(), &sigmap);
		for (auto cell : cone)
			satgen.importCell(cell);
		
		minimizeGatingConditionWithSolver(ez, satgen, good_conds, begin, end, sig_d, sig_q, as_enable);
	}
	
	// Find gating condition for a register
	// Returns: {gating_conds, is_enable, cone_size}
	std::tuple<std::vector<SigBit>, bool, int> findGatingCondition(Cell *reg)
	{
		FfData ff(nullptr, reg);
		
		pool<SigBit> d_inputs;
		for (auto bit : sigmap(ff.sig_d))
			if (bit.wire)
				d_inputs.insert(bit);
		
		pool<SigBit> upstream = getUpstreamSignals(d_inputs, max_cover);
		
		std::vector<SigBit> candidates;
		for (auto bit : upstream)
			candidates.push_back(bit);
		
		if ((int)candidates.size() > max_cover)
			candidates.resize(max_cover);
		
		if (candidates.empty())
			return {{}, false, 0};
		
		// Create SAT solver ONCE for this register
		pool<Cell*> cone = getConeOfLogic(ff.sig_d);
		int cone_size = (int)cone.size();
		
		// Skip registers with trivial cones (not worth gating) or huge cones (too expensive)
		const int MIN_CONE_SIZE = 2;
		const int MAX_CONE_SIZE = 500;
		if (cone_size < MIN_CONE_SIZE || cone_size > MAX_CONE_SIZE)
			return {{}, false, cone_size};
		
		ezSatPtr ez;
		SatGen satgen(ez.get(), &sigmap);
		for (auto cell : cone)
			satgen.importCell(cell);
		
		// Try as clock enable first
		if (isValidGatingSetWithSolver(ez, satgen, candidates, ff.sig_d, ff.sig_q, true)) {
			minimizeGatingConditionWithSolver(ez, satgen, candidates, candidates.begin(), candidates.end(),
			                                   ff.sig_d, ff.sig_q, true);
			if (!candidates.empty())
				return {candidates, true, cone_size};
		}
		
		// Try as clock disable
		if (isValidGatingSetWithSolver(ez, satgen, candidates, ff.sig_d, ff.sig_q, false)) {
			minimizeGatingConditionWithSolver(ez, satgen, candidates, candidates.begin(), candidates.end(),
			                                   ff.sig_d, ff.sig_q, false);
			if (!candidates.empty())
				return {candidates, false, cone_size};
		}
		
		return {{}, false, cone_size};
	}
	
	// Insert clock gating logic for a group of registers
	void insertClockGate(const std::vector<Cell*> &regs, 
	                     const std::vector<SigBit> &gating_conds,
	                     bool as_enable)
	{
		if (regs.empty() || gating_conds.empty())
			return;
		
		// Build gating condition: OR for enable, AND for disable
		SigBit gating_signal;
		if (gating_conds.size() == 1) {
			gating_signal = gating_conds[0];
		} else {
			SigSpec cond_inputs;
			for (auto bit : gating_conds)
				cond_inputs.append(bit);
			
			Wire *cond_wire = module->addWire(NEW_ID);
			if (as_enable)
				module->addReduceOr(NEW_ID, cond_inputs, cond_wire);
			else
				module->addReduceAnd(NEW_ID, cond_inputs, cond_wire);
			gating_signal = cond_wire;
		}
		
		// If disable signal, invert to get enable
		if (!as_enable) {
			Wire *inv_wire = module->addWire(NEW_ID);
			module->addNot(NEW_ID, gating_signal, inv_wire);
			gating_signal = inv_wire;
		}
		
		// Add CE to each register
		for (auto reg : regs) {
			FfData ff(nullptr, reg);
			
			if (ff.has_ce) {
				Wire *combined_ce = module->addWire(NEW_ID);
				module->addAnd(NEW_ID, ff.sig_ce, gating_signal, combined_ce);
				ff.sig_ce = combined_ce;
			} else {
				ff.has_ce = true;
				ff.sig_ce = gating_signal;
				ff.pol_ce = true;
			}
			
			ff.emit();
		}
	}
	
	// Check if register can be added to an existing gate
	bool canReuseGate(const std::vector<SigBit> &existing_conds, Cell *reg, bool is_enable)
	{
		FfData ff(nullptr, reg);
		return isValidGatingSet(existing_conds, ff.sig_d, ff.sig_q, is_enable);
	}
	
	// Main processing function
	void run()
	{
		std::vector<Cell*> registers;
		for (auto cell : module->cells()) {
			if (!cell->type.in(ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
			                   ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr),
			                   ID($dffsre), ID($_DFF_P_), ID($_DFF_N_), ID($_DFFE_PP_),
			                   ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_)))
				continue;
			
			FfData ff(nullptr, cell);
			if (ff.has_ce || !ff.has_clk)
				continue;
			
			registers.push_back(cell);
		}
		
		log("Processing module %s: %zu cells, %zu flip-flops, %zu wires\n",
		    log_id(module), module->cells().size(), registers.size(), module->wires().size());
		
		if (registers.empty())
			return;
		
		struct AcceptedGate {
			std::vector<SigBit> conds;
			pool<SigBit> cond_set;
			std::vector<Cell*> regs;
			bool is_enable;
		};
		std::vector<AcceptedGate> accepted_gates;
		dict<SigBit, std::vector<size_t>> net_to_accepted;
		
		int reg_idx = 0;
		for (auto reg : registers) {
			auto [gating_conds, is_enable, cone_size] = findGatingCondition(reg);
			log("Processing register %d/%zu: %s (cone=%d)\n", ++reg_idx, registers.size(), log_id(reg), cone_size);
			
			if (gating_conds.empty())
				continue;
			
			pool<SigBit> cond_set;
			for (auto bit : gating_conds)
				cond_set.insert(bit);
			
			// Find candidate gates sharing any net
			pool<size_t> candidate_gates;
			for (auto bit : gating_conds)
				if (net_to_accepted.count(bit))
					for (auto idx : net_to_accepted[bit])
						candidate_gates.insert(idx);
			
			// HEURISTIC: Only check limited gates for reuse
			const int MAX_REUSE_CHECKS = 20;
			
			bool found_match = false;
			int checked = 0;
			for (auto idx : candidate_gates) {
				if (checked >= MAX_REUSE_CHECKS)
					break;
				
				auto &gate = accepted_gates[idx];
				if (gate.is_enable != is_enable)
					continue;
				
				checked++;
				if (canReuseGate(gate.conds, reg, is_enable)) {
					gate.regs.push_back(reg);
					found_match = true;
					break;
				}
			}
			
			if (!found_match) {
				size_t new_idx = accepted_gates.size();
				accepted_gates.push_back({gating_conds, cond_set, {reg}, is_enable});
				for (auto bit : gating_conds)
					net_to_accepted[bit].push_back(new_idx);
			}
		}
		
		// Insert clock gates for groups meeting threshold
		for (auto &gate : accepted_gates) {
			if ((int)gate.regs.size() >= min_net_size) {
				insertClockGate(gate.regs, gate.conds, gate.is_enable);
				accepted_count += gate.regs.size();
			}
		}
	}
};

struct InferCePass : public Pass {
	InferCePass() : Pass("infer_ce", "Infer clock enable signals from conditional logic") { }
	
	void help() override
	{
		log("\n");
		log("    infer_ce [options] [selection]\n");
		log("\n");
		log("This command infers clock enable (CE) signals from conditional logic.\n");
		log("It analyzes registers and uses SAT solving to find signals that can\n");
		log("serve as clock enable conditions (when the signal is low, D==Q).\n");
		log("\n");
		log("Algorithm based on:\n");
		log("  - \"Automatic Synthesis of Clock Gating Logic\" by Aaron P. Hurst\n");
		log("  - OpenROAD's cgt module implementation\n");
		log("\n");
		log("    -max_cover <n>\n");
		log("        maximum number of candidate signals to consider per register\n");
		log("        (default: %d)\n", DEFAULT_MAX_COVER);
		log("\n");
		log("    -min_net_size <n>\n");
		log("        minimum number of registers that must share a gating condition\n");
		log("        for a clock gate to be inserted (default: %d)\n", DEFAULT_MIN_NET_SIZE);
		log("\n");
	}
	
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing INFER_CE pass.\n");
		
		int max_cover = DEFAULT_MAX_COVER;
		int min_net_size = DEFAULT_MIN_NET_SIZE;
		
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_cover" && argidx+1 < args.size()) {
				max_cover = std::stoi(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-min_net_size" && argidx+1 < args.size()) {
				min_net_size = std::stoi(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		
		int total_gates = 0;
		for (auto module : design->selected_modules()) {
			InferCeWorker worker(module, max_cover, min_net_size);
			worker.run();
			total_gates += worker.accepted_count;
		}
		
		log("Inserted clock enables for %d registers.\n", total_gates);
	}
} InferCePass;

PRIVATE_NAMESPACE_END
