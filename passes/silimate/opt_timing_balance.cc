/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2026  Abhinav Tondapu   <abhinav@silimate.com>
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
#include "kernel/utils.h"
#include <algorithm>
#include <cmath>
#include <cstring>
#include <deque>
#include <limits>
#include <queue>
#include <tuple>
#include <vector>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

/* Invariants:
 * - Operates on internal word cells ($add/$and/$or/$xor) pre-techmap
 * - Connectivity and timing keys use sigmap-mapped signals
 * - Rewiring uses original head Y bits to avoid alias drift
 * - Disjoint clusters are rewritten per sweep, clean/rebuild happens per iteration
*/

// -----------------------------------------------------------------------------
// Shared constants, helpers, and traits
// -----------------------------------------------------------------------------

static constexpr double kDelayDefault                 = 1.0;
static constexpr double kDelayLogic                   = 0.5;
static constexpr double kMinIterationDelta            = 1e-3;
static constexpr int    kMaxPassIterations            = 10;
static constexpr int    kTraversalStackReserve        = 256;

static const IdString kAttrTimingBalanceGenerated = "\\timing_balance_generated";

static IdString make_id(Cell *anchor, const char *suffix)
{
	// NEW_ID2_SUFFIX relies on a local variable named `cell`
	Cell *cell = anchor;
	return NEW_ID2_SUFFIX(suffix);
}

static inline double log2p1_int(int n) { return std::log2(static_cast<double>(n) + 1.0); }

static int cell_y_width(const Cell *cell)
{
	log_assert(cell != nullptr);
	if (cell->hasParam(ID::Y_WIDTH))
		return std::max(1, cell->getParam(ID::Y_WIDTH).as_int());
	if (cell->hasPort(ID::Y))
		return std::max(1, GetSize(cell->getPort(ID::Y)));

	// TimingOracle can query non-target drivers, fall back to widest output port
	int width = 0;
	for (const auto &[port_id, sig] : cell->connections())
		if (cell->output(port_id))
			width = std::max(width, GetSize(sig));
	return std::max(1, width);
}

enum class BalanceCategory {
	Logic,
	Arith
};

enum class WidthRule {
	MaxInput,
	AddCarry
};

enum class DelayHeuristicKind {
	Fixed,
	AddLike
};

enum class TraversalState : int {
	Unseen = 0,
	Active = 1,
	Done = 2
};

// Per-cell balancing traits and delay heuristic policy
struct SupportedCellSpec
{
	IdString type;
	BalanceCategory category;
	bool requires_strict_width_match = false;
	bool requires_matching_signedness = false;
	WidthRule width_rule = WidthRule::MaxInput;
	DelayHeuristicKind delay_kind = DelayHeuristicKind::Fixed;
	double fixed_delay = 0.0;
};

// Registry for balance targets and their delay/width behavior
// Adding a new associative target should only require editing this table
static const std::vector<SupportedCellSpec> &supported_cell_registry()
{
	static const std::vector<SupportedCellSpec> specs = {
		{ID($and), BalanceCategory::Logic, false, false, WidthRule::MaxInput, DelayHeuristicKind::Fixed, kDelayLogic},
		{ID($or),  BalanceCategory::Logic, false, false, WidthRule::MaxInput, DelayHeuristicKind::Fixed, kDelayLogic},
		{ID($xor), BalanceCategory::Logic, false, false, WidthRule::MaxInput, DelayHeuristicKind::Fixed, kDelayDefault},
		{ID($add), BalanceCategory::Arith, true,  true,  WidthRule::AddCarry, DelayHeuristicKind::AddLike, 0.0},
	};
	return specs;
}

static const dict<IdString, const SupportedCellSpec*> &supported_cell_registry_map()
{
	static const dict<IdString, const SupportedCellSpec*> by_type = []() {
		dict<IdString, const SupportedCellSpec*> m;
		for (const auto &spec : supported_cell_registry())
			m[spec.type] = &spec;
		return m;
	}();
	return by_type;
}

static const SupportedCellSpec *get_supported_cell_spec(IdString type)
{
	const auto &by_type = supported_cell_registry_map();
	auto it = by_type.find(type);
	if (it == by_type.end())
		return nullptr;
	return it->second;
}

static std::vector<IdString> collect_target_cell_ids(bool enable_logic, bool enable_arith)
{
	std::vector<IdString> ids;
	for (const auto &spec : supported_cell_registry())
	{
		bool enabled_category = (spec.category == BalanceCategory::Logic) ? enable_logic : enable_arith;
		if (!enabled_category)
			continue;
		ids.push_back(spec.type);
	}
	return ids;
}

static bool less_sigbit_key(const SigBit &a, const SigBit &b)
{
	bool a_const = a.wire == nullptr;
	bool b_const = b.wire == nullptr;
	if (a_const != b_const)
		return a_const;

	if (a_const) {
		int ad = static_cast<int>(a.data);
		int bd = static_cast<int>(b.data);
		return ad < bd;
	}

	if (a.wire->name != b.wire->name)
		return std::strcmp(a.wire->name.c_str(), b.wire->name.c_str()) < 0;
	return a.offset < b.offset;
}

static bool less_sigspec_key(const SigSpec &a, const SigSpec &b)
{
	if (GetSize(a) != GetSize(b))
		return GetSize(a) < GetSize(b);

	int n = GetSize(a);
	for (int i = 0; i < n; i++) {
		const SigBit &ab = a[i];
		const SigBit &bb = b[i];
		if (ab == bb)
			continue;
		return less_sigbit_key(ab, bb);
	}
	return false;
}

// For supported ops here, result signedness is true only when both inputs are signed
static constexpr bool yosys_binary_result_signed(bool a_signed, bool b_signed) { return a_signed && b_signed; }

static const dict<IdString, double> &fixed_delay_table()
{
	static const auto table = dict<IdString, double>{
		{ID($not),       0.0},
		{ID($pos),       0.0},
		{ID($logic_not), 0.0},
		{ID($and),       kDelayLogic},
		{ID($or),        kDelayLogic},
		{ID($xor),       kDelayDefault},
		{ID($xnor),      kDelayDefault},
		{ID($logic_and), kDelayLogic},
		{ID($logic_or),  kDelayLogic},
		{ID($mux),       kDelayDefault},
	};
	return table;
}

static bool is_timing_boundary_cell(Cell *cell, const CellTypes &cell_types)
{
	if (cell == nullptr)
		return true;

	// Explicit user attributes
	if (cell->get_bool_attribute(ID::keep) || cell->get_bool_attribute(ID::blackbox))
		return true;

	// Flip-flops
	if (cell->is_builtin_ff())
		return true;

	// Latches, memories, and formal/simulation cells
	if (cell->type.in(
			ID($dlatch), ID($adlatch), ID($dlatchsr),
			ID($mem), ID($mem_v2), ID($memrd), ID($memrd_v2), ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2),
			ID($anyconst), ID($anyseq), ID($allconst), ID($allseq), ID($equiv),
			ID($assert), ID($assume), ID($cover), ID($check), ID($print)
			))
		return true;

	// Macro or unknown cell
	return !cell_types.cell_known(cell->type);
}

static double estimate_cell_delay(const Cell *cell, int out_width)
{
	if (cell == nullptr)
		return kDelayDefault;

	IdString type = cell->type;
	int width = out_width;

	const auto &by_type = supported_cell_registry_map();
	auto reg_it = by_type.find(type);
	if (reg_it != by_type.end()) {
		const SupportedCellSpec *spec = reg_it->second;
		switch (spec->delay_kind)
		{
			case DelayHeuristicKind::Fixed:
				return spec->fixed_delay;
			case DelayHeuristicKind::AddLike:
				return log2p1_int(width);
		}
	}

	if (type == ID($pmux)) {
		int s_width = 1;
		if (cell->hasParam(ID::S_WIDTH))
			s_width = cell->getParam(ID::S_WIDTH).as_int();
		return log2p1_int(s_width);
	}
	if (type.in(ID($add), ID($sub), ID($neg), ID($alu)))
		return log2p1_int(width);
	if (type.in(ID($mul), ID($div), ID($mod)))
		return width;
	if (type.in(ID($shl), ID($shr), ID($sshl), ID($sshr)))
		return log2p1_int(width);

	const auto &fixed = fixed_delay_table();
	auto it = fixed.find(type);
	if (it != fixed.end())
		return it->second;
	return kDelayDefault;
}

// -----------------------------------------------------------------------------
// Analysis: connectivity and timing oracle
// -----------------------------------------------------------------------------

struct ConnectivitySnapshot
{
	// One-sweep structural connectivity view
	dict<SigBit, Cell*> unique_driver_by_bit;
	SigSet<Cell*> sinks_by_bit;
	pool<SigBit> output_port_bits;

	ConnectivitySnapshot() = default;
	ConnectivitySnapshot(Module *module, SigMap &sigmap) { build(module, sigmap); }

	void build(Module *module, SigMap &sigmap)
	{
		unique_driver_by_bit.clear();
		sinks_by_bit.clear();
		output_port_bits.clear();

		// Full-module view keeps fanout checks selection-safe
		for (Cell *cell : module->cells()) {
			for (const auto &[port_id, sig] : cell->connections()) {
				SigSpec mapped = sigmap(sig);
				if (cell->output(port_id)) {
					for (auto bit : mapped) {
						if (!bit.wire)
							continue;
						auto [it, inserted] = unique_driver_by_bit.emplace(bit, cell);
						if (!inserted && it->second != cell)
							it->second = nullptr;
					}
				}
				if (cell->input(port_id))
					sinks_by_bit.insert(mapped, cell);
			}
		}
		// Output ports mark head boundaries. Input boundaries are handled in TimingOracle
		for (auto wire : module->wires()) {
			if (wire->port_output) {
				for (auto bit : sigmap(wire))
					output_port_bits.insert(bit);
			}
		}
	}

	Cell *get_unique_driver_mapped(const SigSpec &sig) const
	{
		// Caller passes sigmap-mapped signal slices
		Cell *driver = nullptr;
		for (auto bit : sig)
		{
			if (!bit.wire)
				return nullptr;
			auto it = unique_driver_by_bit.find(bit);
			if (it == unique_driver_by_bit.end() || it->second == nullptr)
				return nullptr;
			if (driver == nullptr)
				driver = it->second;
			else if (driver != it->second)
				return nullptr;
		}
		return driver;
	}

	void collect_sinks_mapped(const SigSpec &mapped_sig, pool<Cell*> &sinks)
	{
		// SigSet::find() is non-const in current Yosys API
		sinks.clear();
		sinks_by_bit.find(mapped_sig, sinks);
	}

};

struct TimingOracle
{
	// Lazy backward arrival estimator over the current connectivity snapshot
	// Unknown or boundary drivers return 0.0, combinational cycles return +inf
	const CellTypes &cell_types;
	SigMap &sigmap;
	const dict<SigBit, Cell*> *driver_map;
	dict<SigBit, double> arrival_cache;
	dict<SigBit, TraversalState> visit_state;
	struct StackEntry {
		SigBit bit;
		// false: expand dependencies, true: finalize after children
		bool finalize_phase = false;
	};
	bool cycle_detected = false;

	TimingOracle(const CellTypes &cell_types, SigMap &sigmap,
			const dict<SigBit, Cell*> &driver_map) :
			cell_types(cell_types), sigmap(sigmap), driver_map(&driver_map) { }

	void clear_timing_cache()
	{
		arrival_cache.clear();
		visit_state.clear();
		cycle_detected = false;
	}

	void rebind_driver_map(const dict<SigBit, Cell*> &new_driver_map)
	{
		driver_map = &new_driver_map;
		clear_timing_cache();
	}

	void cache_final_value(SigBit bit, double arrival)
	{
		if (!bit.wire)
			return;
		bit = sigmap(bit);
		arrival_cache[bit] = arrival;
		visit_state[bit] = TraversalState::Done;
	}

	TraversalState get_visit_state(SigBit bit) const
	{
		if (auto it = visit_state.find(bit); it != visit_state.end())
			return it->second;
		return TraversalState::Unseen;
	}

	void set_visit_state(SigBit bit, TraversalState state)
	{
		visit_state[bit] = state;
	}

	double get_arrival(const SigSpec &sig)
	{
		cycle_detected = false;
		double t = 0.0;
		for (auto bit : sigmap(sig))
			t = std::max(t, get_arrival_noguard(bit));
		return t;
	}

private:
	/* 
	 * Two-phase DFS avoids recursion,
	 * finalize_phase = false expands inputs, true computes and caches node arrival
	 * Active marks the current path, unresolved inputs during finalize are treated as cycles with +inf
	 */
	double get_arrival_noguard(SigBit bit)
	{
		SigBit start = sigmap(bit);
		if (!start.wire)
			return 0.0;
		if (auto it = arrival_cache.find(start); it != arrival_cache.end())
			return it->second;

		// Local stack keeps traversal state scoped to one query
		std::vector<StackEntry> eval_stack;
		eval_stack.reserve(kTraversalStackReserve);
		eval_stack.push_back({start, false});

		while (!eval_stack.empty())
		{
			StackEntry e = std::move(eval_stack.back());
			eval_stack.pop_back();
			SigBit curr = e.bit;
			if (!curr.wire)
				continue;
			if (arrival_cache.count(curr))
				continue;

			if (curr.wire->port_input) {
				cache_final_value(curr, 0.0);
				continue;
			}

			Cell *driver = nullptr;
			if (auto it_drv = driver_map->find(curr); it_drv != driver_map->end())
				driver = it_drv->second;
			if (driver == nullptr || is_timing_boundary_cell(driver, cell_types)) {
				cache_final_value(curr, 0.0);
				continue;
			}

			TraversalState state = get_visit_state(curr);

			if (!e.finalize_phase)
			{
				if (state == TraversalState::Done)
					continue;
				if (state == TraversalState::Active) {
					// Node already on current path, skip duplicate expansion
					continue;
				}

				set_visit_state(curr, TraversalState::Active);
				eval_stack.push_back({curr, true});
				for (const auto &[port_id, sig] : driver->connections()) {
					if (!driver->input(port_id))
						continue;
					for (auto in_bit : sigmap(sig)) {
						if (!in_bit.wire || arrival_cache.count(in_bit))
							continue;
						if (get_visit_state(in_bit) == TraversalState::Active) {
							cycle_detected = true;
							continue;
						}
						eval_stack.push_back({in_bit, false});
					}
				}
				continue;
			}

			double max_input = 0.0;
			for (const auto &[port_id, sig] : driver->connections()) {
				if (!driver->input(port_id))
					continue;
				for (auto in_bit : sigmap(sig)) {
					double in_arrival = 0.0;
					if (in_bit.wire) {
						auto it = arrival_cache.find(in_bit);
						if (it != arrival_cache.end())
							in_arrival = it->second;
						else {
							// Missing child arrival at finalize implies combinational cycle
							cycle_detected = true;
							in_arrival = std::numeric_limits<double>::infinity();
						}
					}
					max_input = std::max(max_input, in_arrival);
				}
			}

			double cell_delay = estimate_cell_delay(driver, cell_y_width(driver));
			double t = max_input + cell_delay;
			cache_final_value(curr, t);
		}

		auto it = arrival_cache.find(start);
		return it != arrival_cache.end() ? it->second : 0.0;
	}
};

// -----------------------------------------------------------------------------
// Rewrite planning and emission
// -----------------------------------------------------------------------------

static int natural_output_width(WidthRule width_rule, int a_width, int b_width)
{
	switch (width_rule)
	{
		case WidthRule::AddCarry:
			return std::max(a_width, b_width) + 1;
		case WidthRule::MaxInput:
		default:
			return std::max(a_width, b_width);
	}
}

static int minimum_y_width_for_reassociation(WidthRule width_rule, int a_width, int b_width)
{
	if (width_rule == WidthRule::AddCarry)
		// Validation-only relaxation for modulo 2^N add reassociation
		return std::max(a_width, b_width);
	return natural_output_width(width_rule, a_width, b_width);
}

struct TreeLeaf
{
	SigSpec signal;
	double arrival_time = 0.0;
	int width = 0;
	bool is_signed = false;
	int stable_id = 0;
};

struct MergeShape
{
	int out_width = 1;
	bool a_signed = false;
	bool b_signed = false;
	bool out_signed = false;
};

struct PlannedMerge
{
	int lhs_node = -1;
	int rhs_node = -1;
	MergeShape shape;
};

// Immutable plan produced by HuffmanPlanner and consumed by TreeEmitter
struct TreePlan
{
	// Node ids are dense:
	// - [0, leaves) are leaf nodes
	// - [leaves, leaves+merges) are merge nodes in emission order
	std::vector<TreeLeaf> leaves;
	std::vector<PlannedMerge> merges;
	int root_node = -1;
	double output_arrival = 0.0;

	bool valid() const { return root_node >= 0; }

	int node_count() const { return GetSize(leaves) + GetSize(merges); }
};

// Computes merge order and expected arrival, does not mutate RTLIL
struct HuffmanPlanner
{
	struct PlanNode
	{
		int node_id = -1;
		double arrival_time = 0.0;
		int width = 0;
		bool is_signed = false;
		int stable_id = 0;
	};

	struct PlanNodeCmp
	{
		bool operator()(const PlanNode &a, const PlanNode &b) const
		{
			// Use a min-heap by inverting comparator for std::priority_queue
			return std::tie(a.arrival_time, a.width, a.stable_id) >
					std::tie(b.arrival_time, b.width, b.stable_id);
		}
	};

	MergeShape compute_merge_shape(const TreeLeaf &a, const TreeLeaf &b,
			const SupportedCellSpec &spec, int target_out_width, bool force_root_width) const
	{
		int out_width = std::max(1, target_out_width);
		if (!force_root_width && spec.width_rule == WidthRule::AddCarry)
			out_width = std::min(out_width, natural_output_width(spec.width_rule, a.width, b.width));
		bool a_signed = a.is_signed;
		bool b_signed = b.is_signed;
		bool out_signed = yosys_binary_result_signed(a_signed, b_signed);
		return {out_width, a_signed, b_signed, out_signed};
	}

	double compute_merge_arrival(double a_arrival, double b_arrival, int out_width, const Cell *delay_ref_cell) const
	{
		return std::max(a_arrival, b_arrival) + estimate_cell_delay(delay_ref_cell, out_width);
	}

	TreePlan plan(const std::vector<TreeLeaf> &leaves, IdString cell_type, Cell *reference_cell) const
	{
		// Deterministic leaf ordering is provided by build_tree_leaves()
		TreePlan plan;
		if (leaves.empty())
			return plan;
		plan.leaves = leaves;
		if (GetSize(leaves) == 1) {
			plan.root_node = 0;
			plan.output_arrival = leaves.front().arrival_time;
			return plan;
		}

		const SupportedCellSpec *spec = get_supported_cell_spec(cell_type);
		if (spec == nullptr)
			return {};

		int target_out_width = std::max(1, cell_y_width(reference_cell));

		std::priority_queue<PlanNode, std::vector<PlanNode>, PlanNodeCmp> pq;
		for (int i = 0; i < GetSize(leaves); i++) {
			const auto &leaf = leaves[i];
			pq.push({i, leaf.arrival_time, leaf.width, leaf.is_signed, leaf.stable_id});
		}

		int next_internal_id = GetSize(leaves);
		int next_stable_id = GetSize(leaves);
		/* Greedy Huffman merge always pops the two best nodes first,
		 * stable_id makes tie breaks deterministic for equal arrival and width,
		 * root merge forces target width to preserve the head output contract
		 */
		while (GetSize(pq) > 1)
		{
			PlanNode a = pq.top(); pq.pop();
			PlanNode b = pq.top(); pq.pop();

			bool force_root_width = pq.empty();
			TreeLeaf a_leaf = {SigSpec(), a.arrival_time, a.width, a.is_signed, a.stable_id};
			TreeLeaf b_leaf = {SigSpec(), b.arrival_time, b.width, b.is_signed, b.stable_id};
			MergeShape shape = compute_merge_shape(a_leaf, b_leaf, *spec, target_out_width, force_root_width);
			int out_width = shape.out_width;
			double new_arrival = compute_merge_arrival(a.arrival_time, b.arrival_time, out_width, reference_cell);

			int node_id = next_internal_id++;
			plan.merges.push_back({a.node_id, b.node_id, shape});
			pq.push({node_id, new_arrival, out_width, shape.out_signed, next_stable_id++});
		}

		log_assert(!pq.empty());
		plan.root_node = pq.top().node_id;
		plan.output_arrival = pq.top().arrival_time;
		return plan;
	}
};

// TreeEmitter materializes a precomputed plan into RTLIL cells and wires
struct TreeEmitter
{
	Module *module;
	dict<IdString, int> &cell_count;

	TreeEmitter(Module *module, dict<IdString, int> &cell_count) :
			module(module), cell_count(cell_count) { }

	SigSpec apply(const TreePlan &plan, IdString cell_type, Cell *reference_cell)
	{
		if (!plan.valid() || plan.leaves.empty())
			return {};
		if (GetSize(plan.leaves) == 1)
			return plan.leaves.front().signal;

		int total_nodes = plan.node_count();
		std::vector<SigSpec> node_signals(total_nodes);
		for (int i = 0; i < GetSize(plan.leaves); i++)
			node_signals[i] = plan.leaves[i].signal;

		for (int merge_idx = 0; merge_idx < GetSize(plan.merges); merge_idx++)
		{
			const PlannedMerge &m = plan.merges[merge_idx];
			log_assert(m.lhs_node >= 0 && m.lhs_node < total_nodes);
			log_assert(m.rhs_node >= 0 && m.rhs_node < total_nodes);

			SigSpec a_sig = node_signals[m.lhs_node];
			SigSpec b_sig = node_signals[m.rhs_node];
			log_assert(GetSize(a_sig) > 0 && GetSize(b_sig) > 0);

			IdString new_cell_name = make_id(reference_cell, "timing_balance");
			Cell *new_cell = module->addCell(new_cell_name, cell_type);
			new_cell->set_bool_attribute(kAttrTimingBalanceGenerated);
			new_cell->set_src_attribute(reference_cell->get_src_attribute());
			IdString out_wire_name = make_id(reference_cell, "timing_balance_y");
			Wire *out_wire = module->addWire(out_wire_name, m.shape.out_width);

			new_cell->setPort(ID::A, a_sig);
			new_cell->setPort(ID::B, b_sig);
			new_cell->setPort(ID::Y, out_wire);
			if (new_cell->hasParam(ID::A_SIGNED))
				new_cell->setParam(ID::A_SIGNED, m.shape.a_signed);
			if (new_cell->hasParam(ID::B_SIGNED))
				new_cell->setParam(ID::B_SIGNED, m.shape.b_signed);
			if (new_cell->hasParam(ID::A_WIDTH))
				new_cell->setParam(ID::A_WIDTH, GetSize(a_sig));
			if (new_cell->hasParam(ID::B_WIDTH))
				new_cell->setParam(ID::B_WIDTH, GetSize(b_sig));
			if (new_cell->hasParam(ID::Y_WIDTH))
				new_cell->setParam(ID::Y_WIDTH, m.shape.out_width);
			new_cell->fixup_parameters();

			int node_id = GetSize(plan.leaves) + merge_idx;
			node_signals[node_id] = SigSpec(out_wire);
			cell_count[cell_type]++;
		}

		log_assert(plan.root_node >= 0 && plan.root_node < total_nodes);
		return node_signals[plan.root_node];
	}
};

// -----------------------------------------------------------------------------
// Rewrite engine: cluster harvest, evaluation, and commit loop
// -----------------------------------------------------------------------------

// Harvested cluster plus external source multiset for one candidate head
struct ClusterHarvest
{
	// Track source multiplicity by signedness to preserve per-use semantics
	dict<SigSpec, int> signed_source_uses;
	dict<SigSpec, int> unsigned_source_uses;
	pool<Cell*> cluster_cells;
};

// Worker contract:
// Finds heads for each target type, harvests and evaluates clusters, commits
// beneficial disjoint rewrites in-sweep, and rebuilds views between iterations
struct OptTimingBalanceWorker
{
	struct RewriteStats
	{
		int candidates = 0;
		int trees = 0;
		int rewrites = 0;
	};

	struct RewriteDecision
	{
		SigSpec head_output;
		TreePlan plan;
	};

	struct ObjectiveScore
	{
		double sum_arrival = 0.0;
	};

	struct SweepContext
	{
		pool<Cell*> candidate_cells;
		pool<Cell*> consumed_cells;
		RewriteStats stats;
		dict<Cell*, bool> target_cache;
		dict<Cell*, SigSpec> y_cache;
	};

	Design *design;
	Module *module;
	SigMap sigmap;
	CellTypes cell_types;
	std::vector<IdString> target_cell_ids;
	dict<IdString, int> cell_count;
	HuffmanPlanner planner;
	TreeEmitter emitter;
	dict<IdString, int> warned_contract_issues;
	static constexpr int warnRequiredPortsErrCode = 1;
	static constexpr int warnRequiredWidthParamsErrCode = 2;

	OptTimingBalanceWorker(Design *design, Module *module, const std::vector<IdString> &target_cell_ids) :
		design(design), module(module), sigmap(module), cell_types(design), target_cell_ids(target_cell_ids),
		planner(), emitter(module, cell_count)
	{ }

	// View lifecycle
	void rebuild_views(ConnectivitySnapshot &graph, TimingOracle &timer)
	{
		sigmap = SigMap(module);
		graph.build(module, sigmap);
		timer.rebind_driver_map(graph.unique_driver_by_bit);
	}

	// Warnings and objective gate
	void warn_contract_once(IdString cell_type, int err_code)
	{
		int &mask = warned_contract_issues[cell_type];
		if (mask & err_code)
			return;
		mask |= err_code;
		if (err_code == warnRequiredPortsErrCode) {
			log_warning("opt_timing_balance: skipping %s cells without A/B/Y ports in module %s.\n",
					log_id(cell_type), log_id(module));
		} else {
			log_warning("opt_timing_balance: skipping %s cells without width parameters in module %s. "
					"Pass expects word-level RTL cells (run before gate-level techmapping).\n",
					log_id(cell_type), log_id(module));
		}
	}

	bool objective_improved(const ObjectiveScore &objective_before, const ObjectiveScore &objective_after) const
	{
		if (!std::isfinite(objective_after.sum_arrival))
			return false;
		if (!std::isfinite(objective_before.sum_arrival))
			return true;
		// Sum-only gating can regress the worst single path, but may unlock deferred global gains in later iterations
		return objective_after.sum_arrival < objective_before.sum_arrival - kMinIterationDelta;
	}

	// Candidate and head predicates
	bool is_target_cell_type(Cell *cell, IdString cell_type, bool exclude_generated)
	{
		if (cell == nullptr || cell->type != cell_type)
			return false;
		if (exclude_generated && cell->get_bool_attribute(kAttrTimingBalanceGenerated))
			return false;
		const SupportedCellSpec *spec = get_supported_cell_spec(cell_type);
		if (spec == nullptr)
			return false;
		if (!cell->hasPort(ID::A) || !cell->hasPort(ID::B) || !cell->hasPort(ID::Y)) {
			warn_contract_once(cell_type, warnRequiredPortsErrCode);
			return false;
		}
		if (!cell->hasParam(ID::Y_WIDTH) || !cell->hasParam(ID::A_WIDTH) || !cell->hasParam(ID::B_WIDTH)) {
			warn_contract_once(cell_type, warnRequiredWidthParamsErrCode);
			return false;
		}

		int y_width = cell->getParam(ID::Y_WIDTH).as_int();
		int a_width = cell->getParam(ID::A_WIDTH).as_int();
		int b_width = cell->getParam(ID::B_WIDTH).as_int();
		if (y_width <= 0 || a_width <= 0 || b_width <= 0)
			return false;
		if (GetSize(cell->getPort(ID::A)) != a_width)
			return false;
		if (GetSize(cell->getPort(ID::B)) != b_width)
			return false;
		if (GetSize(cell->getPort(ID::Y)) != y_width)
			return false;

		if (spec->requires_matching_signedness) {
			if (!cell->hasParam(ID::A_SIGNED) || !cell->hasParam(ID::B_SIGNED))
				return false;
		}

		int required_width = minimum_y_width_for_reassociation(spec->width_rule, a_width, b_width);
		return y_width >= required_width;
	}

	bool is_target_cell_type_cached(Cell *cell, IdString cell_type,
			bool exclude_generated, dict<Cell*, bool> &target_cache)
	{
		if (cell == nullptr)
			return false;
		auto it = target_cache.find(cell);
		if (it != target_cache.end())
			return it->second;
		bool is_target = is_target_cell_type(cell, cell_type, exclude_generated);
		target_cache[cell] = is_target;
		return is_target;
	}

	const SigSpec &mapped_y(Cell *cell, dict<Cell*, SigSpec> &y_cache)
	{
		auto it = y_cache.find(cell);
		if (it != y_cache.end())
			return it->second;
		y_cache[cell] = sigmap(cell->getPort(ID::Y));
		return y_cache[cell];
	}

	// Backward cluster extraction
	bool is_head_cell(Cell *cell, IdString cell_type, bool exclude_generated,
			ConnectivitySnapshot &graph, dict<Cell*, bool> &target_cache, dict<Cell*, SigSpec> &y_cache)
	{
		if (cell == nullptr)
			return false;
		const SigSpec &y = mapped_y(cell, y_cache);
		// Output-port drivers are always heads
		for (auto bit : y)
			if (graph.output_port_bits.count(bit))
				return true;

		pool<Cell*> sinks;
		graph.collect_sinks_mapped(y, sinks);
		// Leaf drivers are heads
		if (sinks.empty())
			return true;

		// Any non-target consumer terminates same-type chain growth
		for (Cell *sink : sinks) {
			if (!is_target_cell_type_cached(sink, cell_type, exclude_generated, target_cache))
				return true;
		}
		return false;
	}

	/* 
	 * BFS over same-type unique drivers from head_cell,
	 * merge only when driver Y exactly matches consumed mapped bits to avoid semantic drift,
	 * when merge stops, record source use count with per-port signedness
	 */
	bool collect_cluster(IdString cell_type, Cell *head_cell, const pool<Cell*> &candidate_cells,
			ConnectivitySnapshot &graph, dict<Cell*, bool> &target_cache, dict<Cell*, SigSpec> &y_cache,
			ClusterHarvest &harvest)
	{
		const SupportedCellSpec *spec = get_supported_cell_spec(cell_type);
		if (spec == nullptr || head_cell == nullptr)
			return false;

		bool enforce_strict_width_match = spec->requires_strict_width_match;
		int target_width = 0;
		if (enforce_strict_width_match) {
			// Strict width preserves truncation points
			target_width = cell_y_width(head_cell);
		}

		bool enforce_matching_signedness = spec->requires_matching_signedness;
		bool target_add_signed = false;
		if (enforce_matching_signedness) {
			if (!head_cell->hasParam(ID::A_SIGNED) || !head_cell->hasParam(ID::B_SIGNED))
				return false;
			bool head_a_signed = head_cell->getParam(ID::A_SIGNED).as_bool();
			bool head_b_signed = head_cell->getParam(ID::B_SIGNED).as_bool();
			if (head_a_signed != head_b_signed)
				return false;
			target_add_signed = head_a_signed;
		}

		harvest = ClusterHarvest();
		harvest.cluster_cells.insert(head_cell);
		std::deque<Cell*> queue = {head_cell};

		while (!queue.empty())
		{
			Cell *cell = queue.front();
			queue.pop_front();

			for (IdString port : {ID::A, ID::B}) {
				SigSpec sig = sigmap(cell->getPort(port));
				Cell *driver = graph.get_unique_driver_mapped(sig);

				bool can_merge = true;
				if (driver == nullptr || driver == cell || !candidate_cells.count(driver))
					can_merge = false;
				if (can_merge && !is_target_cell_type_cached(driver, cell_type, true, target_cache))
					can_merge = false;

				if (can_merge) {
					const SigSpec &drv_y = mapped_y(driver, y_cache);
					// Require exact Y coverage for safe reassociation
					if (GetSize(drv_y) != GetSize(sig) || drv_y != sig)
						can_merge = false;
				}
				if (can_merge && enforce_strict_width_match &&
						cell_y_width(driver) != target_width)
					can_merge = false;
				if (can_merge && enforce_matching_signedness) {
					if (!driver->hasParam(ID::A_SIGNED) || !driver->hasParam(ID::B_SIGNED))
						can_merge = false;
					else {
						bool a_signed = driver->getParam(ID::A_SIGNED).as_bool();
						bool b_signed = driver->getParam(ID::B_SIGNED).as_bool();
						if (a_signed != b_signed || a_signed != target_add_signed)
							can_merge = false;
					}
				}

				if (can_merge) {
					if (!harvest.cluster_cells.count(driver)) {
						harvest.cluster_cells.insert(driver);
						queue.push_back(driver);
					}
					continue;
				}

				IdString signed_param = port == ID::A ? ID::A_SIGNED : ID::B_SIGNED;
				bool signed_port = cell->hasParam(signed_param) && cell->getParam(signed_param).as_bool();
				if (signed_port)
					harvest.signed_source_uses[sig]++;
				else
					harvest.unsigned_source_uses[sig]++;
			}
		}

		// Single-cell cluster is a no-op
		return GetSize(harvest.cluster_cells) > 1;
	}

	std::vector<Cell*> collect_candidates(IdString cell_type, bool exclude_generated, dict<Cell*, bool> &target_cache)
	{
		std::vector<Cell*> cells;
		for (Cell *cell : module->selected_cells())
			if (is_target_cell_type_cached(cell, cell_type, exclude_generated, target_cache))
				cells.push_back(cell);
		// Sort lexically for cross-run deterministic candidate order
		std::sort(cells.begin(), cells.end(), [](Cell *a, Cell *b) {
			return std::strcmp(a->name.c_str(), b->name.c_str()) < 0;
		});
		return cells;
	}

	// Rewrite evaluation and commit
	void rewrite_one_head(IdString cell_type, Cell *head, SweepContext &sweep,
			ConnectivitySnapshot &graph, TimingOracle &timer)
	{
		// No per-head rebuild in this sweep, defer heads that read already consumed drivers
		auto source_uses_consumed_driver = [&](const dict<SigSpec, int> &uses) -> bool {
			// Stale snapshot guard: skip heads fed by already rewritten clusters
			for (const auto &[sig, use_count] : uses) {
				if (use_count <= 0)
					continue;
				for (auto bit : sig) {
					if (!bit.wire)
						continue;
					auto drv_it = graph.unique_driver_by_bit.find(bit);
					if (drv_it == graph.unique_driver_by_bit.end())
						continue;
					Cell *driver = drv_it->second;
					if (driver != nullptr && sweep.consumed_cells.count(driver))
						return true;
				}
			}
			return false;
		};

		if (sweep.consumed_cells.count(head))
			return;
		if (!is_head_cell(head, cell_type, true, graph, sweep.target_cache, sweep.y_cache))
			return;

		ClusterHarvest harvest;
		if (!collect_cluster(cell_type, head, sweep.candidate_cells, graph, sweep.target_cache, sweep.y_cache, harvest))
			return;

		// Batch only disjoint clusters in one sweep
		for (Cell *cell : harvest.cluster_cells)
			if (cell != nullptr && sweep.consumed_cells.count(cell))
				return;

		// Defer heads that depend on already rewritten snapshot drivers
		if (source_uses_consumed_driver(harvest.signed_source_uses) ||
				source_uses_consumed_driver(harvest.unsigned_source_uses))
			return;

		RewriteDecision decision;
		if (!evaluate_rewrite(cell_type, head, harvest, timer, decision))
			return;
		if (!commit_rewrite(cell_type, head, decision))
			return;

		for (Cell *cell : harvest.cluster_cells)
			if (cell != nullptr)
				sweep.consumed_cells.insert(cell);
		sweep.stats.rewrites++;

		// No per-head rebuild, invalidate rewritten Y-cache entries only
		for (Cell *cell : harvest.cluster_cells)
			if (cell != nullptr)
				sweep.y_cache.erase(cell);
		sweep.y_cache.erase(head);
	}

	std::vector<Cell*> order_heads_by_dependency(const std::vector<Cell*> &heads, ConnectivitySnapshot &graph, bool &saw_cycle)
	{
		saw_cycle = false;
		if (heads.empty())
			return {};

		/* 
		 * Backward DFS over driver links,
		 * postorder emits upstream-first head order,
		 * cycles fall back to conservative skip in this sweep
		 */
		pool<Cell*> head_cells;
		for (auto head : heads)
			head_cells.insert(head);

		dict<Cell*, TraversalState> state;
		std::vector<Cell*> postorder_heads;
		struct DfsEntry {
			Cell *cell;
			bool postorder;
		};
		std::vector<DfsEntry> stack;
		stack.reserve(kTraversalStackReserve);

		for (auto root : heads)
		{
			if (root == nullptr)
				continue;

			stack.clear();
			stack.push_back({root, false});
			while (!stack.empty())
			{
				DfsEntry e = stack.back();
				stack.pop_back();
				Cell *cell = e.cell;
				if (cell == nullptr || is_timing_boundary_cell(cell, cell_types))
					continue;

				TraversalState st = TraversalState::Unseen;
				if (auto it = state.find(cell); it != state.end())
					st = it->second;

				if (e.postorder) {
					if (st != TraversalState::Done) {
						state[cell] = TraversalState::Done;
						if (head_cells.count(cell))
							postorder_heads.push_back(cell);
					}
					continue;
				}

				if (st == TraversalState::Done)
					continue;
				if (st == TraversalState::Active) {
					saw_cycle = true;
					continue;
				}

				state[cell] = TraversalState::Active;
				stack.push_back({cell, true});

				for (const auto &[port_id, sig] : cell->connections()) {
					if (!cell->input(port_id))
						continue;
					for (auto bit : sigmap(sig)) {
						if (!bit.wire)
							continue;
						auto drv_it = graph.unique_driver_by_bit.find(bit);
						if (drv_it == graph.unique_driver_by_bit.end())
							continue;
						Cell *driver = drv_it->second;
						if (driver == nullptr || driver == cell)
							continue;
						stack.push_back({driver, false});
					}
				}
			}
		}

		if (saw_cycle)
			log_warning("opt_timing_balance: cycle detected in head ordering in module %s, using conservative order.\n",
					log_id(module));

		// Preserve deterministic order for disconnected heads
		pool<Cell*> seen_heads;
		std::vector<Cell*> ordered_heads;
		ordered_heads.reserve(GetSize(heads));
		for (auto head : postorder_heads) {
			if (!seen_heads.count(head)) {
				seen_heads.insert(head);
				ordered_heads.push_back(head);
			}
		}
		for (auto head : heads) {
			if (!seen_heads.count(head))
				ordered_heads.push_back(head);
		}
		return ordered_heads;
	}

	bool build_tree_leaves(const ClusterHarvest &harvest, TimingOracle &timer, std::vector<TreeLeaf> &leaves)
	{
		struct SourceUse {
			SigSpec sig;
			bool is_signed;
			int count;
		};

		leaves.clear();
		int stable_id = 0;

		// Deterministic source-use ordering for stable tree shape
		std::vector<SourceUse> uses;
		uses.reserve(GetSize(harvest.signed_source_uses) + GetSize(harvest.unsigned_source_uses));
		for (const auto &[sig, count] : harvest.signed_source_uses)
			uses.push_back({sig, true, count});
		for (const auto &[sig, count] : harvest.unsigned_source_uses)
			uses.push_back({sig, false, count});
		std::sort(uses.begin(), uses.end(), [](const SourceUse &a, const SourceUse &b) {
			if (a.sig != b.sig)
				return less_sigspec_key(a.sig, b.sig);
			if (a.is_signed != b.is_signed)
				return a.is_signed > b.is_signed;
			return a.count < b.count;
		});

		for (const auto &use : uses)
		{
			if (use.count <= 0)
				continue;
			double src_arrival = timer.get_arrival(use.sig);
			if (!std::isfinite(src_arrival))
				return false;

			for (int i = 0; i < use.count; i++)
				leaves.push_back({use.sig, src_arrival, GetSize(use.sig), use.is_signed, stable_id++});
		}

		return !leaves.empty() && !timer.cycle_detected;
	}

	bool evaluate_rewrite(IdString cell_type, Cell *head_cell, const ClusterHarvest &harvest,
			TimingOracle &timer, RewriteDecision &decision)
	{
		decision = RewriteDecision();
		// Keep exact head output bits. Mapping here can rewire the wrong alias
		decision.head_output = head_cell->getPort(ID::Y);

		std::vector<TreeLeaf> leaves;
		if (!build_tree_leaves(harvest, timer, leaves))
			return false;

		double old_arrival = timer.get_arrival(decision.head_output);
		if (timer.cycle_detected || !std::isfinite(old_arrival))
			return false;

		decision.plan = planner.plan(leaves, cell_type, head_cell);
		if (!decision.plan.valid())
			return false;

		double estimated_new_arrival = decision.plan.output_arrival;
		if (!std::isfinite(estimated_new_arrival) || estimated_new_arrival >= old_arrival - kMinIterationDelta)
			return false;
		return true;
	}

	bool commit_rewrite(IdString cell_type, Cell *head_cell,
			const RewriteDecision &decision)
	{
		SigSpec head_output = decision.head_output;
		SigSpec tree_output = emitter.apply(decision.plan, cell_type, head_cell);
		if (GetSize(head_output) <= 0 || GetSize(tree_output) <= 0)
			return false;
		if (GetSize(head_output) != GetSize(tree_output))
			return false;

		// Detach old driver first to avoid transient multi-driver aliasing
		IdString detached_name = make_id(head_cell, "timing_balance_detach");
		Wire *detached = module->addWire(detached_name, std::max(1, GetSize(head_output)));
		head_cell->setPort(ID::Y, SigSpec(detached));
		if (head_cell->hasParam(ID::Y_WIDTH))
			head_cell->setParam(ID::Y_WIDTH, GetSize(head_output));
		head_cell->fixup_parameters();

		module->connect(head_output, tree_output);
		return true;
	}

	// Objective and per-type sweep
	ObjectiveScore compute_delay_objective(const std::vector<IdString> &target_cell_ids, ConnectivitySnapshot &graph, TimingOracle &timer)
	{
		ObjectiveScore objective;
		for (auto cell_type : target_cell_ids)
		{
			dict<Cell*, bool> target_cache;
			dict<Cell*, SigSpec> y_cache;
			std::vector<Cell*> candidates = collect_candidates(cell_type, false, target_cache);
			std::vector<Cell*> heads;
			for (Cell *cell : candidates) {
				if (is_head_cell(cell, cell_type, false, graph, target_cache, y_cache))
					heads.push_back(cell);
			}

			for (Cell *cell : heads) {
				double arrival = timer.get_arrival(cell->getPort(ID::Y));
				if (timer.cycle_detected || !std::isfinite(arrival))
					return {std::numeric_limits<double>::infinity()};
				objective.sum_arrival += arrival;
			}
		}
		return objective;
	}

	RewriteStats process_cell_type_once(IdString cell_type, ConnectivitySnapshot &graph, TimingOracle &timer)
	{
		SweepContext sweep;
		std::vector<Cell*> candidates = collect_candidates(cell_type, true, sweep.target_cache);
		for (Cell *cell : candidates)
			sweep.candidate_cells.insert(cell);
		sweep.stats.candidates = GetSize(candidates);

		std::vector<Cell*> heads;
		for (Cell *cell : candidates)
			if (is_head_cell(cell, cell_type, true, graph, sweep.target_cache, sweep.y_cache))
				heads.push_back(cell);
		sweep.stats.trees = GetSize(heads);

		bool saw_cycle = false;
		std::vector<Cell*> ordered_heads = order_heads_by_dependency(heads, graph, saw_cycle);
		if (saw_cycle) {
			// Cyclic cones are rejected conservatively for this sweep
			return sweep.stats;
		}

		for (Cell *head : ordered_heads)
			rewrite_one_head(cell_type, head, sweep, graph, timer);
		return sweep.stats;
	}

	// Top-level worker loop
	void run()
	{
		if (target_cell_ids.empty())
			return;

		ConnectivitySnapshot graph(module, sigmap);
		TimingOracle timer(cell_types, sigmap, graph.unique_driver_by_bit);

		ObjectiveScore objective_before = compute_delay_objective(target_cell_ids, graph, timer);
		bool stopped_early = false;
		log("    processing module %s\n", log_id(module));
		log_flush();

		for (int iter = 0; iter < kMaxPassIterations; iter++) {
			ObjectiveScore iter_before = objective_before;
			ObjectiveScore iter_after = iter_before;
			bool improved = false;
			int generated_before = 0;
			for (IdString cell_type : target_cell_ids)
				generated_before += cell_count[cell_type];

			log("        iteration %d/%d begin\n", iter + 1, kMaxPassIterations);
			int total_rewrites = 0;
			for (IdString cell_type : target_cell_ids) {
				RewriteStats stats = process_cell_type_once(cell_type, graph, timer);
				total_rewrites += stats.rewrites;
				log("            %s trees=%d candidates=%d rewrites=%d\n",
						log_id(cell_type), stats.trees, stats.candidates, stats.rewrites);
			}

			int generated_after = 0;
			for (IdString cell_type : target_cell_ids)
				generated_after += cell_count[cell_type];
			int generated_delta = generated_after - generated_before;
			log("            rewrote_trees=%d generated_cells=%d\n", total_rewrites, generated_delta);

			if (total_rewrites > 0) {
				log("            clean -purge begin\n");
				Pass::call_on_module(design, module, "clean -purge");
				log("            clean -purge end\n");
				rebuild_views(graph, timer);
				iter_after = compute_delay_objective(target_cell_ids, graph, timer);
				improved = objective_improved(iter_before, iter_after);
			}

			log("            before = %.3f after = %.3f, %s\n",
					iter_before.sum_arrival, iter_after.sum_arrival,
					improved ? "timing estimation improved, continuing" : "timing estimation did not improve, stopping");
			log("        iteration %d/%d end\n", iter + 1, kMaxPassIterations);
			log_flush();

			if (!improved) {
				stopped_early = true;
				break;
			}
			objective_before = iter_after;
		}

		if (!stopped_early) {
			log("        reached iteration cap %d stopping\n", kMaxPassIterations);
			log_flush();
		}
	}
};

// -----------------------------------------------------------------------------
// Pass wrapper
// -----------------------------------------------------------------------------

struct OptTimingBalancePass : public Pass
{
	OptTimingBalancePass() : Pass("opt_timing_balance", "timing-aware balancing of associative trees") { }

	void help() override
	{
		log("\n");
		log("    opt_timing_balance [options] [selection]\n");
		log("\n");
		log("Iterative timing-aware balancing for cascaded associative cells.\n");
		log("Uses lazy backward arrival estimation plus DAG-ordered Huffman rebuilding.\n");
		log("\n");
		log("    -arith\n");
		log("        only convert arithmetic cells ($add).\n");
		log("\n");
		log("    -logic\n");
		log("        only convert logic cells ($and/$or/$xor).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_TIMING_BALANCE pass (iterative timing-aware tree rewrite).\n");

		size_t argidx;
		bool saw_type_flag = false;
		bool enable_arith = false;
		bool enable_logic = false;
		for (argidx = 1; argidx < (size_t)GetSize(args); argidx++) {
			if (args[argidx] == "-arith") {
				saw_type_flag = true;
				enable_arith = true;
				continue;
			}
			if (args[argidx] == "-logic") {
				saw_type_flag = true;
				enable_logic = true;
				continue;
			}
			// Remaining args are selection filters
			break;
		}
		extra_args(args, argidx, design);

		if (!saw_type_flag) {
			enable_arith = true;
			enable_logic = true;
		}

		std::vector<IdString> target_cell_ids = collect_target_cell_ids(enable_logic, enable_arith);

		dict<IdString, int> cell_count;
		for (auto module : design->selected_modules()) {
			OptTimingBalanceWorker worker(design, module, target_cell_ids);
			worker.run();
			for (const auto &[type, count] : worker.cell_count)
				cell_count[type] += count;
		}

		for (auto cell_type : target_cell_ids) {
			log("    Converted %d %s cells into timing-balanced trees.\n", cell_count[cell_type], log_id(cell_type));
		}
	}
} OptTimingBalancePass;

PRIVATE_NAMESPACE_END
