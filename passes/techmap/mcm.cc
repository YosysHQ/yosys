/**
 * mcm -- Multiple Constant Multiplication.
 *
 * Replaces $mul cells that have a constant operand with a shared adder graph
 * of shifts, additions and subtractions. Multipliers driven by the same
 * variable operand are solved together, so common subterms are computed once.
 *
 * The graph search is the classic Hcub-style greedy over A-operations
 *
 *     w = | u<<su  +/-  v<<sv |     u,v already computable
 * Constant multiplies that are a plain power of two, zero, or one are left to
 * the existing constant folding.
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <tuple>
#include <utility>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// One A-operation: res == |(u << su) +/- (v << sv)| >> norm
struct AOp {
	int res, u, su, v, sv, norm;
	bool sub, swapped;
};

struct AdderGraphConfig {
	int max_depth = 3;
	int max_shift = 12;
	int max_nodes = 64;
	long long work_budget = 2000000;
};

struct McmConfig {
	AdderGraphConfig search;
	int min_const = 3;
	int min_gain = 0;
	bool force = false;
};

struct AdderGraphCandidate {
	int value = -1;
	int depth = 0;
	int score = -1;
	AOp op;
};

using CandidateMap = dict<int, AdderGraphCandidate>;

struct AdderGraph {
	dict<int, int> depth;
	std::vector<AOp> ops;
};

enum class AdderGraphStatus {
	success,
	no_graph,
	budget_exhausted,
};

static int oddify(int n)
{
	if (n < 0)
		n = -n;
	while (n && (n % 2) == 0)
		n /= 2;
	return n;
}

static int shift_of(int n)
{
	int k = 0;
	if (n < 0)
		n = -n;
	while (n && (n % 2) == 0) { n /= 2; k++; }
	return k;
}

// Number of non-zero digits in the non-adjacent signed-digit form.
static int naf_weight(int n)
{
	uint64_t v = n < 0 ? uint64_t(-(int64_t)n) : uint64_t(n);
	int weight = 0;
	while (v) {
		if (v & 1) {
			weight++;
			if ((v & 3) == 3)
				v++;
			else
				v--;
		}
		v >>= 1;
	}
	return weight;
}

struct AdderGraphSolver {
	AdderGraphConfig config;
	int limit;
	long long search_work;
	bool budget_exhausted;
	AdderGraph graph;
	dict<std::pair<int, int>, std::vector<AOp>> op_cache;

	explicit AdderGraphSolver(const AdderGraphConfig &config)
		: config(config), limit(1), search_work(0), budget_exhausted(false)
	{}

	static bool op_less(const AOp &a, const AOp &b)
	{
		return std::tie(a.u, a.su, a.v, a.sv, a.sub, a.swapped, a.norm) <
				std::tie(b.u, b.su, b.v, b.sv, b.sub, b.swapped, b.norm);
	}

	// Enumerate odd coefficients reachable from a pair of graph nodes.
	const std::vector<AOp> &enumerate_pair(int u, int v)
	{
		if (u > v)
			std::swap(u, v);
		auto key = std::make_pair(u, v);
		if (op_cache.count(key))
			return op_cache.at(key);

		auto &ops = op_cache[key];
		dict<int, AOp> unique;
		long long bound = 4LL * limit;
		for (int su = 0; su <= config.max_shift; su++) {
			if (su >= 63 || (long long) u > (bound >> su))
				break;
			long long us = (long long)u << su;
			for (int sv = 0; sv <= config.max_shift; sv++) {
				if (sv >= 63 || (long long) v > (bound >> sv))
					break;
				if (search_work >= config.work_budget) {
					budget_exhausted = true;
					return ops;
				}
				search_work++;
				long long vs = (long long)v << sv;
				long long results[3] = {us + vs, us - vs, vs - us};
				bool subtract[3] = {false, true, true};
				bool swapped[3] = {false, false, true};
				for (int i = 0; i < 3; i++) {
					if (results[i] <= 0 || results[i] > bound || results[i] > std::numeric_limits<int>::max())
						continue;
					AOp op;
					op.res = oddify((int)results[i]);
					op.u = u;
					op.su = su;
					op.v = v;
					op.sv = sv;
					op.sub = subtract[i];
					op.swapped = swapped[i];
					op.norm = shift_of((int)results[i]);
					if (!unique.count(op.res) || op_less(op, unique.at(op.res)))
						unique[op.res] = op;
				}
			}
		}
		for (auto &it : unique)
			ops.push_back(it.second);
		return ops;
	}

	bool build_frontier(CandidateMap &candidates)
	{
		for (auto &a : graph.depth) {
			for (auto &b : graph.depth) {
				if (a.first > b.first || 1 + std::max(a.second, b.second) > config.max_depth)
					continue;
				for (auto &op : enumerate_pair(a.first, b.first)) {
					if (graph.depth.count(op.res) || op.res == 1)
						continue;
					int d = 1 + std::max(a.second, b.second);
					if (!candidates.count(op.res) || d < candidates.at(op.res).depth ||
							(d == candidates.at(op.res).depth && op_less(op, candidates.at(op.res).op))) {
						AdderGraphCandidate candidate;
						candidate.value = op.res;
						candidate.depth = d;
						candidate.op = op;
						candidates[op.res] = candidate;
					}
				}
				if (budget_exhausted)
					return false;
			}
		}
		return true;
	}

	// Prefer a target we can produce immediately.
	bool select_direct_target(const CandidateMap &candidates, const pool<int> &remaining,
			AdderGraphCandidate &selected) const
	{
		for (auto &entry : candidates) {
			if (!remaining.count(entry.first))
				continue;
			int depth = entry.second.depth;
			if (selected.value < 0 || depth < selected.depth ||
					(depth == selected.depth && entry.first < selected.value)) {
				selected.value = entry.first;
				selected.depth = depth;
				selected.op = entry.second.op;
			}
		}
		return selected.value >= 0;
	}

	// Score an intermediate by how many targets it makes reachable in one step.
	bool score_intermediate(const AdderGraphCandidate &candidate, const pool<int> &remaining, int &score)
	{
		pool<int> unlocked;
		for (auto &node : graph.depth) {
			if (1 + std::max(candidate.depth, node.second) > config.max_depth)
				continue;
			for (auto &op : enumerate_pair(candidate.value, node.first))
				if (remaining.count(op.res))
					unlocked.insert(op.res);
			if (budget_exhausted)
				return false;
		}
		if (1 + candidate.depth <= config.max_depth) {
			for (auto &op : enumerate_pair(candidate.value, candidate.value))
				if (remaining.count(op.res))
					unlocked.insert(op.res);
			if (budget_exhausted)
				return false;
		}
		score = GetSize(unlocked);
		return true;
	}

	bool select_intermediate(const CandidateMap &candidates, const pool<int> &remaining,
			AdderGraphCandidate &selected)
	{
		for (auto &entry : candidates) {
			AdderGraphCandidate candidate = entry.second;
			if (!score_intermediate(candidate, remaining, candidate.score))
				return false;
			if (selected.value < 0 || candidate.score > selected.score ||
					(candidate.score == selected.score && (candidate.depth < selected.depth ||
					(candidate.depth == selected.depth && candidate.value < selected.value))))
				selected = candidate;
		}
		return selected.value >= 0;
	}

	bool select_next_candidate(const CandidateMap &candidates, const pool<int> &remaining,
			AdderGraphCandidate &selected)
	{
		if (select_direct_target(candidates, remaining, selected))
			return true;
		if (candidates.empty())
			return false;
		return select_intermediate(candidates, remaining, selected);
	}

	void commit(const AdderGraphCandidate &candidate)
	{
		graph.depth[candidate.value] = candidate.depth;
		graph.ops.push_back(candidate.op);
	}

	pool<int> find_remaining_targets(const pool<int> &targets) const
	{
		pool<int> remaining;
		for (int target : targets)
			if (!graph.depth.count(target))
				remaining.insert(target);
		return remaining;
	}

	AdderGraphStatus solve(const std::vector<int> &targets_in)
	{
		pool<int> targets;
		for (int target : targets_in) {
			int odd_target = oddify(target);
			if (odd_target > 1)
				targets.insert(odd_target);
		}
		limit = 1;
		for (int target : targets)
			limit = std::max(limit, target);

		graph.depth.clear();
		graph.ops.clear();
		op_cache.clear();
		search_work = 0;
		budget_exhausted = false;
		graph.depth[1] = 0;

		int committed_nodes = 0;
		while (true) {
			pool<int> remaining = find_remaining_targets(targets);
			if (remaining.empty())
				break;
			if (committed_nodes >= config.max_nodes)
				return AdderGraphStatus::no_graph;

			CandidateMap candidates;
			if (!build_frontier(candidates))
				return budget_exhausted ? AdderGraphStatus::budget_exhausted : AdderGraphStatus::no_graph;

			AdderGraphCandidate selected;
			if (!select_next_candidate(candidates, remaining, selected))
				return budget_exhausted ? AdderGraphStatus::budget_exhausted : AdderGraphStatus::no_graph;
			commit(selected);
			committed_nodes++;
		}
		return AdderGraphStatus::success;
	}
};

struct McmItem {
	Cell *cell;
	int coefficient;
};

struct McmGroup {
	SigSpec input;
	bool is_signed = false;
	std::vector<McmItem> items;
};

using McmGroupMap = std::map<std::pair<SigSpec, bool>, McmGroup>;

struct McmPlan {
	std::vector<int> active_items;
	std::vector<AOp> ops;
	dict<int, int> demand;
	dict<int, int> raw_width;
	int realized_depth = 0;
	long long shared_cost = 0;
	long long independent_cost = 0;
};

struct McmWorker {
	Module *module;
	SigMap sigmap;
	McmConfig config;
	int n_groups = 0;
	int n_muls = 0;
	int n_adders = 0;

	McmWorker(Module *m, const McmConfig &config) : module(m), sigmap(m), config(config) {}

	SigSpec shl(SigSpec sig, int n, int w, bool is_signed)
	{
		SigSpec result;
		if (n > 0)
			result.append(SigSpec(State::S0, n));
		result.append(sig);
		result.extend_u0(w, is_signed);
		return result;
	}

	bool decode_multiplier(Cell *cell, SigSpec &input, int &coefficient, bool &is_signed)
	{
		if (cell->type != ID($mul) || cell->has_keep_attr())
			return false;

		SigSpec sig_a = sigmap(cell->getPort(ID::A));
		SigSpec sig_b = sigmap(cell->getPort(ID::B));
		bool a_signed = cell->getParam(ID::A_SIGNED).as_bool();
		bool b_signed = cell->getParam(ID::B_SIGNED).as_bool();
		if (a_signed != b_signed)
			return false;
		is_signed = a_signed;

		Const constant;
		if (sig_b.is_fully_const() && !sig_a.is_fully_const()) {
			input = sig_a;
			constant = sig_b.as_const();
		} else if (sig_a.is_fully_const() && !sig_b.is_fully_const()) {
			input = sig_b;
			constant = sig_a.as_const();
		} else {
			return false;
		}
		if (!constant.is_fully_def())
			return false;

		auto value = constant.try_as_int(is_signed);
		if (!value || *value == std::numeric_limits<int>::min()) {
			log_debug("Skipping constant multiplier %s: coefficient %s is outside the supported range.\n",
					log_id(cell), log_const(constant));
			return false;
		}

		coefficient = *value;
		int magnitude = coefficient < 0 ? -coefficient : coefficient;
		if (magnitude == 0 || magnitude == 1)
			return false;
		if ((magnitude & (magnitude - 1)) == 0)
			return false;
		return magnitude >= config.min_const;
	}

	McmGroupMap collect_groups()
	{
		McmGroupMap groups;
		for (auto cell : module->selected_cells()) {
			SigSpec input;
			int coefficient;
			bool is_signed;
			if (!decode_multiplier(cell, input, coefficient, is_signed))
				continue;

			auto key = std::make_pair(input, is_signed);
			auto &group = groups[key];
			if (group.items.empty()) {
				group.input = input;
				group.is_signed = is_signed;
			}
			group.items.push_back(McmItem{cell, coefficient});
		}
		return groups;
	}

	bool select_active_items(const McmGroup &group, const AdderGraph &graph, McmPlan &plan)
	{
		for (int i = 0; i < GetSize(group.items); i++) {
			int odd = oddify(group.items[i].coefficient);
			int depth = graph.depth.at(odd) + (group.items[i].coefficient < 0 ? 1 : 0);
			if (depth > config.search.max_depth) {
				log_debug("Skipping constant multiplier %s: output negation exceeds depth %d.\n",
						log_id(group.items[i].cell), config.search.max_depth);
				continue;
			}
			plan.active_items.push_back(i);
			plan.realized_depth = std::max(plan.realized_depth, depth);
		}
		return !plan.active_items.empty();
	}

	void prune_graph(const McmGroup &group, const AdderGraph &graph, McmPlan &plan)
	{
		dict<int, int> producer;
		for (int i = 0; i < GetSize(graph.ops); i++)
			producer[graph.ops[i].res] = i;

		pool<int> live_values;
		std::function<void(int)> mark_live = [&](int value) {
			if (value == 1 || live_values.count(value))
				return;
			live_values.insert(value);
			log_assert(producer.count(value));
			auto &op = graph.ops[producer.at(value)];
			mark_live(op.u);
			mark_live(op.v);
		};
		for (int i : plan.active_items)
			mark_live(oddify(group.items[i].coefficient));

		for (auto &op : graph.ops)
			if (live_values.count(op.res))
				plan.ops.push_back(op);
	}

	void propagate_widths(const McmGroup &group, McmPlan &plan)
	{
		for (int i : plan.active_items) {
			int odd = oddify(group.items[i].coefficient);
			int shift = shift_of(group.items[i].coefficient);
			int need = std::max(1, GetSize(group.items[i].cell->getPort(ID::Y)) - shift);
			plan.demand[odd] = std::max(plan.demand[odd], need);
		}
		for (auto it = plan.ops.rbegin(); it != plan.ops.rend(); ++it) {
			auto &op = *it;
			log_assert(plan.demand.count(op.res));
			int width = plan.demand.at(op.res) + op.norm;
			plan.raw_width[op.res] = width;
			plan.demand[op.u] = std::max(plan.demand[op.u], std::max(1, width - op.su));
			plan.demand[op.v] = std::max(plan.demand[op.v], std::max(1, width - op.sv));
		}
	}

	void estimate_cost(const McmGroup &group, McmPlan &plan)
	{
		for (auto &op : plan.ops)
			plan.shared_cost += plan.raw_width.at(op.res);
		for (int i : plan.active_items) {
			auto &item = group.items[i];
			int width = GetSize(item.cell->getPort(ID::Y));
			int multiply_width = std::max(1, width - shift_of(item.coefficient));
			plan.independent_cost +=
					(long long)std::max(0, naf_weight(item.coefficient) - 1) * multiply_width;
			if (item.coefficient < 0) {
				plan.shared_cost += width;
				plan.independent_cost += width;
			}
		}
	}

	bool is_profitable(const McmPlan &plan) const
	{
		if (config.force)
			return true;
		return plan.independent_cost != 0 &&
				(long double)plan.shared_cost * 100 <=
						(long double)plan.independent_cost * (100 - config.min_gain);
	}

	bool prepare_plan(const McmGroup &group, const AdderGraph &graph, McmPlan &plan)
	{
		if (!select_active_items(group, graph, plan))
			return false;
		prune_graph(group, graph, plan);
		propagate_widths(group, plan);
		estimate_cost(group, plan);
		if (is_profitable(plan))
			return true;
		log_debug("Skipping MCM group in module %s: estimated bit cost %lld vs %lld "
				"does not meet %d%% minimum gain.\n", log_id(module), plan.shared_cost,
				plan.independent_cost, config.min_gain);
		return false;
	}

	void emit_plan(McmGroup &group, const McmPlan &plan)
	{
		dict<int, SigSpec> nodes;
		log_assert(plan.demand.count(1));
		SigSpec input = group.input;
		input.extend_u0(plan.demand.at(1), group.is_signed);
		nodes.emplace(1, std::move(input));

		for (auto &op : plan.ops) {
			int width = plan.raw_width.at(op.res);
			SigSpec a = shl(nodes.at(op.u), op.su, width, group.is_signed);
			SigSpec b = shl(nodes.at(op.v), op.sv, width, group.is_signed);
			SigSpec y = module->addWire(NEW_ID, width);
			if (!op.sub)
				module->addAdd(NEW_ID, a, b, y, group.is_signed);
			else if (!op.swapped)
				module->addSub(NEW_ID, a, b, y, group.is_signed);
			else
				module->addSub(NEW_ID, b, a, y, group.is_signed);

			SigSpec normalized = y;
			if (op.norm > 0)
				normalized = y.extract(op.norm, width - op.norm);
			nodes.emplace(op.res, std::move(normalized));
		}
		n_adders += GetSize(plan.ops);

		for (int i : plan.active_items) {
			auto &item = group.items[i];
			int coefficient = item.coefficient;
			int odd = oddify(coefficient);
			int shift = shift_of(coefficient);
			log_assert(nodes.count(odd));
			SigSpec output = item.cell->getPort(ID::Y);
			SigSpec value = shl(nodes.at(odd), shift, GetSize(output), group.is_signed);
			if (coefficient < 0) {
				SigSpec negated = module->addWire(NEW_ID, GetSize(output));
				module->addNeg(NEW_ID, value, negated, group.is_signed);
				value = negated;
				n_adders++;
			}
			module->connect(output, value);
			module->remove(item.cell);
			n_muls++;
		}
	}

	void process_group(McmGroup &group)
	{
		std::vector<int> targets;
		for (auto &item : group.items)
			targets.push_back(item.coefficient);

		AdderGraphSolver solver(config.search);
		AdderGraphStatus status = solver.solve(targets);
		if (status != AdderGraphStatus::success) {
			if (status == AdderGraphStatus::budget_exhausted)
				log("  mcm: search budget of %lld exhausted for %d constant(s), skipping.\n",
						config.search.work_budget, GetSize(group.items));
			else
				log("  mcm: no adder graph within depth %d for %d constant(s), skipping.\n",
						config.search.max_depth, GetSize(group.items));
			return;
		}

		McmPlan plan;
		if (!prepare_plan(group, solver.graph, plan))
			return;
		emit_plan(group, plan);
		n_groups++;

		int negations = std::count_if(plan.active_items.begin(), plan.active_items.end(),
				[&](int i) { return group.items[i].coefficient < 0; });
		log("  mcm: %d constant multiplier(s) sharing one operand -> %d adder(s), depth %d, "
				"estimated bit cost %lld (independent %lld).\n", GetSize(plan.active_items),
				GetSize(plan.ops) + negations, plan.realized_depth, plan.shared_cost, plan.independent_cost);
	}

	void run()
	{
		auto groups = collect_groups();
		for (auto &entry : groups)
			process_group(entry.second);
	}
};

struct McmPass : public Pass {
	McmPass() : Pass("mcm", "replace constant multipliers with shared adder graphs") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    mcm [options] [selection]\n");
		log("\n");
		log("Replaces $mul cells having a constant operand with a shared graph of shifts,\n");
		log("additions and subtractions \n");
		log("\n");
		log("    -depth <n>\n");
		log("        maximum adder depth of the graph (default: 3). Lower bounds delay at\n");
		log("        the cost of possibly more adders.\n");
		log("\n");
		log("    -max_shift <n>\n");
		log("        largest shift considered in an A-operation (default: 12).\n");
		log("\n");
		log("    -min_const <n>\n");
		log("        skip constants whose magnitude is below <n> (default: 3).\n");
		log("\n");
		log("    -min_gain <percent>\n");
		log("        require this estimated one-bit-adder saving over independent\n");
		log("        signed-digit implementations (default: 0).\n");
		log("\n");
		log("    -search_budget <n>\n");
		log("        maximum number of uncached shift-pair evaluations per operand group\n");
		log("        (default: 2000000).\n");
		log("\n");
		log("    -force\n");
		log("        ignore the profitability check.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing MCM pass (constant-multiplication adder graphs).\n");

		McmConfig config;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-depth" && argidx + 1 < args.size()) {
				config.search.max_depth = atoi(args[++argidx].c_str());
				if (config.search.max_depth < 1)
					log_cmd_error("mcm: -depth must be >= 1\n");
				continue;
			}
			if (args[argidx] == "-max_shift" && argidx + 1 < args.size()) {
				config.search.max_shift = atoi(args[++argidx].c_str());
				if (config.search.max_shift < 1)
					log_cmd_error("mcm: -max_shift must be >= 1\n");
				continue;
			}
			if (args[argidx] == "-min_const" && argidx + 1 < args.size()) {
				config.min_const = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min_gain" && argidx + 1 < args.size()) {
				config.min_gain = atoi(args[++argidx].c_str());
				if (config.min_gain < 0 || config.min_gain > 100)
					log_cmd_error("mcm: -min_gain must be between 0 and 100\n");
				continue;
			}
			if (args[argidx] == "-search_budget" && argidx + 1 < args.size()) {
				config.search.work_budget = atoll(args[++argidx].c_str());
				if (config.search.work_budget < 1)
					log_cmd_error("mcm: -search_budget must be >= 1\n");
				continue;
			}
			if (args[argidx] == "-force") {
				config.force = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_groups = 0;
		int total_muls = 0;
		int total_adders = 0;
		for (auto module : design->selected_modules()) {
			if (module->get_blackbox_attribute())
				continue;
			McmWorker worker(module, config);
			worker.run();
			if (worker.n_muls)
				log("Module %s: replaced %d constant multiplier(s) in %d group(s) "
					"with %d adder(s).\n", log_id(module), worker.n_muls, worker.n_groups, worker.n_adders);
			total_groups += worker.n_groups;
			total_muls += worker.n_muls;
			total_adders += worker.n_adders;
		}
		if (total_muls)
			log("Replaced %d constant multiplier(s) in %d group(s) with %d adder(s).\n",
					total_muls, total_groups, total_adders);
		else
			log("No constant multipliers found to restructure.\n");
	}
} McmPass;

PRIVATE_NAMESPACE_END
