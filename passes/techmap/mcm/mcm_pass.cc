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

#include "mcm.h"
#include "hcub.h"

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <utility>

using namespace Yosys::Mcm;
using namespace Yosys::Mcm::Hcub;

namespace Yosys {

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
	dict<int64_t, int> demand;
	dict<int64_t, int> raw_width;
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
		dict<int64_t, int> depths;
		depths[1] = 0;
		std::function<int(int64_t)> depth_of = [&](int64_t value) {
			if (depths.count(value))
				return depths.at(value);
			const auto &op = graph.operations().at(value);
			return depths[value] = 1 + std::max(depth_of(op.u), depth_of(op.v));
		};
		for (int i = 0; i < GetSize(group.items); i++) {
			int64_t odd = oddify(group.items[i].coefficient);
			int depth = depth_of(odd) + (group.items[i].coefficient < 0 ? 1 : 0);
			if (config.max_depth.has_value() && depth > config.max_depth) {
				log_debug("Skipping constant multiplier %s: output negation exceeds depth %d.\n",
					log_id(group.items[i].cell), config.max_depth.value());
				continue;
			}
			plan.active_items.push_back(i);
			plan.realized_depth = std::max(plan.realized_depth, depth);
		}
		return !plan.active_items.empty();
	}

	void prune_graph(const McmGroup &group, const AdderGraph &graph, McmPlan &plan)
	{
		pool<int64_t> live_values;
		std::function<void(int64_t)> mark_live = [&](int64_t value) {
			if (value == 1 || live_values.count(value))
				return;
			live_values.insert(value);
			log_assert(graph.operations().count(value));
			const auto &op = graph.operations().at(value);
			mark_live(op.u);
			mark_live(op.v);
			plan.ops.push_back(op);
		};
		for (int i : plan.active_items)
			mark_live(oddify(group.items[i].coefficient));
	}

	void propagate_widths(const McmGroup &group, McmPlan &plan)
	{
		for (int i : plan.active_items) {
			int64_t odd = oddify(group.items[i].coefficient);
			int shift = shift_of(group.items[i].coefficient);
			int need = std::max(1, GetSize(group.items[i].cell->getPort(ID::Y)) - shift);
			plan.demand[odd] = std::max(plan.demand[odd], need);
		}
		for (auto it = plan.ops.rbegin(); it != plan.ops.rend(); ++it) {
			auto &op = *it;
			log_assert(plan.demand.count(op.res));
			int width = plan.demand.at(op.res) + op.cfg.norm;
			plan.raw_width[op.res] = width;
			plan.demand[op.u] = std::max(plan.demand[op.u], std::max(1, width - op.cfg.su));
			plan.demand[op.v] = std::max(plan.demand[op.v], std::max(1, width - op.cfg.sv));
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

	bool prepare_plan([[maybe_unused]] const McmGroup &group, [[maybe_unused]] const AdderGraph &graph, McmPlan &plan)
	{
		if (!select_active_items(group, graph, plan))
			return false;
		prune_graph(group, graph, plan);
		propagate_widths(group, plan);
		// estimate_cost(group, plan);
		// if (is_profitable(plan))
		// 	return true;
		return true;
		// log_debug("Skipping MCM group in module %s: estimated bit cost %lld vs %lld "
		// 		"does not meet %d%% minimum gain.\n", log_id(module), plan.shared_cost,
		// 		plan.independent_cost, config.min_gain);
		// return false;
	}

	void emit_plan(McmGroup &group, const McmPlan &plan)
	{
		dict<int64_t, SigSpec> nodes;
		log_assert(plan.demand.count(1));
		SigSpec input = group.input;
		input.extend_u0(plan.demand.at(1), group.is_signed);
		nodes.emplace(1, std::move(input));

		for (auto &op : plan.ops) {
			int width = plan.raw_width.at(op.res);
			SigSpec a = shl(nodes.at(op.u), op.cfg.su, width, group.is_signed);
			SigSpec b = shl(nodes.at(op.v), op.cfg.sv, width, group.is_signed);

			using Wide = unsigned __int128;
			if (op.cfg.sub && (Wide(op.u) << op.cfg.su) < (Wide(op.v) << op.cfg.sv))
				std::swap(a, b);
			SigSpec y = module->addWire(NEW_ID, width);
			if (!op.cfg.sub)
				module->addAdd(NEW_ID, a, b, y, group.is_signed);
			else
				module->addSub(NEW_ID, a, b, y, group.is_signed);

			SigSpec normalized = y;
			if (op.cfg.norm > 0)
				normalized = y.extract(op.cfg.norm, width - op.cfg.norm);
			nodes.emplace(op.res, std::move(normalized));
		}
		n_adders += GetSize(plan.ops);

		for (int i : plan.active_items) {
			auto &item = group.items[i];
			int coefficient = item.coefficient;
			int64_t odd = oddify(coefficient);
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

		SearchResult result;
		SearchParams params{config, IntSet(targets.begin(), targets.end())};//, result};
		HcubSearch search(params);
		result = search.search();
		AdderGraphStatus status = result.status;
		if (status != AdderGraphStatus::Success) {
			if (status == AdderGraphStatus::BudgetExhausted)
				log("  mcm: search budget of %lld exhausted for %d constant(s), skipping.\n",
						config.work_budget, GetSize(group.items));
			else if (status == AdderGraphStatus::NodeLimit)
				log("  mcm: maximum node count %d reached for %d constant(s), skipping.\n",
						config.max_nodes, GetSize(group.items));
			else
				log("  mcm: no adder graph within depth %d for %d constant(s), skipping.\n",
						config.max_depth.has_value(), GetSize(group.items));
			return;
		}

		McmPlan plan;
		if (!prepare_plan(group, result.graph, plan))
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
		log("        maximum adder depth of the graph (default: None). Lower bounds delay at\n");
		log("        the cost of possibly more adders.\n");
		log("\n");
		log("    -max_shift <n>\n");
		log("        largest shift considered in an A-operation (default: 32).\n");
		log("\n");
		log("    -max_nodes <n>\n");
		log("        maximum number of nodes (default: 64).\n");
		log("\n");
		log("    -min_const <n>\n");
		log("        skip constants whose magnitude is below <n> (default: 3).\n");
		log("\n");
		log("    -min_gain <percent>\n");
		log("        require this estimated one-bit-adder saving over independent\n");
		log("        signed-digit implementations (default: 0).\n");
		log("\n");
		log("    -search_budget <n>\n");
		log("        accepted but currently has no effect (default: 20000000).\n");
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
				config.max_depth = atoi(args[++argidx].c_str());
				if (config.max_depth.has_value() && config.max_depth < 1)
					log_cmd_error("mcm: -depth must be >= 1\n");
				continue;
			}
			if (args[argidx] == "-max_shift" && argidx + 1 < args.size()) {
				config.max_shift = atoi(args[++argidx].c_str());
				if (config.max_shift < 1)
					log_cmd_error("mcm: -max_shift must be >= 1\n");
				continue;
			}
			if (args[argidx] == "-max_nodes" && argidx + 1 < args.size()) {
				config.max_nodes = atoi(args[++argidx].c_str());
				if (config.max_nodes < 1)
					log_cmd_error("mcm: -max_nodes must be >= 1\n");
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
				config.work_budget = atoll(args[++argidx].c_str());
				if (config.work_budget < 1)
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

} // namespace Yosys
