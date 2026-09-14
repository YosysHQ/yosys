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

struct McmSolver {
	int max_depth, max_shift, limit;
	long long search_budget, search_work;
	bool budget_exhausted;
	dict<int, int> depth;          // value -> depth
	std::vector<AOp> ops;
	dict<std::pair<int, int>, std::vector<AOp>> op_cache;

	McmSolver(int max_depth, int max_shift, long long search_budget)
		: max_depth(max_depth), max_shift(max_shift), limit(1), search_budget(search_budget), search_work(0),
		  budget_exhausted(false)
	{}

	static bool op_less(const AOp &a, const AOp &b)
	{
		return std::tie(a.u, a.su, a.v, a.sv, a.sub, a.swapped, a.norm) <
				std::tie(b.u, b.su, b.v, b.sv, b.sub, b.swapped, b.norm);
	}

	// Enumerate odd values reachable by one A-operation from u,v.
	const std::vector<AOp> &enumerate(int u, int v)
	{
		if (u > v)
			std::swap(u, v);
		auto key = std::make_pair(u, v);
		if (op_cache.count(key))
			return op_cache.at(key);

		auto &out = op_cache[key];
		dict<int, AOp> unique;
		long long bound = 4LL * limit;
		for (int su = 0; su <= max_shift; su++) {
			if (su >= 63 || (long long) u > (bound >> su))
				break;
			long long us = (long long)u << su;
			for (int sv = 0; sv <= max_shift; sv++) {
				if (sv >= 63 || (long long) v > (bound >> sv))
					break;
				if (search_work >= search_budget) {
					budget_exhausted = true;
					return out;
				}
				search_work++;
				long long vs = (long long)v << sv;
				long long cand[3] = { us + vs, us - vs, vs - us };
				bool issub[3] = { false, true, true };
				bool swp[3] = { false, false, true };
				for (int i = 0; i < 3; i++) {
					if (cand[i] <= 0 || cand[i] > bound || cand[i] > std::numeric_limits<int>::max())
						continue;
					AOp o;
					o.res = oddify((int)cand[i]);
					o.u = u; o.su = su; o.v = v; o.sv = sv;
					o.sub = issub[i]; o.swapped = swp[i];
					o.norm = shift_of((int)cand[i]);
					if (!unique.count(o.res) || op_less(o, unique.at(o.res)))
						unique[o.res] = o;
				}
			}
		}
		for (auto &it : unique)
			out.push_back(it.second);
		return out;
	}

	// Keep only the shallowest deterministic realization of each new value.
	bool all_ops(dict<int, std::pair<int, AOp>> &out)
	{
		for (auto &a : depth) {
			for (auto &b : depth) {
				if (a.first > b.first || 1 + std::max(a.second, b.second) > max_depth)
					continue;
				for (auto &o : enumerate(a.first, b.first)) {
					if (depth.count(o.res) || o.res == 1)
						continue;
					int d = 1 + std::max(a.second, b.second);
					if (!out.count(o.res) || d < out.at(o.res).first ||
							(d == out.at(o.res).first && op_less(o, out.at(o.res).second)))
						out[o.res] = std::make_pair(d, o);
				}
				if (budget_exhausted)
					return false;
			}
		}
		return true;
	}

	// Greedy Hcub-style construction. Returns false if no graph found.
	bool solve(const std::vector<int> &targets_in)
	{
		pool<int> targets;
		for (int t : targets_in) {
			int o = oddify(t);
			if (o > 1)
				targets.insert(o);
		}
		limit = 1;
		for (int t : targets)
			limit = std::max(limit, t);

		depth.clear(); ops.clear(); op_cache.clear();
		search_work = 0; budget_exhausted = false;
		depth[1] = 0;

		int guard = 0;
		while (true) {
			pool<int> remaining;
			for (int t : targets)
				if (!depth.count(t))
					remaining.insert(t);
			if (remaining.empty())
				break;
			if (++guard > 64)
				return false;

			dict<int, std::pair<int, AOp>> cand_map;
			if (!all_ops(cand_map))
				return false;

			// 1) take any target directly reachable, shallowest first
			bool progressed = false;
			int best = -1, best_d = -1; AOp best_op;
			for (auto &c : cand_map) {
				if (!remaining.count(c.first))
					continue;
				int d = c.second.first;
				if (best_d < 0 || d < best_d || (d == best_d && c.first < best)) {
					best = c.first; best_d = d; best_op = c.second.second; progressed = true;
				}
			}
			if (progressed) {
				depth[best] = best_d;
				ops.push_back(best_op);
				continue;
			}

			// otherwise add the intermediate unlocking the most targets
			if (cand_map.empty())
				return false;

			int pick = -1, pick_score = -1, pick_depth = 0; AOp pick_op;
			for (auto &c : cand_map) {
				int w = c.first, d = c.second.first;
				// how many remaining targets become reachable once w is present
				pool<int> unlocked;
				for (auto &a : depth) {
					if (1 + std::max(d, a.second) > max_depth)
						continue;
					for (auto &o : enumerate(w, a.first))
						if (remaining.count(o.res))
							unlocked.insert(o.res);
					if (budget_exhausted)
						return false;
				}
				if (1 + d <= max_depth) {
					for (auto &o : enumerate(w, w))
						if (remaining.count(o.res))
							unlocked.insert(o.res);
					if (budget_exhausted)
						return false;
				}
				int score = GetSize(unlocked);
				if (score > pick_score || (score == pick_score && (d < pick_depth ||
						(d == pick_depth && (pick < 0 || w < pick))))) {
					pick_score = score; pick = w; pick_depth = d; pick_op = c.second.second;
				}
			}
			if (pick < 0)
				return false;
			depth[pick] = pick_depth;
			ops.push_back(pick_op);
		}
		return true;
	}
};

struct McmWorker {
	Module *module;
	SigMap sigmap;
	int max_depth, max_shift, min_const, min_gain;
	long long search_budget;
	bool force;
	int n_groups = 0, n_muls = 0, n_adders = 0;

	McmWorker(Module *m, int d, int s, int mc, int mg, long long sb, bool f)
		: module(m), sigmap(m), max_depth(d), max_shift(s), min_const(mc), min_gain(mg), search_budget(sb), force(f) {}

	// sig << n, then widened/truncated to width w
	SigSpec shl(SigSpec sig, int n, int w, bool is_signed)
	{
		SigSpec r;
		if (n > 0)
			r.append(SigSpec(State::S0, n));
		r.append(sig);
		r.extend_u0(w, is_signed);
		return r;
	}

	void run()
	{
		// Group constant multiplies by their variable operand + signedness.
		struct Item { Cell *cell; int konst; };
		std::map<std::pair<std::string, bool>, std::vector<Item>> groups;
		std::map<std::pair<std::string, bool>, SigSpec> gsig;

		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($mul))
				continue;
			if (cell->has_keep_attr())
				continue;
			SigSpec A = sigmap(cell->getPort(ID::A));
			SigSpec B = sigmap(cell->getPort(ID::B));
			bool a_signed = cell->getParam(ID::A_SIGNED).as_bool();
			bool b_signed = cell->getParam(ID::B_SIGNED).as_bool();
			if (a_signed != b_signed)
				continue;

			SigSpec var; Const kc;
			if (B.is_fully_const() && !A.is_fully_const()) {
				var = A; kc = B.as_const();
			} else if (A.is_fully_const() && !B.is_fully_const()) {
				var = B; kc = A.as_const();
			} else
				continue;
			if (!kc.is_fully_def())
				continue;

			auto k_opt = kc.try_as_int(b_signed);
			if (!k_opt || *k_opt == std::numeric_limits<int>::min()) {
				log_debug("Skipping constant multiplier %s: coefficient %s is outside the supported range.\n",
						log_id(cell), log_const(kc));
				continue;
			}
			int k = *k_opt;
			int ak = k < 0 ? -k : k;
			if (ak == 0 || ak == 1)
				continue;                      
			if ((ak & (ak - 1)) == 0)
				continue;                       
			if (ak < min_const)
				continue;

			auto key = std::make_pair(log_signal(var), a_signed);
			groups[key].push_back(Item{cell, k});
			gsig[key] = var;
		}

		for (auto &g : groups) {
			auto &items = g.second;
			SigSpec var = gsig[g.first];
			bool is_signed = g.first.second;
			std::vector<int> targets;
			for (auto &it : items)
				targets.push_back(it.konst);

			McmSolver solver(max_depth, max_shift, search_budget);
			if (!solver.solve(targets)) {
				if (solver.budget_exhausted)
					log("  mcm: search budget of %lld exhausted for %d constant(s), skipping.\n",
							search_budget, GetSize(items));
				else
					log("  mcm: no adder graph within depth %d for %d constant(s), skipping.\n",
							max_depth, GetSize(items));
				continue;
			}

			std::vector<int> active_items;
			int realized_depth = 0;
			for (int i = 0; i < GetSize(items); i++) {
				int od = oddify(items[i].konst);
				int d = solver.depth.at(od) + (items[i].konst < 0 ? 1 : 0);
				if (d > max_depth) {
					log_debug("Skipping constant multiplier %s: output negation exceeds depth %d.\n",
							log_id(items[i].cell), max_depth);
					continue;
				}
				active_items.push_back(i);
				realized_depth = std::max(realized_depth, d);
			}
			if (active_items.empty())
				continue;

			dict<int, int> producer;
			for (int i = 0; i < GetSize(solver.ops); i++)
				producer[solver.ops[i].res] = i;
			pool<int> live_values;
			std::function<void(int)> mark_live = [&](int value) {
				if (value == 1 || live_values.count(value))
					return;
				live_values.insert(value);
				log_assert(producer.count(value));
				auto &o = solver.ops[producer.at(value)];
				mark_live(o.u);
				mark_live(o.v);
			};
			for (int i : active_items)
				mark_live(oddify(items[i].konst));
			std::vector<AOp> ops;
			for (auto &o : solver.ops)
				if (live_values.count(o.res))
					ops.push_back(o);

			// Determine demanded widths backwards.
			dict<int, int> demand, raw_width;
			for (int i : active_items) {
				int od = oddify(items[i].konst);
				int sh = shift_of(items[i].konst);
				int need = std::max(1, GetSize(items[i].cell->getPort(ID::Y)) - sh);
				demand[od] = std::max(demand[od], need);
			}
			for (auto it = ops.rbegin(); it != ops.rend(); ++it) {
				auto &o = *it;
				log_assert(demand.count(o.res));
				int width = demand.at(o.res) + o.norm;
				raw_width[o.res] = width;
				demand[o.u] = std::max(demand[o.u], std::max(1, width - o.su));
				demand[o.v] = std::max(demand[o.v], std::max(1, width - o.sv));
			}

			// Estimate hardware in one-bit adders.
			long long shared_cost = 0, independent_cost = 0;
			for (auto &o : ops)
				shared_cost += raw_width.at(o.res);
			for (int i : active_items) {
				auto &item = items[i];
				int width = GetSize(item.cell->getPort(ID::Y));
				int multiply_width = std::max(1, width - shift_of(item.konst));
				independent_cost += (long long)std::max(0, naf_weight(item.konst) - 1) * multiply_width;
				if (item.konst < 0) {
					shared_cost += width;
					independent_cost += width;
				}
			}
			if (!force && (independent_cost == 0 ||
					(long double)shared_cost * 100 > (long double)independent_cost * (100 - min_gain))) {
				log_debug("Skipping MCM group in module %s: estimated bit cost %lld vs %lld "
						"does not meet %d%% minimum gain.\n", log_id(module), shared_cost,
						independent_cost, min_gain);
				continue;
			}

			dict<int, SigSpec> node;
			log_assert(demand.count(1));
			SigSpec input = var;
			input.extend_u0(demand.at(1), is_signed);
			node.emplace(1, std::move(input));

			for (auto &o : ops) {
				int width = raw_width.at(o.res);
				SigSpec a = shl(node.at(o.u), o.su, width, is_signed);
				SigSpec b = shl(node.at(o.v), o.sv, width, is_signed);
				SigSpec y = module->addWire(NEW_ID, width);
				if (!o.sub)
					module->addAdd(NEW_ID, a, b, y, is_signed);
				else if (!o.swapped)
					module->addSub(NEW_ID, a, b, y, is_signed);
				else
					module->addSub(NEW_ID, b, a, y, is_signed);
				// value == res << norm, so res is y with the low bits dropped
				SigSpec r = y;
				if (o.norm > 0)
					r = y.extract(o.norm, width - o.norm);
				node.emplace(o.res, std::move(r));
			}
			n_adders += GetSize(ops);

			for (int i : active_items) {
				auto &it = items[i];
				int k = it.konst;
				int od = oddify(k), sh = shift_of(k);
				log_assert(node.count(od));
				SigSpec Y = it.cell->getPort(ID::Y);
				SigSpec v = shl(node.at(od), sh, GetSize(Y), is_signed);
				if (k < 0) {
					SigSpec nv = module->addWire(NEW_ID, GetSize(Y));
					module->addNeg(NEW_ID, v, nv, is_signed);
					v = nv;
					n_adders++;
				}
				module->connect(Y, v);
				module->remove(it.cell);
				n_muls++;
			}
			n_groups++;
			log("  mcm: %d constant multiplier(s) sharing one operand -> %d adder(s), depth %d, "
					"estimated bit cost %lld (independent %lld).\n", GetSize(active_items),
					GetSize(ops) + (int)std::count_if(active_items.begin(), active_items.end(),
							[&](int i) { return items[i].konst < 0; }), realized_depth,
					shared_cost, independent_cost);
		}
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
		log_header(design, "Executing MCM pass (multiple constant multiplication).\n");

		int max_depth = 3, max_shift = 12, min_const = 3, min_gain = 0;
		long long search_budget = 2000000;
		bool force = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-depth" && argidx + 1 < args.size()) {
				max_depth = atoi(args[++argidx].c_str());
				if (max_depth < 1)
					log_cmd_error("mcm: -depth must be >= 1\n");
				continue;
			}
			if (args[argidx] == "-max_shift" && argidx + 1 < args.size()) {
				max_shift = atoi(args[++argidx].c_str());
				if (max_shift < 1)
					log_cmd_error("mcm: -max_shift must be >= 1\n");
				continue;
			}
			if (args[argidx] == "-min_const" && argidx + 1 < args.size()) {
				min_const = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min_gain" && argidx + 1 < args.size()) {
				min_gain = atoi(args[++argidx].c_str());
				if (min_gain < 0 || min_gain > 100)
					log_cmd_error("mcm: -min_gain must be between 0 and 100\n");
				continue;
			}
			if (args[argidx] == "-search_budget" && argidx + 1 < args.size()) {
				search_budget = atoll(args[++argidx].c_str());
				if (search_budget < 1)
					log_cmd_error("mcm: -search_budget must be >= 1\n");
				continue;
			}
			if (args[argidx] == "-force") {
				force = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int tot_g = 0, tot_m = 0, tot_a = 0;
		for (auto module : design->selected_modules()) {
			if (module->get_blackbox_attribute())
				continue;
			McmWorker w(module, max_depth, max_shift, min_const, min_gain, search_budget, force);
			w.run();
			if (w.n_muls)
				log("Module %s: replaced %d constant multiplier(s) in %d group(s) "
					"with %d adder(s).\n", log_id(module), w.n_muls, w.n_groups, w.n_adders);
			tot_g += w.n_groups; tot_m += w.n_muls; tot_a += w.n_adders;
		}
		if (tot_m)
			log("Replaced %d constant multiplier(s) in %d group(s) with %d adder(s).\n",
					tot_m, tot_g, tot_a);
		else
			log("No constant multipliers found to restructure.\n");
	}
} McmPass;

PRIVATE_NAMESPACE_END
