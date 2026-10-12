#include "mcm.h"
#include "hcub.h"

#include <algorithm>
#include <cmath>
#include <limits>

using namespace Yosys::Mcm;

namespace Yosys::Mcm::Hcub {

template<typename Map> IntSet keys(const Map &map)
{
	IntSet result;
	for (const auto &entry : map)
		result.insert(entry.first);
	return result;
}

void inline HcubSearch::consume_work() const
{
	if (work_remaining == 0)
		throw BudgetExhausted{};
	work_remaining--;
}

IntSet HcubSearch::quotients(const IntSet &values, const IntSet &divisors) const
{
	IntSet result;
	for (const auto &value : values)
		for (const auto &divisor : divisors) {
			consume_work();
			auto small_value = value.get_uint64_t(), small_divisor = divisor.get_uint64_t();
			if (small_value && small_divisor) {
				if (*small_value % *small_divisor == 0)
					result.insert(*small_value / *small_divisor);
			} else {
				BigUnsigned dividend = value.to_big_unsigned(), denominator = divisor.to_big_unsigned();
				if (dividend % denominator == 0)
					result.insert(dividend / denominator);
			}
		}
	return result;
}

void unite(IntSet &destination, const IntSet &source)
{
	destination.insert(source.begin(), source.end());
}

int auxiliary_cost(const IntSet &values)
{
	int cost = 128;
	for (const auto &value : values)
		cost = std::min(cost, naf_weight(value));
	return cost;
}

HcubSearch::HcubSearch(const SearchParams &params) : Search(params), config(params.config), work_remaining(config.work_budget) {
	std::vector<UnsignedContainer> odd_targets;
	odd_targets.reserve(params.target_set.size());
	for (const auto &target : params.target_set) {
		auto odd = oddify(target);
		if (odd != 0 && odd != 1)
			odd_targets.push_back(odd);
	}

	target_set_remaining = IntSet(odd_targets.begin(), odd_targets.end());
	ready_set.emplace(1, ONE);
	work_list.emplace(1, ONE);
	depths.emplace(1, 0);

	max_bit_width = Yosys::Mcm::max_bit_width(params.target_set);
	if (config.min_shift < 0 || config.max_shift < config.min_shift || config.max_nodes < 0 ||
			config.work_budget < 1 || (config.max_depth && *config.max_depth < 1))
		log_error("Invalid MCM search limits.\n");
	for (const auto &target : target_set_remaining)
		distance_cache[target] = max_bit_width + 3;
}

template<typename Unsigned>
inline bool HcubSearch::a_op_valid(const Unsigned &res) const {
	return is_odd<Unsigned>(res) && bit_width<Unsigned>(res) <= max_bit_width + 1;
}

inline bool HcubSearch::a_op_valid(const AOp &op) const {
	if (auto small = op.res.get_uint64_t())
		return a_op_valid<uint64_t>(*small);
	return a_op_valid<BigUnsigned>(op.res.get<BigUnsigned>());
}

// debug assert that all returned values here are oddified
AOpMap HcubSearch::vertex_fundamental_set(const UnsignedContainer &u, const UnsignedContainer &v) const {
	return enumerate_pair(u, v, config.min_shift, std::min(config.max_shift, max_bit_width + 1));
}

AOpMap HcubSearch::vertex_fundamental_set(const IntSet &u_set, const IntSet &v_set) const {
	AOpMap results{};
	std::set<std::pair<UnsignedContainer, UnsignedContainer>> seen{};
	for (const auto &u : u_set)
		for (const auto &v : v_set) {
			consume_work();
			std::pair<UnsignedContainer, UnsignedContainer> key;
			if (v < u) {
				key = std::pair(u, v);
			} else  {
				key = std::pair(v, u);
			}
			if (seen.contains(key)) continue;
			seen.insert(key);

			results.merge(vertex_fundamental_set(u, v));
		}
	for (const auto &u : u_set)
		results.erase(u);
	for (const auto &v : v_set)
		results.erase(v);
	return results;
}

AOpMap HcubSearch::vertex_fundamental_set(const AOpMap &u_set, const AOpMap &v_set) const {
	AOpMap results{};
	std::set<std::pair<UnsignedContainer, UnsignedContainer>> seen{};
	for (const auto &u : u_set)
		for (const auto  &v : v_set) {
			consume_work();
			if (config.max_depth && 1 + std::max(depths.at(u.first), depths.at(v.first)) > *config.max_depth)
				continue;
			std::pair<UnsignedContainer, UnsignedContainer> key;
			if (v.first < u.first) {
				key = std::pair(u.first, v.first);
			} else  {
				key = std::pair(v.first, u.first);
			}
			if (seen.contains(key)) continue;
			seen.insert(key);

			results.merge(vertex_fundamental_set(u.first, v.first));
		}
	for (const auto &u : u_set)
		results.erase(u.first);
	for (const auto &v : v_set)
		results.erase(v.first);
	return results;
}

SearchResult HcubSearch::search() {
	try {
		return run_search();
	} catch (const BudgetExhausted &) {
		result.status = AdderGraphStatus::BudgetExhausted;
		return result;
	}
}

SearchResult HcubSearch::run_search() {
	bool c1_initialized = false;
	for (const auto &entry : ready_set)
		result.add(entry.second);
	while (!target_set_remaining.empty() || !work_list.empty()) {
		consume_work();
		// optimal part
		while (!work_list.empty()) {
			consume_work();
			// update successor_set & ready_set
			AOpMap current_work = work_list;
			for (const auto &entry : current_work)
				result.add(entry.second);
			ready_set.merge(work_list);
			work_list.clear();
			if (target_set_remaining.empty())
				break;
			for (const auto &entry : vertex_fundamental_set(ready_set, current_work))
				if (!ready_set.count(entry.first))
					successor_set.emplace(entry);
			for (const auto &entry : ready_set)
				successor_set.erase(entry.first);

			// if successor_set contains remaining targets, add them
			for (const auto &target : IntSet(target_set_remaining)) {
				consume_work();
				auto successor = successor_set.find(target);
				if (successor != successor_set.end()) {
					if (ready_set.size() + work_list.size() - 1 >= size_t(config.max_nodes)) {
						result.status = AdderGraphStatus::NodeLimit;
						return result;
					}
					add_target(successor->second);
				}
			}
		}

		// heuristic part
		if (!target_set_remaining.empty()) {
			if (ready_set.size() - 1 >= size_t(config.max_nodes)) {
				result.status = AdderGraphStatus::NodeLimit;
				return result;
			}
			if (successor_set.empty())
				return result;
			if (!c1_initialized) {
				c1 = keys(vertex_fundamental_set(1, 1));
				c1_initialized = true;
			}
			AOp candidate;
			if (!heuristic(candidate))
				return result;
			add_target(candidate);
		}
	}
	result.status = AdderGraphStatus::Success;
	return result;
}

void HcubSearch::add_target(const AOp &target) {
	depths[target.res] = 1 + std::max(depths.at(target.u), depths.at(target.v));
	work_list.emplace(target.res, target);
	target_set_remaining.erase(target.res);
	completion_cache.erase(target.res);
}

HcubSearch::ExactDistance HcubSearch::exact_dist(const UnsignedContainer &target) {
	if (ready_set.count(target))
		return {0, {}};

	ExactDistance result;

	// Distance 1: Case 1: t = A(r1, r2), with r1, r2 ready.
	if (successor_set.count(target)) {
		record_completion(result, target, {{target, successor_set.at(target)}});
		return result;
	}

	auto cached = completion_cache.find(target);
	if (cached != completion_cache.end())
		for (const auto &entry : cached->second.completions)
			record_completion(result, target, entry.second);

	const IntSet ready = keys(ready_set);
	const IntSet successors = keys(successor_set);
	// Distance 2: Case 1: t = A(s, r), with r ready.
	const IntSet inverse = inverse_set(ready, IntSet{target});
	// Distance 2: Case 2: t = c1*s.
	const IntSet divided = quotients(IntSet{target}, c1);
	IntSet candidates = divided;
	unite(candidates, inverse);

	auto collect = [&](int distance) {
		for (const auto &s : candidates) {
			consume_work();
			// continue if the candidate is not in the successor set
			if (!successor_set.count(s))
				continue;
			// continue if the candidate is no better than an existing solution
			if (result.value == distance && result.completions.count(s))
				continue;
			// record the result using a graph that assumes s is ready
			record_completion(result, target, completion_after(s, target, distance, candidates));
		}
	};
	collect(2);
	if (result.value == 2)
		return result;

	// Distance 3: the five topologies in Figure 9(c).
	if (!c2_initialized) {
		for (const auto &c : c1) {
			IntSet constants{1, c};
			unite(c2, keys(vertex_fundamental_set(constants, constants)));
		}
		c2.erase(1);
		for (const auto &c : c1)
			c2.erase(c);
		c2_initialized = true;
	}
	// Distance 3: Cases 1, 2: t = c2*s.
	candidates = quotients(IntSet{target}, c2);
	// Distance 3: Case 3: t = c1*A(s, r), with r ready.
	unite(candidates, inverse_set(divided, ready));
	// Distance 3: Case 4: t = A(c1*s, r), with r ready.
	unite(candidates, quotients(inverse, c1));
	// Distance 3: Case 5: t = A(s1, s2), with s1, s2 successors.
	unite(candidates, inverse_set(successors, IntSet{target}));
	collect(3);
	return result;
}

int HcubSearch::estimate_after(const UnsignedContainer &successor, const UnsignedContainer &target, int previous) {
	auto key = std::make_pair(successor, target);
	auto found = estimate_cache.find(key);
	if (found == estimate_cache.end()) {
		// Figure 10, E1-E3: build the missing z, then finish in 1 or 2 ops.
		int estimate = 1 + auxiliary_cost(inverse_set(IntSet{successor}, IntSet{target}));
		estimate = std::min(estimate, 2 + auxiliary_cost(inverse_set(IntSet{successor}, quotients(IntSet{target}, c1))));
		IntSet scaled;
		for (const auto &c : c1) {
			consume_work();
			auto small_successor = successor.get_uint64_t(), small_c = c.get_uint64_t();
			UnsignedContainer value;
			if (small_successor && small_c && *small_successor <= UINT64_MAX / *small_c)
				value = *small_successor * *small_c;
			else
				value = successor.to_big_unsigned() * c.to_big_unsigned();
			if (a_op_valid(AOp{value, 0, 0, {0, 0, 0, false}}))
				scaled.insert(value);
		}
		estimate = std::min(estimate, 2 + auxiliary_cost(inverse_set(scaled, IntSet{target})));
		found = estimate_cache.emplace(key, estimate).first;
	}
	return std::min(previous, found->second); // Eq. 23: estimates cannot increase.
}

bool HcubSearch::heuristic(AOp &selected) {
	for (const auto &target : target_set_remaining) {
		consume_work();
		auto exact = exact_dist(target);
		if (exact.value >= 0)
			distance_cache[target] = exact.value;
		completion_cache[target] = std::move(exact);
	}
	auto distance_after = [&](const UnsignedContainer &s, const UnsignedContainer &target) {
		const auto &exact = completion_cache.at(target);
		if (exact.value >= 0)
			return exact.value - int(exact.completions.count(s));
		return estimate_after(s, target, distance_cache.at(target));
	};

	AOp best_succ;
	double best_score = 0.0;

	for (auto& s : successor_set) {
		double score = 0.0;
		for (auto& t : target_set_remaining) {
			consume_work();
			int after = distance_after(s.first, t);
			score += std::pow(10.0, -after) * (distance_cache.at(t) - after);
		}
		if (score > best_score) {
			best_score = score;
			best_succ = s.second;
		}
	}
	if (best_score == 0)
		return false;
	selected = best_succ;
	for (const auto &target : target_set_remaining)
		distance_cache[target] = distance_after(selected.res, target);
	return true;
}

AOpMap HcubSearch::enumerate_pair(const UnsignedContainer &u, const UnsignedContainer &v, int min_shift, int max_shift) const {
	AOpMap results;
	enumerate_pair(u, v, min_shift, max_shift, [&](const AOp &op) {
		results.emplace(op.res, op);
		return false;
	});
	return results;
}

template<typename Emit>
bool HcubSearch::enumerate_pair(const UnsignedContainer &u, const UnsignedContainer &v, int min_shift, int max_shift, Emit emit) const {
	if (u == 0u || v == 0u || shift_of(u) != 0 || shift_of(v) != 0)
		log_error("MCM A-operation inputs must be positive odd constants.\n");

	auto small_u = u.get_uint64_t(), small_v = v.get_uint64_t();
	if (small_u && small_v && max_shift < 64 &&
			*small_u <= ((UINT64_MAX - *small_v) >> max_shift) &&
			*small_v <= ((UINT64_MAX - *small_u) >> max_shift))
		return enumerate_pair<uint64_t>(*small_u, *small_v, min_shift, max_shift, emit);
	return enumerate_pair<BigUnsigned>(u.to_big_unsigned(), v.to_big_unsigned(), min_shift, max_shift, emit);
}

template<typename Unsigned, typename Emit>
bool HcubSearch::enumerate_pair(Unsigned u, Unsigned v, int min_shift, int max_shift, Emit emit) const {
	if (!is_odd<Unsigned>(u) || !is_odd<Unsigned>(v))
		log_error("MCM A-operation inputs must be positive odd constants.\n");

	auto visit = [&](int su, int sv, bool sub) {
		consume_work();
		Unsigned lhs = u << su, rhs = v << sv;
		Unsigned raw = sub ? (lhs >= rhs ? lhs - rhs : rhs - lhs) : lhs + rhs;
		if (raw == 0)
			return false;
		int norm = shift_of<Unsigned>(raw);
		Unsigned res = raw >> norm;
		if (res == u || res == v || !a_op_valid<Unsigned>(res))
			return false;
		return emit(AOp{res, u, v, AOpCfg{su, sv, norm, sub}});
	};

	// A common input shift cancels during normalization.
	for (int shift = min_shift; shift <= max_shift; shift++) {
		if (visit(shift, 0, false) || visit(shift, 0, true))
			return true;
		if (shift && (visit(0, shift, false) || visit(0, shift, true)))
			return true;
	}
	return false;
}

IntSet HcubSearch::inverse_set(const IntSet &u, const IntSet &v) const {
	IntSet result;
	for (const auto &lhs : u)
		for (const auto &rhs : v) {
			unite(result, keys(enumerate_pair(lhs, rhs, 0, max_bit_width + 1)));
		}
	return result;
}

std::optional<AOp> HcubSearch::find_operation(const UnsignedContainer &u, const UnsignedContainer &v,
		const UnsignedContainer &target) const {
	std::optional<AOp> result;
	enumerate_pair(u, v, config.min_shift, std::min(config.max_shift, max_bit_width + 1), [&](const AOp &op) {
		if (op.res != target)
			return false;
		result = op;
		return true;
	});
	return result;
}

std::optional<AOp> HcubSearch::finishing_operation(const std::map<UnsignedContainer, int> &available,
		const UnsignedContainer &successor, const UnsignedContainer &target) const {
	int depth = available.at(successor);
	if (!config.max_depth || depth + 1 <= *config.max_depth)
		if (auto op = find_operation(successor, successor, target))
			return op;
	for (const auto &entry : available) {
		consume_work();
		if (entry.first == successor)
			continue;
		if (config.max_depth && 1 + std::max(depth, entry.second) > *config.max_depth)
			continue;
		if (auto op = find_operation(successor, entry.first, target))
			return op;
	}
	return std::nullopt;
}

AOpMap HcubSearch::completion_after(const UnsignedContainer &successor, const UnsignedContainer &target,
		int distance, const IntSet &candidates) const {
	const AOp &first = successor_set.at(successor);
	std::map<UnsignedContainer, int> available = depths;
	available[successor] = 1 + std::max(depths.at(first.u), depths.at(first.v));
	if (distance == 2) {
		if (auto last = finishing_operation(available, successor, target))
			return {{successor, first}, {target, *last}};
		return {};
	}

	// looks for 3 op solutions
	IntSet seconds = candidates;
	unite(seconds, inverse_set(IntSet{successor}, IntSet{target}));
	for (const auto &second : seconds) {
		consume_work();
		if (available.count(second))
			continue;
		std::optional<AOp> middle;
		int middle_depth = std::numeric_limits<int>::max();
		auto found = successor_set.find(second);
		// check if able to reuse an op from the 2 op set to create 3 op solution
		if (found != successor_set.end()) {
			middle = found->second;
			middle_depth = 1 + std::max(depths.at(middle->u), depths.at(middle->v));
		}

		// try to construct new 3 op solution
		for (const auto &entry : available) {
			int depth = 1 + std::max(available.at(successor), entry.second);
			if (depth >= middle_depth || (config.max_depth && depth > *config.max_depth))
				continue;
			if (auto op = find_operation(successor, entry.first, second)) {
				middle = op;
				middle_depth = depth;
			}
		}
		if (!middle || (config.max_depth && middle_depth > *config.max_depth))
			continue;
		available[second] = middle_depth;
		auto last = finishing_operation(available, second, target);
		available.erase(second);
		if (last)
			return {{successor, first}, {second, *middle}, {target, *last}};
	}
	return {};
}

bool HcubSearch::prune_completion(const UnsignedContainer &target, AOpMap &graph) const {
	std::map<UnsignedContainer, int> known_depths = depths;
	AOpMap live;
	IntSet visiting;
	auto visit = [&](auto &&self, const UnsignedContainer &value) -> std::optional<int> {
		consume_work();
		if (auto found = known_depths.find(value); found != known_depths.end())
			return found->second;
		auto found = graph.find(value);
		if (found == graph.end() || !visiting.insert(value).second)
			return std::nullopt;
		const auto &op = found->second;
		auto u = self(self, op.u), v = self(self, op.v);
		if (!u || !v)
			return std::nullopt;
		int depth = 1 + std::max(*u, *v);
		if (config.max_depth && depth > *config.max_depth)
			return std::nullopt;
		visiting.erase(value);
		known_depths[value] = depth;
		live.emplace(value, op);
		return depth;
	};
	if (!visit(visit, target))
		return false;
	graph = std::move(live);
	return true;
}

void HcubSearch::record_completion(ExactDistance &distance, const UnsignedContainer &target, AOpMap graph) const {
	if (graph.empty() || !prune_completion(target, graph))
		return;
	int cost = int(graph.size());
	if (cost == 0 || cost > 3 || (distance.value >= 0 && cost > distance.value))
		return;
	for (const auto &entry : graph) {
		auto first = successor_set.find(entry.first);
		if (first == successor_set.end() || !ready_set.count(entry.second.u) || !ready_set.count(entry.second.v))
			continue;
		AOpMap completion = graph;
		completion[entry.first] = first->second;
		if (!prune_completion(target, completion))
			continue;
		if (distance.value < 0 || cost < distance.value) {
			distance.value = cost;
			distance.completions.clear();
		}
		distance.completions.emplace(entry.first, std::move(completion));
	}
}

} // namespace Yosys::Mcm::Hcub
