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

bool HcubSearch::a_op_valid(const AOp &op) const {
	return op.res != 0 && shift_of(op.res) == 0 && bit_width(op.res) <= max_bit_width + 1;
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
		SearchResult result;
		result.status = AdderGraphStatus::BudgetExhausted;
		return result;
	}
}

SearchResult HcubSearch::run_search() {
	SearchResult result;
	bool distances_initialized = false;
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
			if (!distances_initialized) {
				c1 = keys(vertex_fundamental_set(1, 1));
				for (const auto &c : c1) {
					IntSet constants{1, c};
					unite(c2, keys(vertex_fundamental_set(constants, constants)));
				}
				c2.erase(1);
				for (const auto &c : c1)
					c2.erase(c);
				distances_initialized = true;
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
}

HcubSearch::ExactDistance HcubSearch::exact_dist(const UnsignedContainer &target) const {
	if (ready_set.count(target))
		return {0, {}};
	if (successor_set.count(target))
		return {1, {target}};

	const IntSet ready = keys(ready_set), successors = keys(successor_set);
	const IntSet inverse = inverse_set(ready, IntSet{target});
	const IntSet divided = quotients(IntSet{target}, c1);
	// Distance 2: t = c1*s or t = A(s, r).
	IntSet candidates = divided;
	unite(candidates, inverse);

	ExactDistance result;
	auto collect = [&](int distance) {
		for (const auto &s : candidates) {
			consume_work();
			if (successor_set.count(s) &&
				(distance == 2 ? finishes_in_one(ready, s, target) : finishes_in_two(s, target)))
				result.reducing_successors.insert(s);
		}
		if (!result.reducing_successors.empty())
			result.value = distance;
	};
	collect(2);
	if (result.value != -1)
		return result;

	// Distance 3: the five topologies in Figure 9(c).
	candidates = quotients(IntSet{target}, c2);
	unite(candidates, inverse_set(divided, ready));
	unite(candidates, quotients(inverse, c1));
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
	std::map<UnsignedContainer, ExactDistance> distances;
	for (const auto &target : target_set_remaining) {
		consume_work();
		auto exact = exact_dist(target);
		if (exact.value >= 0)
			distance_cache[target] = exact.value;
		distances.emplace(target, std::move(exact));
	}
	auto distance_after = [&](const UnsignedContainer &s, const UnsignedContainer &target) {
		const auto &exact = distances.at(target);
		if (exact.value >= 0)
			return exact.value - int(exact.reducing_successors.count(s));
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
	if (u == 0u || v == 0u || shift_of(u) != 0 || shift_of(v) != 0)
		log_error("MCM A-operation inputs must be positive odd constants.\n");
	auto small_u = u.get_uint64_t(), small_v = v.get_uint64_t();
	if (small_u && small_v)
		return enumerate_pair<uint64_t>(*small_u, *small_v, min_shift, max_shift);
	return enumerate_pair<BigUnsigned>(u.to_big_unsigned(), v.to_big_unsigned(), min_shift, max_shift);
}

template<typename Unsigned>
AOpMap HcubSearch::enumerate_pair(Unsigned u, Unsigned v, int min_shift, int max_shift) const {
	if (u == 0 || v == 0 || (u & 1) == 0 || (v & 1) == 0)
		log_error("MCM A-operation inputs must be positive odd constants.\n");

	AOpMap results;
	auto emit = [&](int su, int sv, bool sub) {
		consume_work();
		Unsigned lhs = u << su, rhs = v << sv;
		Unsigned raw = sub ? (lhs >= rhs ? lhs - rhs : rhs - lhs) : lhs + rhs;
		if (raw == 0)
			return;
		int norm = shift_of<Unsigned>(raw);
		AOp op{raw >> norm, u, v, AOpCfg{su, sv, norm, sub}};
		if (op.res != u && op.res != v && a_op_valid(op))
			results.emplace(op.res, op);
	};

	// A common input shift cancels during normalization.
	for (int shift = min_shift; shift <= max_shift; shift++) {
		emit(shift, 0, false);
		emit(shift, 0, true);
		if (shift) {
			emit(0, shift, false);
			emit(0, shift, true);
		}
	}
	return results;
}

IntSet HcubSearch::inverse_set(const IntSet &u, const IntSet &v) const {
	IntSet result;
	for (const auto &lhs : u)
		for (const auto &rhs : v) {
			unite(result, keys(enumerate_pair(lhs, rhs, 0, std::max(63, max_bit_width + 1))));
		}
	return result;
}

bool HcubSearch::finishes_in_one(const IntSet &ready, const UnsignedContainer &successor, const UnsignedContainer &target) const {
	if (vertex_fundamental_set(successor, successor).count(target))
		return true;
	for (const auto &r : ready)
		if (vertex_fundamental_set(successor, r).count(target))
			return true;
	return false;
}

bool HcubSearch::finishes_in_two(const UnsignedContainer &successor, const UnsignedContainer &target) const {
	IntSet available = keys(ready_set);
	available.insert(successor);
	IntSet next = keys(successor_set);
	unite(next, keys(vertex_fundamental_set(available, IntSet{successor})));
	for (const auto &r : available)
		next.erase(r);
	for (const auto &second : next)
		if (finishes_in_one(available, second, target))
			return true;
	return false;
}

} // namespace Yosys::Mcm::Hcub
