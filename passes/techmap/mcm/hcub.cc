#include "mcm.h"
#include "hcub.h"

#include <algorithm>
#include <cmath>

using namespace Yosys::Mcm;

namespace Yosys::Mcm::Hcub {

template<typename Map> IntSet keys(const Map &map)
{
	IntSet result;
	for (auto &entry : map)
		result.insert(entry.first);
	return result;
}

void inline HcubSearch::consume_work() const
{
	if (work_remaining == 0)
		throw BudgetExhausted{};
	work_remaining--;
}

std::optional<UnsignedContainer> HcubSearch::quotient(const UnsignedContainer &value, const UnsignedContainer &divisor) const
{
	consume_work();
	std::optional<uint64_t> small_value = value.get_uint64_t(), small_divisor = divisor.get_uint64_t();
	if (small_value && small_divisor) {
		if (*small_value % *small_divisor == 0)
			return UnsignedContainer(*small_value / *small_divisor);
	} else {
		BigUnsigned dividend = value.to_big_unsigned(), denominator = divisor.to_big_unsigned();
		if (dividend % denominator == 0)
			return UnsignedContainer(dividend / denominator);
	}
	return std::nullopt;
}

IntSet HcubSearch::quotients(const IntSet &values, const AOpMap &divisors) const
{
	IntSet result;
	for (const UnsignedContainer &value : values)
		for (const std::pair<const UnsignedContainer, AOp> &entry : divisors) {
			std::optional<UnsignedContainer> divided = quotient(value, entry.first);
			if (divided)
				result.insert(*divided);
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
	for (const UnsignedContainer &value : values)
		cost = std::min(cost, naf_weight(value));
	return cost;
}

HcubSearch::HcubSearch(const SearchParams &params) : Search(params), config(params.config), work_remaining(config.work_budget) {
	std::vector<UnsignedContainer> odd_targets;
	odd_targets.reserve(params.target_set.size());
	for (const UnsignedContainer &target : params.target_set) {
		UnsignedContainer odd = oddify(target);
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
	for (const UnsignedContainer &target : target_set_remaining)
		distance_cache[target] = max_bit_width + 3;
}

template<typename Unsigned>
inline bool HcubSearch::a_op_valid(const Unsigned &res) const {
	return is_odd<Unsigned>(res) && bit_width<Unsigned>(res) <= max_bit_width + 1;
}

inline bool HcubSearch::a_op_valid(const AOp &op) const {
	if (std::optional<uint64_t> small = op.res.get_uint64_t())
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
	for (const UnsignedContainer &u : u_set)
		for (const UnsignedContainer &v : v_set) {
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
	for (const UnsignedContainer &u : u_set)
		results.erase(u);
	for (const UnsignedContainer &v : v_set)
		results.erase(v);
	return results;
}

AOpMap HcubSearch::vertex_fundamental_set(const AOpMap &u_set, const AOpMap &v_set) const {
	AOpMap results{};
	std::set<std::pair<UnsignedContainer, UnsignedContainer>> seen{};
	for (const std::pair<const UnsignedContainer, AOp> &u : u_set)
		for (const std::pair<const UnsignedContainer, AOp> &v : v_set) {
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
	for (const std::pair<const UnsignedContainer, AOp> &u : u_set)
		results.erase(u.first);
	for (const std::pair<const UnsignedContainer, AOp> &v : v_set)
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
	for (const std::pair<const UnsignedContainer, AOp> &entry : ready_set)
		result.add(entry.second);
	while (!target_set_remaining.empty() || !work_list.empty()) {
		consume_work();
		// optimal part
		while (!work_list.empty()) {
			consume_work();
			// update successor_set & ready_set
			AOpMap current_work = work_list;
			for (const std::pair<const UnsignedContainer, AOp> &entry : current_work)
				result.add(entry.second);
			ready_set.merge(work_list);
			work_list.clear();
			if (target_set_remaining.empty())
				break;
			for (const std::pair<const UnsignedContainer, AOp> &entry : vertex_fundamental_set(ready_set, current_work))
				if (!ready_set.count(entry.first))
					successor_set.emplace(entry);
			for (const std::pair<const UnsignedContainer, AOp> &entry : ready_set)
				successor_set.erase(entry.first);

			// if successor_set contains remaining targets, add them
			for (const UnsignedContainer &target : IntSet(target_set_remaining)) {
				consume_work();
				AOpMap::const_iterator successor = successor_set.find(target);
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
				c1 = vertex_fundamental_set(1, 1);
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

	std::map<UnsignedContainer, ExactDistance>::const_iterator cached = completion_cache.find(target);
	if (cached != completion_cache.end())
		for (const std::pair<const UnsignedContainer, AOpMap> &entry : cached->second.completions)
			record_completion(result, target, entry.second);

	auto known_completion = [&](const UnsignedContainer &s, int distance) {
		return result.value == distance && result.completions.count(s);
	};

	// Distance 2: Case 1: t = A(s, r).
	std::vector<AOp> inverse;
	for (const std::pair<const UnsignedContainer, AOp> &r : ready_set) {
		for (const AOp &last : predecessors(r.first, target)) {
			inverse.push_back(last);
			AOpMap::const_iterator first = successor_set.find(last.u);
			if (first != successor_set.end() && !known_completion(last.u, 2))
				record_completion(result, target, {{last.u, first->second}, {target, last}});
		}
	}

	// Distance 2: Case 2: t = c1*s.
	std::vector<AOp> divided;
	for (const std::pair<const UnsignedContainer, AOp> &c : c1) {
		std::optional<UnsignedContainer> s = quotient(target, c.first);
		if (!s)
			continue;
		std::optional<AOp> last = scale_operation(c.second, *s);
		if (!last)
			continue;
		divided.push_back(*last);
		AOpMap::const_iterator first = successor_set.find(*s);
		if (first != successor_set.end() && !known_completion(*s, 2))
			record_completion(result, target, {{*s, first->second}, {target, *last}});
	}
	if (result.value == 2)
		return result;

	// Distance 3: Cases 1, 2: t = c2*s.
	if (!c2_initialized)
		initialize_c2();
	for (const std::pair<const UnsignedContainer, std::vector<AOpMap>> &c : c2) {
		std::optional<UnsignedContainer> s = quotient(target, c.first);
		if (!s)
			continue;
		AOpMap::const_iterator first = successor_set.find(*s);
		if (first == successor_set.end() || known_completion(*s, 3))
			continue;
		for (const AOpMap &entry : c.second) {
			AOpMap graph = scale_template(entry, *s);
			if (graph.empty())
				continue;
			graph.emplace(*s, first->second);
			record_completion(result, target, std::move(graph));
			if (result.completions.count(*s))
				break;
		}
	}

	// Distance 3: Case 3: t = c1*A(s, r).
	for (const AOp &last : divided) {
		for (const std::pair<const UnsignedContainer, AOp> &r : ready_set) {
			for (const AOp &middle : predecessors(r.first, last.u, &successor_set)) {
				AOpMap::const_iterator first = successor_set.find(middle.u);
				if (!known_completion(middle.u, 3))
					record_completion(result, target,
						{{middle.u, first->second}, {middle.res, middle}, {target, last}});
			}
		}
	}

	// Distance 3: Case 4: t = A(c1*s, r).
	for (const AOp &last : inverse) {
		for (const std::pair<const UnsignedContainer, AOp> &c : c1) {
			std::optional<UnsignedContainer> s = quotient(last.u, c.first);
			if (!s)
				continue;
			AOpMap::const_iterator first = successor_set.find(*s);
			if (first == successor_set.end() || known_completion(*s, 3))
				continue;
			if (std::optional<AOp> middle = scale_operation(c.second, *s))
				record_completion(result, target,
						{{*s, first->second}, {middle->res, *middle}, {target, last}});
		}
	}

	// Distance 3: Case 4, unfactored form: t = A(s, A(s, r)).
	std::vector<AOp> successor_inverse;
	for (const std::pair<const UnsignedContainer, AOp> &first : successor_set) {
		for (const AOp &last : predecessors(first.first, target)) {
			successor_inverse.push_back(last);
			if (known_completion(first.first, 3))
				continue;
			for (const AOp &middle : predecessors(first.first, last.u, &ready_set))
				record_completion(result, target,
						{{first.first, first.second}, {middle.res, middle}, {target, last}});
		}
	}

	// Distance 3: Case 5: t = A(s1, s2), with s1, s2 successors.
	for (const AOp &last : successor_inverse) {
		AOpMap::const_iterator first = successor_set.find(last.u);
		if (first != successor_set.end() &&
				(!known_completion(last.u, 3) || !known_completion(last.v, 3)))
			record_completion(result, target,
					{{last.u, first->second}, {last.v, successor_set.at(last.v)}, {target, last}});
	}
	// Distance 3: Case 5, chained form: t = A(A(s, r1), r2).
	for (const AOp &last : inverse) {
		for (const std::pair<const UnsignedContainer, AOp> &r : ready_set) {
			for (const AOp &middle : predecessors(r.first, last.u, &successor_set)) {
				AOpMap::const_iterator first = successor_set.find(middle.u);
				if (!known_completion(middle.u, 3))
					record_completion(result, target,
							{{middle.u, first->second}, {middle.res, middle}, {target, last}});
			}
		}
	}
	return result;
}

int HcubSearch::estimate_after(const UnsignedContainer &successor, const UnsignedContainer &target, int previous) {
	std::pair<UnsignedContainer, UnsignedContainer> key = std::make_pair(successor, target);
	std::map<std::pair<UnsignedContainer, UnsignedContainer>, int>::const_iterator found = estimate_cache.find(key);
	if (found == estimate_cache.end()) {
		// Figure 10, E1-E3: build the missing z, then finish in 1 or 2 ops.
		int estimate = 1 + auxiliary_cost(inverse_set(IntSet{successor}, IntSet{target}));
		estimate = std::min(estimate, 2 + auxiliary_cost(inverse_set(IntSet{successor}, quotients(IntSet{target}, c1))));
		IntSet scaled;
		for (const std::pair<const UnsignedContainer, AOp> &entry : c1) {
			const UnsignedContainer &c = entry.first;
			consume_work();
			std::optional<uint64_t> small_successor = successor.get_uint64_t(), small_c = c.get_uint64_t();
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
	for (const UnsignedContainer &target : target_set_remaining) {
		consume_work();
		ExactDistance exact = exact_dist(target);
		if (exact.value >= 0)
			distance_cache[target] = exact.value;
		completion_cache[target] = std::move(exact);
	}
	auto distance_after = [&](const UnsignedContainer &s, const UnsignedContainer &target) {
		const ExactDistance &exact = completion_cache.at(target);
		if (exact.value >= 0)
			return exact.value - int(exact.completions.count(s));
		return estimate_after(s, target, distance_cache.at(target));
	};

	AOp best_succ;
	double best_score = 0.0;

	for (std::pair<const UnsignedContainer, AOp> &s : successor_set) {
		double score = 0.0;
		for (const UnsignedContainer &t : target_set_remaining) {
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
	for (const UnsignedContainer &target : target_set_remaining)
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

	std::optional<uint64_t> small_u = u.get_uint64_t(), small_v = v.get_uint64_t();
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
	for (const UnsignedContainer &lhs : u)
		for (const UnsignedContainer &rhs : v) {
			unite(result, keys(enumerate_pair(lhs, rhs, 0, max_bit_width + 1)));
		}
	return result;
}

// Forward operations producing target: u is missing, v is input.
std::vector<AOp> HcubSearch::predecessors(const UnsignedContainer &input, const UnsignedContainer &target,
		const AOpMap *allowed) const {
	std::vector<AOp> result;
	if (input == target)
		return result;
	IntSet seen;
	enumerate_pair(input, target, 0, max_bit_width + 1, [&](const AOp &inverse) {
		if (allowed && !allowed->count(inverse.res))
			return false;
		// inverse.res*2^norm = |input*2^su +/- target*2^sv|.
		// then solve for target
		AOpCfg cfg{inverse.cfg.norm, inverse.cfg.su, inverse.cfg.sv, true};
		if (inverse.cfg.sub) {
			std::optional<uint64_t> small_input = input.get_uint64_t(), small_target = target.get_uint64_t();
			if (small_input && small_target && inverse.cfg.su < 64 && inverse.cfg.sv < 64 &&
					*small_input <= (UINT64_MAX >> inverse.cfg.su) &&
					*small_target <= (UINT64_MAX >> inverse.cfg.sv))
				cfg.sub = (*small_input << inverse.cfg.su) >= (*small_target << inverse.cfg.sv);
			else
				cfg.sub = (input.to_big_unsigned() << inverse.cfg.su) >= (target.to_big_unsigned() << inverse.cfg.sv);
		}
		int common_shift = std::min(cfg.su, cfg.sv);
		cfg.su -= common_shift;
		cfg.sv -= common_shift;
		cfg.norm -= common_shift;
		int shift = std::max(cfg.su, cfg.sv);
		if (cfg.norm < 0 || shift < config.min_shift || shift > std::min(config.max_shift, max_bit_width + 1))
			return false;
		if (seen.insert(inverse.res).second)
			result.push_back(AOp{target, inverse.res, input, cfg});
		return false;
	});
	return result;
}

std::optional<AOp> HcubSearch::scale_operation(const AOp &op, const UnsignedContainer &scale) const {
	consume_work();
	auto multiply = [&](const UnsignedContainer &value) -> UnsignedContainer {
		std::optional<uint64_t> small_value = value.get_uint64_t(), small_scale = scale.get_uint64_t();
		if (small_value && small_scale && *small_value <= UINT64_MAX / *small_scale)
			return *small_value * *small_scale;
		return value.to_big_unsigned() * scale.to_big_unsigned();
	};
	AOp scaled{multiply(op.res), multiply(op.u), multiply(op.v), op.cfg};
	if (!a_op_valid(scaled))
		return std::nullopt;
	return scaled;
}

AOpMap HcubSearch::scale_template(const AOpMap &graph, const UnsignedContainer &scale) const {
	AOpMap result;
	for (const std::pair<const UnsignedContainer, AOp> &entry : graph) {
		std::optional<AOp> op = scale_operation(entry.second, scale);
		if (!op)
			return {};
		result.emplace(op->res, *op);
	}
	return result;
}

void HcubSearch::initialize_c2() {
	for (const std::pair<const UnsignedContainer, AOp> &first : c1) {
		IntSet inputs{1, first.first};
		for (const std::pair<const UnsignedContainer, AOp> &second : vertex_fundamental_set(inputs, inputs)) {
			if (second.first == 1 || c1.count(second.first))
				continue;
			c2[second.first].push_back({{first.first, first.second}, {second.first, second.second}});
		}
	}
	c2_initialized = true;
}

bool HcubSearch::prune_completion(const UnsignedContainer &target, AOpMap &graph) const {
	std::map<UnsignedContainer, int> known_depths = depths;
	AOpMap live;
	IntSet visiting;
	auto visit = [&](auto &&self, const UnsignedContainer &value) -> std::optional<int> {
		consume_work();
		if (std::map<UnsignedContainer, int>::const_iterator found = known_depths.find(value); found != known_depths.end())
			return found->second;
		AOpMap::const_iterator found = graph.find(value);
		if (found == graph.end() || !visiting.insert(value).second)
			return std::nullopt;
		const AOp &op = found->second;
		std::optional<int> u = self(self, op.u), v = self(self, op.v);
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
	for (const std::pair<const UnsignedContainer, AOp> &entry : graph) {
		AOpMap::const_iterator first = successor_set.find(entry.first);
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
