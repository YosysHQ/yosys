#ifndef YOSYS_HCUB_H
#define YOSYS_HCUB_H

#include "mcm.h"

namespace Yosys::Mcm::Hcub {

class HcubSearch : public Search {
public:
	explicit HcubSearch(const SearchParams &params);

	bool a_op_valid(const AOp &op) const override;
	AOpMap vertex_fundamental_set(const UnsignedContainer &u, const UnsignedContainer &v) const;
	AOpMap vertex_fundamental_set(const IntSet &u, const IntSet &v) const override;
	AOpMap vertex_fundamental_set(const AOpMap &u, const AOpMap &v) const;
	SearchResult search() override;

private:
	struct BudgetExhausted {};
	void consume_work() const;
	template<typename Unsigned> bool a_op_valid(const Unsigned &res) const;
	SearchResult run_search();
	IntSet quotients(const IntSet &values, const IntSet &divisors) const;
	struct ExactDistance {
		int value = -1; // No distance <= 3 found.
		std::map<UnsignedContainer, AOpMap> completions;
	};

	void add_target(const AOp &target);
	bool heuristic(AOp &selected);
	ExactDistance exact_dist(const UnsignedContainer &target);
	int estimate_after(const UnsignedContainer &successor, const UnsignedContainer &target, int previous);
	std::optional<AOp> find_operation(const UnsignedContainer &u, const UnsignedContainer &v, const UnsignedContainer &target) const;
	std::optional<AOp> finishing_operation(const std::map<UnsignedContainer, int> &available,
			const UnsignedContainer &successor, const UnsignedContainer &target) const;
	AOpMap completion_after(const UnsignedContainer &successor, const UnsignedContainer &target,
			int distance, const IntSet &finish_candidates) const;
	bool prune_completion(const UnsignedContainer &target, AOpMap &graph) const;
	void record_completion(ExactDistance &distance, const UnsignedContainer &target, AOpMap graph) const;
	AOpMap enumerate_pair(const UnsignedContainer &u, const UnsignedContainer &v, int min_shift, int max_shift) const;
	template<typename Emit> bool enumerate_pair(const UnsignedContainer &u, const UnsignedContainer &v,
			int min_shift, int max_shift, Emit emit) const;
	template<typename Unsigned, typename Emit> bool enumerate_pair(Unsigned u, Unsigned v,
			int min_shift, int max_shift, Emit emit) const;
	IntSet inverse_set(const IntSet &u, const IntSet &v) const;

	McmConfig config;
	mutable long long work_remaining;
	std::map<UnsignedContainer, int> depths;
	IntSet target_set_remaining;
	AOpMap ready_set;
	AOpMap work_list;
	AOpMap successor_set;
	IntSet c1, c2;
	bool c2_initialized = false;
	std::map<UnsignedContainer, int> distance_cache;
	std::map<UnsignedContainer, ExactDistance> completion_cache;
	std::map<std::pair<UnsignedContainer, UnsignedContainer>, int> estimate_cache;
	int max_bit_width;

	SearchResult result;
};

} // namespace Yosys::Mcm::Hcub

#endif // YOSYS_HCUB_H
