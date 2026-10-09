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
	SearchResult run_search();
	IntSet quotients(const IntSet &values, const IntSet &divisors) const;
	struct ExactDistance {
		int value = -1; // No distance <= 3 found.
		IntSet reducing_successors;
	};

	void add_target(const AOp &target);
	bool heuristic(AOp &selected);
	ExactDistance exact_dist(const UnsignedContainer &target) const;
	int estimate_after(const UnsignedContainer &successor, const UnsignedContainer &target, int previous);
	bool finishes_in_one(const IntSet &ready, const UnsignedContainer &successor, const UnsignedContainer &target) const;
	bool finishes_in_two(const UnsignedContainer &successor, const UnsignedContainer &target) const;
	AOpMap enumerate_pair(const UnsignedContainer &u, const UnsignedContainer &v, int min_shift, int max_shift) const;
	template<typename Unsigned> AOpMap enumerate_pair(Unsigned u, Unsigned v, int min_shift, int max_shift) const;
	IntSet inverse_set(const IntSet &u, const IntSet &v) const;

	McmConfig config;
	mutable long long work_remaining;
	std::map<UnsignedContainer, int> depths;
	IntSet target_set_remaining;
	AOpMap ready_set;
	AOpMap work_list;
	AOpMap successor_set;
	IntSet c1, c2;
	std::map<UnsignedContainer, int> distance_cache;
	std::map<std::pair<UnsignedContainer, UnsignedContainer>, int> estimate_cache;
	int max_bit_width;
};

} // namespace Yosys::Mcm::Hcub

#endif // YOSYS_HCUB_H
