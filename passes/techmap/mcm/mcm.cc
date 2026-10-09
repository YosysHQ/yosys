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

#include <algorithm>
#include <tuple>
#include <utility>



namespace Yosys::Mcm {

UnsignedContainer::UnsignedContainer(const BigUnsigned &integer) : value(uint64_t(0))
{
	if (integer.bitLength() <= 64) {
		// uint64_t small = 0;
		// for (BigUnsigned::Index i = 0; i < integer.getLength(); i++)
		// 	small |= uint64_t(integer.getBlock(i)) << (i * BigUnsigned::N);
		// value = small;
		value = integer.toUnsignedLong();
	} else {
		value = integer;
	}
}

BigUnsigned UnsignedContainer::to_big_unsigned() const
{
	if (auto small = get_uint64_t())
		// static cast needed for MacOS
		return BigUnsigned(static_cast<unsigned long>(*small));
	return get<BigUnsigned>();
}

int max_bit_width(const IntSet &int_set) {
	int max_width = 0;
	for (const auto &n : int_set)
		max_width = std::max(max_width, bit_width(n));
	return max_width;
}

AdderGraph::AdderGraph() {
	ops.insert(std::pair<UnsignedContainer, AOp>(1, ONE));
}

} // namespace Yosys::Mcm
