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
#include <limits>
#include <tuple>
#include <utility>

namespace Yosys::Mcm {

// right shifts until n % 2 == 1
int64_t oddify(int64_t n)
{
	if (n == std::numeric_limits<int64_t>::min())
		log_error("cannot oddify INT64_MIN.\n");
	if (n < 0)
		n = -n;
	while (n && (n % 2) == 0)
		n /= 2;
	return n;
}

// number of right shifts until n % 2 == 1
int shift_of(int64_t n)
{
	int k = 0;
	if (n == std::numeric_limits<int64_t>::min())
		log_error("cannot compute shift_of(INT64_MIN).\n");
	if (n < 0)
		n = -n;
	while (n && (n % 2) == 0) { n /= 2; k++; }
	return k;
}

// number of right shifts until n % 2 == 1
int bit_width(int64_t n)
{
	int k = 0;
	if (n == std::numeric_limits<int64_t>::min())
		log_error("cannot compute bit_width(INT64_MIN).\n");
	if (n < 0)
		n = -n;
	while (n) { n /= 2; k++; }
	return k;
}

// Number of non-zero digits in the non-adjacent signed-digit form.
int naf_weight(int64_t n)
{
	uint64_t v = n < 0 ? uint64_t(-(n + 1)) + 1 : uint64_t(n);
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

int max_bit_width(const IntSet &int_set) {
	int max_width = 0;
	for (int64_t n : int_set)
		max_width = std::max(max_width, bit_width(n));
	return max_width;
}

AdderGraph::AdderGraph() {
	ops.insert(std::pair<int64_t, AOp>(1, ONE));
}

} // namespace Yosys::Mcm
