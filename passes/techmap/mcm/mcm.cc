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
#include "libs/bigint/BigInteger.hh"
#include "libs/bigint/BigUnsigned.hh"

#include <algorithm>
#include <limits>
#include <tuple>
#include <utility>



namespace Yosys::Mcm {

// right shifts until n % 2 == 1
BigUnsigned oddify(BigUnsigned n)
{
	while (n > 0 && (n % 2) == 0)
		n /= 2;
	return n;
}

// number of right shifts until n % 2 == 1
int shift_of(BigUnsigned n)
{
	int k = 0;
	while (n > 0 && (n % 2) == 0) { n /= 2; k++; }
	return k;
}

// number of right shifts until n % 2 == 1
int bit_width(BigUnsigned n)
{
	int k = 0;
	while (n > 1) { n /= 2; k++; }
	return k + 1;
}

// Number of non-zero digits in the non-adjacent signed-digit form.
int naf_weight(BigUnsigned n)
{
	BigUnsigned v = n;
	int weight = 0;
	while (v > 0) {
		if ((v & 1) == 1 && v != 0) {
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
	for (BigUnsigned n : int_set)
		max_width = std::max(max_width, bit_width(n));
	return max_width;
}

AdderGraph::AdderGraph() {
	ops.insert(std::pair<BigUnsigned, AOp>(1, ONE));
}

} // namespace Yosys::Mcm
