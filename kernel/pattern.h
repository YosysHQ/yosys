#ifndef OPT_DFF_COMP_H
#define OPT_DFF_COMP_H

#include "kernel/rtlil.h"
#include <map>
#include <optional>

YOSYS_NAMESPACE_BEGIN

/**
 *  Pattern matching utilities for control signal analysis.
 *
 *  A pattern_t maps control signals to required values, representing a
 *  product term (conjunction): {A=1, B=0} means "A AND !B".
 *
 *  A patterns_t is a set of patterns representing a sum-of-products:
 *  {{A=1, B=0}, {A=0, C=1}} means "(A AND !B) OR (!A AND C)".
 *
 *  Used for analyzing MUX tree control paths in DFF optimization.
 */

typedef std::map<RTLIL::SigBit, bool> pattern_t; // Control signal -> required vals
typedef std::set<pattern_t> patterns_t;          // Alternative patterns (OR)

/**
 * Find if two patterns differ in exactly one variable.
 * Example: {A=1,B=1} vs {A=1,B=0} returns B, allows simplification: (A&B) | (A&!B) => A
 */
inline std::optional<RTLIL::SigBit> find_complementary_pattern_var(
	const pattern_t& left,
	const pattern_t& right
) {
	std::optional<RTLIL::SigBit> ret;
	for (const auto &pt : left) {
		// Left requires signal that right doesn't constrain - incompatible domains
		if (right.count(pt.first) == 0)
			return std::nullopt;
		// Signal has same required value in both - not the complement variable
		if (right.at(pt.first) == pt.second)
			continue;
		// Already found one differing signal, now found another - not simplifiable
		if (ret)
			return std::nullopt;
		// First differing signal - candidate complement variable
		ret = pt.first;
	}
	return ret;
}

/**
 * Simplify a sum-of-products by merging complementary patterns: (A&B) | (A&!B) => A,
 * and removing redundant patterns: A | (A&B) => A
 */
inline void simplify_patterns(patterns_t& patterns) {
	auto new_patterns = patterns;

	// Merge complementary patterns
	bool optimized;
	do {
		optimized = false;
		for (auto i = patterns.begin(); i != patterns.end(); i++) {
			for (auto j = std::next(i, 1); j != patterns.end(); j++) {
				const auto& left = (GetSize(*j) <= GetSize(*i)) ? *j : *i;
				auto right = (GetSize(*i) < GetSize(*j)) ? *j : *i;
				const auto complementary_var = find_complementary_pattern_var(left, right);

				if (complementary_var && new_patterns.count(right)) {
					new_patterns.erase(right);
					right.erase(complementary_var.value());
					new_patterns.insert(right);
					optimized = true;
				}
			}
		}
		patterns = new_patterns;
	} while(optimized);

	// Remove redundant patterns
	for (auto i = patterns.begin(); i != patterns.end(); ++i) {
		for (auto j = std::next(i, 1); j != patterns.end(); ++j) {
			const auto& left = (GetSize(*j) <= GetSize(*i)) ? *j : *i;
			const auto& right = (GetSize(*i) < GetSize(*j)) ? *j : *i;
			bool redundant = true;

			for (const auto& pt : left)
				if (right.count(pt.first) == 0 || right.at(pt.first) != pt.second)
					redundant = false;
			if (redundant)
				new_patterns.erase(right);
		}
	}

	patterns = std::move(new_patterns);
}

YOSYS_NAMESPACE_END

#endif
