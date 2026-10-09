#ifndef YOSYS_MCM_H
#define YOSYS_MCM_H

#include "kernel/yosys.h"
#include <cstdint>
#include <cstdlib>
#include <map>
#include <optional>
#include <set>
#include <variant>
#include <vector>

#include "libs/bigint/BigUnsigned.hh"

namespace Yosys::Mcm {

class UnsignedContainer {
public:
	UnsignedContainer(uint64_t integer = 0) : value(integer) {}
	UnsignedContainer(const BigUnsigned &integer);
	BigUnsigned to_big_unsigned() const;

	bool operator==(const UnsignedContainer &other) const { return value == other.value; }
	bool operator<(const UnsignedContainer &other) const { return value < other.value; }

	template<typename Unsigned> const Unsigned &get() const {
		return std::get<Unsigned>(value);
	}
	std::optional<uint64_t> get_uint64_t() const {
		if (auto small = std::get_if<uint64_t>(&value))
			return *small;
		return std::nullopt;
	}

private:
	std::variant<uint64_t, BigUnsigned> value;
};

template<typename Unsigned>
int shift_of(const Unsigned &n)
{
	if constexpr (std::is_same_v<Unsigned, uint64_t>) {
		return n ? std::countr_zero(n) : 0;
	} else {
		for (BigUnsigned::Index i = 0; i < n.getLength(); i++)
			if (auto block = n.getBlock(i))
				return i * BigUnsigned::N + std::countr_zero(block);
		return 0;
	}
}

template<typename Unsigned> Unsigned oddify(Unsigned n)
{
	return n >> shift_of(n);
}

template<typename Unsigned> int bit_width(const Unsigned &n)
{
	if constexpr (std::is_same_v<Unsigned, uint64_t>)
		return std::bit_width(n);
	else
		return n.bitLength();
}


// Number of non-zero digits in the non-adjacent signed-digit form.
template<typename Unsigned> int naf_weight(Unsigned n)
{
	int weight = 0;
	while (n != 0) {
		if ((n & 1) != 0) {
			weight++;
			if ((n & 3) == 3) {
				n >>= 1;
				n++;
				continue;
			}
		}
		n >>= 1;
	}
	return weight;
}

inline UnsignedContainer oddify(const UnsignedContainer &n) {
	if (auto small = n.get_uint64_t())
		return oddify<uint64_t>(*small);
	return oddify<BigUnsigned>(n.get<BigUnsigned>());
}
inline int shift_of(const UnsignedContainer &n) {
	if (auto small = n.get_uint64_t())
		return shift_of<uint64_t>(*small);
	return shift_of<BigUnsigned>(n.get<BigUnsigned>());
}
inline int bit_width(const UnsignedContainer &n) {
	if (auto small = n.get_uint64_t())
		return bit_width<uint64_t>(*small);
	return bit_width<BigUnsigned>(n.get<BigUnsigned>());
}
inline int naf_weight(const UnsignedContainer &n) {
	if (auto small = n.get_uint64_t())
		return naf_weight<uint64_t>(*small);
	return naf_weight<BigUnsigned>(n.get<BigUnsigned>());
}

struct AOpCfg {
	int su, sv, norm;
	bool sub;

	BigUnsigned eval(BigUnsigned u, BigUnsigned v) const {
		if (su < 0 || sv < 0 || norm < 0)
			log_error("invalid shift in AOpCfg::eval.\n");
		BigUnsigned lhs = u << su, rhs = v << sv;
		BigUnsigned res = sub ? (lhs >= rhs ? lhs - rhs : rhs - lhs) : lhs + rhs;
		if (res != 0 && shift_of(res) < norm)
			log_error("inexact right shift in AOpCfg::eval.\n");
		return res >> norm;
	}

};

// One A-operation: res == |(u << su) +/- (v << sv)| >> norm
struct AOp {
	UnsignedContainer res;
	UnsignedContainer u, v;
	AOpCfg cfg;
};

const static AOp ONE = AOp{1, 0, 0, AOpCfg{0, 0, 0, false}};

struct McmConfig {
	std::optional<int> max_depth = std::nullopt;
	int max_shift = 32;
	int min_shift = 0;
	int max_nodes = 64;
	long long work_budget = 200000000;
	int min_const = 3;
	int min_gain = 0;
	bool force = false;
};


class AdderGraph {

public:
	AdderGraph();
	void add(const AOp &op) { ops[op.res] = op; }
	const std::map<UnsignedContainer, AOp> &operations() const { return ops; }

private:
	std::map<UnsignedContainer, AOp> ops;
};

enum class AdderGraphStatus {
	Success,
	NoGraph,
	NodeLimit,
	BudgetExhausted,
};

// ######################

using IntSet = std::set<UnsignedContainer>;
using AOpMap = std::map<UnsignedContainer, AOp>;

struct SearchResult {
	AdderGraph graph;
	AdderGraphStatus status = AdderGraphStatus::NoGraph;

	void add(const AOp &op) { graph.add(op); }
};

struct SearchParams {
	McmConfig config;
	IntSet target_set;
};

int max_bit_width(const IntSet &int_set);

class Search {
public:
	Search(const SearchParams &params) : params(params) {}
	virtual ~Search() = default;


	virtual SearchResult search() = 0;
	virtual bool a_op_valid(const AOp &op) const = 0;

	// A_*(u, v) = {forall cfg, op(u, v, cfg) where a_op_valid(cfg)}
	// Can this be made lazy? Probably not
	virtual AOpMap vertex_fundamental_set(const IntSet &u, const IntSet &v) const = 0;
private:
	const SearchParams &params;
};

} // namespace Yosys::Mcm

#endif // YOSYS_MCM_H
