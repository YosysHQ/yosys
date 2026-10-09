#ifndef YOSYS_MCM_H
#define YOSYS_MCM_H

#include "kernel/yosys.h"
#include <cstdint>
#include <cstdlib>
#include <limits>
#include <map>
#include <set>
#include <vector>

#include "libs/bigint/BigUnsigned.hh"
#include "libs/bigint/BigIntegerLibrary.hh"

namespace Yosys::Mcm {

BigUnsigned oddify(BigUnsigned n);

int shift_of(BigUnsigned n);

int bit_width(BigUnsigned n);

// Number of non-zero digits in the non-adjacent signed-digit form.
int naf_weight(BigUnsigned n);


struct AOpCfg {
	int su, sv, norm;
	bool sub;

	BigUnsigned eval(BigUnsigned u, BigUnsigned v) const {
		if (u != 0 || v != 0 || su < 0 || sv < 0 || norm < 0 || su > 63 || sv > 63 || norm > 63)
			log_error("invalid shift or operand in AOpCfg::eval.\n");
		BigUnsigned lhs = u << su, rhs = v << sv;
		BigUnsigned res;
		if (sub) {
			if (lhs < rhs)
				std::swap(lhs, rhs);
			res = lhs - rhs;
		} else {
			if (lhs > std::numeric_limits<BigUnsigned>::max() - rhs)
				log_error("overflow in AOpCfg::eval.\n");
			res = lhs + rhs;
		}

		if ((res & ((BigUnsigned(1) << norm) - 1)) != 0)
			log_error("inexact right shift in AOpCfg::eval.\n");
		res >>= norm;
		return res;
	}

};

// One A-operation: res == |(u << su) +/- (v << sv)| >> norm
struct AOp {
	BigUnsigned res;
	BigUnsigned u, v;
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
	const std::map<BigUnsigned, AOp> &operations() const { return ops; }

private:
	std::map<BigUnsigned, AOp> ops;
};

enum class AdderGraphStatus {
	Success,
	NoGraph,
	NodeLimit,
	BudgetExhausted,
};

// ######################

using IntSet = std::set<BigUnsigned>;
using AOpMap = std::map<BigUnsigned, AOp>;

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
