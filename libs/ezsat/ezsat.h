/*
 *  ezSAT -- A simple and easy to use CNF generator for SAT solvers
 *
 *  Copyright (C) 2013  Clifford Wolf <clifford@clifford.at>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#ifndef EZSAT_H
#define EZSAT_H

#include <set>
#include <map>
#include <vector>
#include <string>
#include <stdio.h>
#include <stdint.h>

class ezSAT
{
	// each token (terminal or non-terminal) is represented by an integer number
	//
	// the zero token:
	// the number zero is not used as valid token number and is used to encode
	// unused parameters for the functions.
	//
	// positive numbers are literals, with 1 = CONST_TRUE and 2 = CONST_FALSE;
	//
	// negative numbers are non-literal expressions. each expression is represented
	// by an operator id and a list of expressions (literals or non-literals).

public:
	enum OpId {
		OpNot, OpAnd, OpOr, OpXor, OpIFF, OpITE
	};

	static const int CONST_TRUE;
	static const int CONST_FALSE;

private:
	bool flag_keep_cnf;
	bool flag_non_incremental;

	bool non_incremental_solve_used_up;

	std::map<std::string, int> literalsCache;
	std::vector<std::string> literals;

	std::map<std::pair<OpId, std::vector<int>>, int> expressionsCache;
	std::vector<std::pair<OpId, std::vector<int>>> expressions;

	bool cnfConsumed;
	int cnfVariableCount, cnfClausesCount;
	std::vector<int> cnfLiteralVariables, cnfExpressionVariables;
	std::vector<std::vector<int>> cnfClauses, cnfClausesBackup;

	void add_clause(const std::vector<int> &args);
	void add_clause(const std::vector<int> &args, bool argsPolarity, int a = 0, int b = 0, int c = 0);
	void add_clause(int a, int b = 0, int c = 0);

	int bind_cnf_not(const std::vector<int> &args);
	int bind_cnf_and(const std::vector<int> &args);
	int bind_cnf_or(const std::vector<int> &args);

protected:
	void preSolverCallback();

public:
	int solverTimeout;
	bool solverTimoutStatus;

	ezSAT();
	virtual ~ezSAT();

	unsigned int statehash;
	void addhash(unsigned int);

	void keep_cnf() { flag_keep_cnf = true; }
	void non_incremental() { flag_non_incremental = true; }

	bool mode_keep_cnf() const { return flag_keep_cnf; }
	bool mode_non_incremental() const { return flag_non_incremental; }

	// manage expressions

	int value(bool val);
	int literal();
	int literal(const std::string &name);
	int frozen_literal();
	int frozen_literal(const std::string &name);
	int expression(OpId op, int a = 0, int b = 0, int c = 0, int d = 0, int e = 0, int f = 0);
	int expression(OpId op, const std::vector<int> &args);

	void lookup_literal(int id, std::string &name) const;
	const std::string &lookup_literal(int id) const;

	void lookup_expression(int id, OpId &op, std::vector<int> &args) const;
	const std::vector<int> &lookup_expression(int id, OpId &op) const;

	int parse_string(const std::string &text);
	std::string to_string(int id) const;

	int numLiterals() const { return literals.size(); }
	int numExpressions() const { return expressions.size(); }

	int eval(int id, const std::vector<int> &values) const;

	// SAT solver interface
	// If you are planning on using the solver API (and not simply create a CNF) you must use a child class
	// of ezSAT that actually implements a solver backend, such as ezMiniSAT (see ezminisat.h).

	virtual bool solver(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, const std::vector<int> &assumptions);

	bool solve(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, const std::vector<int> &assumptions) {
		return solver(modelExpressions, modelValues, assumptions);
	}

	bool solve(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, int a = 0, int b = 0, int c = 0, int d = 0, int e = 0, int f = 0) {
		std::vector<int> assumptions;
		if (a != 0) assumptions.push_back(a);
		if (b != 0) assumptions.push_back(b);
		if (c != 0) assumptions.push_back(c);
		if (d != 0) assumptions.push_back(d);
		if (e != 0) assumptions.push_back(e);
		if (f != 0) assumptions.push_back(f);
		return solver(modelExpressions, modelValues, assumptions);
	}

	bool solve(int a = 0, int b = 0, int c = 0, int d = 0, int e = 0, int f = 0) {
		std::vector<int> assumptions, modelExpressions;
		std::vector<bool> modelValues;
		if (a != 0) assumptions.push_back(a);
		if (b != 0) assumptions.push_back(b);
		if (c != 0) assumptions.push_back(c);
		if (d != 0) assumptions.push_back(d);
		if (e != 0) assumptions.push_back(e);
		if (f != 0) assumptions.push_back(f);
		return solver(modelExpressions, modelValues, assumptions);
	}

	void setSolverTimeout(int newTimeoutSeconds) {
		solverTimeout = newTimeoutSeconds;
	}

	bool getSolverTimoutStatus() {
		return solverTimoutStatus;
	}

	// manage CNF (usually only accessed by SAT solvers)

	virtual void clear();
	virtual void freeze(int id);
	virtual bool eliminated(int idx);
	void assume(int id);
	void assume(int id, int context_id) { assume(OR(id, NOT(context_id))); }
	int bind(int id, bool auto_freeze = true);
	int bound(int id) const;

	int numCnfVariables() const { return cnfVariableCount; }
	int numCnfClauses() const { return cnfClausesCount; }
	const std::vector<std::vector<int>> &cnf() const { return cnfClauses; }

	void consumeCnf();
	void consumeCnf(std::vector<std::vector<int>> &cnf);

	// use this function to get the full CNF in keep_cnf mode
	void getFullCnf(std::vector<std::vector<int>> &full_cnf) const;

	std::string cnfLiteralInfo(int idx) const;

	// simple helpers for build expressions easily

	struct _V {
		int id;
		std::string name;
		_V(int id) : id(id) { }
		_V(const char *name) : id(0), name(name) { }
		_V(const std::string &name) : id(0), name(name) { }
		int get(ezSAT *that) {
			if (name.empty())
				return id;
			return that->frozen_literal(name);
		}
	};

	int VAR(_V a) {
		return a.get(this);
	}

	int NOT(_V a) {
		return expression(OpNot, a.get(this));
	}

	int AND(_V a = 0, _V b = 0, _V c = 0, _V d = 0, _V e = 0, _V f = 0) {
		return expression(OpAnd, a.get(this), b.get(this), c.get(this), d.get(this), e.get(this), f.get(this));
	}

	int OR(_V a = 0, _V b = 0, _V c = 0, _V d = 0, _V e = 0, _V f = 0) {
		return expression(OpOr, a.get(this), b.get(this), c.get(this), d.get(this), e.get(this), f.get(this));
	}

	int XOR(_V a = 0, _V b = 0, _V c = 0, _V d = 0, _V e = 0, _V f = 0) {
		return expression(OpXor, a.get(this), b.get(this), c.get(this), d.get(this), e.get(this), f.get(this));
	}

	int IFF(_V a, _V b = 0, _V c = 0, _V d = 0, _V e = 0, _V f = 0) {
		return expression(OpIFF, a.get(this), b.get(this), c.get(this), d.get(this), e.get(this), f.get(this));
	}

	int ITE(_V a, _V b, _V c) {
		return expression(OpITE, a.get(this), b.get(this), c.get(this));
	}

	void SET(_V a, _V b) {
		assume(IFF(a.get(this), b.get(this)));
	}

	// simple helpers for building expressions with bit vectors

	std::vector<int> vec_const(const std::vector<bool> &bits);
	std::vector<int> vec_const_signed(int64_t value, int numBits);
	std::vector<int> vec_const_unsigned(uint64_t value, int numBits);
	std::vector<int> vec_var(int numBits);
	std::vector<int> vec_var(std::string name, int numBits);
	std::vector<int> vec_cast(const std::vector<int> &vec1, int toBits, bool signExtend = false);

	std::vector<int> vec_not(const std::vector<int> &vec1);
	std::vector<int> vec_and(const std::vector<int> &vec1, const std::vector<int> &vec2);
	std::vector<int> vec_or(const std::vector<int> &vec1, const std::vector<int> &vec2);
	std::vector<int> vec_xor(const std::vector<int> &vec1, const std::vector<int> &vec2);

	std::vector<int> vec_iff(const std::vector<int> &vec1, const std::vector<int> &vec2);
	std::vector<int> vec_ite(const std::vector<int> &vec1, const std::vector<int> &vec2, const std::vector<int> &vec3);
	std::vector<int> vec_ite(int sel, const std::vector<int> &vec1, const std::vector<int> &vec2);

	std::vector<int> vec_count(const std::vector<int> &vec, int numBits, bool clip = true);
	std::vector<int> vec_add(const std::vector<int> &vec1, const std::vector<int> &vec2);
	std::vector<int> vec_sub(const std::vector<int> &vec1, const std::vector<int> &vec2);
	std::vector<int> vec_neg(const std::vector<int> &vec);

	void vec_cmp(const std::vector<int> &vec1, const std::vector<int> &vec2, int &carry, int &overflow, int &sign, int &zero);

	int vec_lt_signed(const std::vector<int> &vec1, const std::vector<int> &vec2);
	int vec_le_signed(const std::vector<int> &vec1, const std::vector<int> &vec2);
	int vec_ge_signed(const std::vector<int> &vec1, const std::vector<int> &vec2);
	int vec_gt_signed(const std::vector<int> &vec1, const std::vector<int> &vec2);

	int vec_lt_unsigned(const std::vector<int> &vec1, const std::vector<int> &vec2);
	int vec_le_unsigned(const std::vector<int> &vec1, const std::vector<int> &vec2);
	int vec_ge_unsigned(const std::vector<int> &vec1, const std::vector<int> &vec2);
	int vec_gt_unsigned(const std::vector<int> &vec1, const std::vector<int> &vec2);

	int vec_eq(const std::vector<int> &vec1, const std::vector<int> &vec2);
	int vec_ne(const std::vector<int> &vec1, const std::vector<int> &vec2);

	std::vector<int> vec_shl(const std::vector<int> &vec1, int shift, bool signExtend = false);
	std::vector<int> vec_srl(const std::vector<int> &vec1, int shift);

	std::vector<int> vec_shr(const std::vector<int> &vec1, int shift, bool signExtend = false) { return vec_shl(vec1, -shift, signExtend); }
	std::vector<int> vec_srr(const std::vector<int> &vec1, int shift) { return vec_srl(vec1, -shift); }

	std::vector<int> vec_shift(const std::vector<int> &vec1, int shift, int extend_left, int extend_right);
	std::vector<int> vec_shift_right(const std::vector<int> &vec1, const std::vector<int> &vec2, bool vec2_signed, int extend_left, int extend_right);
	std::vector<int> vec_shift_left(const std::vector<int> &vec1, const std::vector<int> &vec2, bool vec2_signed, int extend_left, int extend_right);

	void vec_append(std::vector<int> &vec, const std::vector<int> &vec1) const;
	void vec_append_signed(std::vector<int> &vec, const std::vector<int> &vec1, int64_t value);
	void vec_append_unsigned(std::vector<int> &vec, const std::vector<int> &vec1, uint64_t value);

	int64_t vec_model_get_signed(const std::vector<int> &modelExpressions, const std::vector<bool> &modelValues, const std::vector<int> &vec1) const;
	uint64_t vec_model_get_unsigned(const std::vector<int> &modelExpressions, const std::vector<bool> &modelValues, const std::vector<int> &vec1) const;

	int vec_reduce_and(const std::vector<int> &vec1);
	int vec_reduce_or(const std::vector<int> &vec1);

	void vec_set(const std::vector<int> &vec1, const std::vector<int> &vec2);
	void vec_set_signed(const std::vector<int> &vec1, int64_t value);
	void vec_set_unsigned(const std::vector<int> &vec1, uint64_t value);

	// helpers for generating ezSATbit and ezSATvec objects

	struct ezSATbit bit(_V a);
	struct ezSATvec vec(const std::vector<int> &vec);

	// printing CNF and internal state

	void printDIMACS(FILE *f, bool verbose = false) const;
	void printInternalState(FILE *f) const;

	// more sophisticated constraints (designed to be used directly with assume(..))

	int onehot(const std::vector<int> &vec, bool max_only = false);
	int manyhot(const std::vector<int> &vec, int min_hot, int max_hot = -1);
	int ordered(const std::vector<int> &vec1, const std::vector<int> &vec2, bool allow_equal = true);
};

// helper classes for using operator overloading when generating complex expressions

struct ezSATbit
{
	ezSAT &sat;
	int id;

	ezSATbit(ezSAT &sat, ezSAT::_V a) : sat(sat), id(sat.VAR(a)) { }

	ezSATbit operator ~() { return ezSATbit(sat, sat.NOT(id)); }
	ezSATbit operator &(const ezSATbit &other) { return ezSATbit(sat, sat.AND(id, other.id)); }
	ezSATbit operator |(const ezSATbit &other) { return ezSATbit(sat, sat.OR(id, other.id)); }
	ezSATbit operator ^(const ezSATbit &other) { return ezSATbit(sat, sat.XOR(id, other.id)); }
	ezSATbit operator ==(const ezSATbit &other) { return ezSATbit(sat, sat.IFF(id, other.id)); }
	ezSATbit operator !=(const ezSATbit &other) { return ezSATbit(sat, sat.NOT(sat.IFF(id, other.id))); }

	operator int() const { return id; }
	operator ezSAT::_V() const { return ezSAT::_V(id); }
	operator std::vector<int>() const { return std::vector<int>(1, id); }
};

struct ezSATvec
{
	ezSAT &sat;
	std::vector<int> vec;

	ezSATvec(ezSAT &sat, const std::vector<int> &vec) : sat(sat), vec(vec) { }

	ezSATvec operator ~() { return ezSATvec(sat, sat.vec_not(vec)); }
	ezSATvec operator -() { return ezSATvec(sat, sat.vec_neg(vec)); }

	ezSATvec operator &(const ezSATvec &other) { return ezSATvec(sat, sat.vec_and(vec, other.vec)); }
	ezSATvec operator |(const ezSATvec &other) { return ezSATvec(sat, sat.vec_or(vec, other.vec)); }
	ezSATvec operator ^(const ezSATvec &other) { return ezSATvec(sat, sat.vec_xor(vec, other.vec)); }

	ezSATvec operator +(const ezSATvec &other) { return ezSATvec(sat, sat.vec_add(vec, other.vec)); }
	ezSATvec operator -(const ezSATvec &other) { return ezSATvec(sat, sat.vec_sub(vec, other.vec)); }

	ezSATbit operator < (const ezSATvec &other) { return ezSATbit(sat, sat.vec_lt_unsigned(vec, other.vec)); }
	ezSATbit operator <=(const ezSATvec &other) { return ezSATbit(sat, sat.vec_le_unsigned(vec, other.vec)); }
	ezSATbit operator ==(const ezSATvec &other) { return ezSATbit(sat, sat.vec_eq(vec, other.vec)); }
	ezSATbit operator !=(const ezSATvec &other) { return ezSATbit(sat, sat.vec_ne(vec, other.vec)); }
	ezSATbit operator >=(const ezSATvec &other) { return ezSATbit(sat, sat.vec_ge_unsigned(vec, other.vec)); }
	ezSATbit operator > (const ezSATvec &other) { return ezSATbit(sat, sat.vec_gt_unsigned(vec, other.vec)); }

	ezSATvec operator <<(int shift) { return ezSATvec(sat, sat.vec_shl(vec, shift)); }
	ezSATvec operator >>(int shift) { return ezSATvec(sat, sat.vec_shr(vec, shift)); }

	operator std::vector<int>() const { return vec; }
};

#endif
