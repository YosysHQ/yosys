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

#include "ezsat.h"

#include <cmath>
#include <algorithm>
#include <cassert>
#include <string>

#include <stdlib.h>

const int ezSAT::CONST_TRUE = 1;
const int ezSAT::CONST_FALSE = 2;

static std::string my_int_to_string(int i)
{
#ifdef __MINGW32__
	char buffer[64];
	snprintf(buffer, 64, "%d", i);
	return buffer;
#else
	return std::to_string(i);
#endif
}

ezSAT::ezSAT()
{
	statehash = 5381;

	flag_keep_cnf = false;
	flag_non_incremental = false;

	non_incremental_solve_used_up = false;

	cnfConsumed = false;
	cnfVariableCount = 0;
	cnfClausesCount = 0;

	solverTimeout = 0;
	solverTimoutStatus = false;

	literal("CONST_TRUE");
	literal("CONST_FALSE");

	assert(literal("CONST_TRUE") == CONST_TRUE);
	assert(literal("CONST_FALSE") == CONST_FALSE);
}

ezSAT::~ezSAT()
{
}

void ezSAT::addhash(unsigned int h)
{
	statehash = ((statehash << 5) + statehash) ^ h;
}

int ezSAT::value(bool val)
{
	return val ? CONST_TRUE : CONST_FALSE;
}

int ezSAT::literal()
{
	literals.push_back(std::string());
	return literals.size();
}

int ezSAT::literal(const std::string &name)
{
	if (literalsCache.count(name) == 0) {
		literals.push_back(name);
		literalsCache[name] = literals.size();
	}
	return literalsCache.at(name);
}

int ezSAT::frozen_literal()
{
	int id = literal();
	freeze(id);
	return id;
}

int ezSAT::frozen_literal(const std::string &name)
{
	int id = literal(name);
	freeze(id);
	return id;
}

int ezSAT::expression(OpId op, int a, int b, int c, int d, int e, int f)
{
	std::vector<int> args(6);
	args[0] = a, args[1] = b, args[2] = c;
	args[3] = d, args[4] = e, args[5] = f;
	return expression(op, args);
}

int ezSAT::expression(OpId op, const std::vector<int> &args)
{
	std::vector<int> myArgs;
	myArgs.reserve(args.size());
	bool xorRemovedOddTrues = false;

	addhash(__LINE__);
	addhash(op);

	for (auto arg : args)
	{
		addhash(__LINE__);
		addhash(arg);

		if (arg == 0)
			continue;
		if (op == OpAnd && arg == CONST_TRUE)
			continue;
		if ((op == OpOr || op == OpXor) && arg == CONST_FALSE)
			continue;
		if (op == OpXor && arg == CONST_TRUE) {
			xorRemovedOddTrues = !xorRemovedOddTrues;
			continue;
		}
		myArgs.push_back(arg);
	}

	if (myArgs.size() > 0 && (op == OpAnd || op == OpOr || op == OpXor || op == OpIFF)) {
		std::sort(myArgs.begin(), myArgs.end());
		int j = 0;
		for (int i = 1; i < int(myArgs.size()); i++)
			if (j < 0 || myArgs[j] != myArgs[i])
				myArgs[++j] = myArgs[i];
			else if (op == OpXor)
				j--;
		myArgs.resize(j+1);
	}

	switch (op)
	{
	case OpNot:
		assert(myArgs.size() == 1);
		if (myArgs[0] == CONST_TRUE)
			return CONST_FALSE;
		if (myArgs[0] == CONST_FALSE)
			return CONST_TRUE;
		break;

	case OpAnd:
		if (myArgs.size() == 0)
			return CONST_TRUE;
		if (myArgs.size() == 1)
			return myArgs[0];
		break;

	case OpOr:
		if (myArgs.size() == 0)
			return CONST_FALSE;
		if (myArgs.size() == 1)
			return myArgs[0];
		break;

	case OpXor:
		if (myArgs.size() == 0)
			return xorRemovedOddTrues ? CONST_TRUE : CONST_FALSE;
		if (myArgs.size() == 1)
			return xorRemovedOddTrues ? NOT(myArgs[0]) : myArgs[0];
		break;

	case OpIFF:
		assert(myArgs.size() >= 1);
		if (myArgs.size() == 1)
			return CONST_TRUE;
		// FIXME: Add proper const folding
		break;

	case OpITE:
		assert(myArgs.size() == 3);
		if (myArgs[0] == CONST_TRUE)
			return myArgs[1];
		if (myArgs[0] == CONST_FALSE)
			return myArgs[2];
		break;

	default:
		abort();
	}

	std::pair<OpId, std::vector<int>> myExpr(op, myArgs);
	int id = 0;

	if (expressionsCache.count(myExpr) > 0) {
		id = expressionsCache.at(myExpr);
	} else {
		id = -(int(expressions.size()) + 1);
		expressionsCache[myExpr] = id;
		expressions.push_back(myExpr);
	}

	if (xorRemovedOddTrues)
		id = NOT(id);

	addhash(__LINE__);
	addhash(id);

	return id;
}

void ezSAT::lookup_literal(int id, std::string &name) const
{
	assert(0 < id && id <= int(literals.size()));
	name = literals[id - 1];
}

const std::string &ezSAT::lookup_literal(int id) const
{
	assert(0 < id && id <= int(literals.size()));
	return literals[id - 1];
}

void ezSAT::lookup_expression(int id, OpId &op, std::vector<int> &args) const
{
	assert(0 < -id && -id <= int(expressions.size()));
	op = expressions[-id - 1].first;
	args = expressions[-id - 1].second;
}

const std::vector<int> &ezSAT::lookup_expression(int id, OpId &op) const
{
	assert(0 < -id && -id <= int(expressions.size()));
	op = expressions[-id - 1].first;
	return expressions[-id - 1].second;
}

int ezSAT::parse_string(const std::string &)
{
	abort();
}

std::string ezSAT::to_string(int id) const
{
	std::string text;

	if (id > 0)
	{
		lookup_literal(id, text);
	}
	else
	{
		OpId op;
		std::vector<int> args;
		lookup_expression(id, op, args);

		switch (op)
		{
		case OpNot:
			text = "not(";
			break;

		case OpAnd:
			text = "and(";
			break;

		case OpOr:
			text = "or(";
			break;

		case OpXor:
			text = "xor(";
			break;

		case OpIFF:
			text = "iff(";
			break;

		case OpITE:
			text = "ite(";
			break;

		default:
			abort();
		}

		for (int i = 0; i < int(args.size()); i++) {
			if (i > 0)
				text += ", ";
			text += to_string(args[i]);
		}

		text += ")";
	}

	return text;
}

int ezSAT::eval(int id, const std::vector<int> &values) const
{
	if (id > 0) {
		if (id <= int(values.size()) && (values[id-1] == CONST_TRUE || values[id-1] == CONST_FALSE || values[id-1] == 0))
			return values[id-1];
		return 0;
	}

	OpId op;
	const std::vector<int> &args = lookup_expression(id, op);
	int a, b;

	switch (op)
	{
	case OpNot:
		assert(args.size() == 1);
		a = eval(args[0], values);
		if (a == CONST_TRUE)
			return CONST_FALSE;
		if (a == CONST_FALSE)
			return CONST_TRUE;
		return 0;
	case OpAnd:
		a = CONST_TRUE;
		for (auto arg : args) {
			b = eval(arg, values);
			if (b != CONST_TRUE && b != CONST_FALSE)
				a = 0;
			if (b == CONST_FALSE)
				return CONST_FALSE;
		}
		return a;
	case OpOr:
		a = CONST_FALSE;
		for (auto arg : args) {
			b = eval(arg, values);
			if (b != CONST_TRUE && b != CONST_FALSE)
				a = 0;
			if (b == CONST_TRUE)
				return CONST_TRUE;
		}
		return a;
	case OpXor:
		a = CONST_FALSE;
		for (auto arg : args) {
			b = eval(arg, values);
			if (b != CONST_TRUE && b != CONST_FALSE)
				return 0;
			if (b == CONST_TRUE)
				a = a == CONST_TRUE ? CONST_FALSE : CONST_TRUE;
		}
		return a;
	case OpIFF:
		assert(args.size() > 0);
		a = eval(args[0], values);
		for (auto arg : args) {
			b = eval(arg, values);
			if (b != CONST_TRUE && b != CONST_FALSE)
				return 0;
			if (b != a)
				return CONST_FALSE;
		}
		return CONST_TRUE;
	case OpITE:
		assert(args.size() == 3);
		a = eval(args[0], values);
		if (a == CONST_TRUE)
			return eval(args[1], values);
		if (a == CONST_FALSE)
			return eval(args[2], values);
		return 0;
	default:
		abort();
	}
}

void ezSAT::clear()
{
	cnfConsumed = false;
	cnfVariableCount = 0;
	cnfClausesCount = 0;
	cnfLiteralVariables.clear();
	cnfExpressionVariables.clear();
	cnfClauses.clear();
}

void ezSAT::freeze(int)
{
}

bool ezSAT::eliminated(int)
{
	return false;
}

void ezSAT::assume(int id)
{
	addhash(__LINE__);
	addhash(id);

	if (id < 0)
	{
		assert(0 < -id && -id <= int(expressions.size()));
		cnfExpressionVariables.resize(expressions.size());

		if (cnfExpressionVariables[-id-1] == 0)
		{
			OpId op;
			std::vector<int> args;
			lookup_expression(id, op, args);

			if (op == OpNot) {
				int idx = bind(args[0]);
				cnfClauses.push_back(std::vector<int>(1, -idx));
				cnfClausesCount++;
				return;
			}
			if (op == OpOr) {
				std::vector<int> clause;
				for (int arg : args)
					clause.push_back(bind(arg));
				cnfClauses.push_back(clause);
				cnfClausesCount++;
				return;
			}
			if (op == OpAnd) {
				for (int arg : args) {
					cnfClauses.push_back(std::vector<int>(1, bind(arg)));
					cnfClausesCount++;
				}
				return;
			}
		}
	}

	int idx = bind(id);
	cnfClauses.push_back(std::vector<int>(1, idx));
	cnfClausesCount++;
}

void ezSAT::add_clause(const std::vector<int> &args)
{
	addhash(__LINE__);
	for (auto arg : args)
		addhash(arg);

	cnfClauses.push_back(args);
	cnfClausesCount++;
}

void ezSAT::add_clause(const std::vector<int> &args, bool argsPolarity, int a, int b, int c)
{
	std::vector<int> clause;
	for (auto arg : args)
		clause.push_back(argsPolarity ? +arg : -arg);
	if (a != 0)
		clause.push_back(a);
	if (b != 0)
		clause.push_back(b);
	if (c != 0)
		clause.push_back(c);
	add_clause(clause);
}

void ezSAT::add_clause(int a, int b, int c)
{
	std::vector<int> clause;
	if (a != 0)
		clause.push_back(a);
	if (b != 0)
		clause.push_back(b);
	if (c != 0)
		clause.push_back(c);
	add_clause(clause);
}

int ezSAT::bind_cnf_not(const std::vector<int> &args)
{
	assert(args.size() == 1);
	return -args[0];
}

int ezSAT::bind_cnf_and(const std::vector<int> &args)
{
	assert(args.size() >= 2);

	int idx = ++cnfVariableCount;
	add_clause(args, false, idx);

	for (auto arg : args)
		add_clause(-idx, arg);

	return idx;
}

int ezSAT::bind_cnf_or(const std::vector<int> &args)
{
	assert(args.size() >= 2);

	int idx = ++cnfVariableCount;
	add_clause(args, true, -idx);

	for (auto arg : args)
		add_clause(idx, -arg);

	return idx;
}

int ezSAT::bound(int id) const
{
	if (id > 0 && id <= int(cnfLiteralVariables.size()))
		return cnfLiteralVariables[id-1];
	if (-id > 0 && -id <= int(cnfExpressionVariables.size()))
		return cnfExpressionVariables[-id-1];
	return 0;
}

std::string ezSAT::cnfLiteralInfo(int idx) const
{
	for (int i = 0; i < int(cnfLiteralVariables.size()); i++) {
		if (cnfLiteralVariables[i] == idx)
			return to_string(i+1);
		if (cnfLiteralVariables[i] == -idx)
			return "NOT " + to_string(i+1);
	}
	for (int i = 0; i < int(cnfExpressionVariables.size()); i++) {
		if (cnfExpressionVariables[i] == idx)
			return to_string(-i-1);
		if (cnfExpressionVariables[i] == -idx)
			return "NOT " + to_string(-i-1);
	}
	return "<unnamed>";
}

int ezSAT::bind(int id, bool auto_freeze)
{
	addhash(__LINE__);
	addhash(id);
	addhash(auto_freeze);

	if (id >= 0) {
		assert(0 < id && id <= int(literals.size()));
		cnfLiteralVariables.resize(literals.size());
		if (eliminated(cnfLiteralVariables[id-1])) {
			fprintf(stderr, "ezSAT: Missing freeze on literal `%s'.\n", to_string(id).c_str());
			abort();
		}
		if (cnfLiteralVariables[id-1] == 0) {
			cnfLiteralVariables[id-1] = ++cnfVariableCount;
			if (id == CONST_TRUE)
				add_clause(+cnfLiteralVariables[id-1]);
			if (id == CONST_FALSE)
				add_clause(-cnfLiteralVariables[id-1]);
		}
		return cnfLiteralVariables[id-1];
	}

	assert(0 < -id && -id <= int(expressions.size()));
	cnfExpressionVariables.resize(expressions.size());

	if (eliminated(cnfExpressionVariables[-id-1]))
	{
		cnfExpressionVariables[-id-1] = 0;

		// this will recursively call bind(id). within the recursion
		// the cnf is pre-set to 0. an idx is allocated there, then it
		// is frozen, then it returns here with the new idx already set.
		if (auto_freeze)
			freeze(id);
	}

	if (cnfExpressionVariables[-id-1] == 0)
	{
		OpId op;
		std::vector<int> args;
		lookup_expression(id, op, args);
		int idx = 0;

		if (op == OpXor) {
			while (args.size() > 1) {
				std::vector<int> newArgs;
				for (int i = 0; i < int(args.size()); i += 2)
					if (i+1 == int(args.size())) {
						newArgs.push_back(args[i]);
					} else {
						int sub1 = AND(args[i], NOT(args[i+1]));
						int sub2 = AND(NOT(args[i]), args[i+1]);
						newArgs.push_back(OR(sub1, sub2));
					}
				args.swap(newArgs);
			}
			idx = bind(args.at(0), false);
			goto assign_idx;
		}

		if (op == OpIFF) {
			std::vector<int> invArgs;
			for (auto arg : args)
				invArgs.push_back(NOT(arg));
			int sub1 = expression(OpAnd, args);
			int sub2 = expression(OpAnd, invArgs);
			idx = bind(OR(sub1, sub2), false);
			goto assign_idx;
		}

		if (op == OpITE) {
			int sub1 = AND(args[0], args[1]);
			int sub2 = AND(NOT(args[0]), args[2]);
			idx = bind(OR(sub1, sub2), false);
			goto assign_idx;
		}

		for (int i = 0; i < int(args.size()); i++)
			args[i] = bind(args[i], false);

		switch (op)
		{
			case OpNot: idx = bind_cnf_not(args); break;
			case OpAnd: idx = bind_cnf_and(args); break;
			case OpOr:  idx = bind_cnf_or(args);  break;
			default: abort();
		}

	assign_idx:
		assert(idx != 0);
		cnfExpressionVariables[-id-1] = idx;
	}

	return cnfExpressionVariables[-id-1];
}

void ezSAT::consumeCnf()
{
	if (mode_keep_cnf())
		cnfClausesBackup.insert(cnfClausesBackup.end(), cnfClauses.begin(), cnfClauses.end());
	else
		cnfConsumed = true;
	cnfClauses.clear();
}

void ezSAT::consumeCnf(std::vector<std::vector<int>> &cnf)
{
	if (mode_keep_cnf())
		cnfClausesBackup.insert(cnfClausesBackup.end(), cnfClauses.begin(), cnfClauses.end());
	else
		cnfConsumed = true;
	cnf.swap(cnfClauses);
	cnfClauses.clear();
}

void ezSAT::getFullCnf(std::vector<std::vector<int>> &full_cnf) const
{
	assert(full_cnf.empty());
	full_cnf.insert(full_cnf.end(), cnfClausesBackup.begin(), cnfClausesBackup.end());
	full_cnf.insert(full_cnf.end(), cnfClauses.begin(), cnfClauses.end());
}

void ezSAT::preSolverCallback()
{
	assert(!non_incremental_solve_used_up);
	if (mode_non_incremental())
		non_incremental_solve_used_up = true;
}

bool ezSAT::solver(const std::vector<int>&, std::vector<bool>&, const std::vector<int>&)
{
	preSolverCallback();
	fprintf(stderr, "************************************************************************\n");
	fprintf(stderr, "ERROR: You are trying to use the solve() method of the ezSAT base class!\n");
	fprintf(stderr, "Use a dervied class like ezMiniSAT instead.\n");
	fprintf(stderr, "************************************************************************\n");
	abort();
}

std::vector<int> ezSAT::vec_const(const std::vector<bool> &bits)
{
	std::vector<int> vec;
	for (auto bit : bits)
		vec.push_back(bit ? CONST_TRUE : CONST_FALSE);
	return vec;
}

std::vector<int> ezSAT::vec_const_signed(int64_t value, int numBits)
{
	std::vector<int> vec;
	for (int i = 0; i < numBits; i++)
		vec.push_back(((value >> i) & 1) != 0 ? CONST_TRUE : CONST_FALSE);
	return vec;
}

std::vector<int> ezSAT::vec_const_unsigned(uint64_t value, int numBits)
{
	std::vector<int> vec;
	for (int i = 0; i < numBits; i++)
		vec.push_back(((value >> i) & 1) != 0 ? CONST_TRUE : CONST_FALSE);
	return vec;
}

std::vector<int> ezSAT::vec_var(int numBits)
{
	std::vector<int> vec;
	for (int i = 0; i < numBits; i++)
		vec.push_back(literal());
	return vec;
}

std::vector<int> ezSAT::vec_var(std::string name, int numBits)
{
	std::vector<int> vec;
	for (int i = 0; i < numBits; i++) {
		vec.push_back(VAR(name + my_int_to_string(i)));
	}
	return vec;
}

std::vector<int> ezSAT::vec_cast(const std::vector<int> &vec1, int toBits, bool signExtend)
{
	std::vector<int> vec;
	for (int i = 0; i < toBits; i++)
		if (i >= int(vec1.size()))
			vec.push_back(signExtend ? vec1.back() : CONST_FALSE);
		else
			vec.push_back(vec1[i]);
	return vec;
}

std::vector<int> ezSAT::vec_not(const std::vector<int> &vec1)
{
	std::vector<int> vec;
	for (auto bit : vec1)
		vec.push_back(NOT(bit));
	return vec;
}

std::vector<int> ezSAT::vec_and(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	assert(vec1.size() == vec2.size());
	std::vector<int> vec(vec1.size());
	for (int i = 0; i < int(vec1.size()); i++)
		vec[i] = AND(vec1[i], vec2[i]);
	return vec;
}

std::vector<int> ezSAT::vec_or(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	assert(vec1.size() == vec2.size());
	std::vector<int> vec(vec1.size());
	for (int i = 0; i < int(vec1.size()); i++)
		vec[i] = OR(vec1[i], vec2[i]);
	return vec;
}

std::vector<int> ezSAT::vec_xor(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	assert(vec1.size() == vec2.size());
	std::vector<int> vec(vec1.size());
	for (int i = 0; i < int(vec1.size()); i++)
		vec[i] = XOR(vec1[i], vec2[i]);
	return vec;
}

std::vector<int> ezSAT::vec_iff(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	assert(vec1.size() == vec2.size());
	std::vector<int> vec(vec1.size());
	for (int i = 0; i < int(vec1.size()); i++)
		vec[i] = IFF(vec1[i], vec2[i]);
	return vec;
}

std::vector<int> ezSAT::vec_ite(const std::vector<int> &vec1, const std::vector<int> &vec2, const std::vector<int> &vec3)
{
	assert(vec1.size() == vec2.size() && vec2.size() == vec3.size());
	std::vector<int> vec(vec1.size());
	for (int i = 0; i < int(vec1.size()); i++)
		vec[i] = ITE(vec1[i], vec2[i], vec3[i]);
	return vec;
}


std::vector<int> ezSAT::vec_ite(int sel, const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	assert(vec1.size() == vec2.size());
	std::vector<int> vec(vec1.size());
	for (int i = 0; i < int(vec1.size()); i++)
		vec[i] = ITE(sel, vec1[i], vec2[i]);
	return vec;
}

// 'y' is the MSB (carry) and x the LSB (sum) output
static void fulladder(ezSAT *that, int a, int b, int c, int &y, int &x)
{
	int tmp = that->XOR(a, b);
	int new_x = that->XOR(tmp, c);
	int new_y = that->OR(that->AND(a, b), that->AND(c, tmp));
#if 0
	printf("FULLADD> a=%s, b=%s, c=%s, carry=%s, sum=%s\n", that->to_string(a).c_str(), that->to_string(b).c_str(),
			that->to_string(c).c_str(), that->to_string(new_y).c_str(), that->to_string(new_x).c_str());
#endif
	x = new_x, y = new_y;
}

// 'y' is the MSB (carry) and x the LSB (sum) output
static void halfadder(ezSAT *that, int a, int b, int &y, int &x)
{
	int new_x = that->XOR(a, b);
	int new_y = that->AND(a, b);
#if 0
	printf("HALFADD> a=%s, b=%s, carry=%s, sum=%s\n", that->to_string(a).c_str(), that->to_string(b).c_str(),
			that->to_string(new_y).c_str(), that->to_string(new_x).c_str());
#endif
	x = new_x, y = new_y;
}

std::vector<int> ezSAT::vec_count(const std::vector<int> &vec, int numBits, bool clip)
{
	std::vector<int> sum = vec_const_unsigned(0, numBits);
	std::vector<int> carry_vector;

	for (auto bit : vec) {
		int carry = bit;
		for (int i = 0; i < numBits; i++)
			halfadder(this, carry, sum[i], carry, sum[i]);
		carry_vector.push_back(carry);
	}

	if (clip) {
		int overflow = vec_reduce_or(carry_vector);
		sum = vec_ite(overflow, vec_const_unsigned(~0, numBits), sum);
	}

#if 0
	printf("COUNT> vec=[");
	for (int i = int(vec.size())-1; i >= 0; i--)
		printf("%s%s", to_string(vec[i]).c_str(), i ? ", " : "");
	printf("], result=[");
	for (int i = int(sum.size())-1; i >= 0; i--)
		printf("%s%s", to_string(sum[i]).c_str(), i ? ", " : "");
	printf("]\n");
#endif

	return sum;
}

std::vector<int> ezSAT::vec_add(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	assert(vec1.size() == vec2.size());
	std::vector<int> vec(vec1.size());
	int carry = CONST_FALSE;
	for (int i = 0; i < int(vec1.size()); i++)
		fulladder(this, vec1[i], vec2[i], carry, carry, vec[i]);

#if 0
	printf("ADD> vec1=[");
	for (int i = int(vec1.size())-1; i >= 0; i--)
		printf("%s%s", to_string(vec1[i]).c_str(), i ? ", " : "");
	printf("], vec2=[");
	for (int i = int(vec2.size())-1; i >= 0; i--)
		printf("%s%s", to_string(vec2[i]).c_str(), i ? ", " : "");
	printf("], result=[");
	for (int i = int(vec.size())-1; i >= 0; i--)
		printf("%s%s", to_string(vec[i]).c_str(), i ? ", " : "");
	printf("]\n");
#endif

	return vec;
}

std::vector<int> ezSAT::vec_sub(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	assert(vec1.size() == vec2.size());
	std::vector<int> vec(vec1.size());
	int carry = CONST_TRUE;
	for (int i = 0; i < int(vec1.size()); i++)
		fulladder(this, vec1[i], NOT(vec2[i]), carry, carry, vec[i]);

#if 0
	printf("SUB> vec1=[");
	for (int i = int(vec1.size())-1; i >= 0; i--)
		printf("%s%s", to_string(vec1[i]).c_str(), i ? ", " : "");
	printf("], vec2=[");
	for (int i = int(vec2.size())-1; i >= 0; i--)
		printf("%s%s", to_string(vec2[i]).c_str(), i ? ", " : "");
	printf("], result=[");
	for (int i = int(vec.size())-1; i >= 0; i--)
		printf("%s%s", to_string(vec[i]).c_str(), i ? ", " : "");
	printf("]\n");
#endif

	return vec;
}

std::vector<int> ezSAT::vec_neg(const std::vector<int> &vec)
{
	std::vector<int> zero(vec.size(), CONST_FALSE);
	return vec_sub(zero, vec);
}

void ezSAT::vec_cmp(const std::vector<int> &vec1, const std::vector<int> &vec2, int &carry, int &overflow, int &sign, int &zero)
{
	assert(vec1.size() == vec2.size());
	carry = CONST_TRUE;
	zero = CONST_FALSE;
	for (int i = 0; i < int(vec1.size()); i++) {
		overflow = carry;
		fulladder(this, vec1[i], NOT(vec2[i]), carry, carry, sign);
		zero = OR(zero, sign);
	}
	overflow = XOR(overflow, carry);
	carry = NOT(carry);
	zero = NOT(zero);

#if 0
	printf("CMP> vec1=[");
	for (int i = int(vec1.size())-1; i >= 0; i--)
		printf("%s%s", to_string(vec1[i]).c_str(), i ? ", " : "");
	printf("], vec2=[");
	for (int i = int(vec2.size())-1; i >= 0; i--)
		printf("%s%s", to_string(vec2[i]).c_str(), i ? ", " : "");
	printf("], carry=%s, overflow=%s, sign=%s, zero=%s\n", to_string(carry).c_str(), to_string(overflow).c_str(), to_string(sign).c_str(), to_string(zero).c_str());
#endif
}

int ezSAT::vec_lt_signed(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	int carry, overflow, sign, zero;
	vec_cmp(vec1, vec2, carry, overflow, sign, zero);
	return OR(AND(NOT(overflow), sign), AND(overflow, NOT(sign)));
}

int ezSAT::vec_le_signed(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	int carry, overflow, sign, zero;
	vec_cmp(vec1, vec2, carry, overflow, sign, zero);
	return OR(AND(NOT(overflow), sign), AND(overflow, NOT(sign)), zero);
}

int ezSAT::vec_ge_signed(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	int carry, overflow, sign, zero;
	vec_cmp(vec1, vec2, carry, overflow, sign, zero);
	return OR(AND(NOT(overflow), NOT(sign)), AND(overflow, sign));
}

int ezSAT::vec_gt_signed(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	int carry, overflow, sign, zero;
	vec_cmp(vec1, vec2, carry, overflow, sign, zero);
	return AND(OR(AND(NOT(overflow), NOT(sign)), AND(overflow, sign)), NOT(zero));
}

int ezSAT::vec_lt_unsigned(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	int carry, overflow, sign, zero;
	vec_cmp(vec1, vec2, carry, overflow, sign, zero);
	return carry;
}

int ezSAT::vec_le_unsigned(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	int carry, overflow, sign, zero;
	vec_cmp(vec1, vec2, carry, overflow, sign, zero);
	return OR(carry, zero);
}

int ezSAT::vec_ge_unsigned(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	int carry, overflow, sign, zero;
	vec_cmp(vec1, vec2, carry, overflow, sign, zero);
	return NOT(carry);
}

int ezSAT::vec_gt_unsigned(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	int carry, overflow, sign, zero;
	vec_cmp(vec1, vec2, carry, overflow, sign, zero);
	return AND(NOT(carry), NOT(zero));
}

int ezSAT::vec_eq(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	return vec_reduce_and(vec_iff(vec1, vec2));
}

int ezSAT::vec_ne(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	return NOT(vec_reduce_and(vec_iff(vec1, vec2)));
}

std::vector<int> ezSAT::vec_shl(const std::vector<int> &vec1, int shift, bool signExtend)
{
	std::vector<int> vec;
	for (int i = 0; i < int(vec1.size()); i++) {
		int j = i-shift;
		if (int(vec1.size()) <= j)
			vec.push_back(signExtend ? vec1.back() : CONST_FALSE);
		else if (0 <= j)
			vec.push_back(vec1[j]);
		else
			vec.push_back(CONST_FALSE);
	}
	return vec;
}

std::vector<int> ezSAT::vec_srl(const std::vector<int> &vec1, int shift)
{
	std::vector<int> vec;
	for (int i = 0; i < int(vec1.size()); i++) {
		int j = i-shift;
		while (j < 0)
			j += vec1.size();
		while (j >= int(vec1.size()))
			j -= vec1.size();
		vec.push_back(vec1[j]);
	}
	return vec;
}

std::vector<int> ezSAT::vec_shift(const std::vector<int> &vec1, int shift, int extend_left, int extend_right)
{
	std::vector<int> vec;
	for (int i = 0; i < int(vec1.size()); i++) {
		int j = i+shift;
		if (j < 0)
			vec.push_back(extend_right);
		else if (j >= int(vec1.size()))
			vec.push_back(extend_left);
		else
			vec.push_back(vec1[j]);
	}
	return vec;
}

static int my_clog2(int x)
{
	int result = 0;
	for (x--; x > 0; result++)
		x >>= 1;
	return result;
}

std::vector<int> ezSAT::vec_shift_right(const std::vector<int> &vec1, const std::vector<int> &vec2, bool vec2_signed, int extend_left, int extend_right)
{
	int vec2_bits = std::min(my_clog2(vec1.size()) + (vec2_signed ? 1 : 0), int(vec2.size()));

	std::vector<int> overflow_bits(vec2.begin() + vec2_bits, vec2.end());
	int overflow_left = CONST_FALSE, overflow_right = CONST_FALSE;

	if (vec2_signed) {
		int overflow = CONST_FALSE;
		for (auto bit : overflow_bits)
			overflow = OR(overflow, XOR(bit, vec2[vec2_bits-1]));
		overflow_left = AND(overflow, NOT(vec2.back()));
		overflow_right = AND(overflow, vec2.back());
	} else
		overflow_left = vec_reduce_or(overflow_bits);

	std::vector<int> buffer = vec1;

	if (vec2_signed)
		while (buffer.size() < vec1.size() + (1 << vec2_bits))
			buffer.push_back(extend_left);

	std::vector<int> overflow_pattern_left(buffer.size(), extend_left);
	std::vector<int> overflow_pattern_right(buffer.size(), extend_right);

	buffer = vec_ite(overflow_left, overflow_pattern_left, buffer);

	if (vec2_signed)
		buffer = vec_ite(overflow_right, overflow_pattern_left, buffer);

	for (int i = vec2_bits-1; i >= 0; i--) {
		std::vector<int> shifted_buffer;
		if (vec2_signed && i == vec2_bits-1)
			shifted_buffer = vec_shift(buffer, -(1 << i), extend_left, extend_right);
		else
			shifted_buffer = vec_shift(buffer, 1 << i, extend_left, extend_right);
		buffer = vec_ite(vec2[i], shifted_buffer, buffer);
	}

	buffer.resize(vec1.size());
	return buffer;
}

std::vector<int> ezSAT::vec_shift_left(const std::vector<int> &vec1, const std::vector<int> &vec2, bool vec2_signed, int extend_left, int extend_right)
{
	// vec2_signed is not implemented in vec_shift_left() yet
	if (vec2_signed) assert(vec2_signed == false);

	int vec2_bits = std::min(my_clog2(vec1.size()), int(vec2.size()));

	std::vector<int> overflow_bits(vec2.begin() + vec2_bits, vec2.end());
	int overflow = vec_reduce_or(overflow_bits);

	std::vector<int> buffer = vec1;
	std::vector<int> overflow_pattern_right(buffer.size(), extend_right);
	buffer = vec_ite(overflow, overflow_pattern_right, buffer);

	for (int i = 0; i < vec2_bits; i++) {
		std::vector<int> shifted_buffer;
		shifted_buffer = vec_shift(buffer, -(1 << i), extend_left, extend_right);
		buffer = vec_ite(vec2[i], shifted_buffer, buffer);
	}

	buffer.resize(vec1.size());
	return buffer;
}

void ezSAT::vec_append(std::vector<int> &vec, const std::vector<int> &vec1) const
{
	for (auto bit : vec1)
		vec.push_back(bit);
}

void ezSAT::vec_append_signed(std::vector<int> &vec, const std::vector<int> &vec1, int64_t value)
{
	assert(int(vec1.size()) <= 64);
	for (int i = 0; i < int(vec1.size()); i++) {
		if (((value >> i) & 1) != 0)
			vec.push_back(vec1[i]);
		else
			vec.push_back(NOT(vec1[i]));
	}
}

void ezSAT::vec_append_unsigned(std::vector<int> &vec, const std::vector<int> &vec1, uint64_t value)
{
	assert(int(vec1.size()) <= 64);
	for (int i = 0; i < int(vec1.size()); i++) {
		if (((value >> i) & 1) != 0)
			vec.push_back(vec1[i]);
		else
			vec.push_back(NOT(vec1[i]));
	}
}

int64_t ezSAT::vec_model_get_signed(const std::vector<int> &modelExpressions, const std::vector<bool> &modelValues, const std::vector<int> &vec1) const
{
	int64_t value = 0;
	std::map<int, bool> modelMap;
	assert(modelExpressions.size() == modelValues.size());
	for (int i = 0; i < int(modelExpressions.size()); i++)
		modelMap[modelExpressions[i]] = modelValues[i];
	for (int i = 0; i < 64; i++) {
		int j = i < int(vec1.size()) ? i : vec1.size()-1;
		if (modelMap.at(vec1[j]))
			value |= int64_t(1) << i;
	}
	return value;
}

uint64_t ezSAT::vec_model_get_unsigned(const std::vector<int> &modelExpressions, const std::vector<bool> &modelValues, const std::vector<int> &vec1) const
{
	uint64_t value = 0;
	std::map<int, bool> modelMap;
	assert(modelExpressions.size() == modelValues.size());
	for (int i = 0; i < int(modelExpressions.size()); i++)
		modelMap[modelExpressions[i]] = modelValues[i];
	for (int i = 0; i < int(vec1.size()); i++)
		if (modelMap.at(vec1[i]))
			value |= uint64_t(1) << i;
	return value;
}

int ezSAT::vec_reduce_and(const std::vector<int> &vec1)
{
	return expression(OpAnd, vec1);
}

int ezSAT::vec_reduce_or(const std::vector<int> &vec1)
{
	return expression(OpOr, vec1);
}

void ezSAT::vec_set(const std::vector<int> &vec1, const std::vector<int> &vec2)
{
	assert(vec1.size() == vec2.size());
	for (int i = 0; i < int(vec1.size()); i++)
		SET(vec1[i], vec2[i]);
}

void ezSAT::vec_set_signed(const std::vector<int> &vec1, int64_t value)
{
	assert(int(vec1.size()) <= 64);
	for (int i = 0; i < int(vec1.size()); i++) {
		if (((value >> i) & 1) != 0)
			assume(vec1[i]);
		else
			assume(NOT(vec1[i]));
	}
}

void ezSAT::vec_set_unsigned(const std::vector<int> &vec1, uint64_t value)
{
	assert(int(vec1.size()) <= 64);
	for (int i = 0; i < int(vec1.size()); i++) {
		if (((value >> i) & 1) != 0)
			assume(vec1[i]);
		else
			assume(NOT(vec1[i]));
	}
}

ezSATbit ezSAT::bit(_V a)
{
	return ezSATbit(*this, a);
}

ezSATvec ezSAT::vec(const std::vector<int> &vec)
{
	return ezSATvec(*this, vec);
}

void ezSAT::printDIMACS(FILE *f, bool verbose) const
{
	if (cnfConsumed) {
		fprintf(stderr, "Usage error: printDIMACS() must not be called after cnfConsumed()!");
		abort();
	}

	int digits = ceil(log10f(cnfVariableCount)) + 2;

	fprintf(f, "c generated by ezSAT\n");

	if (verbose)
	{
		fprintf(f, "c\n");
		fprintf(f, "c mapping of variables to literals:\n");
		for (int i = 0; i < int(cnfLiteralVariables.size()); i++)
			if (cnfLiteralVariables[i] != 0)
				fprintf(f, "c %*d: %s\n", digits, cnfLiteralVariables[i], literals[i].c_str());

		fprintf(f, "c\n");
		fprintf(f, "c mapping of variables to expressions:\n");
		for (int i = 0; i < int(cnfExpressionVariables.size()); i++)
			if (cnfExpressionVariables[i] != 0)
				fprintf(f, "c %*d: %d\n", digits, cnfExpressionVariables[i], -i-1);

		if (mode_keep_cnf()) {
			fprintf(f, "c\n");
			fprintf(f, "c %d clauses from backup, %d from current buffer\n",
					int(cnfClausesBackup.size()), int(cnfClauses.size()));
		}

		fprintf(f, "c\n");
	}

	std::vector<std::vector<int>> all_clauses;
	getFullCnf(all_clauses);
	assert(cnfClausesCount == int(all_clauses.size()));

	fprintf(f, "p cnf %d %d\n", cnfVariableCount, cnfClausesCount);
	int maxClauseLen = 0;
	for (auto &clause : all_clauses)
		maxClauseLen = std::max(int(clause.size()), maxClauseLen);
	if (!verbose)
		maxClauseLen = std::min(maxClauseLen, 3);
	for (auto &clause : all_clauses) {
		for (auto idx : clause)
			fprintf(f, " %*d", digits, idx);
		if (maxClauseLen >= int(clause.size()))
			fprintf(f, " %*d\n", (digits + 1)*int(maxClauseLen - clause.size()) + digits, 0);
		else
			fprintf(f, " %*d\n", digits, 0);
	}
}

static std::string expression2str(const std::pair<ezSAT::OpId, std::vector<int>> &data)
{
	std::string text;
	switch (data.first) {
#define X(op) case ezSAT::op: text += #op; break;
		X(OpNot)
		X(OpAnd)
		X(OpOr)
		X(OpXor)
		X(OpIFF)
		X(OpITE)
	default:
		abort();
#undef X
	}
	text += ":";
	for (auto it : data.second)
		text += " " + my_int_to_string(it);
	return text;
}

void ezSAT::printInternalState(FILE *f) const
{
	fprintf(f, "--8<-- snip --8<--\n");

	fprintf(f, "literalsCache:\n");
	for (auto &it : literalsCache)
		fprintf(f, "    `%s' -> %d\n", it.first.c_str(), it.second);

	fprintf(f, "literals:\n");
	for (int i = 0; i < int(literals.size()); i++)
		fprintf(f, "    %d: `%s'\n", i+1, literals[i].c_str());

	fprintf(f, "expressionsCache:\n");
	for (auto &it : expressionsCache)
		fprintf(f, "    `%s' -> %d\n", expression2str(it.first).c_str(), it.second);

	fprintf(f, "expressions:\n");
	for (int i = 0; i < int(expressions.size()); i++)
		fprintf(f, "    %d: `%s'\n", -i-1, expression2str(expressions[i]).c_str());

	fprintf(f, "cnfVariables (count=%d):\n", cnfVariableCount);
	for (int i = 0; i < int(cnfLiteralVariables.size()); i++)
		if (cnfLiteralVariables[i] != 0)
			fprintf(f, "    literal %d -> %d (%s)\n", i+1, cnfLiteralVariables[i], to_string(i+1).c_str());
	for (int i = 0; i < int(cnfExpressionVariables.size()); i++)
		if (cnfExpressionVariables[i] != 0)
			fprintf(f, "    expression %d -> %d (%s)\n", -i-1, cnfExpressionVariables[i], to_string(-i-1).c_str());

	fprintf(f, "cnfClauses:\n");
	for (auto &i1 : cnfClauses) {
		for (auto &i2 : i1)
			fprintf(f, " %4d", i2);
		fprintf(f, "\n");
	}
	if (cnfConsumed)
		fprintf(f, " *** more clauses consumed via cnfConsume() ***\n");

	fprintf(f, "--8<-- snap --8<--\n");
}

static int clog2(int x)
{
	int y = (x & (x - 1));
	y = (y | -y) >> 31;

	x |= (x >> 1);
	x |= (x >> 2);
	x |= (x >> 4);
	x |= (x >> 8);
	x |= (x >> 16);

	x >>= 1;
	x -= ((x >> 1) & 0x55555555);
	x = (((x >> 2) & 0x33333333) + (x & 0x33333333));
	x = (((x >> 4) + x) & 0x0f0f0f0f);
	x += (x >> 8);
	x += (x >> 16);
	x = x & 0x0000003f;

	return x - y;
}

int ezSAT::onehot(const std::vector<int> &vec, bool max_only)
{
	// Mixed one-hot/binary encoding as described by Claessen in Sec. 4.2 of
	// "Successful SAT Encoding Techniques. Magnus Bjiirk. 25th July 2009".
	// http://jsat.ewi.tudelft.nl/addendum/Bjork_encoding.pdf

	std::vector<int> formula;

	// add at-leat-one constraint
	if (max_only == false)
		formula.push_back(expression(OpOr, vec));

	// create binary vector
	int num_bits = clog2(vec.size());
	std::vector<int> bits;
	for (int k = 0; k < num_bits; k++)
		bits.push_back(literal());

	// add at-most-one clauses using binary encoding
	for (size_t i = 0; i < vec.size(); i++)
		for (int k = 0; k < num_bits; k++) {
			std::vector<int> clause;
			clause.push_back(NOT(vec[i]));
			clause.push_back((i & (1 << k)) != 0 ? bits[k] : NOT(bits[k]));
			formula.push_back(expression(OpOr, clause));
		}

	return expression(OpAnd, formula);
}

int ezSAT::manyhot(const std::vector<int> &vec, int min_hot, int max_hot)
{
	// many-hot encoding using a simple sorting network

	if (max_hot < 0)
		max_hot = min_hot;

	std::vector<int> formula;
	int M = max_hot+1, N = vec.size();
	std::map<std::pair<int,int>, int> x;

	for (int i = -1; i < N; i++)
	for (int j = -1; j < M; j++)
		x[std::pair<int,int>(i,j)] = j < 0 ? CONST_TRUE : i < 0 ? CONST_FALSE : literal();

	for (int i = 0; i < N; i++)
	for (int j = 0; j < M; j++) {
		formula.push_back(OR(NOT(vec[i]), x[std::pair<int,int>(i-1,j-1)], NOT(x[std::pair<int,int>(i,j)])));
		formula.push_back(OR(NOT(vec[i]), NOT(x[std::pair<int,int>(i-1,j-1)]), x[std::pair<int,int>(i,j)]));
		formula.push_back(OR(vec[i], x[std::pair<int,int>(i-1,j)], NOT(x[std::pair<int,int>(i,j)])));
		formula.push_back(OR(vec[i], NOT(x[std::pair<int,int>(i-1,j)]), x[std::pair<int,int>(i,j)]));
#if 0
		// explicit resolution clauses -- in tests it was better to let the sat solver figure those out
		formula.push_back(OR(NOT(x[std::pair<int,int>(i-1,j-1)]), NOT(x[std::pair<int,int>(i-1,j)]), x[std::pair<int,int>(i,j)]));
		formula.push_back(OR(x[std::pair<int,int>(i-1,j-1)], x[std::pair<int,int>(i-1,j)], NOT(x[std::pair<int,int>(i,j)])));
#endif
	}

	for (int j = 0; j < M; j++) {
		if (j+1 <= min_hot)
			formula.push_back(x[std::pair<int,int>(N-1,j)]);
		else if (j+1 > max_hot)
			formula.push_back(NOT(x[std::pair<int,int>(N-1,j)]));
	}

	return expression(OpAnd, formula);
}

int ezSAT::ordered(const std::vector<int> &vec1, const std::vector<int> &vec2, bool allow_equal)
{
	std::vector<int> formula;
	int last_x = CONST_FALSE;

	assert(vec1.size() == vec2.size());
	for (size_t i = 0; i < vec1.size(); i++)
	{
		int a = vec1[i], b = vec2[i];
		formula.push_back(OR(NOT(a), b, last_x));

		int next_x = i+1 < vec1.size() ? literal() : allow_equal ? CONST_FALSE : CONST_TRUE;
		formula.push_back(OR(a, b, last_x, NOT(next_x)));
		formula.push_back(OR(NOT(a), NOT(b), last_x, NOT(next_x)));
		last_x = next_x;
	}

	return expression(OpAnd, formula);
}

