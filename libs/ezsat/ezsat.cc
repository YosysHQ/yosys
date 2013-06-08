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

#include <algorithm>

#include <stdlib.h>
#include <assert.h>

ezSAT::ezSAT()
{
	literal("TRUE");
	literal("FALSE");

	assert(literal("TRUE") == TRUE);
	assert(literal("FALSE") == FALSE);

	cnfConsumed = false;
	cnfVariableCount = 0;
	cnfClausesCount = 0;
}

ezSAT::~ezSAT()
{
}

int ezSAT::value(bool val)
{
	return val ? TRUE : FALSE;
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

	for (auto arg : args)
	{
		if (arg == 0)
			continue;
		if (op == OpAnd && arg == TRUE)
			continue;
		if ((op == OpOr || op == OpXor) && arg == FALSE)
			continue;
		if (op == OpXor && arg == TRUE) {
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
		if (myArgs[0] == TRUE)
			return FALSE;
		if (myArgs[0] == FALSE)
			return TRUE;
		break;

	case OpAnd:
		if (myArgs.size() == 0)
			return TRUE;
		if (myArgs.size() == 1)
			return myArgs[0];
		break;

	case OpOr:
		if (myArgs.size() == 0)
			return FALSE;
		if (myArgs.size() == 1)
			return myArgs[0];
		break;

	case OpXor:
		if (myArgs.size() == 0)
			return xorRemovedOddTrues ? TRUE : FALSE;
		if (myArgs.size() == 1)
			return xorRemovedOddTrues ? NOT(myArgs[0]) : myArgs[0];
		break;

	case OpIFF:
		assert(myArgs.size() >= 1);
		if (myArgs.size() == 1)
			return TRUE;
		// FIXME: Add proper const folding
		break;

	case OpITE:
		assert(myArgs.size() == 3);
		if (myArgs[0] == TRUE)
			return myArgs[1];
		if (myArgs[0] == FALSE)
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
		id = -(expressions.size() + 1);
		expressionsCache[myExpr] = id;
		expressions.push_back(myExpr);
	}

	return xorRemovedOddTrues ? NOT(id) : id;
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
		if (id <= int(values.size()) && (values[id-1] == TRUE || values[id-1] == FALSE || values[id-1] == 0))
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
		if (a == TRUE)
			return FALSE;
		if (a == FALSE)
			return TRUE;
		return 0;
	case OpAnd:
		a = TRUE;
		for (auto arg : args) {
			b = eval(arg, values);
			if (b != TRUE && b != FALSE)
				a = 0;
			if (b == FALSE)
				return FALSE;
		}
		return a;
	case OpOr:
		a = FALSE;
		for (auto arg : args) {
			b = eval(arg, values);
			if (b != TRUE && b != FALSE)
				a = 0;
			if (b == TRUE)
				return TRUE;
		}
		return a;
	case OpXor:
		a = FALSE;
		for (auto arg : args) {
			b = eval(arg, values);
			if (b != TRUE && b != FALSE)
				return 0;
			if (b == TRUE)
				a = a == TRUE ? FALSE : TRUE;
		}
		return a;
	case OpIFF:
		assert(args.size() > 0);
		a = eval(args[0], values);
		for (auto arg : args) {
			b = eval(arg, values);
			if (b != TRUE && b != FALSE)
				return 0;
			if (b != a)
				return FALSE;
		}
		return TRUE;
	case OpITE:
		assert(args.size() == 3);
		a = eval(args[0], values);
		if (a == TRUE)
			return eval(args[1], values);
		if (a == FALSE)
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
	cnfAssumptions.clear();
}

void ezSAT::assume(int id)
{
	cnfAssumptions.insert(id);

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

int ezSAT::bind(int id)
{
	if (id >= 0) {
		assert(0 < id && id <= int(literals.size()));
		cnfLiteralVariables.resize(literals.size());
		if (cnfLiteralVariables[id-1] == 0) {
			cnfLiteralVariables[id-1] = ++cnfVariableCount;
			if (id == TRUE)
				add_clause(+cnfLiteralVariables[id-1]);
			if (id == FALSE)
				add_clause(-cnfLiteralVariables[id-1]);
		}
		return cnfLiteralVariables[id-1];
	}

	assert(0 < -id && -id <= int(expressions.size()));
	cnfExpressionVariables.resize(expressions.size());

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
					if (i+1 == int(args.size()))
						newArgs.push_back(args[i]);
					else
						newArgs.push_back(OR(AND(args[i], NOT(args[i+1])), AND(NOT(args[i]), args[i+1])));
				args.swap(newArgs);
			}
			idx = bind(args.at(0));
			goto assign_idx;
		}

		if (op == OpIFF) {
			std::vector<int> invArgs;
			for (auto arg : args)
				invArgs.push_back(NOT(arg));
			idx = bind(OR(expression(OpAnd, args), expression(OpAnd, invArgs)));
			goto assign_idx;
		}

		if (op == OpITE) {
			idx = bind(OR(AND(args[0], args[1]), AND(NOT(args[0]), args[2])));
			goto assign_idx;
		}

		for (int i = 0; i < int(args.size()); i++)
			args[i] = bind(args[i]);

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
	cnfConsumed = true;
	cnfClauses.clear();
}

void ezSAT::consumeCnf(std::vector<std::vector<int>> &cnf)
{
	cnfConsumed = true;
	cnf.swap(cnfClauses);
	cnfClauses.clear();
}

static bool test_bit(uint32_t bitmask, int idx)
{
	if (idx > 0)
		return (bitmask & (1 << (+idx-1))) != 0;
	else
		return (bitmask & (1 << (-idx-1))) == 0;
}

bool ezSAT::solver(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, const std::vector<int> &assumptions)
{
	std::vector<int> extraClauses, modelIdx;
	std::vector<int> values(numLiterals());

	for (auto id : assumptions)
		extraClauses.push_back(bind(id));
	for (auto id : modelExpressions)
		modelIdx.push_back(bind(id));

	if (cnfVariableCount > 20) {
		fprintf(stderr, "*************************************************************************************\n");
		fprintf(stderr, "ERROR: You are trying to use the builtin solver of ezSAT with more than 20 variables!\n");
		fprintf(stderr, "The builtin solver is a  dumb  brute force solver  and only ment for testing and demo\n");
		fprintf(stderr, "purposes. Use a real SAT solve like MiniSAT (e.g. using the ezMiniSAT class) instead.\n");
		fprintf(stderr, "*************************************************************************************\n");
		abort();
	}

	for (uint32_t bitmask = 0; bitmask < (1 << numCnfVariables()); bitmask++)
	{
		// printf("%07o:", int(bitmask));
		// for (int i = 2; i < numLiterals(); i++)
		// 	if (bound(i+1))
		// 		printf(" %s=%d", to_string(i+1).c_str(), test_bit(bitmask, bound(i+1)));
		// printf(" |");
		// for (int idx = 1; idx <= numCnfVariables(); idx++)
		// 	printf(" %3d", test_bit(bitmask, idx) ? idx : -idx);
		// printf("\n");

		for (auto idx : extraClauses)
			if (!test_bit(bitmask, idx))
				goto next;

		for (auto &clause : cnfClauses) {
			for (auto idx : clause)
				if (test_bit(bitmask, idx))
					goto next_clause;
			// printf("failed clause:");
			// for (auto idx2 : clause)
			// 	printf(" %3d", idx2);
			// printf("\n");
			goto next;
		next_clause:;
			// printf("passed clause:");
			// for (auto idx2 : clause)
			// 	printf(" %3d", idx2);
			// printf("\n");
		}

		modelValues.resize(modelIdx.size());
		for (int i = 0; i < int(modelIdx.size()); i++)
			modelValues[i] = test_bit(bitmask, modelIdx[i]);

		// validate result using eval()

		values[0] = TRUE, values[1] = FALSE;
		for (int i = 2; i < numLiterals(); i++) {
			int idx = bound(i+1);
			values[i] = idx != 0 ? (test_bit(bitmask, idx) ? TRUE : FALSE) : 0;
		}

		for (auto id : cnfAssumptions) {
			int result = eval(id, values);
			if (result != TRUE) {
				printInternalState(stderr);
				fprintf(stderr, "Variables:");
				for (int i = 0; i < numLiterals(); i++)
					fprintf(stderr, " %s=%s", lookup_literal(i+1).c_str(), values[i] == TRUE ? "TRUE" : values[i] == FALSE ? "FALSE" : "UNDEF");
				fprintf(stderr, "\nValidation of solver results failed: got `%d' (%s) for assumption '%d': %s\n",
						result, result == FALSE ? "FALSE" : "UNDEF", id, to_string(id).c_str());
				abort();
			}
			// printf("OK: %d -> %d\n", id, result);
		}

		for (auto id : assumptions) {
			int result = eval(id, values);
			if (result != TRUE) {
				printInternalState(stderr);
				fprintf(stderr, "Variables:");
				for (int i = 0; i < numLiterals(); i++)
					fprintf(stderr, " %s=%s", lookup_literal(i+1).c_str(), values[i] == TRUE ? "TRUE" : values[i] == FALSE ? "FALSE" : "UNDEF");
				fprintf(stderr, "\nValidation of solver results failed: got `%d' (%s) for assumption '%d': %s\n",
						result, result == FALSE ? "FALSE" : "UNDEF", id, to_string(id).c_str());
				abort();
			}
			// printf("OK: %d -> %d\n", id, result);
		}

		return true;
	next:;
	}

	return false;
}

std::vector<int> ezSAT::vec_const_signed(int64_t value, int bits)
{
	std::vector<int> vec;
	for (int i = 0; i < bits; i++)
		vec.push_back(((value >> i) & 1) != 0 ? TRUE : FALSE);
	return vec;
}

std::vector<int> ezSAT::vec_const_unsigned(uint64_t value, int bits)
{
	std::vector<int> vec;
	for (int i = 0; i < bits; i++)
		vec.push_back(((value >> i) & 1) != 0 ? TRUE : FALSE);
	return vec;
}

std::vector<int> ezSAT::vec_var(std::string name, int bits)
{
	std::vector<int> vec;
	for (int i = 0; i < bits; i++)
		vec.push_back(VAR(name + "[" + std::to_string(i) + "]"));
	return vec;
}

std::vector<int> ezSAT::vec_cast(const std::vector<int> &vec1, int toBits, bool signExtend)
{
	std::vector<int> vec;
	for (int i = 0; i < toBits; i++)
		if (i >= int(vec1.size()))
			vec.push_back(signExtend ? vec1.back() : FALSE);
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

std::vector<int> ezSAT::vec_count(const std::vector<int> &vec, int bits, bool clip)
{
	std::vector<int> sum = vec_const_unsigned(0, bits);
	std::vector<int> carry_vector;

	for (auto bit : vec) {
		int carry = bit;
		for (int i = 0; i < bits; i++)
			halfadder(this, carry, sum[i], carry, sum[i]);
		carry_vector.push_back(carry);
	}

	if (clip) {
		int overflow = vec_reduce_or(carry_vector);
		sum = vec_ite(overflow, vec_const_unsigned(~0, bits), sum);
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
	int carry = FALSE;
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
	int carry = TRUE;
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

void ezSAT::vec_cmp(const std::vector<int> &vec1, const std::vector<int> &vec2, int &carry, int &overflow, int &sign, int &zero)
{
	assert(vec1.size() == vec2.size());
	carry = TRUE;
	zero = FALSE;
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
			vec.push_back(signExtend ? vec1.back() : FALSE);
		else if (0 <= j)
			vec.push_back(vec1[j]);
		else
			vec.push_back(FALSE);
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
			value |= 1 << i;
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
			value |= 1 << i;
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
				fprintf(f, "c %*d: %s\n", digits, cnfExpressionVariables[i], to_string(-i-1).c_str());

		fprintf(f, "c\n");
	}

	fprintf(f, "p cnf %d %d\n", cnfVariableCount, int(cnfClauses.size()));
	int maxClauseLen = 0;
	for (auto &clause : cnfClauses)
		maxClauseLen = std::max(int(clause.size()), maxClauseLen);
	for (auto &clause : cnfClauses) {
		for (auto idx : clause)
			fprintf(f, " %*d", digits, idx);
		fprintf(f, " %*d\n", (digits + 1)*int(maxClauseLen - clause.size()) + digits, 0);
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
		text += " " + std::to_string(it);
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
	int num_bits = ceil(log2(vec.size()));
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
		x[std::pair<int,int>(i,j)] = j < 0 ? TRUE : i < 0 ? FALSE : literal();

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
	int last_x = FALSE;

	assert(vec1.size() == vec2.size());
	for (size_t i = 0; i < vec1.size(); i++)
	{
		int a = vec1[i], b = vec2[i];
		formula.push_back(OR(NOT(a), b, last_x));

		int next_x = i+1 < vec1.size() ? literal() : allow_equal ? FALSE : TRUE;
		formula.push_back(OR(a, b, last_x, NOT(next_x)));
		formula.push_back(OR(NOT(a), NOT(b), last_x, NOT(next_x)));
		last_x = next_x;
	}

	return expression(OpAnd, formula);
}

