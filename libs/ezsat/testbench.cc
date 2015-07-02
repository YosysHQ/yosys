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

#include "ezminisat.h"
#include <stdio.h>

struct xorshift128 {
	uint32_t x, y, z, w;
	xorshift128() {
		x = 123456789;
		y = 362436069;
		z = 521288629;
		w = 88675123;
	}
	uint32_t operator()() {
		uint32_t t = x ^ (x << 11);
		x = y; y = z; z = w;
		w ^= (w >> 19) ^ t ^ (t >> 8);
		return w;
	}
};

bool test(ezSAT &sat, int assumption = 0)
{
	std::vector<int> modelExpressions;
	std::vector<bool> modelValues;

	for (int id = 1; id <= sat.numLiterals(); id++)
		if (sat.bound(id))
			modelExpressions.push_back(id);

	if (sat.solve(modelExpressions, modelValues, assumption)) {
		printf("satisfiable:");
		for (int i = 0; i < int(modelExpressions.size()); i++)
			printf(" %s=%d", sat.to_string(modelExpressions[i]).c_str(), int(modelValues[i]));
		printf("\n\n");
		return true;
	} else {
		printf("not satisfiable.\n\n");
		return false;
	}
}

// ------------------------------------------------------------------------------------------------------------

void test_simple()
{
	printf("==== %s ====\n\n", __PRETTY_FUNCTION__);

	ezMiniSAT sat;
	sat.non_incremental();
	sat.assume(sat.OR("A", "B"));
	sat.assume(sat.NOT(sat.AND("A", "B")));
	test(sat);
}

// ------------------------------------------------------------------------------------------------------------

void test_xorshift32_try(ezSAT &sat, uint32_t input_pattern)
{
	uint32_t output_pattern = input_pattern;
	output_pattern ^= output_pattern << 13;
	output_pattern ^= output_pattern >> 17;
	output_pattern ^= output_pattern << 5;

	std::vector<int> modelExpressions;
	std::vector<int> forwardAssumptions, backwardAssumptions;
	std::vector<bool> forwardModel, backwardModel;

	sat.vec_append(modelExpressions, sat.vec_var("i", 32));
	sat.vec_append(modelExpressions, sat.vec_var("o", 32));

	sat.vec_append_unsigned(forwardAssumptions,  sat.vec_var("i", 32), input_pattern);
	sat.vec_append_unsigned(backwardAssumptions,  sat.vec_var("o", 32), output_pattern);

	if (!sat.solve(modelExpressions, backwardModel, backwardAssumptions)) {
		printf("backward solving failed!\n");
		abort();
	}

	if (!sat.solve(modelExpressions, forwardModel, forwardAssumptions)) {
		printf("forward solving failed!\n");
		abort();
	}

	printf("xorshift32 test with input pattern 0x%08x:\n", input_pattern);

	printf("forward  solution: input=0x%08x output=0x%08x\n",
			(unsigned int)sat.vec_model_get_unsigned(modelExpressions, forwardModel, sat.vec_var("i", 32)),
			(unsigned int)sat.vec_model_get_unsigned(modelExpressions, forwardModel, sat.vec_var("o", 32)));

	printf("backward solution: input=0x%08x output=0x%08x\n",
			(unsigned int)sat.vec_model_get_unsigned(modelExpressions, backwardModel, sat.vec_var("i", 32)),
			(unsigned int)sat.vec_model_get_unsigned(modelExpressions, backwardModel, sat.vec_var("o", 32)));

	if (forwardModel != backwardModel) {
		printf("forward and backward results are inconsistend!\n");
		abort();
	}

	printf("passed.\n\n");
}

void test_xorshift32()
{
	printf("==== %s ====\n\n", __PRETTY_FUNCTION__);

	ezMiniSAT sat;
	sat.keep_cnf();

	xorshift128 rng;

	std::vector<int> bits = sat.vec_var("i", 32);

	bits = sat.vec_xor(bits, sat.vec_shl(bits, 13));
	bits = sat.vec_xor(bits, sat.vec_shr(bits, 17));
	bits = sat.vec_xor(bits, sat.vec_shl(bits,  5));

	sat.vec_set(bits, sat.vec_var("o", 32));

	test_xorshift32_try(sat, 0);
	test_xorshift32_try(sat, 314159265);
	test_xorshift32_try(sat, rng());
	test_xorshift32_try(sat, rng());
	test_xorshift32_try(sat, rng());
	test_xorshift32_try(sat, rng());

	sat.printDIMACS(stdout, true);
	printf("\n");
}

// ------------------------------------------------------------------------------------------------------------

#define CHECK(_expr1, _expr2) check(#_expr1, _expr1, #_expr2, _expr2)

void check(const char *expr1_str, bool expr1, const char *expr2_str, bool expr2)
{
	if (expr1 == expr2) {
		printf("[ %s ] == [ %s ] .. ok (%s == %s)\n", expr1_str, expr2_str, expr1 ? "true" : "false", expr2 ? "true" : "false");
	} else {
		printf("[ %s ] != [ %s ] .. ERROR (%s != %s)\n", expr1_str, expr2_str, expr1 ? "true" : "false", expr2 ? "true" : "false");
		abort();
	}
}

void test_signed(int8_t a, int8_t b, int8_t c)
{
	ezMiniSAT sat;

	std::vector<int> av = sat.vec_const_signed(a, 8);
	std::vector<int> bv = sat.vec_const_signed(b, 8);
	std::vector<int> cv = sat.vec_const_signed(c, 8);

	printf("Testing signed arithmetic using: a=%+d, b=%+d, c=%+d\n", int(a), int(b), int(c));

	CHECK(a <  b+c, sat.solve(sat.vec_lt_signed(av, sat.vec_add(bv, cv))));
	CHECK(a <= b-c, sat.solve(sat.vec_le_signed(av, sat.vec_sub(bv, cv))));

	CHECK(a >  b+c, sat.solve(sat.vec_gt_signed(av, sat.vec_add(bv, cv))));
	CHECK(a >= b-c, sat.solve(sat.vec_ge_signed(av, sat.vec_sub(bv, cv))));

	printf("\n");
}

void test_unsigned(uint8_t a, uint8_t b, uint8_t c)
{
	ezMiniSAT sat;

	if (b < c)
		b ^= c, c ^= b, b ^= c;

	std::vector<int> av = sat.vec_const_unsigned(a, 8);
	std::vector<int> bv = sat.vec_const_unsigned(b, 8);
	std::vector<int> cv = sat.vec_const_unsigned(c, 8);

	printf("Testing unsigned arithmetic using: a=%d, b=%d, c=%d\n", int(a), int(b), int(c));

	CHECK(a <  b+c, sat.solve(sat.vec_lt_unsigned(av, sat.vec_add(bv, cv))));
	CHECK(a <= b-c, sat.solve(sat.vec_le_unsigned(av, sat.vec_sub(bv, cv))));

	CHECK(a >  b+c, sat.solve(sat.vec_gt_unsigned(av, sat.vec_add(bv, cv))));
	CHECK(a >= b-c, sat.solve(sat.vec_ge_unsigned(av, sat.vec_sub(bv, cv))));

	printf("\n");
}

void test_count(uint32_t x)
{
	ezMiniSAT sat;

	int count = 0;
	for (int i = 0; i < 32; i++)
		if (((x >> i) & 1) != 0)
			count++;

	printf("Testing bit counting using x=0x%08x (%d set bits) .. ", x, count);

	std::vector<int> v = sat.vec_const_unsigned(x, 32);

	std::vector<int> cv6 = sat.vec_const_unsigned(count, 6);
	std::vector<int> cv4 = sat.vec_const_unsigned(count <= 15 ? count : 15, 4);

	if (cv6 != sat.vec_count(v, 6, false)) {
		fprintf(stderr, "FAILED 6bit-no-clipping test!\n");
		abort();
	}

	if (cv4 != sat.vec_count(v, 4, true)) {
		fprintf(stderr, "FAILED 4bit-clipping test!\n");
		abort();
	}

	printf("ok.\n");
}

void test_arith()
{
	printf("==== %s ====\n\n", __PRETTY_FUNCTION__);

	xorshift128 rng;

	for (int i = 0; i < 100; i++)
		test_signed(rng() % 19 - 10, rng() % 19 - 10, rng() % 19 - 10);

	for (int i = 0; i < 100; i++)
		test_unsigned(rng() % 10, rng() % 10, rng() % 10);

	test_count(0x00000000);
	test_count(0xffffffff);
	for (int i = 0; i < 30; i++)
		test_count(rng());

	printf("\n");
}

// ------------------------------------------------------------------------------------------------------------

void test_onehot()
{
	printf("==== %s ====\n\n", __PRETTY_FUNCTION__);
	ezMiniSAT ez;

	int a = ez.frozen_literal("a");
	int b = ez.frozen_literal("b");
	int c = ez.frozen_literal("c");
	int d = ez.frozen_literal("d");

	std::vector<int> abcd;
	abcd.push_back(a);
	abcd.push_back(b);
	abcd.push_back(c);
	abcd.push_back(d);

	ez.assume(ez.onehot(abcd));

	int solution_counter = 0;
	while (1)
	{
		std::vector<bool> modelValues;
		bool ok = ez.solve(abcd, modelValues);

		if (!ok)
			break;

		printf("Solution: %d %d %d %d\n", int(modelValues[0]), int(modelValues[1]), int(modelValues[2]), int(modelValues[3]));

		int count_hot = 0;
		std::vector<int> sol;
		for (int i = 0; i < 4; i++) {
			if (modelValues[i])
				count_hot++;
			sol.push_back(modelValues[i] ? abcd[i] : ez.NOT(abcd[i]));
		}
		ez.assume(ez.NOT(ez.expression(ezSAT::OpAnd, sol)));

		if (count_hot != 1) {
			fprintf(stderr, "Wrong number of hot bits!\n");
			abort();
		}

		solution_counter++;
	}

	if (solution_counter != 4) {
		fprintf(stderr, "Wrong number of one-hot solutions!\n");
		abort();
	}

	printf("\n");
}

void test_manyhot()
{
	printf("==== %s ====\n\n", __PRETTY_FUNCTION__);
	ezMiniSAT ez;

	int a = ez.frozen_literal("a");
	int b = ez.frozen_literal("b");
	int c = ez.frozen_literal("c");
	int d = ez.frozen_literal("d");

	std::vector<int> abcd;
	abcd.push_back(a);
	abcd.push_back(b);
	abcd.push_back(c);
	abcd.push_back(d);

	ez.assume(ez.manyhot(abcd, 1, 2));

	int solution_counter = 0;
	while (1)
	{
		std::vector<bool> modelValues;
		bool ok = ez.solve(abcd, modelValues);

		if (!ok)
			break;

		printf("Solution: %d %d %d %d\n", int(modelValues[0]), int(modelValues[1]), int(modelValues[2]), int(modelValues[3]));

		int count_hot = 0;
		std::vector<int> sol;
		for (int i = 0; i < 4; i++) {
			if (modelValues[i])
				count_hot++;
			sol.push_back(modelValues[i] ? abcd[i] : ez.NOT(abcd[i]));
		}
		ez.assume(ez.NOT(ez.expression(ezSAT::OpAnd, sol)));

		if (count_hot != 1 && count_hot != 2) {
			fprintf(stderr, "Wrong number of hot bits!\n");
			abort();
		}

		solution_counter++;
	}

	if (solution_counter != 4 + 4*3/2) {
		fprintf(stderr, "Wrong number of one-hot solutions!\n");
		abort();
	}

	printf("\n");
}

void test_ordered()
{
	printf("==== %s ====\n\n", __PRETTY_FUNCTION__);
	ezMiniSAT ez;

	int a = ez.frozen_literal("a");
	int b = ez.frozen_literal("b");
	int c = ez.frozen_literal("c");

	int x = ez.frozen_literal("x");
	int y = ez.frozen_literal("y");
	int z = ez.frozen_literal("z");

	std::vector<int> abc;
	abc.push_back(a);
	abc.push_back(b);
	abc.push_back(c);

	std::vector<int> xyz;
	xyz.push_back(x);
	xyz.push_back(y);
	xyz.push_back(z);

	ez.assume(ez.ordered(abc, xyz));

	int solution_counter = 0;

	while (1)
	{
		std::vector<int> modelVariables;
		std::vector<bool> modelValues;

		modelVariables.push_back(a);
		modelVariables.push_back(b);
		modelVariables.push_back(c);

		modelVariables.push_back(x);
		modelVariables.push_back(y);
		modelVariables.push_back(z);

		bool ok = ez.solve(modelVariables, modelValues);

		if (!ok)
			break;

		printf("Solution: %d %d %d | %d %d %d\n",
				int(modelValues[0]), int(modelValues[1]), int(modelValues[2]),
				int(modelValues[3]), int(modelValues[4]), int(modelValues[5]));

		std::vector<int> sol;
		for (size_t i = 0; i < modelVariables.size(); i++)
			sol.push_back(modelValues[i] ? modelVariables[i] : ez.NOT(modelVariables[i]));
		ez.assume(ez.NOT(ez.expression(ezSAT::OpAnd, sol)));

		solution_counter++;
	}

	if (solution_counter != 8+7+6+5+4+3+2+1) {
		fprintf(stderr, "Wrong number of solutions!\n");
		abort();
	}

	printf("\n");
}

// ------------------------------------------------------------------------------------------------------------


int main()
{
	test_simple();
	test_xorshift32();
	test_arith();
	test_onehot();
	test_manyhot();
	test_ordered();
	printf("Passed all tests.\n\n");
	return 0;
}

