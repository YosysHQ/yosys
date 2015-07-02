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
#include <assert.h>

#define INIT_X 123456789
#define INIT_Y 362436069
#define INIT_Z 521288629
#define INIT_W  88675123

uint32_t xorshift128() {
	static uint32_t x = INIT_X;
	static uint32_t y = INIT_Y;
	static uint32_t z = INIT_Z;
	static uint32_t w = INIT_W;
	uint32_t t = x ^ (x << 11);
	x = y; y = z; z = w;
	w ^= (w >> 19) ^ t ^ (t >> 8);
	return w;
}

void test_cmp(uint32_t a, uint32_t b)
{
	ezMiniSAT sat;

	printf("A = %10u (%10d)\n", a, int32_t(a));
	printf("B = %10u (%10d)\n", b, int32_t(b));
	printf("\n");

	std::vector<int> va = sat.vec_var("a", 32);
	std::vector<int> vb = sat.vec_var("b", 32);

	sat.vec_set_unsigned(va, a);
	sat.vec_set_unsigned(vb, b);

#define MONITOR_VARS \
	X(carry) X(overflow) X(sign) X(zero) \
	X(lt_signed) X(le_signed) X(ge_signed) X(gt_signed) \
	X(lt_unsigned) X(le_unsigned) X(ge_unsigned) X(gt_unsigned)

#define X(_n) int _n; bool _n ## _master;
	MONITOR_VARS
#undef X

	carry_master = ((uint64_t(a) - uint64_t(b)) >> 32) & 1;
	overflow_master = (int32_t(a) - int32_t(b)) != (int64_t(int32_t(a)) - int64_t(int32_t(b)));
	sign_master = ((a - b) >> 31) & 1;
	zero_master = a == b;

	sat.vec_cmp(va, vb, carry, overflow, sign, zero);

	lt_signed_master = int32_t(a) <  int32_t(b);
	le_signed_master = int32_t(a) <= int32_t(b);
	ge_signed_master = int32_t(a) >= int32_t(b);
	gt_signed_master = int32_t(a) >  int32_t(b);

	lt_unsigned_master = a <  b;
	le_unsigned_master = a <= b;
	ge_unsigned_master = a >= b;
	gt_unsigned_master = a >  b;

	lt_signed = sat.vec_lt_signed(va, vb);
	le_signed = sat.vec_le_signed(va, vb);
	ge_signed = sat.vec_ge_signed(va, vb);
	gt_signed = sat.vec_gt_signed(va, vb);

	lt_unsigned = sat.vec_lt_unsigned(va, vb);
	le_unsigned = sat.vec_le_unsigned(va, vb);
	ge_unsigned = sat.vec_ge_unsigned(va, vb);
	gt_unsigned = sat.vec_gt_unsigned(va, vb);

	std::vector<int> modelExpressions;
	std::vector<bool> modelValues, modelMaster;
	std::vector<std::string> modelNames;

#define X(_n) modelExpressions.push_back(_n); modelNames.push_back(#_n); modelMaster.push_back(_n ## _master);
	MONITOR_VARS
#undef X

	std::vector<int> add_ab = sat.vec_add(va, vb);
	std::vector<int> sub_ab = sat.vec_sub(va, vb);
	std::vector<int> sub_ba = sat.vec_sub(vb, va);

	sat.vec_append(modelExpressions, add_ab);
	sat.vec_append(modelExpressions, sub_ab);
	sat.vec_append(modelExpressions, sub_ba);

	if (!sat.solve(modelExpressions, modelValues)) {
		fprintf(stderr, "SAT solver failed to find a model!\n");
		abort();
	}

	bool found_error = false;

	for (size_t i = 0; i < modelMaster.size(); i++) {
		if (modelMaster.at(i) != int(modelValues.at(i)))
			found_error = true;
		printf("%-20s %d%s\n", modelNames.at(i).c_str(), int(modelValues.at(i)),
				modelMaster.at(i) != modelValues.at(i) ? "   !!!" : "");
	}
	printf("\n");

	uint32_t add_ab_value = sat.vec_model_get_unsigned(modelExpressions, modelValues, add_ab);
	uint32_t sub_ab_value = sat.vec_model_get_unsigned(modelExpressions, modelValues, sub_ab);
	uint32_t sub_ba_value = sat.vec_model_get_unsigned(modelExpressions, modelValues, sub_ba);

	printf("%-20s %10u %10u%s\n", "result(a+b)", add_ab_value, a+b, add_ab_value != a+b ? "   !!!" : "");
	printf("%-20s %10u %10u%s\n", "result(a-b)", sub_ab_value, a-b, sub_ab_value != a-b ? "   !!!" : "");
	printf("%-20s %10u %10u%s\n", "result(b-a)", sub_ba_value, b-a, sub_ba_value != b-a ? "   !!!" : "");
	printf("\n");

	if (found_error || add_ab_value != a+b || sub_ab_value != a-b || sub_ba_value != b-a)
		abort();
}

int main()
{
	printf("\n");
	for (int i = 0; i < 1024; i++) {
		printf("************** %d **************\n\n", i);
		uint32_t a = xorshift128();
		uint32_t b = xorshift128();
		if (xorshift128() % 16 == 0)
			a = b;
		test_cmp(a, b);
	}
	return 0;
}

