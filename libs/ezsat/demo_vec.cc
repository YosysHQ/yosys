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

void xorshift128_sat(ezSAT &sat, std::vector<int> &x, std::vector<int> &y, std::vector<int> &z, std::vector<int> &w)
{
	std::vector<int> t = sat.vec_xor(x, sat.vec_shl(x, 11));
	x = y; y = z; z = w;
	w = sat.vec_xor(sat.vec_xor(w, sat.vec_shr(w, 19)), sat.vec_xor(t, sat.vec_shr(t, 8)));
}

void find_xorshift128_init_state(uint32_t &x, uint32_t &y, uint32_t &z, uint32_t &w, uint32_t w1, uint32_t w2, uint32_t w3, uint32_t w4)
{
	ezMiniSAT sat;

	std::vector<int> vx = sat.vec_var("x", 32);
	std::vector<int> vy = sat.vec_var("y", 32);
	std::vector<int> vz = sat.vec_var("z", 32);
	std::vector<int> vw = sat.vec_var("w", 32);

	xorshift128_sat(sat, vx, vy, vz, vw);
	sat.vec_set_unsigned(vw, w1);

	xorshift128_sat(sat, vx, vy, vz, vw);
	sat.vec_set_unsigned(vw, w2);

	xorshift128_sat(sat, vx, vy, vz, vw);
	sat.vec_set_unsigned(vw, w3);

	xorshift128_sat(sat, vx, vy, vz, vw);
	sat.vec_set_unsigned(vw, w4);

	std::vector<int> modelExpressions;
	std::vector<bool> modelValues;

	sat.vec_append(modelExpressions, sat.vec_var("x", 32));
	sat.vec_append(modelExpressions, sat.vec_var("y", 32));
	sat.vec_append(modelExpressions, sat.vec_var("z", 32));
	sat.vec_append(modelExpressions, sat.vec_var("w", 32));

	// sat.printDIMACS(stdout);

	if (!sat.solve(modelExpressions, modelValues)) {
		fprintf(stderr, "SAT solver failed to find a model!\n");
		abort();
	}

	x = sat.vec_model_get_unsigned(modelExpressions, modelValues, sat.vec_var("x", 32));
	y = sat.vec_model_get_unsigned(modelExpressions, modelValues, sat.vec_var("y", 32));
	z = sat.vec_model_get_unsigned(modelExpressions, modelValues, sat.vec_var("z", 32));
	w = sat.vec_model_get_unsigned(modelExpressions, modelValues, sat.vec_var("w", 32));
}

int main()
{
	uint32_t w1 = xorshift128();
	uint32_t w2 = xorshift128();
	uint32_t w3 = xorshift128();
	uint32_t w4 = xorshift128();
	uint32_t x, y, z, w;

	printf("\n");

	find_xorshift128_init_state(x, y, z, w, w1, w2, w3, w4);

	printf("x = %9u (%s)\n", (unsigned int)x, x == INIT_X ? "ok" : "ERROR");
	printf("y = %9u (%s)\n", (unsigned int)y, y == INIT_Y ? "ok" : "ERROR");
	printf("z = %9u (%s)\n", (unsigned int)z, z == INIT_Z ? "ok" : "ERROR");
	printf("w = %9u (%s)\n", (unsigned int)w, w == INIT_W ? "ok" : "ERROR");

	if (x != INIT_X || y != INIT_Y || z != INIT_Z || w != INIT_W)
		abort();

	printf("\n");

	return 0;
}

