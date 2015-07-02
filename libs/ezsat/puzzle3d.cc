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
#include <assert.h>

#define DIM_X 5
#define DIM_Y 5
#define DIM_Z 5

#define NUM_124 6
#define NUM_223 6

ezMiniSAT ez;
int blockidx = 0;
std::map<int, std::string> blockinfo;
std::vector<int> grid[DIM_X][DIM_Y][DIM_Z];

struct blockgeom_t
{
	int center_x, center_y, center_z;
	int size_x, size_y, size_z;
	int var;

	void mirror_x() { center_x *= -1; }
	void mirror_y() { center_y *= -1; }
	void mirror_z() { center_z *= -1; }

	void rotate_x() { int tmp[4] = { center_y, center_z, size_y, size_z }; center_y = tmp[1]; center_z = -tmp[0]; size_y = tmp[3]; size_z = tmp[2]; }
	void rotate_y() { int tmp[4] = { center_x, center_z, size_x, size_z }; center_x = tmp[1]; center_z = -tmp[0]; size_x = tmp[3]; size_z = tmp[2]; }
	void rotate_z() { int tmp[4] = { center_x, center_y, size_x, size_y }; center_x = tmp[1]; center_y = -tmp[0]; size_x = tmp[3]; size_y = tmp[2]; }

	bool operator< (const blockgeom_t &other) const {
		if (center_x != other.center_x) return center_x < other.center_x;
		if (center_y != other.center_y) return center_y < other.center_y;
		if (center_z != other.center_z) return center_z < other.center_z;
		if (size_x != other.size_x) return size_x < other.size_x;
		if (size_y != other.size_y) return size_y < other.size_y;
		if (size_z != other.size_z) return size_z < other.size_z;
		if (var != other.var) return var < other.var;
		return false;
	}
};

// geometry data for spatial symmetry constraints
std::set<blockgeom_t> blockgeom;

int add_block(int pos_x, int pos_y, int pos_z, int size_x, int size_y, int size_z, int blockidx)
{
	char buffer[1024];
	snprintf(buffer, 1024, "block(%d,%d,%d,%d,%d,%d,%d);", size_x, size_y, size_z, pos_x, pos_y, pos_z, blockidx);

	int var = ez.literal();
	blockinfo[var] = buffer;

	for (int ix = pos_x; ix < pos_x+size_x; ix++)
	for (int iy = pos_y; iy < pos_y+size_y; iy++)
	for (int iz = pos_z; iz < pos_z+size_z; iz++)
		grid[ix][iy][iz].push_back(var);

	blockgeom_t bg;
	bg.size_x = 2*size_x;
	bg.size_y = 2*size_y;
	bg.size_z = 2*size_z;
	bg.center_x = (2*pos_x + size_x) - DIM_X;
	bg.center_y = (2*pos_y + size_y) - DIM_Y;
	bg.center_z = (2*pos_z + size_z) - DIM_Z;
	bg.var = var;

	assert(blockgeom.count(bg) == 0);
	blockgeom.insert(bg);

	return var;
}

void add_block_positions_124(std::vector<int> &block_positions_124)
{
	block_positions_124.clear();
	for (int size_x = 1; size_x <= 4; size_x *= 2)
	for (int size_y = 1; size_y <= 4; size_y *= 2)
	for (int size_z = 1; size_z <= 4; size_z *= 2) {
		if (size_x == size_y || size_y == size_z || size_z == size_x)
			continue;
		for (int ix = 0; ix <= DIM_X-size_x; ix++)
		for (int iy = 0; iy <= DIM_Y-size_y; iy++)
		for (int iz = 0; iz <= DIM_Z-size_z; iz++)
			block_positions_124.push_back(add_block(ix, iy, iz, size_x, size_y, size_z, blockidx++));
	}
}

void add_block_positions_223(std::vector<int> &block_positions_223)
{
	block_positions_223.clear();
	for (int orientation = 0; orientation < 3; orientation++) {
		int size_x = orientation == 0 ? 3 : 2;
		int size_y = orientation == 1 ? 3 : 2;
		int size_z = orientation == 2 ? 3 : 2;
		for (int ix = 0; ix <= DIM_X-size_x; ix++)
		for (int iy = 0; iy <= DIM_Y-size_y; iy++)
		for (int iz = 0; iz <= DIM_Z-size_z; iz++)
			block_positions_223.push_back(add_block(ix, iy, iz, size_x, size_y, size_z, blockidx++));
	}
}

// use simple built-in random number generator to
// ensure determinism of the program across platforms
uint32_t xorshift32() {
	static uint32_t x = 314159265;
	x ^= x << 13;
	x ^= x >> 17;
	x ^= x << 5;
	return x;
}

void condense_exclusives(std::vector<int> &vars)
{
	std::map<int, std::set<int>> exclusive;

	for (int ix = 0; ix < DIM_X; ix++)
	for (int iy = 0; iy < DIM_Y; iy++)
	for (int iz = 0; iz < DIM_Z; iz++) {
		for (int a : grid[ix][iy][iz])
		for (int b : grid[ix][iy][iz])
			if (a != b)
				exclusive[a].insert(b);
	}

	std::vector<std::vector<int>> pools;

	for (int a : vars)
	{
		std::vector<int> candidate_pools;
		for (size_t i = 0; i < pools.size(); i++)
		{
			for (int b : pools[i])
				if (exclusive[a].count(b) == 0)
					goto no_candidate_pool;
			candidate_pools.push_back(i);
		no_candidate_pool:;
		}

		if (candidate_pools.size() > 0) {
			int p = candidate_pools[xorshift32() % candidate_pools.size()];
			pools[p].push_back(a);
		} else {
			pools.push_back(std::vector<int>());
			pools.back().push_back(a);
		}
	}

	std::vector<int> new_vars;
	for (auto &pool : pools)
	{
		std::vector<int> formula;
		int var = ez.literal();

		for (int a : pool)
			formula.push_back(ez.OR(ez.NOT(a), var));
		formula.push_back(ez.OR(ez.expression(ezSAT::OpOr, pool), ez.NOT(var)));

		ez.assume(ez.onehot(pool, true));
		ez.assume(ez.expression(ezSAT::OpAnd, formula));
		new_vars.push_back(var);
	}

	printf("Condensed %d variables into %d one-hot pools.\n", int(vars.size()), int(new_vars.size()));
	vars.swap(new_vars);
}

int main()
{
	printf("\nCreating SAT encoding..\n");

	// add 1x2x4 blocks
	std::vector<int> block_positions_124;
	add_block_positions_124(block_positions_124);
	condense_exclusives(block_positions_124);
	ez.assume(ez.manyhot(block_positions_124, NUM_124));

	// add 2x2x3 blocks
	std::vector<int> block_positions_223;
	add_block_positions_223(block_positions_223);
	condense_exclusives(block_positions_223);
	ez.assume(ez.manyhot(block_positions_223, NUM_223));

	// add constraint for max one block per grid element
	for (int ix = 0; ix < DIM_X; ix++)
	for (int iy = 0; iy < DIM_Y; iy++)
	for (int iz = 0; iz < DIM_Z; iz++) {
		assert(grid[ix][iy][iz].size() > 0);
		ez.assume(ez.onehot(grid[ix][iy][iz], true));
	}

	printf("Found %d possible block positions.\n", int(blockgeom.size()));

	// look for spatial symmetries
	std::set<std::set<blockgeom_t>> symmetries;
	symmetries.insert(blockgeom);
	bool keep_running = true;
	while (keep_running) {
		keep_running = false;
		std::set<std::set<blockgeom_t>> old_sym;
		old_sym.swap(symmetries);
		for (auto &old_sym_set : old_sym)
		{
			std::set<blockgeom_t> mx, my, mz;
			std::set<blockgeom_t> rx, ry, rz;
			for (auto &bg : old_sym_set) {
				blockgeom_t bg_mx = bg, bg_my = bg, bg_mz = bg;
				blockgeom_t bg_rx = bg, bg_ry = bg, bg_rz = bg;
				bg_mx.mirror_x(), bg_my.mirror_y(), bg_mz.mirror_z();
				bg_rx.rotate_x(), bg_ry.rotate_y(), bg_rz.rotate_z();
				mx.insert(bg_mx), my.insert(bg_my), mz.insert(bg_mz);
				rx.insert(bg_rx), ry.insert(bg_ry), rz.insert(bg_rz);
			}
			if (!old_sym.count(mx) || !old_sym.count(my) || !old_sym.count(mz) ||
					!old_sym.count(rx) || !old_sym.count(ry) || !old_sym.count(rz))
				keep_running = true;
			symmetries.insert(old_sym_set);
			symmetries.insert(mx);
			symmetries.insert(my);
			symmetries.insert(mz);
			symmetries.insert(rx);
			symmetries.insert(ry);
			symmetries.insert(rz);
		}
	}

	// add constraints to eliminate all the spatial symmetries
	std::vector<std::vector<int>> vecvec;
	for (auto &sym : symmetries) {
		std::vector<int> vec;
		for (auto &bg : sym)
			vec.push_back(bg.var);
		vecvec.push_back(vec);
	}
	for (size_t i = 1; i < vecvec.size(); i++)
		ez.assume(ez.ordered(vecvec[0], vecvec[1]));

	printf("Found and eliminated %d spatial symmetries.\n", int(symmetries.size()));
	printf("Generated %d clauses over %d variables.\n", ez.numCnfClauses(), ez.numCnfVariables());

	std::vector<int> modelExpressions;
	std::vector<bool> modelValues;

	for (auto &it : blockinfo) {
		ez.freeze(it.first);
		modelExpressions.push_back(it.first);
	}

	int solution_counter = 0;
	while (1)
	{
		printf("\nSolving puzzle..\n");
		bool ok = ez.solve(modelExpressions, modelValues);

		if (!ok) {
			printf("No more solutions found!\n");
			break;
		}

		printf("Puzzle solution:\n");
		std::vector<int> constraint;
		for (size_t i = 0; i < modelExpressions.size(); i++)
			if (modelValues[i]) {
				constraint.push_back(ez.NOT(modelExpressions[i]));
				printf("%s\n", blockinfo.at(modelExpressions[i]).c_str());
			}
		ez.assume(ez.expression(ezSAT::OpOr, constraint));
		solution_counter++;
	}

	printf("\nFound %d distinct solutions.\n", solution_counter);
	printf("Have a nice day.\n\n");

	return 0;
}

