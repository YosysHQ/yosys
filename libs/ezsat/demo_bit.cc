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

void print_results(bool satisfiable, const std::vector<bool> &modelValues)
{
	if (!satisfiable) {
		printf("not satisfiable.\n\n");
	} else {
		printf("satisfiable:");
		for (auto val : modelValues)
			printf(" %d", val ? 1 : 0);
		printf("\n\n");
	}
}

int main()
{
	ezMiniSAT sat;

	// 3 input AOI-Gate
	// 'pos_active' encodes the condition under which the pullup path of the gate is active
	// 'neg_active' encodes the condition under which the pulldown path of the gate is active
	// 'impossible' encodes the condition that both or none of the above paths is active
	int pos_active = sat.AND(sat.NOT("A"), sat.OR(sat.NOT("B"), sat.NOT("C")));
	int neg_active = sat.OR("A", sat.AND("B", "C"));
	int impossible = sat.IFF(pos_active, neg_active);

	std::vector<int> modelVars;
	std::vector<bool> modelValues;
	bool satisfiable;

	modelVars.push_back(sat.VAR("A"));
	modelVars.push_back(sat.VAR("B"));
	modelVars.push_back(sat.VAR("C"));

	printf("\n");

	printf("pos_active: %s\n", sat.to_string(pos_active).c_str());
	satisfiable = sat.solve(modelVars, modelValues, pos_active);
	print_results(satisfiable, modelValues);

	printf("neg_active: %s\n", sat.to_string(neg_active).c_str());
	satisfiable = sat.solve(modelVars, modelValues, neg_active);
	print_results(satisfiable, modelValues);

	printf("impossible: %s\n", sat.to_string(impossible).c_str());
	satisfiable = sat.solve(modelVars, modelValues, impossible);
	print_results(satisfiable, modelValues);

	return 0;
}

