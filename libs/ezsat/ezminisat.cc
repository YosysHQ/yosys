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

#define __STDC_LIMIT_MACROS 1

#include "ezminisat.h"

#include <limits.h>
#include <stdint.h>
#include <cinttypes>

#include "minisat/core/Solver.h"

ezMiniSAT::ezMiniSAT() : minisatSolver(NULL)
{
	minisatSolver = NULL;
	foundContradiction = false;
}

ezMiniSAT::~ezMiniSAT()
{
	if (minisatSolver != NULL)
		delete minisatSolver;
}

void ezMiniSAT::clear()
{
	if (minisatSolver != NULL) {
		delete minisatSolver;
		minisatSolver = NULL;
	}
	foundContradiction = false;
	minisatVars.clear();
	ezSAT::clear();
}

bool ezMiniSAT::solver(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, const std::vector<int> &assumptions)
{
	if (0) {
contradiction:
		delete minisatSolver;
		minisatSolver = NULL;
		minisatVars.clear();
		foundContradiction = true;
		return false;
	}

	if (foundContradiction) {
		consumeCnf();
		return false;
	}

	std::vector<int> extraClauses, modelIdx;

	for (auto id : assumptions)
		extraClauses.push_back(bind(id));
	for (auto id : modelExpressions)
		modelIdx.push_back(bind(id));

	if (minisatSolver == NULL)
		minisatSolver = new Minisat::Solver;

	std::vector<std::vector<int>> cnf;
	consumeCnf(cnf);

	while (int(minisatVars.size()) < numCnfVariables())
		minisatVars.push_back(minisatSolver->newVar());

	for (auto &clause : cnf) {
		Minisat::vec<Minisat::Lit> ps;
		for (auto idx : clause)
			if (idx > 0)
				ps.push(Minisat::mkLit(minisatVars[idx-1]));
			else
				ps.push(Minisat::mkLit(minisatVars[-idx-1], true));
		if (!minisatSolver->addClause(ps))
			goto contradiction;
	}

	if (cnf.size() > 0 && !minisatSolver->simplify())
		goto contradiction;

	Minisat::vec<Minisat::Lit> assumps;

	for (auto idx : extraClauses)
		if (idx > 0)
			assumps.push(Minisat::mkLit(minisatVars[idx-1]));
		else
			assumps.push(Minisat::mkLit(minisatVars[-idx-1], true));

	if (!minisatSolver->solve(assumps))
		return false;

	modelValues.clear();
	modelValues.reserve(modelIdx.size());
	for (auto idx : modelIdx) {
		auto value = minisatSolver->modelValue(minisatVars[idx-1]);
		// FIXME: Undef values
		modelValues.push_back(value == Minisat::lbool(true));
	}

	return true;
}

