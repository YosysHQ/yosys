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
#include <signal.h>
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

ezMiniSAT *ezMiniSAT::alarmHandlerThis = NULL;
clock_t ezMiniSAT::alarmHandlerTimeout = 0;

void ezMiniSAT::alarmHandler(int)
{
	if (clock() > alarmHandlerTimeout) {
		alarmHandlerThis->minisatSolver->interrupt();
		alarmHandlerTimeout = 0;
	} else
		alarm(1);
}

bool ezMiniSAT::solver(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, const std::vector<int> &assumptions)
{
	solverTimoutStatus = false;

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
				ps.push(Minisat::mkLit(minisatVars.at(idx-1)));
			else
				ps.push(Minisat::mkLit(minisatVars.at(-idx-1), true));
		if (!minisatSolver->addClause(ps))
			goto contradiction;
	}

	if (cnf.size() > 0 && !minisatSolver->simplify())
		goto contradiction;

	Minisat::vec<Minisat::Lit> assumps;

	for (auto idx : extraClauses)
		if (idx > 0)
			assumps.push(Minisat::mkLit(minisatVars.at(idx-1)));
		else
			assumps.push(Minisat::mkLit(minisatVars.at(-idx-1), true));

	sighandler_t old_alarm_sighandler;
	int old_alarm_timeout;

	if (solverTimeout > 0) {
		alarmHandlerThis = this;
		alarmHandlerTimeout = clock() + solverTimeout*CLOCKS_PER_SEC;
		old_alarm_timeout = alarm(0);
		old_alarm_sighandler = signal(SIGALRM, alarmHandler);
		alarm(1);
	}

	bool foundSolution = minisatSolver->solve(assumps);

	if (solverTimeout > 0) {
		if (alarmHandlerTimeout == 0)
			solverTimoutStatus = true;
		alarm(0);
		signal(SIGALRM, old_alarm_sighandler);
		alarm(old_alarm_timeout);
	}

	if (!foundSolution)
		return false;

	modelValues.clear();
	modelValues.resize(2 * modelIdx.size());

	for (size_t i = 0; i < modelIdx.size(); i++)
	{
		int idx = modelIdx[i];
		bool refvalue = true;

		if (idx < 0)
			idx = -idx, refvalue = false;

		using namespace Minisat;
		lbool value = minisatSolver->modelValue(minisatVars.at(idx-1));
		if (value == l_Undef) {
			modelValues[i] = false;
			modelValues[modelIdx.size() + i] = true;
		} else {
			modelValues[i] = value == Minisat::lbool(refvalue);
			modelValues[modelIdx.size() + i] = false;
		}
	}

	return true;
}

