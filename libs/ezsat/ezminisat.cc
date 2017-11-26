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

// needed for MiniSAT headers (see Minisat Makefile)
#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif
#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS
#endif

#include "ezminisat.h"

#include <limits.h>
#include <stdint.h>
#include <csignal>
#include <cinttypes>

#ifndef _WIN32
#  include <unistd.h>
#endif

#include "../minisat/Solver.h"
#include "../minisat/SimpSolver.h"

ezMiniSAT::ezMiniSAT() : minisatSolver(NULL)
{
	minisatSolver = NULL;
	foundContradiction = false;

	freeze(CONST_TRUE);
	freeze(CONST_FALSE);
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
#if EZMINISAT_SIMPSOLVER && EZMINISAT_INCREMENTAL
	cnfFrozenVars.clear();
#endif
	ezSAT::clear();
}

#if EZMINISAT_SIMPSOLVER && EZMINISAT_INCREMENTAL
void ezMiniSAT::freeze(int id)
{
	if (!mode_non_incremental())
		cnfFrozenVars.insert(bind(id));
}

bool ezMiniSAT::eliminated(int idx)
{
	idx = idx < 0 ? -idx : idx;
	if (minisatSolver != NULL && idx > 0 && idx <= int(minisatVars.size()))
		return minisatSolver->isEliminated(minisatVars.at(idx-1));
	return false;
}
#endif

#ifndef _WIN32
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
#endif

bool ezMiniSAT::solver(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, const std::vector<int> &assumptions)
{
	preSolverCallback();

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

	if (minisatSolver == NULL) {
		minisatSolver = new Solver;
		minisatSolver->verbosity = EZMINISAT_VERBOSITY;
	}

#if EZMINISAT_INCREMENTAL
	std::vector<std::vector<int>> cnf;
	consumeCnf(cnf);
#else
	const std::vector<std::vector<int>> &cnf = this->cnf();
#endif

	while (int(minisatVars.size()) < numCnfVariables())
		minisatVars.push_back(minisatSolver->newVar());

#if EZMINISAT_SIMPSOLVER && EZMINISAT_INCREMENTAL
	for (auto idx : cnfFrozenVars)
		minisatSolver->setFrozen(minisatVars.at(idx > 0 ? idx-1 : -idx-1), true);
	cnfFrozenVars.clear();
#endif

	for (auto &clause : cnf) {
		Minisat::vec<Minisat::Lit> ps;
		for (auto idx : clause) {
			if (idx > 0)
				ps.push(Minisat::mkLit(minisatVars.at(idx-1)));
			else
				ps.push(Minisat::mkLit(minisatVars.at(-idx-1), true));
#if EZMINISAT_SIMPSOLVER
			if (minisatSolver->isEliminated(minisatVars.at(idx > 0 ? idx-1 : -idx-1))) {
				fprintf(stderr, "Assert in %s:%d failed! Missing call to ezsat->freeze(): %s (lit=%d)\n",
						__FILE__, __LINE__, cnfLiteralInfo(idx).c_str(), idx);
				abort();
			}
#endif
		}
		if (!minisatSolver->addClause(ps))
			goto contradiction;
	}

	if (cnf.size() > 0 && !minisatSolver->simplify())
		goto contradiction;

	Minisat::vec<Minisat::Lit> assumps;

	for (auto idx : extraClauses) {
		if (idx > 0)
			assumps.push(Minisat::mkLit(minisatVars.at(idx-1)));
		else
			assumps.push(Minisat::mkLit(minisatVars.at(-idx-1), true));
#if EZMINISAT_SIMPSOLVER
		if (minisatSolver->isEliminated(minisatVars.at(idx > 0 ? idx-1 : -idx-1))) {
			fprintf(stderr, "Assert in %s:%d failed! Missing call to ezsat->freeze(): %s\n", __FILE__, __LINE__, cnfLiteralInfo(idx).c_str());
			abort();
		}
#endif
	}

#ifndef _WIN32
	struct sigaction sig_action;
	struct sigaction old_sig_action;
	int old_alarm_timeout = 0;

	if (solverTimeout > 0) {
		sig_action.sa_handler = alarmHandler;
		sigemptyset(&sig_action.sa_mask);
		sig_action.sa_flags = SA_RESTART;
		alarmHandlerThis = this;
		alarmHandlerTimeout = clock() + solverTimeout*CLOCKS_PER_SEC;
		old_alarm_timeout = alarm(0);
		sigaction(SIGALRM, &sig_action, &old_sig_action);
		alarm(1);
	}
#endif

	bool foundSolution = minisatSolver->solve(assumps);

#ifndef _WIN32
	if (solverTimeout > 0) {
		if (alarmHandlerTimeout == 0)
			solverTimoutStatus = true;
		alarm(0);
		sigaction(SIGALRM, &old_sig_action, NULL);
		alarm(old_alarm_timeout);
	}
#endif

	if (!foundSolution) {
#if !EZMINISAT_INCREMENTAL
		delete minisatSolver;
		minisatSolver = NULL;
		minisatVars.clear();
#endif
		return false;
	}

	modelValues.clear();
	modelValues.resize(modelIdx.size());

	for (size_t i = 0; i < modelIdx.size(); i++)
	{
		int idx = modelIdx[i];
		bool refvalue = true;

		if (idx < 0)
			idx = -idx, refvalue = false;

		using namespace Minisat;
		lbool value = minisatSolver->modelValue(minisatVars.at(idx-1));
		modelValues[i] = (value == Minisat::lbool(refvalue));
	}

#if !EZMINISAT_INCREMENTAL
	delete minisatSolver;
	minisatSolver = NULL;
	minisatVars.clear();
#endif
	return true;
}

