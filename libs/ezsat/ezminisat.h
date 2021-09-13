/*
 *  ezSAT -- A simple and easy to use CNF generator for SAT solvers
 *
 *  Copyright (C) 2013  Claire Xenia Wolf <claire@yosyshq.com>
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

#ifndef EZMINISAT_H
#define EZMINISAT_H

#define EZMINISAT_SIMPSOLVER 1
#define EZMINISAT_VERBOSITY 0
#define EZMINISAT_INCREMENTAL 1

#include "ezsat.h"
#include <time.h>

// minisat is using limit macros and format macros in their headers that
// can be the source of some troubles when used from c++11. therefore we
// don't force ezSAT users to use minisat headers..
namespace Minisat {
	class Solver;
	class SimpSolver;
}

class ezMiniSAT : public ezSAT
{
private:
#if EZMINISAT_SIMPSOLVER
	typedef Minisat::SimpSolver Solver;
#else
	typedef Minisat::Solver Solver;
#endif
	Solver *minisatSolver;
	std::vector<int> minisatVars;
	bool foundContradiction;

#if EZMINISAT_SIMPSOLVER && EZMINISAT_INCREMENTAL
	std::set<int> cnfFrozenVars;
#endif

#ifndef _WIN32
	static ezMiniSAT *alarmHandlerThis;
	static clock_t alarmHandlerTimeout;
	static void alarmHandler(int);
#endif

public:
	ezMiniSAT();
	virtual ~ezMiniSAT();
	virtual void clear();
#if EZMINISAT_SIMPSOLVER && EZMINISAT_INCREMENTAL
	virtual void freeze(int id);
	virtual bool eliminated(int idx);
#endif
	virtual bool solver(const std::vector<int> &modelExpressions, std::vector<bool> &modelValues, const std::vector<int> &assumptions);
};

#endif
