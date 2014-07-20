/****************************************************************************************[System.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_System_h
#define Minisat_System_h

#if defined(__linux__)
#include <fpu_control.h>
#endif

#include "IntTypes.h"

//-------------------------------------------------------------------------------------------------

namespace Minisat {

static inline double cpuTime(void); // CPU-time in seconds.

extern double memUsed();            // Memory in mega bytes (returns 0 for unsupported architectures).
extern double memUsedPeak(bool strictlyPeak = false); // Peak-memory in mega bytes (returns 0 for unsupported architectures).

extern void   setX86FPUPrecision(); // Make sure double's are represented with the same precision
                                    // in memory and registers.

extern void   limitMemory(uint64_t max_mem_mb); // Set a limit on total memory usage. The exact
                                                // semantics varies depending on architecture.

extern void   limitTime(uint32_t max_cpu_time); // Set a limit on maximum CPU time. The exact
                                                // semantics varies depending on architecture.

extern void   sigTerm(void handler(int));      // Set up handling of available termination signals.

}

//-------------------------------------------------------------------------------------------------
// Implementation of inline functions:

#if defined(_MSC_VER) || defined(__MINGW32__)
#include <time.h>

static inline double Minisat::cpuTime(void) { return (double)clock() / CLOCKS_PER_SEC; }

#else
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static inline double Minisat::cpuTime(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }

#endif

#endif
