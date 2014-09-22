/*******************************************************************************************[Rnd.h]
Copyright (c) 2012, Niklas Sorensson
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

#ifndef Minisat_Rnd_h
#define Minisat_Rnd_h

#include "Vec.h"

namespace Minisat {

// Generate a random double:
static inline double drand(double& seed)
{
    seed *= 1389796;
    int q = (int)(seed / 2147483647);
    seed -= (double)q * 2147483647;
    return seed / 2147483647;
}


// Generate a random integer:
static inline int irand(double& seed, int size) { return (int)(drand(seed) * size); }


// Randomly shuffle the contents of a vector:
template<class T>
static void randomShuffle(double& seed, vec<T>& xs)
{
    for (int i = 0; i < xs.size(); i++){
        int pick = i + irand(seed, xs.size() - i);
        T tmp = xs[i];
        xs[i] = xs[pick];
        xs[pick] = tmp;
    }
}

// Randomly shuffle a vector of a vector (ugly)
template<class T>
static void randomShuffle(double& seed, vec<vec<T> >& xs)
{
    for (int i = 0; i < xs.size(); i++){
        int pick = i + irand(seed, xs.size() - i);
        vec<T> tmp; xs[i].moveTo(tmp);
        xs[pick].moveTo(xs[i]);
        tmp.moveTo(xs[pick]);
    }
}


//=================================================================================================
} // namespace Minisat
#endif
