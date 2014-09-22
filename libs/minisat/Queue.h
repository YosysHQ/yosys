/*****************************************************************************************[Queue.h]
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

#ifndef Minisat_Queue_h
#define Minisat_Queue_h

#include "Vec.h"

namespace Minisat {

//=================================================================================================

template<class T>
class Queue {
    vec<T>  buf;
    int     first;
    int     end;

public:
    typedef T Key;

    Queue() : buf(1), first(0), end(0) {}

    void clear (bool dealloc = false) { buf.clear(dealloc); buf.growTo(1); first = end = 0; }
    int  size  () const { return (end >= first) ? end - first : end - first + buf.size(); }

    const T& operator [] (int index) const  { assert(index >= 0); assert(index < size()); return buf[(first + index) % buf.size()]; }
    T&       operator [] (int index)        { assert(index >= 0); assert(index < size()); return buf[(first + index) % buf.size()]; }

    T    peek  () const { assert(first != end); return buf[first]; }
    void pop   () { assert(first != end); first++; if (first == buf.size()) first = 0; }
    void insert(T elem) {   // INVARIANT: buf[end] is always unused
        buf[end++] = elem;
        if (end == buf.size()) end = 0;
        if (first == end){  // Resize:
            vec<T>  tmp((buf.size()*3 + 1) >> 1);
            //**/printf("queue alloc: %d elems (%.1f MB)\n", tmp.size(), tmp.size() * sizeof(T) / 1000000.0);
            int     i = 0;
            for (int j = first; j < buf.size(); j++) tmp[i++] = buf[j];
            for (int j = 0    ; j < end       ; j++) tmp[i++] = buf[j];
            first = 0;
            end   = buf.size();
            tmp.moveTo(buf);
        }
    }
};


//=================================================================================================
}

#endif
