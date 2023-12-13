#include <cassert>
#include <cstdint>

#include "cxxrtl/cxxrtl.h"

int main()
{
    {
        // shl exceeding Bits should be masked
        cxxrtl::value<6> a(1u);
        cxxrtl::value<6> b(8u);
        cxxrtl::value<6> c = a.shl(b);
        assert(c.get<uint64_t>() == 0);
    }
}