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

    {
        // sshr of unreasonably large size should sign extend correctly
        cxxrtl::value<64> a(0u, 0x80000000u);
        cxxrtl::value<64> b(0u, 1u);
        cxxrtl::value<64> c = a.sshr(b);
        assert(c.get<uint64_t>() == 0xffffffffffffffffu);
    }

    {
        // sshr of exteeding Bits should sign extend correctly
        cxxrtl::value<8> a(0x80u);
        cxxrtl::value<8> b(10u);
        cxxrtl::value<8> c = a.sshr(b);
        assert(c.get<uint64_t>() == 0xffu);
    }

    {
        // Sign extension should occur correctly
        cxxrtl::value<64> a(0x23456789u, 0x8abcdef1u);
        cxxrtl::value<8> b(32u);
        cxxrtl::value<64> c = a.sshr(b);
        assert(c.get<uint64_t>() == 0xffffffff8abcdef1u);
    }

    {
        // ctlz should work with Bits that are a multiple of chunk size
        cxxrtl::value<32> a(0x00040000u);
        assert(a.ctlz() == 13);
    }

    {
        // bmux clears top bits of result
        cxxrtl::value<8> val(0x1fu);
        cxxrtl::value<1> sel(0u);
        assert(val.template bmux<4>(sel).get<uint64_t>() == 0xfu);
    }

    {
        // stream operator smoke test
        cxxrtl::value<8> val(0x1fu);
        std::ostringstream oss;
        oss << val;
        assert(oss.str() == "8'1f");
    }
}
