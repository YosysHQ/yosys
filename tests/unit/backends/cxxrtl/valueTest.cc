#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <random>
#include <type_traits>

#include "cxxrtl/cxxrtl.h"

template<typename T>
T rand_int(T min = std::numeric_limits<T>::min(), T max = std::numeric_limits<T>::max()) {
	static_assert(std::is_integral<T>::value, "T must be an integral type.");
	static_assert(!std::is_same<T, signed char>::value && !std::is_same<T, unsigned char>::value,
		      "Using char with uniform_int_distribution is undefined behavior.");

	static std::mt19937 generator = [] {
		std::random_device rd;
		std::mt19937 mt{rd()};
		return mt;
	}();

	std::uniform_int_distribution<T> dist(min, max);
	return dist(generator);
}

template<size_t Bits, typename Lambda1, typename Lambda2, typename TweakInputLambda>
void test_binary_operation_for_bitsize(Lambda1 f1, Lambda2 f2, TweakInputLambda tweak_input) {
	constexpr int iteration_count = 10'000'000;

    constexpr uint64_t mask = std::numeric_limits<uint64_t>::max() >> (64 - Bits);

    using chunk_type = typename cxxrtl::value<Bits>::chunk::type;
    constexpr size_t chunk_bits = cxxrtl::value<Bits>::chunk::bits;

    for (int iteration = 0; iteration < iteration_count; iteration++)
    {
        uint64_t ia = rand_int<uint64_t>() >> (64 - Bits);
        uint64_t ib = rand_int<uint64_t>() >> (64 - Bits);
        tweak_input(ia, ib);

        cxxrtl::value<Bits> va, vb;
        for (size_t i = 0; i * chunk_bits < Bits; i++) {
            va.data[i] = (chunk_type)(ia >> (i * chunk_bits));
            vb.data[i] = (chunk_type)(ib >> (i * chunk_bits));
        }

        uint64_t iresult = f1(Bits, ia, ib) & mask;
        cxxrtl::value<Bits> vresult = f2(va, vb);

        for (size_t i = 0; i * chunk_bits < Bits; i++) {
            EXPECT_EQ((chunk_type)(iresult >> (i * chunk_bits)), vresult.data[i]);
        }
    }
}

template<typename Lambda1, typename Lambda2, typename TweakInputLambda>
void test_binary_operation(Lambda1 f1, Lambda2 f2, TweakInputLambda tweak_input) {
    // Test at a variety of bitwidths
    test_binary_operation_for_bitsize<6>(f1, f2, tweak_input);
    test_binary_operation_for_bitsize<32>(f1, f2, tweak_input);
    test_binary_operation_for_bitsize<42>(f1, f2, tweak_input);
    test_binary_operation_for_bitsize<63>(f1, f2, tweak_input);
    test_binary_operation_for_bitsize<64>(f1, f2, tweak_input);
}

template<typename Lambda1, typename Lambda2>
void test_binary_operation(Lambda1 f1, Lambda2 f2) {
    test_binary_operation(f1, f2, [](uint64_t, uint64_t){});
}

template<typename Lambda1, typename Lambda2>
void test_unary_operation(Lambda1 f1, Lambda2 f2) {
    test_binary_operation([&f1](size_t bits, uint64_t a, uint64_t) { return f1(bits, a); }, [&f2](auto a, auto) { return f2(a); });
}

TEST(CxxrtlValueTest, shl) {
    test_binary_operation(
        [](size_t, uint64_t a, uint64_t b) { return b >= 64 ? 0 : a << b; },
        [](auto a, auto b) { return a.shl(b); },
        [](uint64_t&, uint64_t& b) { b &= 0x7f; });
}

TEST(CxxrtlValueTest, shr) {
    test_binary_operation(
        [](size_t, uint64_t a, uint64_t b) { return b >= 64 ? 0 : a >> b; },
        [](auto a, auto b) { return a.shr(b); },
        [](uint64_t&, uint64_t& b) { b &= 0x7f; });
}

TEST(CxxrtlValueTest, sshr) {
    test_binary_operation(
        [](size_t bits, uint64_t a, uint64_t b) {
            int64_t sa = (int64_t)(a << (64 - bits));
            return sa >> (b >= bits ? 63 : (b + 64 - bits));
        },
        [](auto a, auto b) { return a.sshr(b); },
        [](uint64_t&, uint64_t& b) { b &= 0x7f; });
}

TEST(CxxrtlValueTest, add) {
	test_binary_operation(
        [](size_t, uint64_t a, uint64_t b) { return a + b; },
        [](auto a, auto b) { return a.add(b); });
}

TEST(CxxrtlValueTest, sub) {
    test_binary_operation(
        [](size_t, uint64_t a, uint64_t b) { return a - b; },
        [](auto a, auto b) { return a.sub(b); });
}

TEST(CxxrtlValueTest, ctlz) {
    test_unary_operation(
        [](size_t bits, uint64_t a) -> uint64_t {
            if (a == 0)
                return bits;
            return __builtin_clzl(a) - (64 - bits);
        },
        [](auto a) { return decltype(a)((cxxrtl::chunk_t)a.ctlz()); });
}
