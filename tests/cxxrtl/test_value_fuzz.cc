#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <exception>
#include <limits>
#include <random>
#include <type_traits>

#include "cxxrtl/cxxrtl.h"

template<typename T>
T rand_int(T min = std::numeric_limits<T>::min(), T max = std::numeric_limits<T>::max())
{
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

struct BinaryOperationBase
{
	void tweak_input(uint64_t &a, uint64_t &b) {}
};

template<size_t Bits, typename Operation>
void test_binary_operation_for_bitsize(Operation &op)
{
	constexpr int iteration_count = 10000000;

	constexpr uint64_t mask = std::numeric_limits<uint64_t>::max() >> (64 - Bits);

	using chunk_type = typename cxxrtl::value<Bits>::chunk::type;
	constexpr size_t chunk_bits = cxxrtl::value<Bits>::chunk::bits;

	for (int iteration = 0; iteration < iteration_count; iteration++) {
		uint64_t ia = rand_int<uint64_t>() >> (64 - Bits);
		uint64_t ib = rand_int<uint64_t>() >> (64 - Bits);
		op.tweak_input(ia, ib);

		cxxrtl::value<Bits> va, vb;
		for (size_t i = 0; i * chunk_bits < Bits; i++) {
			va.data[i] = (chunk_type)(ia >> (i * chunk_bits));
			vb.data[i] = (chunk_type)(ib >> (i * chunk_bits));
		}

		uint64_t iresult = op.reference_impl(Bits, ia, ib) & mask;
		cxxrtl::value<Bits> vresult = op.template testing_impl<Bits>(va, vb);

		for (size_t i = 0; i * chunk_bits < Bits; i++) {
			if ((chunk_type)(iresult >> (i * chunk_bits)) != vresult.data[i]) {
				std::printf("Test failure:\n");
				std::printf("Bits:    %i\n", Bits);
				std::printf("a:       %016lx\n", ia);
				std::printf("b:       %016lx\n", ib);
				std::printf("iresult: %016lx\n", iresult);
				std::printf("vresult: %016lx\n", vresult.template get<uint64_t>());

				std::terminate();
			}
		}
	}
	std::printf("Test passed @ Bits = %i.\n", Bits);
}

template<typename Operation>
void test_binary_operation(Operation &op)
{
	// Test at a variety of bitwidths
	test_binary_operation_for_bitsize<8>(op);
	test_binary_operation_for_bitsize<32>(op);
	test_binary_operation_for_bitsize<42>(op);
	test_binary_operation_for_bitsize<63>(op);
	test_binary_operation_for_bitsize<64>(op);
}

template<typename Operation>
struct UnaryOperationWrapper : BinaryOperationBase 
{
	Operation &op;

	UnaryOperationWrapper(Operation &op) : op(op) {}

	uint64_t reference_impl(size_t bits, uint64_t a, uint64_t b)
	{
		return op.reference_impl(bits, a);
	}

	template<size_t Bits>
	cxxrtl::value<Bits> testing_impl(cxxrtl::value<Bits> a, cxxrtl::value<Bits> b)
	{
		return op.template testing_impl<Bits>(a);
	}
};

template<typename Operation>
void test_unary_operation(Operation &op)
{
	UnaryOperationWrapper<Operation> wrapped(op);
	test_binary_operation(wrapped);
}

struct ShlTest : BinaryOperationBase 
{
	ShlTest()
	{
		std::printf("Randomized tests for value::shl:\n");
		test_binary_operation(*this);
	}

	uint64_t reference_impl(size_t bits, uint64_t a, uint64_t b)
	{
		return b >= 64 ? 0 : a << b;
	}

	template<size_t Bits>
	cxxrtl::value<Bits> testing_impl(cxxrtl::value<Bits> a, cxxrtl::value<Bits> b)
	{
		return a.shl(b);
	}

	void tweak_input(uint64_t &, uint64_t &b)
	{
		b &= 0x7f;
	}
} shl;

struct ShrTest : BinaryOperationBase 
{
	ShrTest()
	{
		std::printf("Randomized tests for value::shr:\n");
		test_binary_operation(*this);
	}

	uint64_t reference_impl(size_t bits, uint64_t a, uint64_t b)
	{
		return b >= 64 ? 0 : a >> b;
	}

	template<size_t Bits>
	cxxrtl::value<Bits> testing_impl(cxxrtl::value<Bits> a, cxxrtl::value<Bits> b)
	{
		return a.shr(b);
	}

	void tweak_input(uint64_t &, uint64_t &b)
	{
		b &= 0x7f;
	}
} shr;

struct SshrTest : BinaryOperationBase 
{
	SshrTest()
	{
		std::printf("Randomized tests for value::sshr:\n");
		test_binary_operation(*this);
	}

	uint64_t reference_impl(size_t bits, uint64_t a, uint64_t b)
	{
		int64_t sa = (int64_t)(a << (64 - bits));
		return sa >> (b >= bits ? 63 : (b + 64 - bits));
	}

	template<size_t Bits>
	cxxrtl::value<Bits> testing_impl(cxxrtl::value<Bits> a, cxxrtl::value<Bits> b)
	{
		return a.sshr(b);
	}

	void tweak_input(uint64_t &, uint64_t &b)
	{
		b &= 0x7f;
	}
} sshr;

struct AddTest : BinaryOperationBase 
{
	AddTest()
	{
		std::printf("Randomized tests for value::add:\n");
		test_binary_operation(*this);
	}

	uint64_t reference_impl(size_t bits, uint64_t a, uint64_t b)
	{
		return a + b;
	}

	template<size_t Bits>
	cxxrtl::value<Bits> testing_impl(cxxrtl::value<Bits> a, cxxrtl::value<Bits> b)
	{
		return a.add(b);
	}
} add;

struct SubTest : BinaryOperationBase 
{
	SubTest()
	{
		std::printf("Randomized tests for value::sub:\n");
		test_binary_operation(*this);
	}

	uint64_t reference_impl(size_t bits, uint64_t a, uint64_t b)
	{
		return a - b;
	}

	template<size_t Bits>
	cxxrtl::value<Bits> testing_impl(cxxrtl::value<Bits> a, cxxrtl::value<Bits> b)
	{
		return a.sub(b);
	}
} sub;

struct CtlzTest
{
	CtlzTest()
	{
		std::printf("Randomized tests for value::ctlz:\n");
		test_unary_operation(*this);
	}

	uint64_t reference_impl(size_t bits, uint64_t a)
	{
		if (a == 0)
			return bits;
		return __builtin_clzl(a) - (64 - bits);
	}

	template<size_t Bits>
	cxxrtl::value<Bits> testing_impl(cxxrtl::value<Bits> a)
	{
		size_t result = a.ctlz();
		return cxxrtl::value<Bits>((cxxrtl::chunk_t)result);
	}
} ctlz;

int main()
{
}
