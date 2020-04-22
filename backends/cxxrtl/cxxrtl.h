/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2019-2020  whitequark <whitequark@whitequark.org>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted.
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

// This file is included by the designs generated with `write_cxxrtl`. It is not used in Yosys itself.

#ifndef CXXRTL_H
#define CXXRTL_H

#include <cstddef>
#include <cstdint>
#include <cassert>
#include <limits>
#include <type_traits>
#include <tuple>
#include <vector>
#include <map>
#include <algorithm>
#include <memory>
#include <sstream>

// The cxxrtl support library implements compile time specialized arbitrary width arithmetics, as well as provides
// composite lvalues made out of bit slices and concatenations of lvalues. This allows the `write_cxxrtl` pass
// to perform a straightforward translation of RTLIL structures to readable C++, relying on the C++ compiler
// to unwrap the abstraction and generate efficient code.
namespace cxxrtl {

// All arbitrary-width values in cxxrtl are backed by arrays of unsigned integers called chunks. The chunk size
// is the same regardless of the value width to simplify manipulating values via FFI interfaces, e.g. driving
// and introspecting the simulation in Python.
//
// It is practical to use chunk sizes between 32 bits and platform register size because when arithmetics on
// narrower integer types is legalized by the C++ compiler, it inserts code to clear the high bits of the register.
// However, (a) most of our operations do not change those bits in the first place because of invariants that are
// invisible to the compiler, (b) we often operate on non-power-of-2 values and have to clear the high bits anyway.
// Therefore, using relatively wide chunks and clearing the high bits explicitly and only when we know they may be
// clobbered results in simpler generated code.
template<typename T>
struct chunk_traits {
	static_assert(std::is_integral<T>::value && std::is_unsigned<T>::value,
	              "chunk type must be an unsigned integral type");
	using type = T;
	static constexpr size_t bits = std::numeric_limits<T>::digits;
	static constexpr T mask = std::numeric_limits<T>::max();
};

template<class T>
struct expr_base;

template<size_t Bits>
struct value : public expr_base<value<Bits>> {
	static constexpr size_t bits = Bits;

	using chunk = chunk_traits<uint32_t>;
	static constexpr chunk::type msb_mask = (Bits % chunk::bits == 0) ? chunk::mask
		: chunk::mask >> (chunk::bits - (Bits % chunk::bits));

	static constexpr size_t chunks = (Bits + chunk::bits - 1) / chunk::bits;
	chunk::type data[chunks] = {};

	value() = default;
	template<typename... Init>
	explicit constexpr value(Init ...init) : data{init...} {}

	value(const value<Bits> &) = default;
	value(value<Bits> &&) = default;
	value<Bits> &operator=(const value<Bits> &) = default;

	// A (no-op) helper that forces the cast to value<>.
	const value<Bits> &val() const {
		return *this;
	}

	std::string str() const {
		std::stringstream ss;
		ss << *this;
		return ss.str();
	}

	// Operations with compile-time parameters.
	//
	// These operations are used to implement slicing, concatenation, and blitting.
	// The trunc, zext and sext operations add or remove most significant bits (i.e. on the left);
	// the rtrunc and rzext operations add or remove least significant bits (i.e. on the right).
	template<size_t NewBits>
	value<NewBits> trunc() const {
		static_assert(NewBits <= Bits, "trunc() may not increase width");
		value<NewBits> result;
		for (size_t n = 0; n < result.chunks; n++)
			result.data[n] = data[n];
		result.data[result.chunks - 1] &= result.msb_mask;
		return result;
	}

	template<size_t NewBits>
	value<NewBits> zext() const {
		static_assert(NewBits >= Bits, "zext() may not decrease width");
		value<NewBits> result;
		for (size_t n = 0; n < chunks; n++)
			result.data[n] = data[n];
		return result;
	}

	template<size_t NewBits>
	value<NewBits> sext() const {
		static_assert(NewBits >= Bits, "sext() may not decrease width");
		value<NewBits> result;
		for (size_t n = 0; n < chunks; n++)
			result.data[n] = data[n];
		if (is_neg()) {
			result.data[chunks - 1] |= ~msb_mask;
			for (size_t n = chunks; n < result.chunks; n++)
				result.data[n] = chunk::mask;
			result.data[result.chunks - 1] &= result.msb_mask;
		}
		return result;
	}

	template<size_t NewBits>
	value<NewBits> rtrunc() const {
		static_assert(NewBits <= Bits, "rtrunc() may not increase width");
		value<NewBits> result;
		constexpr size_t shift_chunks = (Bits - NewBits) / chunk::bits;
		constexpr size_t shift_bits   = (Bits - NewBits) % chunk::bits;
		chunk::type carry = 0;
		if (shift_chunks + result.chunks < chunks) {
			carry = (shift_bits == 0) ? 0
				: data[shift_chunks + result.chunks] << (chunk::bits - shift_bits);
		}
		for (size_t n = result.chunks; n > 0; n--) {
			result.data[n - 1] = carry | (data[shift_chunks + n - 1] >> shift_bits);
			carry = (shift_bits == 0) ? 0
				: data[shift_chunks + n - 1] << (chunk::bits - shift_bits);
		}
		return result;
	}

	template<size_t NewBits>
	value<NewBits> rzext() const {
		static_assert(NewBits >= Bits, "rzext() may not decrease width");
		value<NewBits> result;
		constexpr size_t shift_chunks = (NewBits - Bits) / chunk::bits;
		constexpr size_t shift_bits   = (NewBits - Bits) % chunk::bits;
		chunk::type carry = 0;
		for (size_t n = 0; n < chunks; n++) {
			result.data[shift_chunks + n] = (data[n] << shift_bits) | carry;
			carry = (shift_bits == 0) ? 0
				: data[n] >> (chunk::bits - shift_bits);
		}
		if (carry != 0)
			result.data[result.chunks - 1] = carry;
		return result;
	}

	// Bit blit operation, i.e. a partial read-modify-write.
	template<size_t Stop, size_t Start>
	value<Bits> blit(const value<Stop - Start + 1> &source) const {
		static_assert(Stop >= Start, "blit() may not reverse bit order");
		constexpr chunk::type start_mask = ~(chunk::mask << (Start % chunk::bits));
		constexpr chunk::type stop_mask = (Stop % chunk::bits + 1 == chunk::bits) ? 0
			: (chunk::mask << (Stop % chunk::bits + 1));
		value<Bits> masked = *this;
		if (Start / chunk::bits == Stop / chunk::bits) {
			masked.data[Start / chunk::bits] &= stop_mask | start_mask;
		} else {
			masked.data[Start / chunk::bits] &= start_mask;
			for (size_t n = Start / chunk::bits + 1; n < Stop / chunk::bits; n++)
				masked.data[n] = 0;
			masked.data[Stop / chunk::bits] &= stop_mask;
		}
		value<Bits> shifted = source
			.template rzext<Stop + 1>()
			.template zext<Bits>();
		return masked.bit_or(shifted);
	}

	// Helpers for selecting extending or truncating operation depending on whether the result is wider or narrower
	// than the operand. In C++17 these can be replaced with `if constexpr`.
	template<size_t NewBits, typename = void>
	struct zext_cast {
		value<NewBits> operator()(const value<Bits> &val) {
			return val.template zext<NewBits>();
		}
	};

	template<size_t NewBits>
	struct zext_cast<NewBits, typename std::enable_if<(NewBits < Bits)>::type> {
		value<NewBits> operator()(const value<Bits> &val) {
			return val.template trunc<NewBits>();
		}
	};

	template<size_t NewBits, typename = void>
	struct sext_cast {
		value<NewBits> operator()(const value<Bits> &val) {
			return val.template sext<NewBits>();
		}
	};

	template<size_t NewBits>
	struct sext_cast<NewBits, typename std::enable_if<(NewBits < Bits)>::type> {
		value<NewBits> operator()(const value<Bits> &val) {
			return val.template trunc<NewBits>();
		}
	};

	template<size_t NewBits>
	value<NewBits> zcast() const {
		return zext_cast<NewBits>()(*this);
	}

	template<size_t NewBits>
	value<NewBits> scast() const {
		return sext_cast<NewBits>()(*this);
	}

	// Operations with run-time parameters (offsets, amounts, etc).
	//
	// These operations are used for computations.
	bool bit(size_t offset) const {
		return data[offset / chunk::bits] & (1 << (offset % chunk::bits));
	}

	void set_bit(size_t offset, bool value = true) {
		size_t offset_chunks = offset / chunk::bits;
		size_t offset_bits = offset % chunk::bits;
		data[offset_chunks] &= ~(1 << offset_bits);
		data[offset_chunks] |= value ? 1 << offset_bits : 0;
	}

	bool is_zero() const {
		for (size_t n = 0; n < chunks; n++)
			if (data[n] != 0)
				return false;
		return true;
	}

	explicit operator bool() const {
		return !is_zero();
	}

	bool is_neg() const {
		return data[chunks - 1] & (1 << ((Bits - 1) % chunk::bits));
	}

	bool operator ==(const value<Bits> &other) const {
		for (size_t n = 0; n < chunks; n++)
			if (data[n] != other.data[n])
				return false;
		return true;
	}

	bool operator !=(const value<Bits> &other) const {
		return !(*this == other);
	}

	value<Bits> bit_not() const {
		value<Bits> result;
		for (size_t n = 0; n < chunks; n++)
			result.data[n] = ~data[n];
		result.data[chunks - 1] &= msb_mask;
		return result;
	}

	value<Bits> bit_and(const value<Bits> &other) const {
		value<Bits> result;
		for (size_t n = 0; n < chunks; n++)
			result.data[n] = data[n] & other.data[n];
		return result;
	}

	value<Bits> bit_or(const value<Bits> &other) const {
		value<Bits> result;
		for (size_t n = 0; n < chunks; n++)
			result.data[n] = data[n] | other.data[n];
		return result;
	}

	value<Bits> bit_xor(const value<Bits> &other) const {
		value<Bits> result;
		for (size_t n = 0; n < chunks; n++)
			result.data[n] = data[n] ^ other.data[n];
		return result;
	}

	value<Bits> update(const value<Bits> &val, const value<Bits> &mask) const {
		return bit_and(mask.bit_not()).bit_or(val.bit_and(mask));
	}

	template<size_t AmountBits>
	value<Bits> shl(const value<AmountBits> &amount) const {
		// Ensure our early return is correct by prohibiting values larger than 4 Gbit.
		static_assert(Bits <= chunk::mask, "shl() of unreasonably large values is not supported");
		// Detect shifts definitely large than Bits early.
		for (size_t n = 1; n < amount.chunks; n++)
			if (amount.data[n] != 0)
				return {};
		// Past this point we can use the least significant chunk as the shift size.
		size_t shift_chunks = amount.data[0] / chunk::bits;
		size_t shift_bits   = amount.data[0] % chunk::bits;
		if (shift_chunks >= chunks)
			return {};
		value<Bits> result;
		chunk::type carry = 0;
		for (size_t n = 0; n < chunks - shift_chunks; n++) {
			result.data[shift_chunks + n] = (data[n] << shift_bits) | carry;
			carry = (shift_bits == 0) ? 0
				: data[n] >> (chunk::bits - shift_bits);
		}
		return result;
	}

	template<size_t AmountBits, bool Signed = false>
	value<Bits> shr(const value<AmountBits> &amount) const {
		// Ensure our early return is correct by prohibiting values larger than 4 Gbit.
		static_assert(Bits <= chunk::mask, "shr() of unreasonably large values is not supported");
		// Detect shifts definitely large than Bits early.
		for (size_t n = 1; n < amount.chunks; n++)
			if (amount.data[n] != 0)
				return {};
		// Past this point we can use the least significant chunk as the shift size.
		size_t shift_chunks = amount.data[0] / chunk::bits;
		size_t shift_bits   = amount.data[0] % chunk::bits;
		if (shift_chunks >= chunks)
			return {};
		value<Bits> result;
		chunk::type carry = 0;
		for (size_t n = 0; n < chunks - shift_chunks; n++) {
			result.data[chunks - shift_chunks - 1 - n] = carry | (data[chunks - 1 - n] >> shift_bits);
			carry = (shift_bits == 0) ? 0
				: data[chunks - 1 - n] << (chunk::bits - shift_bits);
		}
		if (Signed && is_neg()) {
			for (size_t n = chunks - shift_chunks; n < chunks; n++)
				result.data[n] = chunk::mask;
			if (shift_bits != 0)
				result.data[chunks - shift_chunks] |= chunk::mask << (chunk::bits - shift_bits);
		}
		return result;
	}

	template<size_t AmountBits>
	value<Bits> sshr(const value<AmountBits> &amount) const {
		return shr<AmountBits, /*Signed=*/true>(amount);
	}

	size_t ctpop() const {
		size_t count = 0;
		for (size_t n = 0; n < chunks; n++) {
			// This loop implements the population count idiom as recognized by LLVM and GCC.
			for (chunk::type x = data[n]; x != 0; count++)
				x = x & (x - 1);
		}
		return count;
	}

	size_t ctlz() const {
		size_t count = 0;
		for (size_t n = 0; n < chunks; n++) {
			chunk::type x = data[chunks - 1 - n];
			if (x == 0) {
				count += (n == 0 ? Bits % chunk::bits : chunk::bits);
			} else {
				// This loop implements the find first set idiom as recognized by LLVM.
				for (; x != 0; count++)
					x >>= 1;
			}
		}
		return count;
	}

	template<bool Invert, bool CarryIn>
	std::pair<value<Bits>, bool /*CarryOut*/> alu(const value<Bits> &other) const {
		value<Bits> result;
		bool carry = CarryIn;
		for (size_t n = 0; n < result.chunks; n++) {
			result.data[n] = data[n] + (Invert ? ~other.data[n] : other.data[n]) + carry;
			carry = (result.data[n] <  data[n]) ||
			        (result.data[n] == data[n] && carry);
		}
		result.data[result.chunks - 1] &= result.msb_mask;
		return {result, carry};
	}

	value<Bits> add(const value<Bits> &other) const {
		return alu</*Invert=*/false, /*CarryIn=*/false>(other).first;
	}

	value<Bits> sub(const value<Bits> &other) const {
		return alu</*Invert=*/true, /*CarryIn=*/true>(other).first;
	}

	value<Bits> neg() const {
		return value<Bits> { 0u }.sub(*this);
	}

	bool ucmp(const value<Bits> &other) const {
		bool carry;
		std::tie(std::ignore, carry) = alu</*Invert=*/true, /*CarryIn=*/true>(other);
		return !carry; // a.ucmp(b) ≡ a u< b
	}

	bool scmp(const value<Bits> &other) const {
		value<Bits> result;
		bool carry;
		std::tie(result, carry) = alu</*Invert=*/true, /*CarryIn=*/true>(other);
		bool overflow = (is_neg() == !other.is_neg()) && (is_neg() != result.is_neg());
		return result.is_neg() ^ overflow; // a.scmp(b) ≡ a s< b
	}
};

// Expression template for a slice, usable as lvalue or rvalue, and composable with other expression templates here.
template<class T, size_t Stop, size_t Start>
struct slice_expr : public expr_base<slice_expr<T, Stop, Start>> {
	static_assert(Stop >= Start, "slice_expr() may not reverse bit order");
	static_assert(Start < T::bits && Stop < T::bits, "slice_expr() must be within bounds");
	static constexpr size_t bits = Stop - Start + 1;

	T &expr;

	slice_expr(T &expr) : expr(expr) {}
	slice_expr(const slice_expr<T, Stop, Start> &) = delete;

	operator value<bits>() const {
		return static_cast<const value<T::bits> &>(expr)
			.template rtrunc<T::bits - Start>()
			.template trunc<bits>();
	}

	slice_expr<T, Stop, Start> &operator=(const value<bits> &rhs) {
		// Generic partial assignment implemented using a read-modify-write operation on the sliced expression.
		expr = static_cast<const value<T::bits> &>(expr)
			.template blit<Stop, Start>(rhs);
		return *this;
	}

	// A helper that forces the cast to value<>, which allows deduction to work.
	value<bits> val() const {
		return static_cast<const value<bits> &>(*this);
	}
};

// Expression template for a concatenation, usable as lvalue or rvalue, and composable with other expression templates here.
template<class T, class U>
struct concat_expr : public expr_base<concat_expr<T, U>> {
	static constexpr size_t bits = T::bits + U::bits;

	T &ms_expr;
	U &ls_expr;

	concat_expr(T &ms_expr, U &ls_expr) : ms_expr(ms_expr), ls_expr(ls_expr) {}
	concat_expr(const concat_expr<T, U> &) = delete;

	operator value<bits>() const {
		value<bits> ms_shifted = static_cast<const value<T::bits> &>(ms_expr)
			.template rzext<bits>();
		value<bits> ls_extended = static_cast<const value<U::bits> &>(ls_expr)
			.template zext<bits>();
		return ms_shifted.bit_or(ls_extended);
	}

	concat_expr<T, U> &operator=(const value<bits> &rhs) {
		ms_expr = rhs.template rtrunc<T::bits>();
		ls_expr = rhs.template trunc<U::bits>();
		return *this;
	}

	// A helper that forces the cast to value<>, which allows deduction to work.
	value<bits> val() const {
		return static_cast<const value<bits> &>(*this);
	}
};

// Base class for expression templates, providing helper methods for operations that are valid on both rvalues and lvalues.
//
// Note that expression objects (slices and concatenations) constructed in this way should NEVER be captured because
// they refer to temporaries that will, in general, only live until the end of the statement. For example, both of
// these snippets perform use-after-free:
//
//    const auto &a = val.slice<7,0>().slice<1>();
//    value<1> b = a;
//
//    auto &&c = val.slice<7,0>().slice<1>();
//    c = value<1>{1u};
//
// An easy way to write code using slices and concatenations safely is to follow two simple rules:
//   * Never explicitly name any type except `value<W>` or `const value<W> &`.
//   * Never use a `const auto &` or `auto &&` in any such expression.
// Then, any code that compiles will be well-defined.
template<class T>
struct expr_base {
	template<size_t Stop, size_t Start = Stop>
	slice_expr<const T, Stop, Start> slice() const {
		return {*static_cast<const T *>(this)};
	}

	template<size_t Stop, size_t Start = Stop>
	slice_expr<T, Stop, Start> slice() {
		return {*static_cast<T *>(this)};
	}

	template<class U>
	concat_expr<const T, typename std::remove_reference<const U>::type> concat(const U &other) const {
		return {*static_cast<const T *>(this), other};
	}

	template<class U>
	concat_expr<T, typename std::remove_reference<U>::type> concat(U &&other) {
		return {*static_cast<T *>(this), other};
	}
};

template<size_t Bits>
std::ostream &operator<<(std::ostream &os, const value<Bits> &val) {
	auto old_flags = os.flags(std::ios::right);
	auto old_width = os.width(0);
	auto old_fill  = os.fill('0');
	os << val.bits << '\'' << std::hex;
	for (size_t n = val.chunks - 1; n != (size_t)-1; n--) {
		if (n == val.chunks - 1 && Bits % value<Bits>::chunk::bits != 0)
			os.width((Bits % value<Bits>::chunk::bits + 3) / 4);
		else
			os.width((value<Bits>::chunk::bits + 3) / 4);
		os << val.data[n];
	}
	os.fill(old_fill);
	os.width(old_width);
	os.flags(old_flags);
	return os;
}

template<size_t Bits>
struct wire {
	static constexpr size_t bits = Bits;

	value<Bits> curr;
	value<Bits> next;

	wire() = default;
	constexpr wire(const value<Bits> &init) : curr(init), next(init) {}
	template<typename... Init>
	explicit constexpr wire(Init ...init) : curr{init...}, next{init...} {}

	wire(const wire<Bits> &) = delete;
	wire(wire<Bits> &&) = default;
	wire<Bits> &operator=(const wire<Bits> &) = delete;

	bool commit() {
		if (curr != next) {
			curr = next;
			return true;
		}
		return false;
	}
};

template<size_t Bits>
std::ostream &operator<<(std::ostream &os, const wire<Bits> &val) {
	os << val.curr;
	return os;
}

template<size_t Width>
struct memory {
	std::vector<value<Width>> data;

	size_t depth() const {
		return data.size();
	}

	memory() = delete;
	explicit memory(size_t depth) : data(depth) {}

	memory(const memory<Width> &) = delete;
	memory<Width> &operator=(const memory<Width> &) = delete;

	// The only way to get the compiler to put the initializer in .rodata and do not copy it on stack is to stuff it
	// into a plain array. You'd think an std::initializer_list would work here, but it doesn't, because you can't
	// construct an initializer_list in a constexpr (or something) and so if you try to do that the whole thing is
	// first copied on the stack (probably overflowing it) and then again into `data`.
	template<size_t Size>
	struct init {
		size_t offset;
		value<Width> data[Size];
	};

	template<size_t... InitSize>
	explicit memory(size_t depth, const init<InitSize> &...init) : data(depth) {
		data.resize(depth);
		// This utterly reprehensible construct is the most reasonable way to apply a function to every element
		// of a parameter pack, if the elements all have different types and so cannot be cast to an initializer list.
		auto _ = {std::move(std::begin(init.data), std::end(init.data), data.begin() + init.offset)...};
	}

	// An operator for direct memory reads. May be used at any time during the simulation.
	const value<Width> &operator [](size_t index) const {
		assert(index < data.size());
		return data[index];
	}

	// An operator for direct memory writes. May only be used before the simulation is started. If used
	// after the simulation is started, the design may malfunction.
	value<Width> &operator [](size_t index) {
		assert(index < data.size());
		return data[index];
	}

	// A simple way to make a writable memory would be to use an array of wires instead of an array of values.
	// However, there are two significant downsides to this approach: first, it has large overhead (2× space
	// overhead, and O(depth) time overhead during commit); second, it does not simplify handling write port
	// priorities. Although in principle write ports could be ordered or conditionally enabled in generated
	// code based on their priorities and selected addresses, the feedback arc set problem is computationally
	// expensive, and the heuristic based algorithms are not easily modified to guarantee (rather than prefer)
	// a particular write port evaluation order.
	//
	// The approach used here instead is to queue writes into a buffer during the eval phase, then perform
	// the writes during the commit phase in the priority order. This approach has low overhead, with both space
	// and time proportional to the amount of write ports. Because virtually every memory in a practical design
	// has at most two write ports, linear search is used on every write, being the fastest and simplest approach.
	struct write {
		size_t index;
		value<Width> val;
		value<Width> mask;
		int priority;
	};
	std::vector<write> write_queue;

	void update(size_t index, const value<Width> &val, const value<Width> &mask, int priority = 0) {
		assert(index < data.size());
		write_queue.emplace_back(write { index, val, mask, priority });
	}

	bool commit() {
		bool changed = false;
		std::sort(write_queue.begin(), write_queue.end(),
			[](const write &a, const write &b) { return a.priority < b.priority; });
		for (const write &entry : write_queue) {
			value<Width> elem = data[entry.index];
			elem = elem.update(entry.val, entry.mask);
			changed |= (data[entry.index] != elem);
			data[entry.index] = elem;
		}
		write_queue.clear();
		return changed;
	}
};

struct metadata {
	const enum {
		MISSING = 0,
		UINT   	= 1,
		SINT   	= 2,
		STRING 	= 3,
		DOUBLE 	= 4,
	} value_type;

	// In debug mode, using the wrong .as_*() function will assert.
	// In release mode, using the wrong .as_*() function will safely return a default value.
	union {
		const unsigned  uint_value = 0;
		const signed    sint_value;
	};
	const std::string string_value = "";
	const double      double_value = 0.0;

	metadata() : value_type(MISSING) {}
	metadata(unsigned value) : value_type(UINT), uint_value(value) {}
	metadata(signed value) : value_type(SINT), sint_value(value) {}
	metadata(const std::string &value) : value_type(STRING), string_value(value) {}
	metadata(const char *value) : value_type(STRING), string_value(value) {}
	metadata(double value) : value_type(DOUBLE), double_value(value) {}

	metadata(const metadata &) = default;
	metadata &operator=(const metadata &) = delete;

	unsigned as_uint() const {
		assert(value_type == UINT);
		return uint_value;
	}

	signed as_sint() const {
		assert(value_type == SINT);
		return sint_value;
	}

	const std::string &as_string() const {
		assert(value_type == STRING);
		return string_value;
	}

	double as_double() const {
		assert(value_type == DOUBLE);
		return double_value;
	}
};

typedef std::map<std::string, metadata> metadata_map;

struct module {
	module() {}
	virtual ~module() {}

	module(const module &) = delete;
	module &operator=(const module &) = delete;

	virtual bool eval() = 0;
	virtual bool commit() = 0;

	size_t step() {
		size_t deltas = 0;
		bool converged = false;
		do {
			converged = eval();
			deltas++;
		} while (commit() && !converged);
		return deltas;
	}
};

} // namespace cxxrtl

// Definitions of internal Yosys cells. Other than the functions in this namespace, cxxrtl is fully generic
// and indepenent of Yosys implementation details.
//
// The `write_cxxrtl` pass translates internal cells (cells with names that start with `$`) to calls of these
// functions. All of Yosys arithmetic and logical cells perform sign or zero extension on their operands,
// whereas basic operations on arbitrary width values require operands to be of the same width. These functions
// bridge the gap by performing the necessary casts. They are named similar to `cell_A[B]`, where A and B are `u`
// if the corresponding operand is unsigned, and `s` if it is signed.
namespace cxxrtl_yosys {

using namespace cxxrtl;

// std::max isn't constexpr until C++14 for no particular reason (it's an oversight), so we define our own.
template<class T>
constexpr T max(const T &a, const T &b) {
	return a > b ? a : b;
}

// Logic operations
template<size_t BitsY, size_t BitsA>
value<BitsY> not_u(const value<BitsA> &a) {
	return a.template zcast<BitsY>().bit_not();
}

template<size_t BitsY, size_t BitsA>
value<BitsY> not_s(const value<BitsA> &a) {
	return a.template scast<BitsY>().bit_not();
}

template<size_t BitsY, size_t BitsA>
value<BitsY> logic_not_u(const value<BitsA> &a) {
	return value<BitsY> { a ? 0u : 1u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> logic_not_s(const value<BitsA> &a) {
	return value<BitsY> { a ? 0u : 1u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_and_u(const value<BitsA> &a) {
	return value<BitsY> { a.bit_not().is_zero() ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_and_s(const value<BitsA> &a) {
	return value<BitsY> { a.bit_not().is_zero() ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_or_u(const value<BitsA> &a) {
	return value<BitsY> { a ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_or_s(const value<BitsA> &a) {
	return value<BitsY> { a ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_xor_u(const value<BitsA> &a) {
	return value<BitsY> { (a.ctpop() % 2) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_xor_s(const value<BitsA> &a) {
	return value<BitsY> { (a.ctpop() % 2) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_xnor_u(const value<BitsA> &a) {
	return value<BitsY> { (a.ctpop() % 2) ? 0u : 1u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_xnor_s(const value<BitsA> &a) {
	return value<BitsY> { (a.ctpop() % 2) ? 0u : 1u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_bool_u(const value<BitsA> &a) {
	return value<BitsY> { a ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA>
value<BitsY> reduce_bool_s(const value<BitsA> &a) {
	return value<BitsY> { a ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> and_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template zcast<BitsY>().bit_and(b.template zcast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> and_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template scast<BitsY>().bit_and(b.template scast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> or_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template zcast<BitsY>().bit_or(b.template zcast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> or_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template scast<BitsY>().bit_or(b.template scast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> xor_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template zcast<BitsY>().bit_xor(b.template zcast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> xor_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template scast<BitsY>().bit_xor(b.template scast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> xnor_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template zcast<BitsY>().bit_xor(b.template zcast<BitsY>()).bit_not();
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> xnor_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template scast<BitsY>().bit_xor(b.template scast<BitsY>()).bit_not();
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> logic_and_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return value<BitsY> { (bool(a) & bool(b)) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> logic_and_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return value<BitsY> { (bool(a) & bool(b)) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> logic_or_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return value<BitsY> { (bool(a) | bool(b)) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> logic_or_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return value<BitsY> { (bool(a) | bool(b)) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shl_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template zcast<BitsY>().template shl(b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shl_su(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template scast<BitsY>().template shl(b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> sshl_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template zcast<BitsY>().template shl(b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> sshl_su(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template scast<BitsY>().template shl(b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shr_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template shr(b).template zcast<BitsY>();
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shr_su(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template shr(b).template scast<BitsY>();
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> sshr_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template shr(b).template zcast<BitsY>();
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> sshr_su(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template shr(b).template scast<BitsY>();
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shift_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return shr_uu<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shift_su(const value<BitsA> &a, const value<BitsB> &b) {
	return shr_su<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shift_us(const value<BitsA> &a, const value<BitsB> &b) {
	return b.is_neg() ? shl_uu<BitsY>(a, b.template sext<BitsB + 1>().neg()) : shr_uu<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shift_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return b.is_neg() ? shl_su<BitsY>(a, b.template sext<BitsB + 1>().neg()) : shr_su<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shiftx_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return shift_uu<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shiftx_su(const value<BitsA> &a, const value<BitsB> &b) {
	return shift_su<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shiftx_us(const value<BitsA> &a, const value<BitsB> &b) {
	return shift_us<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> shiftx_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return shift_ss<BitsY>(a, b);
}

// Comparison operations
template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> eq_uu(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY>{ a.template zext<BitsExt>() == b.template zext<BitsExt>() ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> eq_ss(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY>{ a.template sext<BitsExt>() == b.template sext<BitsExt>() ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> ne_uu(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY>{ a.template zext<BitsExt>() != b.template zext<BitsExt>() ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> ne_ss(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY>{ a.template sext<BitsExt>() != b.template sext<BitsExt>() ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> eqx_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return eq_uu<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> eqx_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return eq_ss<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> nex_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return ne_uu<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> nex_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return ne_ss<BitsY>(a, b);
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> gt_uu(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY> { b.template zext<BitsExt>().ucmp(a.template zext<BitsExt>()) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> gt_ss(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY> { b.template sext<BitsExt>().scmp(a.template sext<BitsExt>()) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> ge_uu(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY> { !a.template zext<BitsExt>().ucmp(b.template zext<BitsExt>()) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> ge_ss(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY> { !a.template sext<BitsExt>().scmp(b.template sext<BitsExt>()) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> lt_uu(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY> { a.template zext<BitsExt>().ucmp(b.template zext<BitsExt>()) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> lt_ss(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY> { a.template sext<BitsExt>().scmp(b.template sext<BitsExt>()) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> le_uu(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY> { !b.template zext<BitsExt>().ucmp(a.template zext<BitsExt>()) ? 1u : 0u };
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> le_ss(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t BitsExt = max(BitsA, BitsB);
	return value<BitsY> { !b.template sext<BitsExt>().scmp(a.template sext<BitsExt>()) ? 1u : 0u };
}

// Arithmetic operations
template<size_t BitsY, size_t BitsA>
value<BitsY> pos_u(const value<BitsA> &a) {
	return a.template zcast<BitsY>();
}

template<size_t BitsY, size_t BitsA>
value<BitsY> pos_s(const value<BitsA> &a) {
	return a.template scast<BitsY>();
}

template<size_t BitsY, size_t BitsA>
value<BitsY> neg_u(const value<BitsA> &a) {
	return a.template zcast<BitsY>().neg();
}

template<size_t BitsY, size_t BitsA>
value<BitsY> neg_s(const value<BitsA> &a) {
	return a.template scast<BitsY>().neg();
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> add_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template zcast<BitsY>().add(b.template zcast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> add_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template scast<BitsY>().add(b.template scast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> sub_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template zcast<BitsY>().sub(b.template zcast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> sub_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return a.template scast<BitsY>().sub(b.template scast<BitsY>());
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> mul_uu(const value<BitsA> &a, const value<BitsB> &b) {
	value<BitsY> product;
	value<BitsY> multiplicand = a.template zcast<BitsY>();
	const value<BitsB> &multiplier = b;
	uint32_t multiplicand_shift = 0;
	for (size_t step = 0; step < BitsB; step++) {
		if (multiplier.bit(step)) {
			multiplicand = multiplicand.shl(value<32> { multiplicand_shift });
			product = product.add(multiplicand);
			multiplicand_shift = 0;
		}
		multiplicand_shift++;
	}
	return product;
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> mul_ss(const value<BitsA> &a, const value<BitsB> &b) {
	value<BitsB + 1> ub = b.template sext<BitsB + 1>();
	if (ub.is_neg()) ub = ub.neg();
	value<BitsY> y = mul_uu<BitsY>(a.template scast<BitsY>(), ub);
	return b.is_neg() ? y.neg() : y;
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
std::pair<value<BitsY>, value<BitsY>> divmod_uu(const value<BitsA> &a, const value<BitsB> &b) {
	constexpr size_t Bits = max(BitsY, max(BitsA, BitsB));
	value<Bits> quotient;
	value<Bits> dividend = a.template zext<Bits>();
	value<Bits> divisor = b.template zext<Bits>();
	if (dividend.ucmp(divisor))
		return {/*quotient=*/value<BitsY> { 0u }, /*remainder=*/dividend.template trunc<BitsY>()};
	uint32_t divisor_shift = dividend.ctlz() - divisor.ctlz();
	divisor = divisor.shl(value<32> { divisor_shift });
	for (size_t step = 0; step <= divisor_shift; step++) {
		quotient = quotient.shl(value<1> { 1u });
		if (!dividend.ucmp(divisor)) {
			dividend = dividend.sub(divisor);
			quotient.set_bit(0, true);
		}
		divisor = divisor.shr(value<1> { 1u });
	}
	return {quotient.template trunc<BitsY>(), /*remainder=*/dividend.template trunc<BitsY>()};
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
std::pair<value<BitsY>, value<BitsY>> divmod_ss(const value<BitsA> &a, const value<BitsB> &b) {
	value<BitsA + 1> ua = a.template sext<BitsA + 1>();
	value<BitsB + 1> ub = b.template sext<BitsB + 1>();
	if (ua.is_neg()) ua = ua.neg();
	if (ub.is_neg()) ub = ub.neg();
	value<BitsY> y, r;
	std::tie(y, r) = divmod_uu<BitsY>(ua, ub);
	if (a.is_neg() != b.is_neg()) y = y.neg();
	if (a.is_neg()) r = r.neg();
	return {y, r};
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> div_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return divmod_uu<BitsY>(a, b).first;
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> div_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return divmod_ss<BitsY>(a, b).first;
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> mod_uu(const value<BitsA> &a, const value<BitsB> &b) {
	return divmod_uu<BitsY>(a, b).second;
}

template<size_t BitsY, size_t BitsA, size_t BitsB>
value<BitsY> mod_ss(const value<BitsA> &a, const value<BitsB> &b) {
	return divmod_ss<BitsY>(a, b).second;
}

// Memory helper
struct memory_index {
	bool valid;
	size_t index;

	template<size_t BitsAddr>
	memory_index(const value<BitsAddr> &addr, size_t offset, size_t depth) {
		static_assert(value<BitsAddr>::chunks <= 1, "memory address is too wide");
		size_t offset_index = addr.data[0];

		valid = (offset_index >= offset && offset_index < offset + depth);
		index = offset_index - offset;
	}
};

} // namespace cxxrtl_yosys

#endif
