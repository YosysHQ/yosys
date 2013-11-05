/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#include "kernel/rtlil.h"
#include "libs/bigint/BigIntegerLibrary.hh"
#include <assert.h>

static BigInteger const2big(const RTLIL::Const &val, bool as_signed, int &undef_bit_pos)
{
	BigInteger result = 0, this_bit = 1;
	for (size_t i = 0; i < val.bits.size(); i++) {
		if (val.bits[i] == RTLIL::State::S1) {
			if (as_signed && i+1 == val.bits.size())
				result -= this_bit;
			else
				result += this_bit;
		}
		else if (val.bits[i] != RTLIL::State::S0) {
			if (undef_bit_pos < 0)
				undef_bit_pos = i;
		}
		this_bit *= 2;
	}
	return result;
}

static RTLIL::Const big2const(const BigInteger &val, int result_len, int undef_bit_pos)
{
	BigUnsigned mag = val.getMagnitude();
	RTLIL::Const result(0, result_len);

	if (!mag.isZero())
	{
		if (val.getSign() < 0)
		{
			mag--;
			for (int i = 0; i < result_len; i++)
				result.bits[i] = mag.getBit(i) ? RTLIL::State::S0 : RTLIL::State::S1;
		}
		else
		{
			for (int i = 0; i < result_len; i++)
				result.bits[i] = mag.getBit(i) ? RTLIL::State::S1 : RTLIL::State::S0;
		}
	}

	if (undef_bit_pos >= 0)
		for (int i = undef_bit_pos; i < result_len; i++)
			result.bits[i] = RTLIL::State::Sx;

	return result;
}

static RTLIL::State logic_and(RTLIL::State a, RTLIL::State b)
{
	if (a == RTLIL::State::S0) return RTLIL::State::S0;
	if (b == RTLIL::State::S0) return RTLIL::State::S0;
	if (a != RTLIL::State::S1) return RTLIL::State::Sx;
	if (b != RTLIL::State::S1) return RTLIL::State::Sx;
	return RTLIL::State::S1;
}

static RTLIL::State logic_or(RTLIL::State a, RTLIL::State b)
{
	if (a == RTLIL::State::S1) return RTLIL::State::S1;
	if (b == RTLIL::State::S1) return RTLIL::State::S1;
	if (a != RTLIL::State::S0) return RTLIL::State::Sx;
	if (b != RTLIL::State::S0) return RTLIL::State::Sx;
	return RTLIL::State::S0;
}

static RTLIL::State logic_xor(RTLIL::State a, RTLIL::State b)
{
	if (a != RTLIL::State::S0 && a != RTLIL::State::S1) return RTLIL::State::Sx;
	if (b != RTLIL::State::S0 && b != RTLIL::State::S1) return RTLIL::State::Sx;
	return a != b ? RTLIL::State::S1 : RTLIL::State::S0;
}

static RTLIL::State logic_xnor(RTLIL::State a, RTLIL::State b)
{
	if (a != RTLIL::State::S0 && a != RTLIL::State::S1) return RTLIL::State::Sx;
	if (b != RTLIL::State::S0 && b != RTLIL::State::S1) return RTLIL::State::Sx;
	return a == b ? RTLIL::State::S1 : RTLIL::State::S0;
}

RTLIL::Const RTLIL::const_not(const RTLIL::Const &arg1, const RTLIL::Const&, bool signed1, bool, int result_len)
{
	if (result_len < 0)
		result_len = arg1.bits.size();

	RTLIL::Const arg1_ext = arg1;
	while (int(arg1_ext.bits.size()) < result_len)
		arg1_ext.bits.push_back(signed1 && arg1_ext.bits.size() ? arg1_ext.bits.back() : RTLIL::State::S0);

	RTLIL::Const result(RTLIL::State::Sx, result_len);
	for (size_t i = 0; i < size_t(result_len); i++) {
		if (i >= arg1_ext.bits.size())
			result.bits[i] = RTLIL::State::S0;
		else if (arg1_ext.bits[i] == RTLIL::State::S0)
			result.bits[i] = RTLIL::State::S1;
		else if (arg1_ext.bits[i] == RTLIL::State::S1)
			result.bits[i] = RTLIL::State::S0;
	}

	return result;
}

static RTLIL::Const logic_wrapper(RTLIL::State(*logic_func)(RTLIL::State, RTLIL::State),
		RTLIL::Const arg1, RTLIL::Const arg2, bool signed1, bool signed2, int result_len = -1)
{
	if (result_len < 0)
		result_len = std::max(arg1.bits.size(), arg2.bits.size());

	while (int(arg1.bits.size()) < result_len)
		arg1.bits.push_back(signed1 && arg1.bits.size() ? arg1.bits.back() : RTLIL::State::S0);

	while (int(arg2.bits.size()) < result_len)
		arg2.bits.push_back(signed2 && arg2.bits.size() ? arg2.bits.back() : RTLIL::State::S0);

	RTLIL::Const result(RTLIL::State::Sx, result_len);
	for (size_t i = 0; i < size_t(result_len); i++) {
		RTLIL::State a = i < arg1.bits.size() ? arg1.bits[i] : RTLIL::State::S0;
		RTLIL::State b = i < arg2.bits.size() ? arg2.bits[i] : RTLIL::State::S0;
		result.bits[i] = logic_func(a, b);
	}

	return result;
}

RTLIL::Const RTLIL::const_and(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	return logic_wrapper(logic_and, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::Const RTLIL::const_or(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	return logic_wrapper(logic_or, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::Const RTLIL::const_xor(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	return logic_wrapper(logic_xor, arg1, arg2, signed1, signed2, result_len);
}

RTLIL::Const RTLIL::const_xnor(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	return logic_wrapper(logic_xnor, arg1, arg2, signed1, signed2, result_len);
}

static RTLIL::Const logic_reduce_wrapper(RTLIL::State initial, RTLIL::State(*logic_func)(RTLIL::State, RTLIL::State), const RTLIL::Const &arg1)
{
	RTLIL::State temp = initial;

	for (size_t i = 0; i < arg1.bits.size(); i++)
		temp = logic_func(temp, arg1.bits[i]);

	return RTLIL::Const(temp);
}

RTLIL::Const RTLIL::const_reduce_and(const RTLIL::Const &arg1, const RTLIL::Const&, bool, bool, int)
{
	return logic_reduce_wrapper(RTLIL::State::S1, logic_and, arg1);
}

RTLIL::Const RTLIL::const_reduce_or(const RTLIL::Const &arg1, const RTLIL::Const&, bool, bool, int)
{
	return logic_reduce_wrapper(RTLIL::State::S0, logic_or, arg1);
}

RTLIL::Const RTLIL::const_reduce_xor(const RTLIL::Const &arg1, const RTLIL::Const&, bool, bool, int)
{
	return logic_reduce_wrapper(RTLIL::State::S0, logic_xor, arg1);
}

RTLIL::Const RTLIL::const_reduce_xnor(const RTLIL::Const &arg1, const RTLIL::Const&, bool, bool, int)
{
	RTLIL::Const not_y = logic_reduce_wrapper(RTLIL::State::S0, logic_xor, arg1);
	if (not_y.bits.front() == RTLIL::State::S0) return RTLIL::State::S1;
	if (not_y.bits.front() == RTLIL::State::S1) return RTLIL::State::S0;
	return RTLIL::State::Sx;
}

RTLIL::Const RTLIL::const_reduce_bool(const RTLIL::Const &arg1, const RTLIL::Const&, bool, bool, int)
{
	return logic_reduce_wrapper(RTLIL::State::S0, logic_or, arg1);
}

RTLIL::Const RTLIL::const_logic_not(const RTLIL::Const &arg1, const RTLIL::Const&, bool signed1, bool, int)
{
	int undef_bit_pos_a = -1;
	BigInteger a = const2big(arg1, signed1, undef_bit_pos_a);

	if (a.isZero()) {
		if (undef_bit_pos_a >= 0)
			return RTLIL::Const(RTLIL::State::Sx);
		return RTLIL::Const(RTLIL::State::S1);
	}

	return RTLIL::Const(RTLIL::State::S0);
}

RTLIL::Const RTLIL::const_logic_and(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int)
{
	int undef_bit_pos_a = -1, undef_bit_pos_b = -1;
	BigInteger a = const2big(arg1, signed1, undef_bit_pos_a);
	BigInteger b = const2big(arg2, signed2, undef_bit_pos_b);

	if (a.isZero() || b.isZero()) {
		if (undef_bit_pos_a >= 0 && undef_bit_pos_b >= 0)
			return RTLIL::Const(RTLIL::State::Sx);
		return RTLIL::Const(RTLIL::State::S0);
	}

	return RTLIL::Const(RTLIL::State::S1);
}

RTLIL::Const RTLIL::const_logic_or(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int)
{
	int undef_bit_pos_a = -1, undef_bit_pos_b = -1;
	BigInteger a = const2big(arg1, signed1, undef_bit_pos_a);
	BigInteger b = const2big(arg2, signed2, undef_bit_pos_b);

	if (a.isZero() && b.isZero()) {
		if (undef_bit_pos_a >= 0 || undef_bit_pos_b >= 0)
			return RTLIL::Const(RTLIL::State::Sx);
		return RTLIL::Const(RTLIL::State::S0);
	}

	return RTLIL::Const(RTLIL::State::S1);
}

static RTLIL::Const const_shift(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool sign_ext, int direction, int result_len)
{
	int undef_bit_pos = -1;
	BigInteger offset = const2big(arg2, false, undef_bit_pos) * direction;

	if (result_len < 0)
		result_len = arg1.bits.size();

	RTLIL::Const result(RTLIL::State::Sx, result_len);
	if (undef_bit_pos >= 0)
		return result;

	for (int i = 0; i < result_len; i++) {
		BigInteger pos = BigInteger(i) + offset;
		if (pos < 0)
			result.bits[i] = RTLIL::State::S0;
		else if (pos >= arg1.bits.size())
			result.bits[i] = sign_ext ? arg1.bits.back() : RTLIL::State::S0;
		else
			result.bits[i] = arg1.bits[pos.toInt()];
	}

	return result;
}

RTLIL::Const RTLIL::const_shl(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool, int result_len)
{
	RTLIL::Const arg1_ext = arg1;
	while (int(arg1_ext.bits.size()) < result_len)
		arg1_ext.bits.push_back(signed1 && arg1_ext.bits.size() ? arg1_ext.bits.back() : RTLIL::State::S0);
	return const_shift(arg1_ext, arg2, false, -1, result_len);
}

RTLIL::Const RTLIL::const_shr(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool, int result_len)
{
	RTLIL::Const arg1_ext = arg1;
	while (int(arg1_ext.bits.size()) < result_len)
		arg1_ext.bits.push_back(signed1 && arg1_ext.bits.size() ? arg1_ext.bits.back() : RTLIL::State::S0);
	return const_shift(arg1_ext, arg2, false, +1, result_len);
}

RTLIL::Const RTLIL::const_sshl(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	if (!signed1)
		return const_shl(arg1, arg2, signed1, signed2, result_len);
	return const_shift(arg1, arg2, true, -1, result_len);
}

RTLIL::Const RTLIL::const_sshr(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	if (!signed1)
		return const_shr(arg1, arg2, signed1, signed2, result_len);
	return const_shift(arg1, arg2, true, +1, result_len);
}

RTLIL::Const RTLIL::const_lt(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int)
{
	int undef_bit_pos = -1;
	bool y = const2big(arg1, signed1, undef_bit_pos) < const2big(arg2, signed2, undef_bit_pos);
	return RTLIL::Const(undef_bit_pos >= 0 ? RTLIL::State::Sx : y ? RTLIL::State::S1 : RTLIL::State::S0);
}

RTLIL::Const RTLIL::const_le(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int)
{
	int undef_bit_pos = -1;
	bool y = const2big(arg1, signed1, undef_bit_pos) <= const2big(arg2, signed2, undef_bit_pos);
	return RTLIL::Const(undef_bit_pos >= 0 ? RTLIL::State::Sx : y ? RTLIL::State::S1 : RTLIL::State::S0);
}

RTLIL::Const RTLIL::const_eq(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int)
{
	int undef_bit_pos = -1;
	bool y = const2big(arg1, signed1, undef_bit_pos) == const2big(arg2, signed2, undef_bit_pos);
	return RTLIL::Const(undef_bit_pos >= 0 ? RTLIL::State::Sx : y ? RTLIL::State::S1 : RTLIL::State::S0);
}

RTLIL::Const RTLIL::const_ne(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int)
{
	int undef_bit_pos = -1;
	bool y = const2big(arg1, signed1, undef_bit_pos) != const2big(arg2, signed2, undef_bit_pos);
	return RTLIL::Const(undef_bit_pos >= 0 ? RTLIL::State::Sx : y ? RTLIL::State::S1 : RTLIL::State::S0);
}

RTLIL::Const RTLIL::const_ge(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int)
{
	int undef_bit_pos = -1;
	bool y = const2big(arg1, signed1, undef_bit_pos) >= const2big(arg2, signed2, undef_bit_pos);
	return RTLIL::Const(undef_bit_pos >= 0 ? RTLIL::State::Sx : y ? RTLIL::State::S1 : RTLIL::State::S0);
}

RTLIL::Const RTLIL::const_gt(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int)
{
	int undef_bit_pos = -1;
	bool y = const2big(arg1, signed1, undef_bit_pos) > const2big(arg2, signed2, undef_bit_pos);
	return RTLIL::Const(undef_bit_pos >= 0 ? RTLIL::State::Sx : y ? RTLIL::State::S1 : RTLIL::State::S0);
}

RTLIL::Const RTLIL::const_add(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	int undef_bit_pos = -1;
	BigInteger y = const2big(arg1, signed1, undef_bit_pos) + const2big(arg2, signed2, undef_bit_pos);
	return big2const(y, result_len >= 0 ? result_len : std::max(arg1.bits.size(), arg2.bits.size()), undef_bit_pos);
}

RTLIL::Const RTLIL::const_sub(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	int undef_bit_pos = -1;
	BigInteger y = const2big(arg1, signed1, undef_bit_pos) - const2big(arg2, signed2, undef_bit_pos);
	return big2const(y, result_len >= 0 ? result_len : std::max(arg1.bits.size(), arg2.bits.size()), undef_bit_pos);
}

RTLIL::Const RTLIL::const_mul(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	int undef_bit_pos = -1;
	BigInteger y = const2big(arg1, signed1, undef_bit_pos) * const2big(arg2, signed2, undef_bit_pos);
	return big2const(y, result_len >= 0 ? result_len : std::max(arg1.bits.size(), arg2.bits.size()), std::min(undef_bit_pos, 0));
}

RTLIL::Const RTLIL::const_div(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	int undef_bit_pos = -1;
	BigInteger a = const2big(arg1, signed1, undef_bit_pos);
	BigInteger b = const2big(arg2, signed2, undef_bit_pos);
	if (b.isZero())
		return RTLIL::Const(RTLIL::State::Sx, result_len);
	bool result_neg = (a.getSign() == BigInteger::negative) != (b.getSign() == BigInteger::negative);
	a = a.getSign() == BigInteger::negative ? -a : a;
	b = b.getSign() == BigInteger::negative ? -b : b;
	return big2const(result_neg ? -(a / b) : (a / b), result_len >= 0 ? result_len : std::max(arg1.bits.size(), arg2.bits.size()), std::min(undef_bit_pos, 0));
}

RTLIL::Const RTLIL::const_mod(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	int undef_bit_pos = -1;
	BigInteger a = const2big(arg1, signed1, undef_bit_pos);
	BigInteger b = const2big(arg2, signed2, undef_bit_pos);
	if (b.isZero())
		return RTLIL::Const(RTLIL::State::Sx, result_len);
	bool result_neg = a.getSign() == BigInteger::negative;
	a = a.getSign() == BigInteger::negative ? -a : a;
	b = b.getSign() == BigInteger::negative ? -b : b;
	return big2const(result_neg ? -(a % b) : (a % b), result_len >= 0 ? result_len : std::max(arg1.bits.size(), arg2.bits.size()), std::min(undef_bit_pos, 0));
}

RTLIL::Const RTLIL::const_pow(const RTLIL::Const &arg1, const RTLIL::Const &arg2, bool signed1, bool signed2, int result_len)
{
	int undef_bit_pos = -1;

	BigInteger a = const2big(arg1, signed1, undef_bit_pos);
	BigInteger b = const2big(arg2, signed2, undef_bit_pos);
	BigInteger y = 1;

	if (b < 0 || a == 0) {
		y = 0;
	} else { 
		while (b > 0) {
			y = y * a;
			if (y.getLength() > 0x10000) {
				undef_bit_pos = 0;
				break;
			}
			b--;
		}
	}

	return big2const(y, result_len >= 0 ? result_len : std::max(arg1.bits.size(), arg2.bits.size()), std::min(undef_bit_pos, 0));
}

RTLIL::Const RTLIL::const_pos(const RTLIL::Const &arg1, const RTLIL::Const&, bool signed1, bool, int result_len)
{
	RTLIL::Const arg1_ext = arg1;
	while (int(arg1_ext.bits.size()) < result_len)
		arg1_ext.bits.push_back(signed1 && arg1_ext.bits.size() ? arg1_ext.bits.back() : RTLIL::State::S0);

	RTLIL::Const zero(RTLIL::State::S0, 1);
	return RTLIL::const_add(zero, arg1_ext, false, signed1, result_len);
}

RTLIL::Const RTLIL::const_neg(const RTLIL::Const &arg1, const RTLIL::Const&, bool signed1, bool, int result_len)
{
	RTLIL::Const arg1_ext = arg1;
	while (int(arg1_ext.bits.size()) < result_len)
		arg1_ext.bits.push_back(signed1 && arg1_ext.bits.size() ? arg1_ext.bits.back() : RTLIL::State::S0);

	RTLIL::Const zero(RTLIL::State::S0, 1);
	return RTLIL::const_sub(zero, arg1_ext, false, signed1, result_len);
}

