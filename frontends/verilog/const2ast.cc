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
 *  ---
 *
 *  The Verilog frontend.
 *
 *  This frontend is using the AST frontend library (see frontends/ast/).
 *  Thus this frontend does not generate RTLIL code directly but creates an
 *  AST directly from the Verilog parse tree and then passes this AST to
 *  the AST frontend library.
 *
 *  ---
 *
 *  This file contains an ad-hoc parser for Verilog constants. The Verilog
 *  lexer does only recognize a constant but does not actually split it to its
 *  components. I.e. it just passes the Verilog code for the constant to the
 *  bison parser. The parser then uses the function const2ast() from this file
 *  to create an AST node for the constant.
 *
 */

#include "verilog_frontend.h"
#include "kernel/log.h"
#include <string.h>
#include <math.h>

YOSYS_NAMESPACE_BEGIN

using namespace AST;

// divide an arbitrary length decimal number by two and return the rest
static int my_decimal_div_by_two(std::vector<uint8_t> &digits)
{
	int carry = 0;
	for (size_t i = 0; i < digits.size(); i++) {
		log_assert(digits[i] < 10);
		digits[i] += carry * 10;
		carry = digits[i] % 2;
		digits[i] /= 2;
	}
	while (!digits.empty() && !digits.front())
		digits.erase(digits.begin());
	return carry;
}

// find the number of significant bits in a binary number (not including the sign bit)
static int my_ilog2(int x)
{
	int ret = 0;
	while (x != 0 && x != -1) {
		x = x >> 1;
		ret++;
	}
	return ret;
}

// parse a binary, decimal, hexadecimal or octal number with support for special bits ('x', 'z' and '?')
static void my_strtobin(std::vector<RTLIL::State> &data, const char *str, int len_in_bits, int base, char case_type)
{
	// all digits in string (MSB at index 0)
	std::vector<uint8_t> digits;

	while (*str) {
		if ('0' <= *str && *str <= '9')
			digits.push_back(*str - '0');
		else if ('a' <= *str && *str <= 'f')
			digits.push_back(10 + *str - 'a');
		else if ('A' <= *str && *str <= 'F')
			digits.push_back(10 + *str - 'A');
		else if (*str == 'x' || *str == 'X')
			digits.push_back(0xf0);
		else if (*str == 'z' || *str == 'Z')
			digits.push_back(0xf1);
		else if (*str == '?')
			digits.push_back(0xf2);
		str++;
	}

	if (base == 10) {
		data.clear();
		if (len_in_bits < 0) {
			while (!digits.empty())
				data.push_back(my_decimal_div_by_two(digits) ? RTLIL::S1 : RTLIL::S0);
			while (data.size() < 32)
				data.push_back(RTLIL::S0);
		} else {
			for (int i = 0; i < len_in_bits; i++)
				data.push_back(my_decimal_div_by_two(digits) ? RTLIL::S1 : RTLIL::S0);
		}
		return;
	}

	int bits_per_digit = my_ilog2(base-1);
	if (len_in_bits < 0)
		len_in_bits = std::max<int>(digits.size() * bits_per_digit, 32);

	data.clear();
	data.resize(len_in_bits);

	for (int i = 0; i < len_in_bits; i++) {
		int bitmask = 1 << (i % bits_per_digit);
		int digitidx = digits.size() - (i / bits_per_digit) - 1;
		if (digitidx < 0) {
			if (i > 0 && (data[i-1] == RTLIL::Sz || data[i-1] == RTLIL::Sx || data[i-1] == RTLIL::Sa))
				data[i] = data[i-1];
			else
				data[i] = RTLIL::S0;
		} else if (digits[digitidx] == 0xf0)
			data[i] = case_type == 'x' ? RTLIL::Sa : RTLIL::Sx;
		else if (digits[digitidx] == 0xf1)
			data[i] = case_type == 'x' || case_type == 'z' ? RTLIL::Sa : RTLIL::Sz;
		else if (digits[digitidx] == 0xf2)
			data[i] = RTLIL::Sa;
		else
			data[i] = (digits[digitidx] & bitmask) ? RTLIL::S1 : RTLIL::S0;
	}
}

// convert the verilog code for a constant to an AST node
AstNode *VERILOG_FRONTEND::const2ast(std::string code, char case_type, bool warn_z)
{
	if (warn_z) {
		AstNode *ret = const2ast(code, case_type);
		if (std::find(ret->bits.begin(), ret->bits.end(), RTLIL::State::Sz) != ret->bits.end())
			log_warning("Yosys does not support tri-state logic at the moment. (%s:%d)\n",
				current_filename.c_str(), frontend_verilog_yyget_lineno());
		return ret;
	}

	const char *str = code.c_str();

	// Strings
	if (*str == '"') {
		int len = strlen(str) - 2;
		std::vector<RTLIL::State> data;
		data.reserve(len * 8);
		for (int i = 0; i < len; i++) {
			unsigned char ch = str[len - i];
			for (int j = 0; j < 8; j++) {
				data.push_back((ch & 1) ? RTLIL::S1 : RTLIL::S0);
				ch = ch >> 1;
			}
		}
		AstNode *ast = AstNode::mkconst_bits(data, false);
		ast->str = code;
		return ast;
	}

	for (size_t i = 0; i < code.size(); i++)
		if (code[i] == '_' || code[i] == ' ' || code[i] == '\t' || code[i] == '\r' || code[i] == '\n')
			code.erase(code.begin()+(i--));
	str = code.c_str();

	char *endptr;
	long len_in_bits = strtol(str, &endptr, 10);

	// Simple base-10 integer
	if (*endptr == 0) {
		std::vector<RTLIL::State> data;
		my_strtobin(data, str, -1, 10, case_type);
		if (data.back() == RTLIL::S1)
			data.push_back(RTLIL::S0);
		return AstNode::mkconst_bits(data, true);
	}

	// unsized constant
	if (str == endptr)
		len_in_bits = -1;

	// The "<bits>'s?[bodhBODH]<digits>" syntax
	if (*endptr == '\'')
	{
		std::vector<RTLIL::State> data;
		bool is_signed = false;
		if (*(endptr+1) == 's') {
			is_signed = true;
			endptr++;
		}
		switch (*(endptr+1))
		{
		case 'b':
		case 'B':
			my_strtobin(data, endptr+2, len_in_bits, 2, case_type);
			break;
		case 'o':
		case 'O':
			my_strtobin(data, endptr+2, len_in_bits, 8, case_type);
			break;
		case 'd':
		case 'D':
			my_strtobin(data, endptr+2, len_in_bits, 10, case_type);
			break;
		case 'h':
		case 'H':
			my_strtobin(data, endptr+2, len_in_bits, 16, case_type);
			break;
		default:
			return NULL;
		}
		if (len_in_bits < 0) {
			if (is_signed && data.back() == RTLIL::S1)
				data.push_back(RTLIL::S0);
			while (data.size() < 32)
				data.push_back(RTLIL::S0);
		}
		return AstNode::mkconst_bits(data, is_signed);
	}

	return NULL;
}

YOSYS_NAMESPACE_END

