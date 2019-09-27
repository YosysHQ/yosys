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
		if (digits[i] >= 10)
			log_file_error(current_filename, get_line_num(), "Invalid use of [a-fxz?] in decimal constant.\n");
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
static void my_strtobin(std::vector<RTLIL::State> &data, const char *str, int len_in_bits, int base, char case_type, bool is_unsized)
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
		else if (*str == 'z' || *str == 'Z' || *str == '?')
			digits.push_back(0xf1);
		str++;
	}

	if (base == 10 && GetSize(digits) == 1 && digits.front() >= 0xf0)
		base = 2;

	data.clear();

	if (base == 10) {
		while (!digits.empty())
			data.push_back(my_decimal_div_by_two(digits) ? State::S1 : State::S0);
	} else {
		int bits_per_digit = my_ilog2(base-1);
		for (auto it = digits.rbegin(), e = digits.rend(); it != e; it++) {
			if (*it > (base-1) && *it < 0xf0)
				log_file_error(current_filename, get_line_num(), "Digit larger than %d used in in base-%d constant.\n",
					       base-1, base);
			for (int i = 0; i < bits_per_digit; i++) {
				int bitmask = 1 << i;
				if (*it == 0xf0)
					data.push_back(case_type == 'x' ? RTLIL::Sa : RTLIL::Sx);
				else if (*it == 0xf1)
					data.push_back(case_type == 'x' || case_type == 'z' ? RTLIL::Sa : RTLIL::Sz);
				else
					data.push_back((*it & bitmask) ? State::S1 : State::S0);
			}
		}
	}

	int len = GetSize(data);
	RTLIL::State msb = data.empty() ? State::S0 : data.back();

	if (len_in_bits < 0) {
		if (len < 32)
			data.resize(32, msb == State::S0 || msb == State::S1 ? RTLIL::S0 : msb);
		return;
	}

	if (is_unsized && (len > len_in_bits))
		log_file_error(current_filename, get_line_num(), "Unsized constant must have width of 1 bit, but have %d bits!\n", len);

	for (len = len - 1; len >= 0; len--)
		if (data[len] == State::S1)
			break;
	if (msb == State::S0 || msb == State::S1) {
		len += 1;
		data.resize(len_in_bits, State::S0);
	} else {
		len += 2;
		data.resize(len_in_bits, msb);
	}

	if (len > len_in_bits)
		log_warning("Literal has a width of %d bit, but value requires %d bit. (%s:%d)\n",
			len_in_bits, len, current_filename.c_str(), get_line_num());
}

// convert the Verilog code for a constant to an AST node
AstNode *VERILOG_FRONTEND::const2ast(std::string code, char case_type, bool warn_z)
{
	if (warn_z) {
		AstNode *ret = const2ast(code, case_type);
		if (ret != nullptr && std::find(ret->bits.begin(), ret->bits.end(), RTLIL::State::Sz) != ret->bits.end())
			log_warning("Yosys has only limited support for tri-state logic at the moment. (%s:%d)\n",
				current_filename.c_str(), get_line_num());
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
				data.push_back((ch & 1) ? State::S1 : State::S0);
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
		my_strtobin(data, str, -1, 10, case_type, false);
		if (data.back() == State::S1)
			data.push_back(State::S0);
		return AstNode::mkconst_bits(data, true);
	}

	// unsized constant
	if (str == endptr)
		len_in_bits = -1;

	// The "<bits>'[sS]?[bodhBODH]<digits>" syntax
	if (*endptr == '\'')
	{
		std::vector<RTLIL::State> data;
		bool is_signed = false;
		bool is_unsized = len_in_bits < 0;
		if (*(endptr+1) == 's' || *(endptr+1) == 'S') {
			is_signed = true;
			endptr++;
		}
		switch (*(endptr+1))
		{
		case 'b':
		case 'B':
			my_strtobin(data, endptr+2, len_in_bits, 2, case_type, is_unsized);
			break;
		case 'o':
		case 'O':
			my_strtobin(data, endptr+2, len_in_bits, 8, case_type, is_unsized);
			break;
		case 'd':
		case 'D':
			my_strtobin(data, endptr+2, len_in_bits, 10, case_type, is_unsized);
			break;
		case 'h':
		case 'H':
			my_strtobin(data, endptr+2, len_in_bits, 16, case_type, is_unsized);
			break;
		default:
			char next_char = char(tolower(*(endptr+1)));
			if (next_char == '0' || next_char == '1' || next_char == 'x' || next_char == 'z') {
				is_unsized = true;
				my_strtobin(data, endptr+1, 1, 2, case_type, is_unsized);
			} else {
				return NULL;
			}
		}
		if (len_in_bits < 0) {
			if (is_signed && data.back() == State::S1)
				data.push_back(State::S0);
		}
		return AstNode::mkconst_bits(data, is_signed, is_unsized);
	}

	return NULL;
}

YOSYS_NAMESPACE_END
