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

#ifndef BITPATTERN_H
#define BITPATTERN_H

#include "kernel/log.h"
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

struct BitPatternPool
{
	int width;
	typedef std::vector<RTLIL::State> bits_t;
	std::set<bits_t> pool;

	BitPatternPool(RTLIL::SigSpec sig)
	{
		width = sig.size();
		if (width > 0) {
			std::vector<RTLIL::State> pattern(width);
			for (int i = 0; i < width; i++) {
				if (sig[i].wire == NULL && sig[i].data <= RTLIL::State::S1)
					pattern[i] = sig[i].data;
				else
					pattern[i] = RTLIL::State::Sa;
			}
			pool.insert(pattern);
		}
	}

	BitPatternPool(int width)
	{
		this->width = width;
		if (width > 0) {
			std::vector<RTLIL::State> pattern(width);
			for (int i = 0; i < width; i++)
				pattern[i] = RTLIL::State::Sa;
			pool.insert(pattern);
		}
	}

	bits_t sig2bits(RTLIL::SigSpec sig)
	{
		bits_t bits = sig.as_const().bits;
		for (auto &b : bits)
			if (b > RTLIL::State::S1)
				b = RTLIL::State::Sa;
		return bits;
	}

	bool match(bits_t a, bits_t b)
	{
		log_assert(int(a.size()) == width);
		log_assert(int(b.size()) == width);
		for (int i = 0; i < width; i++)
			if (a[i] <= RTLIL::State::S1 && b[i] <= RTLIL::State::S1 && a[i] != b[i])
				return false;
		return true;
	}

	bool has_any(RTLIL::SigSpec sig)
	{
		bits_t bits = sig2bits(sig);
		for (auto &it : pool)
			if (match(it, bits))
				return true;
		return false;
	}

	bool has_all(RTLIL::SigSpec sig)
	{
		bits_t bits = sig2bits(sig);
		for (auto &it : pool)
			if (match(it, bits)) {
				for (int i = 0; i < width; i++)
					if (bits[i] > RTLIL::State::S1 && it[i] <= RTLIL::State::S1)
						goto next_pool_entry;
				return true;
	next_pool_entry:;
			}
		return false;
	}

	bool take(RTLIL::SigSpec sig)
	{
		bool status = false;
		bits_t bits = sig2bits(sig);
		std::vector<bits_t> pattern_list;
		for (auto &it : pool)
			if (match(it, bits))
				pattern_list.push_back(it);
		for (auto pattern : pattern_list) {
			pool.erase(pattern);
			for (int i = 0; i < width; i++) {
				if (pattern[i] != RTLIL::State::Sa || bits[i] == RTLIL::State::Sa)
					continue;
				bits_t new_pattern = pattern;
				new_pattern[i] = bits[i] == RTLIL::State::S1 ? RTLIL::State::S0 : RTLIL::State::S1;
				pool.insert(new_pattern);
			}
			status = true;
		}
		return status;
	}

	bool take_all()
	{
		if (pool.empty())
			return false;
		pool.clear();
		return true;
	}

	bool empty()
	{
		return pool.empty();
	}
}; 

YOSYS_NAMESPACE_END

#endif
