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
	struct bits_t {
		std::vector<RTLIL::State> bitdata;
		mutable unsigned int cached_hash;
		bits_t(int width = 0) : bitdata(width), cached_hash(0) { }
		RTLIL::State &operator[](int index) {
			return bitdata[index];
		}
		const RTLIL::State &operator[](int index) const {
			return bitdata[index];
		}
		bool operator==(const bits_t &other) const {
			if (hash() != other.hash())
				return false;
			return bitdata == other.bitdata;
		}
		unsigned int hash() const {
			if (!cached_hash)
				cached_hash = hash_ops<std::vector<RTLIL::State>>::hash(bitdata);
			return cached_hash;
		}
	};
	pool<bits_t> database;

	BitPatternPool(RTLIL::SigSpec sig)
	{
		width = sig.size();
		if (width > 0) {
			bits_t pattern(width);
			for (int i = 0; i < width; i++) {
				if (sig[i].wire == NULL && sig[i].data <= RTLIL::State::S1)
					pattern[i] = sig[i].data;
				else
					pattern[i] = RTLIL::State::Sa;
			}
			database.insert(pattern);
		}
	}

	BitPatternPool(int width)
	{
		this->width = width;
		if (width > 0) {
			bits_t pattern(width);
			for (int i = 0; i < width; i++)
				pattern[i] = RTLIL::State::Sa;
			database.insert(pattern);
		}
	}

	bits_t sig2bits(RTLIL::SigSpec sig)
	{
		bits_t bits;
		bits.bitdata = sig.as_const().bits;
		for (auto &b : bits.bitdata)
			if (b > RTLIL::State::S1)
				b = RTLIL::State::Sa;
		return bits;
	}

	bool match(bits_t a, bits_t b)
	{
		log_assert(int(a.bitdata.size()) == width);
		log_assert(int(b.bitdata.size()) == width);
		for (int i = 0; i < width; i++)
			if (a[i] <= RTLIL::State::S1 && b[i] <= RTLIL::State::S1 && a[i] != b[i])
				return false;
		return true;
	}

	bool has_any(RTLIL::SigSpec sig)
	{
		bits_t bits = sig2bits(sig);
		for (auto &it : database)
			if (match(it, bits))
				return true;
		return false;
	}

	bool has_all(RTLIL::SigSpec sig)
	{
		bits_t bits = sig2bits(sig);
		for (auto &it : database)
			if (match(it, bits)) {
				for (int i = 0; i < width; i++)
					if (bits[i] > RTLIL::State::S1 && it[i] <= RTLIL::State::S1)
						goto next_database_entry;
				return true;
	next_database_entry:;
			}
		return false;
	}

	bool take(RTLIL::SigSpec sig)
	{
		bool status = false;
		bits_t bits = sig2bits(sig);
		for (auto it = database.begin(); it != database.end();)
			if (match(*it, bits)) {
				for (int i = 0; i < width; i++) {
					if ((*it)[i] != RTLIL::State::Sa || bits[i] == RTLIL::State::Sa)
						continue;
					bits_t new_pattern;
					new_pattern.bitdata = it->bitdata;
					new_pattern[i] = bits[i] == RTLIL::State::S1 ? RTLIL::State::S0 : RTLIL::State::S1;
					database.insert(new_pattern);
				}
				it = database.erase(it);
				status = true;
				continue;
			} else
				++it;
		return status;
	}

	bool take_all()
	{
		if (database.empty())
			return false;
		database.clear();
		return true;
	}

	bool empty()
	{
		return database.empty();
	}
};

YOSYS_NAMESPACE_END

#endif
