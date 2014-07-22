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

#ifndef SIGTOOLS_H
#define SIGTOOLS_H

#include "kernel/rtlil.h"
#include "kernel/log.h"
#include <assert.h>
#include <set>

struct SigPool
{
	typedef std::pair<RTLIL::Wire*,int> bitDef_t;
	std::set<bitDef_t> bits;

	void clear()
	{
		bits.clear();
	}

	void add(RTLIL::SigSpec sig)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			assert(c.width == 1);
			bitDef_t bit(c.wire, c.offset);
			bits.insert(bit);
		}
	}

	void add(const SigPool &other)
	{
		for (auto &bit : other.bits)
			bits.insert(bit);
	}

	void del(RTLIL::SigSpec sig)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			assert(c.width == 1);
			bitDef_t bit(c.wire, c.offset);
			bits.erase(bit);
		}
	}

	void del(const SigPool &other)
	{
		for (auto &bit : other.bits)
			bits.erase(bit);
	}

	void expand(RTLIL::SigSpec from, RTLIL::SigSpec to)
	{
		from.expand();
		to.expand();
		assert(from.chunks().size() == to.chunks().size());
		for (size_t i = 0; i < from.chunks().size(); i++) {
			bitDef_t bit_from(from.chunks()[i].wire, from.chunks()[i].offset);
			bitDef_t bit_to(to.chunks()[i].wire, to.chunks()[i].offset);
			if (bit_from.first == NULL || bit_to.first == NULL)
				continue;
			if (bits.count(bit_from) > 0)
				bits.insert(bit_to);
		}
	}

	RTLIL::SigSpec extract(RTLIL::SigSpec sig)
	{
		RTLIL::SigSpec result;
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			bitDef_t bit(c.wire, c.offset);
			if (bits.count(bit) > 0)
				result.append(c);
		}
		return result;
	}

	RTLIL::SigSpec remove(RTLIL::SigSpec sig)
	{
		RTLIL::SigSpec result;
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			bitDef_t bit(c.wire, c.offset);
			if (bits.count(bit) == 0)
				result.append(c);
		}
		return result;
	}

	bool check_any(RTLIL::SigSpec sig)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			bitDef_t bit(c.wire, c.offset);
			if (bits.count(bit) != 0)
				return true;
		}
		return false;
	}

	bool check_all(RTLIL::SigSpec sig)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			bitDef_t bit(c.wire, c.offset);
			if (bits.count(bit) == 0)
				return false;
		}
		return true;
	}

	RTLIL::SigSpec export_one()
	{
		RTLIL::SigSpec sig;
		for (auto &bit : bits) {
			sig.append(RTLIL::SigSpec(bit.first, 1, bit.second));
			break;
		}
		return sig;
	}

	RTLIL::SigSpec export_all()
	{
		RTLIL::SigSpec sig;
		for (auto &bit : bits)
			sig.append(RTLIL::SigSpec(bit.first, 1, bit.second));
		sig.sort_and_unify();
		return sig;
	}

	size_t size()
	{
		return bits.size();
	}
};

template <typename T, class Compare = std::less<T>>
struct SigSet
{
	typedef std::pair<RTLIL::Wire*,int> bitDef_t;
	std::map<bitDef_t, std::set<T, Compare>> bits;

	void clear()
	{
		bits.clear();
	}

	void insert(RTLIL::SigSpec sig, T data)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			assert(c.width == 1);
			bitDef_t bit(c.wire, c.offset);
			bits[bit].insert(data);
		}
	}

	void insert(RTLIL::SigSpec sig, const std::set<T> &data)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			assert(c.width == 1);
			bitDef_t bit(c.wire, c.offset);
			bits[bit].insert(data.begin(), data.end());
		}
	}

	void erase(RTLIL::SigSpec sig)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			assert(c.width == 1);
			bitDef_t bit(c.wire, c.offset);
			bits[bit].clear();
		}
	}

	void erase(RTLIL::SigSpec sig, T data)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			assert(c.width == 1);
			bitDef_t bit(c.wire, c.offset);
			bits[bit].erase(data);
		}
	}

	void erase(RTLIL::SigSpec sig, const std::set<T> &data)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			assert(c.width == 1);
			bitDef_t bit(c.wire, c.offset);
			bits[bit].erase(data.begin(), data.end());
		}
	}

	void find(RTLIL::SigSpec sig, std::set<T> &result)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			assert(c.width == 1);
			bitDef_t bit(c.wire, c.offset);
			for (auto &data : bits[bit])
				result.insert(data);
		}
	}

	std::set<T> find(RTLIL::SigSpec sig)
	{
		std::set<T> result;
		find(sig, result);
		return result;
	}

	bool has(RTLIL::SigSpec sig)
	{
		sig.expand();
		for (auto &c : sig.chunks()) {
			if (c.wire == NULL)
				continue;
			assert(c.width == 1);
			bitDef_t bit(c.wire, c.offset);
			if (bits.count(bit))
				return true;
		}
		return false;
	}
};

struct SigMap
{
	typedef std::pair<RTLIL::Wire*,int> bitDef_t;

	struct shared_bit_data_t {
		RTLIL::SigBit map_to;
		std::set<bitDef_t> bits;
	};

	std::map<bitDef_t, shared_bit_data_t*> bits;

	SigMap(RTLIL::Module *module = NULL)
	{
		if (module != NULL)
			set(module);
	}

	SigMap(const SigMap &other)
	{
		copy(other);
	}

	const SigMap &operator=(const SigMap &other)
	{
		copy(other);
		return *this;
	}

	void copy(const SigMap &other)
	{
		clear();
		for (auto &bit : other.bits) {
			bits[bit.first] = new shared_bit_data_t;
			bits[bit.first]->map_to = bit.second->map_to;
			bits[bit.first]->bits = bit.second->bits;
		}
	}

	void swap(SigMap &other)
	{
		bits.swap(other.bits);
	}

	~SigMap()
	{
		clear();
	}

	void clear()
	{
		std::set<shared_bit_data_t*> all_bd_ptr;
		for (auto &it : bits)
			all_bd_ptr.insert(it.second);
		for (auto bd_ptr : all_bd_ptr)
			delete bd_ptr;
		bits.clear();
	}

	void set(RTLIL::Module *module)
	{
		clear();
		for (auto &it : module->connections)
			add(it.first, it.second);
	}

	// internal helper function
	void register_bit(const RTLIL::SigBit &b)
	{
		bitDef_t bit(b.wire, b.offset);
		if (b.wire && bits.count(bit) == 0) {
			shared_bit_data_t *bd = new shared_bit_data_t;
			bd->map_to = b;
			bd->bits.insert(bit);
			bits[bit] = bd;
		}
	}

	// internal helper function
	void unregister_bit(const RTLIL::SigBit &b)
	{
		bitDef_t bit(b.wire, b.offset);
		if (b.wire && bits.count(bit) > 0) {
			shared_bit_data_t *bd = bits[bit];
			bd->bits.erase(bit);
			if (bd->bits.size() == 0)
				delete bd;
			bits.erase(bit);
		}
	}

	// internal helper function
	void merge_bit(const RTLIL::SigBit &bit1, const RTLIL::SigBit &bit2)
	{
		assert(bit1.wire != NULL && bit2.wire != NULL);

		bitDef_t b1(bit1.wire, bit1.offset);
		bitDef_t b2(bit2.wire, bit2.offset);

		shared_bit_data_t *bd1 = bits[b1];
		shared_bit_data_t *bd2 = bits[b2];
		assert(bd1 != NULL && bd2 != NULL);

		if (bd1 == bd2)
			return;

		if (bd1->bits.size() < bd2->bits.size())
		{
			for (auto &bit : bd1->bits)
				bits[bit] = bd2;
			bd2->bits.insert(bd1->bits.begin(), bd1->bits.end());
			delete bd1;
		}
		else
		{
			bd1->map_to = bd2->map_to;
			for (auto &bit : bd2->bits)
				bits[bit] = bd1;
			bd1->bits.insert(bd2->bits.begin(), bd2->bits.end());
			delete bd2;
		}
	}

	// internal helper function
	void set_bit(const RTLIL::SigBit &b1, const RTLIL::SigBit &b2)
	{
		assert(b1.wire != NULL);
		bitDef_t bit(b1.wire, b1.offset);
		assert(bits.count(bit) > 0);
		bits[bit]->map_to = b2;
	}

	// internal helper function
	void map_bit(RTLIL::SigBit &b) const
	{
		bitDef_t bit(b.wire, b.offset);
		if (b.wire && bits.count(bit) > 0)
			b = bits.at(bit)->map_to;
	}

	void add(RTLIL::SigSpec from, RTLIL::SigSpec to)
	{
		assert(SIZE(from) == SIZE(to));

		for (int i = 0; i < SIZE(from); i++)
		{
			RTLIL::SigBit &bf = from[i];
			RTLIL::SigBit &bt = to[i];

			if (bf.wire == NULL)
				continue;

			register_bit(bf);
			register_bit(bt);

			if (bt.wire != NULL)
				merge_bit(bf, bt);
			else
				set_bit(bf, bt);
		}
	}

	void add(RTLIL::SigSpec sig)
	{
		for (auto &bit : sig) {
			register_bit(bit);
			set_bit(bit, bit);
		}
	}

	void del(RTLIL::SigSpec sig)
	{
		for (auto &bit : sig)
			unregister_bit(bit);
	}

	void apply(RTLIL::SigSpec &sig) const
	{
		for (auto &bit : sig)
			map_bit(bit);
	}

	RTLIL::SigSpec operator()(RTLIL::SigSpec sig) const
	{
		apply(sig);
		return sig;
	}
};

#endif /* SIGTOOLS_H */
