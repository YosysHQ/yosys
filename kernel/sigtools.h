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
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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
		assert(from.chunks.size() == to.chunks.size());
		for (size_t i = 0; i < from.chunks.size(); i++) {
			bitDef_t bit_from(from.chunks[i].wire, from.chunks[i].offset);
			bitDef_t bit_to(to.chunks[i].wire, to.chunks[i].offset);
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
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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

template <typename T>
struct SigSet
{
	typedef std::pair<RTLIL::Wire*,int> bitDef_t;
	std::map<bitDef_t, std::set<T>> bits;

	void clear()
	{
		bits.clear();
	}

	void insert(RTLIL::SigSpec sig, T data)
	{
		sig.expand();
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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
		for (auto &c : sig.chunks) {
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
		RTLIL::SigChunk chunk;
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
			bits[bit.first]->chunk = bit.second->chunk;
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
	void register_bit(const RTLIL::SigChunk &c)
	{
		assert(c.width == 1);
		bitDef_t bit(c.wire, c.offset);
		if (c.wire && bits.count(bit) == 0) {
			shared_bit_data_t *bd = new shared_bit_data_t;
			bd->chunk = c;
			bd->bits.insert(bit);
			bits[bit] = bd;
		}
	}

	// internal helper function
	void unregister_bit(const RTLIL::SigChunk &c)
	{
		assert(c.width == 1);
		bitDef_t bit(c.wire, c.offset);
		if (c.wire && bits.count(bit) > 0) {
			shared_bit_data_t *bd = bits[bit];
			bd->bits.erase(bit);
			if (bd->bits.size() == 0)
				delete bd;
			bits.erase(bit);
		}
	}

	// internal helper function
	void merge_bit(const RTLIL::SigChunk &c1, const RTLIL::SigChunk &c2)
	{
		assert(c1.wire != NULL && c2.wire != NULL);
		assert(c1.width == 1 && c2.width == 1);

		bitDef_t b1(c1.wire, c1.offset);
		bitDef_t b2(c2.wire, c2.offset);

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
			bd1->chunk = bd2->chunk;
			for (auto &bit : bd2->bits)
				bits[bit] = bd1;
			bd1->bits.insert(bd2->bits.begin(), bd2->bits.end());
			delete bd2;
		}
	}

	// internal helper function
	void set_bit(const RTLIL::SigChunk &c1, const RTLIL::SigChunk &c2)
	{
		assert(c1.wire != NULL);
		assert(c1.width == 1 && c2.width == 1);
		bitDef_t bit(c1.wire, c1.offset);
		assert(bits.count(bit) > 0);
		bits[bit]->chunk = c2;
	}

	// internal helper function
	void map_bit(RTLIL::SigChunk &c)
	{
		assert(c.width == 1);
		bitDef_t bit(c.wire, c.offset);
		if (c.wire && bits.count(bit) > 0)
			c = bits[bit]->chunk;
	}

	void add(RTLIL::SigSpec from, RTLIL::SigSpec to)
	{
		from.expand();
		to.expand();

		assert(from.chunks.size() == to.chunks.size());
		for (size_t i = 0; i < from.chunks.size(); i++)
		{
			RTLIL::SigChunk &cf = from.chunks[i];
			RTLIL::SigChunk &ct = to.chunks[i];

			if (cf.wire == NULL)
				continue;

			register_bit(cf);
			register_bit(ct);

			if (ct.wire != NULL)
				merge_bit(cf, ct);
			else
				set_bit(cf, ct);
		}
	}

	void add(RTLIL::SigSpec sig)
	{
		sig.expand();
		for (size_t i = 0; i < sig.chunks.size(); i++)
		{
			RTLIL::SigChunk &c = sig.chunks[i];
			if (c.wire != NULL) {
				register_bit(c);
				set_bit(c, c);
			}
		}
	}

	void del(RTLIL::SigSpec sig)
	{
		sig.expand();
		for (auto &c : sig.chunks)
			unregister_bit(c);
	}

	void apply(RTLIL::SigSpec &sig)
	{
		sig.expand();
		for (auto &c : sig.chunks)
			map_bit(c);
		sig.optimize();
	}

	RTLIL::SigSpec operator()(RTLIL::SigSpec sig)
	{
		apply(sig);
		return sig;
	}
};

#endif /* SIGTOOLS_H */
