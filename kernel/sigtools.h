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

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct SigPool
{
	struct bitDef_t : public std::pair<RTLIL::Wire*, int> {
		bitDef_t() : std::pair<RTLIL::Wire*, int>(NULL, 0) { }
		bitDef_t(const RTLIL::SigBit &bit) : std::pair<RTLIL::Wire*, int>(bit.wire, bit.offset) { }
		unsigned int hash() const { return first->name.hash() + second; }
	};

	pool<bitDef_t> bits;

	void clear()
	{
		bits.clear();
	}

	void add(RTLIL::SigSpec sig)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL)
				bits.insert(bit);
	}

	void add(const SigPool &other)
	{
		for (auto &bit : other.bits)
			bits.insert(bit);
	}

	void del(RTLIL::SigSpec sig)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL)
				bits.erase(bit);
	}

	void del(const SigPool &other)
	{
		for (auto &bit : other.bits)
			bits.erase(bit);
	}

	void expand(RTLIL::SigSpec from, RTLIL::SigSpec to)
	{
		log_assert(GetSize(from) == GetSize(to));
		for (int i = 0; i < GetSize(from); i++) {
			bitDef_t bit_from(from[i]), bit_to(to[i]);
			if (bit_from.first != NULL && bit_to.first != NULL && bits.count(bit_from) > 0)
				bits.insert(bit_to);
		}
	}

	RTLIL::SigSpec extract(RTLIL::SigSpec sig)
	{
		RTLIL::SigSpec result;
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit))
				result.append_bit(bit);
		return result;
	}

	RTLIL::SigSpec remove(RTLIL::SigSpec sig)
	{
		RTLIL::SigSpec result;
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit) == 0)
				result.append(bit);
		return result;
	}

	bool check(RTLIL::SigBit bit)
	{
		return bit.wire != NULL && bits.count(bit);
	}

	bool check_any(RTLIL::SigSpec sig)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit))
				return true;
		return false;
	}

	bool check_all(RTLIL::SigSpec sig)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit) == 0)
				return false;
		return true;
	}

	RTLIL::SigSpec export_one()
	{
		for (auto &bit : bits)
			return RTLIL::SigSpec(bit.first, bit.second);
		return RTLIL::SigSpec();
	}

	RTLIL::SigSpec export_all()
	{
		pool<RTLIL::SigBit> sig;
		for (auto &bit : bits)
			sig.insert(RTLIL::SigBit(bit.first, bit.second));
		return sig;
	}

	size_t size() const
	{
		return bits.size();
	}
};

template <typename T, class Compare = std::less<T>>
struct SigSet
{
	struct bitDef_t : public std::pair<RTLIL::Wire*, int> {
		bitDef_t() : std::pair<RTLIL::Wire*, int>(NULL, 0) { }
		bitDef_t(const RTLIL::SigBit &bit) : std::pair<RTLIL::Wire*, int>(bit.wire, bit.offset) { }
		unsigned int hash() const { return first->name.hash() + second; }
	};

	dict<bitDef_t, std::set<T, Compare>> bits;

	void clear()
	{
		bits.clear();
	}

	void insert(RTLIL::SigSpec sig, T data)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].insert(data);
	}

	void insert(RTLIL::SigSpec sig, const std::set<T> &data)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].insert(data.begin(), data.end());
	}

	void erase(RTLIL::SigSpec sig)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].clear();
	}

	void erase(RTLIL::SigSpec sig, T data)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].erase(data);
	}

	void erase(RTLIL::SigSpec sig, const std::set<T> &data)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].erase(data.begin(), data.end());
	}

	void find(RTLIL::SigSpec sig, std::set<T> &result)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL) {
				auto &data = bits[bit];
				result.insert(data.begin(), data.end());
			}
	}

	void find(RTLIL::SigSpec sig, pool<T> &result)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL) {
				auto &data = bits[bit];
				result.insert(data.begin(), data.end());
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
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit))
				return true;
		return false;
	}
};

struct SigMap
{
	struct bitDef_t : public std::pair<RTLIL::Wire*, int> {
		bitDef_t() : std::pair<RTLIL::Wire*, int>(NULL, 0) { }
		bitDef_t(const RTLIL::SigBit &bit) : std::pair<RTLIL::Wire*, int>(bit.wire, bit.offset) { }
		unsigned int hash() const { return first->name.hash() + second; }
	};

	struct shared_bit_data_t {
		RTLIL::SigBit map_to;
		std::set<bitDef_t> bits;
	};

	dict<bitDef_t, shared_bit_data_t*> bits;

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
		for (auto &it : module->connections())
			add(it.first, it.second);
	}

	// internal helper function
	void register_bit(const RTLIL::SigBit &bit)
	{
		if (bit.wire && bits.count(bit) == 0) {
			shared_bit_data_t *bd = new shared_bit_data_t;
			bd->map_to = bit;
			bd->bits.insert(bit);
			bits[bit] = bd;
		}
	}

	// internal helper function
	void unregister_bit(const RTLIL::SigBit &bit)
	{
		if (bit.wire && bits.count(bit) > 0) {
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
		log_assert(bit1.wire != NULL && bit2.wire != NULL);

		shared_bit_data_t *bd1 = bits[bit1];
		shared_bit_data_t *bd2 = bits[bit2];
		log_assert(bd1 != NULL && bd2 != NULL);

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
	void set_bit(const RTLIL::SigBit &bit1, const RTLIL::SigBit &bit2)
	{
		log_assert(bit1.wire != NULL);
		log_assert(bits.count(bit1) > 0);
		bits[bit1]->map_to = bit2;
	}

	// internal helper function
	void map_bit(RTLIL::SigBit &bit) const
	{
		if (bit.wire && bits.count(bit) > 0)
			bit = bits.at(bit)->map_to;
	}

	void add(RTLIL::SigSpec from, RTLIL::SigSpec to)
	{
		log_assert(GetSize(from) == GetSize(to));

		for (int i = 0; i < GetSize(from); i++)
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

	void apply(RTLIL::SigBit &bit) const
	{
		map_bit(bit);
	}

	void apply(RTLIL::SigSpec &sig) const
	{
		for (auto &bit : sig)
			map_bit(bit);
	}

	RTLIL::SigBit operator()(RTLIL::SigBit bit) const
	{
		apply(bit);
		return bit;
	}

	RTLIL::SigSpec operator()(RTLIL::SigSpec sig) const
	{
		apply(sig);
		return sig;
	}

	RTLIL::SigSpec operator()(RTLIL::Wire *wire) const
	{
		RTLIL::SigSpec sig(wire);
		apply(sig);
		return sig;
	}

	RTLIL::SigSpec allbits() const
	{
		RTLIL::SigSpec sig;
		for (auto &it : bits)
			sig.append(SigBit(it.first.first, it.first.second));
		return sig;
	}
};

YOSYS_NAMESPACE_END

#endif /* SIGTOOLS_H */
