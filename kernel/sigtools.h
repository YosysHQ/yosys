/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

	void add(const RTLIL::SigSpec &sig)
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

	void del(const RTLIL::SigSpec &sig)
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

	void expand(const RTLIL::SigSpec &from, const RTLIL::SigSpec &to)
	{
		log_assert(GetSize(from) == GetSize(to));
		for (int i = 0; i < GetSize(from); i++) {
			bitDef_t bit_from(from[i]), bit_to(to[i]);
			if (bit_from.first != NULL && bit_to.first != NULL && bits.count(bit_from) > 0)
				bits.insert(bit_to);
		}
	}

	RTLIL::SigSpec extract(const RTLIL::SigSpec &sig) const
	{
		RTLIL::SigSpec result;
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit))
				result.append(bit);
		return result;
	}

	RTLIL::SigSpec remove(const RTLIL::SigSpec &sig) const
	{
		RTLIL::SigSpec result;
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit) == 0)
				result.append(bit);
		return result;
	}

	bool check(const RTLIL::SigBit &bit) const
	{
		return bit.wire != NULL && bits.count(bit);
	}

	bool check_any(const RTLIL::SigSpec &sig) const
	{
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit))
				return true;
		return false;
	}

	bool check_all(const RTLIL::SigSpec &sig) const
	{
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit) == 0)
				return false;
		return true;
	}

	RTLIL::SigSpec export_one() const
	{
		for (auto &bit : bits)
			return RTLIL::SigSpec(bit.first, bit.second);
		return RTLIL::SigSpec();
	}

	RTLIL::SigSpec export_all() const
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

template <typename T, class Compare = void>
struct SigSet
{
	static_assert(!std::is_same<Compare,void>::value, "Default value for `Compare' class not found for SigSet<T>. Please specify.");

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

	void insert(const RTLIL::SigSpec &sig, T data)
	{
		for (const auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].insert(data);
	}

	void insert(const RTLIL::SigSpec& sig, const std::set<T> &data)
	{
		for (const auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].insert(data.begin(), data.end());
	}

	void erase(const RTLIL::SigSpec& sig)
	{
		for (const auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].clear();
	}

	void erase(const RTLIL::SigSpec &sig, T data)
	{
		for (const auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].erase(data);
	}

	void erase(const RTLIL::SigSpec &sig, const std::set<T> &data)
	{
		for (const auto &bit : sig)
			if (bit.wire != NULL)
				bits[bit].erase(data.begin(), data.end());
	}

	void find(const RTLIL::SigSpec &sig, std::set<T> &result)
	{
		for (const auto &bit : sig)
			if (bit.wire != NULL) {
				auto &data = bits[bit];
				result.insert(data.begin(), data.end());
			}
	}

	void find(const RTLIL::SigSpec &sig, pool<T> &result)
	{
		for (const auto &bit : sig)
			if (bit.wire != NULL) {
				auto &data = bits[bit];
				result.insert(data.begin(), data.end());
			}
	}

	std::set<T> find(const RTLIL::SigSpec &sig)
	{
		std::set<T> result;
		find(sig, result);
		return result;
	}

	bool has(const RTLIL::SigSpec &sig)
	{
		for (auto &bit : sig)
			if (bit.wire != NULL && bits.count(bit))
				return true;
		return false;
	}
};

template<typename T>
class SigSet<T, typename std::enable_if<!std::is_pointer<T>::value>::type> : public SigSet<T, std::less<T>> {};
template<typename T>
using sort_by_name_id_guard = typename std::enable_if<std::is_same<T,RTLIL::Cell*>::value>::type;
template<typename T>
class SigSet<T, sort_by_name_id_guard<T>> : public SigSet<T, RTLIL::sort_by_name_id<typename std::remove_pointer<T>::type>> {};

struct SigMap
{
	mfp<SigBit> database;

	SigMap(RTLIL::Module *module = NULL)
	{
		if (module != NULL)
			set(module);
	}

	void swap(SigMap &other)
	{
		database.swap(other.database);
	}

	void clear()
	{
		database.clear();
	}

	void set(RTLIL::Module *module)
	{
		int bitcount = 0;
		for (auto &it : module->connections())
			bitcount += it.first.size();

		database.clear();
		database.reserve(bitcount);

		for (auto &it : module->connections())
			add(it.first, it.second);
	}

	void add(const RTLIL::SigSpec& from, const RTLIL::SigSpec& to)
	{
		log_assert(GetSize(from) == GetSize(to));

		for (int i = 0; i < GetSize(from); i++)
		{
			int bfi = database.lookup(from[i]);
			int bti = database.lookup(to[i]);

			const RTLIL::SigBit &bf = database[bfi];
			const RTLIL::SigBit &bt = database[bti];

			if (bf.wire || bt.wire)
			{
				database.imerge(bfi, bti);

				if (bf.wire == nullptr)
					database.ipromote(bfi);

				if (bt.wire == nullptr)
					database.ipromote(bti);
			}
		}
	}

	void add(const RTLIL::SigBit &bit)
	{
		const auto &b = database.find(bit);
		if (b.wire != nullptr)
			database.promote(bit);
	}

	void add(const RTLIL::SigSpec &sig)
	{
		for (const auto &bit : sig)
			add(bit);
	}

	inline void add(Wire *wire) { return add(RTLIL::SigSpec(wire)); }

	void apply(RTLIL::SigBit &bit) const
	{
		bit = database.find(bit);
	}

	void apply(RTLIL::SigSpec &sig) const
	{
		for (auto &bit : sig)
			apply(bit);
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
		SigSpec sig(wire);
		apply(sig);
		return sig;
	}

	RTLIL::SigSpec allbits() const
	{
		RTLIL::SigSpec sig;
		for (const auto &bit : database)
			if (bit.wire != nullptr)
				sig.append(bit);
		return sig;
	}
};

YOSYS_NAMESPACE_END

#endif /* SIGTOOLS_H */
