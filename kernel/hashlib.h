// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

// -------------------------------------------------------
// Written by Claire Xenia Wolf <claire@yosyshq.com> in 2014
// -------------------------------------------------------

#ifndef HASHLIB_H
#define HASHLIB_H

#include <stdexcept>
#include <algorithm>
#include <optional>
#include <string>
#include <variant>
#include <vector>
#include <type_traits>
#include <stdint.h>

#define YS_HASHING_VERSION 1

namespace hashlib {

/**
 * HASHING
 *
 * Also refer to docs/source/yosys_internals/hashing.rst
 *
 * The Hasher knows how to hash 32 and 64-bit integers. That's it.
 * In the future, it could be expanded to do vectors with SIMD.
 *
 * The Hasher doesn't know how to hash common standard containers
 * and compositions. However, hashlib provides centralized wrappers.
 *
 * Hashlib doesn't know how to hash silly Yosys-specific types.
 * Hashlib doesn't depend on Yosys and can be used standalone.
 * Please don't use hashlib standalone for new projects.
 * Never directly include kernel/hashlib.h in Yosys code.
 * Instead include kernel/yosys_common.h
 *
 * The hash_ops type is now always left to its default value, derived
 * from templated functions through SFINAE. Providing custom ops is
 * still supported.
 *
 * HASH TABLES
 *
 * We implement associative data structures with separate chaining.
 * Linked lists use integers into the indirection hashtable array
 * instead of pointers.
 */

const int hashtable_size_trigger = 2;
const int hashtable_size_factor = 3;

namespace legacy {
	inline uint32_t djb2_add(uint32_t a, uint32_t b) {
		return ((a << 5) + a) + b;
	}
};

template<typename T>
struct hash_ops;

inline unsigned int mkhash_xorshift(unsigned int a) {
	if (sizeof(a) == 4) {
		a ^= a << 13;
		a ^= a >> 17;
		a ^= a << 5;
	} else if (sizeof(a) == 8) {
		a ^= a << 13;
		a ^= a >> 7;
		a ^= a << 17;
	} else
		throw std::runtime_error("mkhash_xorshift() only implemented for 32 bit and 64 bit ints");
	return a;
}

class HasherDJB32 {
public:
	using hash_t = uint32_t;

	HasherDJB32() {
		// traditionally 5381 is used as starting value for the djb2 hash
		state = 5381;
	}
	static void set_fudge(hash_t f) {
		fudge = f;
	}

private:
	uint32_t state;
	static uint32_t fudge;
	// The XOR version of DJB2
	[[nodiscard]]
	static uint32_t djb2_xor(uint32_t a, uint32_t b) {
		uint32_t hash = ((a << 5) + a) ^ b;
		return hash;
	}
	public:
	void hash32(uint32_t i) {
		state = djb2_xor(i, state);
		state = mkhash_xorshift(fudge ^ state);
		return;
	}
	void hash64(uint64_t i) {
		state = djb2_xor((uint32_t)(i & 0xFFFFFFFFULL), state);
		state = djb2_xor((uint32_t)(i >> 32ULL), state);
		state = mkhash_xorshift(fudge ^ state);
		return;
	}
	[[nodiscard]]
	hash_t yield() {
		return (hash_t)state;
	}

	template<typename T>
	void eat(T&& t) {
		*this = hash_ops<std::remove_cv_t<std::remove_reference_t<T>>>::hash_into(std::forward<T>(t), *this);
	}

	template<typename T>
	void eat(const T& t) {
		*this = hash_ops<T>::hash_into(t, *this);
	}

	void commutative_eat(hash_t t) {
		state ^= t;
	}

	void force(hash_t new_state) {
		state = new_state;
	}
};

using Hasher = HasherDJB32;

// Boilerplate compressor for trivially implementing
// top-level hash method with hash_into
#define HASH_TOP_LOOP_FST [[nodiscard]] static inline Hasher hash
#define HASH_TOP_LOOP_SND { \
	Hasher h; \
	h = hash_into(a, h); \
	return h; \
}

template<typename T>
struct hash_ops {
	static inline bool cmp(const T &a, const T &b) {
		return a == b;
	}
	[[nodiscard]] static inline Hasher hash_into(const T &a, Hasher h) {
		if constexpr (std::is_integral_v<T>) {
			static_assert(sizeof(T) <= sizeof(uint64_t));
			if (sizeof(T) == sizeof(uint64_t))
				h.hash64(a);
			else
				h.hash32(a);
			return h;
		} else if constexpr (std::is_enum_v<T>) {
			using u_type = std::underlying_type_t<T>;
			return hash_ops<u_type>::hash_into((u_type) a, h);
		} else if constexpr (std::is_pointer_v<T>) {
			return hash_ops<uintptr_t>::hash_into((uintptr_t) a, h);
		} else if constexpr (std::is_same_v<T, std::string>) {
			for (auto c : a)
				h.hash32(c);
			return h;
		} else {
			return a.hash_into(h);
		}
	}
	HASH_TOP_LOOP_FST (const T &a) HASH_TOP_LOOP_SND
};

template<typename P, typename Q> struct hash_ops<std::pair<P, Q>> {
	static inline bool cmp(std::pair<P, Q> a, std::pair<P, Q> b) {
		return a == b;
	}
	[[nodiscard]] static inline Hasher hash_into(std::pair<P, Q> a, Hasher h) {
		h = hash_ops<P>::hash_into(a.first, h);
		h = hash_ops<Q>::hash_into(a.second, h);
		return h;
	}
	HASH_TOP_LOOP_FST (std::pair<P, Q> a) HASH_TOP_LOOP_SND
};

template<typename... T> struct hash_ops<std::tuple<T...>> {
	static inline bool cmp(std::tuple<T...> a, std::tuple<T...> b) {
		return a == b;
	}
	template<size_t I = 0>
	static inline typename std::enable_if<I == sizeof...(T), Hasher>::type hash_into(std::tuple<T...>, Hasher h) {
		return h;
	}
	template<size_t I = 0>
	static inline typename std::enable_if<I != sizeof...(T), Hasher>::type hash_into(std::tuple<T...> a, Hasher h) {
		typedef hash_ops<typename std::tuple_element<I, std::tuple<T...>>::type> element_ops_t;
		h = hash_into<I+1>(a, h);
		h = element_ops_t::hash_into(std::get<I>(a), h);
		return h;
	}
	HASH_TOP_LOOP_FST (std::tuple<T...> a) HASH_TOP_LOOP_SND
};

template<typename T> struct hash_ops<std::vector<T>> {
	static inline bool cmp(std::vector<T> a, std::vector<T> b) {
		return a == b;
	}
	[[nodiscard]] static inline Hasher hash_into(std::vector<T> a, Hasher h) {
		h.eat((uint32_t)a.size());
		for (auto k : a)
			h.eat(k);
		return h;
	}
	HASH_TOP_LOOP_FST (std::vector<T> a) HASH_TOP_LOOP_SND
};

template<typename T, size_t N> struct hash_ops<std::array<T, N>> {
    static inline bool cmp(std::array<T, N> a, std::array<T, N> b) {
        return a == b;
    }
    [[nodiscard]] static inline Hasher hash_into(std::array<T, N> a, Hasher h) {
        for (const auto& k : a)
            h = hash_ops<T>::hash_into(k, h);
        return h;
    }
	HASH_TOP_LOOP_FST (std::array<T, N> a) HASH_TOP_LOOP_SND
};

struct hash_cstr_ops {
	static inline bool cmp(const char *a, const char *b) {
		return strcmp(a, b) == 0;
	}
	[[nodiscard]] static inline Hasher hash_into(const char *a, Hasher h) {
		while (*a)
			h.hash32(*(a++));
		return h;
	}
	HASH_TOP_LOOP_FST (const char *a) HASH_TOP_LOOP_SND
};

template <> struct hash_ops<char*> : hash_cstr_ops {};

struct hash_ptr_ops {
	static inline bool cmp(const void *a, const void *b) {
		return a == b;
	}
	[[nodiscard]] static inline Hasher hash_into(const void *a, Hasher h) {
		return hash_ops<uintptr_t>::hash_into((uintptr_t)a, h);
	}
	HASH_TOP_LOOP_FST (const void *a) HASH_TOP_LOOP_SND
};

struct hash_obj_ops {
	static inline bool cmp(const void *a, const void *b) {
		return a == b;
	}
	template<typename T>
	[[nodiscard]] static inline Hasher hash_into(const T *a, Hasher h) {
		if (a)
			h = a->hash_into(h);
		else
			h.eat(0);
		return h;
	}
	template<typename T>
	HASH_TOP_LOOP_FST (const T *a) HASH_TOP_LOOP_SND
};
/**
 * If you find yourself using this function, think hard
 * about if it's the right thing to do. Mixing finalized
 * hashes together with XORs or worse can destroy
 * desirable qualities of the hash function
 */
template<typename T>
[[nodiscard]]
Hasher::hash_t run_hash(const T& obj) {
	return hash_ops<T>::hash(obj).yield();
}

/** Refer to docs/source/yosys_internals/hashing.rst */
template<typename T>
[[nodiscard]]
[[deprecated]]
inline unsigned int mkhash(const T &v) {
	return (unsigned int) run_hash<T>(v);
}

template<> struct hash_ops<std::monostate> {
	static inline bool cmp(std::monostate a, std::monostate b) {
		return a == b;
	}
	[[nodiscard]] static inline Hasher hash_into(std::monostate, Hasher h) {
		return h;
	}
};

template<typename... T> struct hash_ops<std::variant<T...>> {
	static inline bool cmp(std::variant<T...> a, std::variant<T...> b) {
		return a == b;
	}
	[[nodiscard]] static inline Hasher hash_into(std::variant<T...> a, Hasher h) {
		std::visit([& h](const auto &v) { h.eat(v); }, a);
		h.eat(a.index());
		return h;
	}
};

template<typename T> struct hash_ops<std::optional<T>> {
	static inline bool cmp(std::optional<T> a, std::optional<T> b) {
		return a == b;
	}
	[[nodiscard]] static inline Hasher hash_into(std::optional<T> a, Hasher h) {
		if(a.has_value())
			h.eat(*a);
		else
			h.eat(0);
		return h;
	}
};

inline unsigned int hashtable_size(unsigned int min_size)
{
	// Primes as generated by https://oeis.org/A175953
	static std::vector<unsigned int> zero_and_some_primes = {
		0, 23, 29, 37, 47, 59, 79, 101, 127, 163, 211, 269, 337, 431, 541, 677,
		853, 1069, 1361, 1709, 2137, 2677, 3347, 4201, 5261, 6577, 8231, 10289,
		12889, 16127, 20161, 25219, 31531, 39419, 49277, 61603, 77017, 96281,
		120371, 150473, 188107, 235159, 293957, 367453, 459317, 574157, 717697,
		897133, 1121423, 1401791, 1752239, 2190299, 2737937, 3422429, 4278037,
		5347553, 6684443, 8355563, 10444457, 13055587, 16319519, 20399411,
		25499291, 31874149, 39842687, 49803361, 62254207, 77817767, 97272239,
		121590311, 151987889, 189984863, 237481091, 296851369, 371064217,
		463830313, 579787991, 724735009, 905918777, 1132398479, 1415498113,
		1769372713, 2211715897, 2764644887, 3455806139
	};

	for (auto p : zero_and_some_primes)
		if (p >= min_size) return p;

	if (sizeof(unsigned int) == 4)
		throw std::length_error("hash table exceeded maximum size.\nDesign is likely too large for yosys to handle, if possible try not to flatten the design.");

	for (auto p : zero_and_some_primes)
		if (100129 * p > min_size) return 100129 * p;

	throw std::length_error("hash table exceeded maximum size.");
}

template<typename K, typename T, typename OPS = hash_ops<K>> class dict;
template<typename K, int offset = 0, typename OPS = hash_ops<K>> class idict;
template<typename K, typename OPS = hash_ops<K>> class pool;
template<typename K, typename OPS = hash_ops<K>> class mfp;

template<typename K, typename T, typename OPS>
class dict {
	struct entry_t
	{
		std::pair<K, T> udata;
		int next;

		entry_t() { }
		entry_t(const std::pair<K, T> &udata, int next) : udata(udata), next(next) { }
		entry_t(std::pair<K, T> &&udata, int next) : udata(std::move(udata)), next(next) { }
		bool operator<(const entry_t &other) const { return udata.first < other.udata.first; }
	};

	std::vector<int> hashtable;
	std::vector<entry_t> entries;
	OPS ops;

#ifdef NDEBUG
	static inline void do_assert(bool) { }
#else
	static inline void do_assert(bool cond) {
		if (!cond) throw std::runtime_error("dict<> assert failed.");
	}
#endif

	Hasher::hash_t do_hash(const K &key) const
	{
		Hasher::hash_t hash = 0;
		if (!hashtable.empty())
			hash = ops.hash(key).yield() % (unsigned int)(hashtable.size());
		return hash;
	}

	void do_rehash()
	{
		hashtable.clear();
		hashtable.resize(hashtable_size(entries.capacity() * hashtable_size_factor), -1);

		for (int i = 0; i < int(entries.size()); i++) {
			do_assert(-1 <= entries[i].next && entries[i].next < int(entries.size()));
			Hasher::hash_t hash = do_hash(entries[i].udata.first);
			entries[i].next = hashtable[hash];
			hashtable[hash] = i;
		}
	}

	int do_erase(int index, Hasher::hash_t hash)
	{
		do_assert(index < int(entries.size()));
		if (hashtable.empty() || index < 0)
			return 0;

		int k = hashtable[hash];
		do_assert(0 <= k && k < int(entries.size()));

		if (k == index) {
			hashtable[hash] = entries[index].next;
		} else {
			while (entries[k].next != index) {
				k = entries[k].next;
				do_assert(0 <= k && k < int(entries.size()));
			}
			entries[k].next = entries[index].next;
		}

		int back_idx = entries.size()-1;

		if (index != back_idx)
		{
			Hasher::hash_t back_hash = do_hash(entries[back_idx].udata.first);

			k = hashtable[back_hash];
			do_assert(0 <= k && k < int(entries.size()));

			if (k == back_idx) {
				hashtable[back_hash] = index;
			} else {
				while (entries[k].next != back_idx) {
					k = entries[k].next;
					do_assert(0 <= k && k < int(entries.size()));
				}
				entries[k].next = index;
			}

			entries[index] = std::move(entries[back_idx]);
		}

		entries.pop_back();

		if (entries.empty())
			hashtable.clear();

		return 1;
	}

	int do_lookup(const K &key, Hasher::hash_t &hash) const
	{
		if (hashtable.empty())
			return -1;

		if (entries.size() * hashtable_size_trigger > hashtable.size()) {
			((dict*)this)->do_rehash();
			hash = do_hash(key);
		}

		int index = hashtable[hash];

		while (index >= 0 && !ops.cmp(entries[index].udata.first, key)) {
			index = entries[index].next;
			do_assert(-1 <= index && index < int(entries.size()));
		}

		return index;
	}

	int do_insert(const K &key, Hasher::hash_t &hash)
	{
		if (hashtable.empty()) {
			entries.emplace_back(std::pair<K, T>(key, T()), -1);
			do_rehash();
			hash = do_hash(key);
		} else {
			entries.emplace_back(std::pair<K, T>(key, T()), hashtable[hash]);
			hashtable[hash] = entries.size() - 1;
		}
		return entries.size() - 1;
	}

	int do_insert(const std::pair<K, T> &value, Hasher::hash_t &hash)
	{
		if (hashtable.empty()) {
			entries.emplace_back(value, -1);
			do_rehash();
			hash = do_hash(value.first);
		} else {
			entries.emplace_back(value, hashtable[hash]);
			hashtable[hash] = entries.size() - 1;
		}
		return entries.size() - 1;
	}

	int do_insert(std::pair<K, T> &&rvalue, Hasher::hash_t &hash)
	{
		if (hashtable.empty()) {
			auto key = rvalue.first;
			entries.emplace_back(std::forward<std::pair<K, T>>(rvalue), -1);
			do_rehash();
			hash = do_hash(key);
		} else {
			entries.emplace_back(std::forward<std::pair<K, T>>(rvalue), hashtable[hash]);
			hashtable[hash] = entries.size() - 1;
		}
		return entries.size() - 1;
	}

public:
	class const_iterator
	{
		friend class dict;
	protected:
		const dict *ptr;
		int index;
		const_iterator(const dict *ptr, int index) : ptr(ptr), index(index) { }
	public:
		typedef std::forward_iterator_tag iterator_category;
		typedef std::pair<K, T> value_type;
		typedef ptrdiff_t difference_type;
		typedef std::pair<K, T>* pointer;
		typedef std::pair<K, T>& reference;
		const_iterator() { }
		const_iterator operator++() { index--; return *this; }
		const_iterator operator+=(int amt) { index -= amt; return *this; }
		bool operator<(const const_iterator &other) const { return index > other.index; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const std::pair<K, T> &operator*() const { return ptr->entries[index].udata; }
		const std::pair<K, T> *operator->() const { return &ptr->entries[index].udata; }
	};

	class iterator
	{
		friend class dict;
	protected:
		dict *ptr;
		int index;
		iterator(dict *ptr, int index) : ptr(ptr), index(index) { }
	public:
		typedef std::forward_iterator_tag iterator_category;
		typedef std::pair<K, T> value_type;
		typedef ptrdiff_t difference_type;
		typedef std::pair<K, T>* pointer;
		typedef std::pair<K, T>& reference;
		iterator() { }
		iterator operator++() { index--; return *this; }
		iterator operator+=(int amt) { index -= amt; return *this; }
		bool operator<(const iterator &other) const { return index > other.index; }
		bool operator==(const iterator &other) const { return index == other.index; }
		bool operator!=(const iterator &other) const { return index != other.index; }
		std::pair<K, T> &operator*() { return ptr->entries[index].udata; }
		std::pair<K, T> *operator->() { return &ptr->entries[index].udata; }
		const std::pair<K, T> &operator*() const { return ptr->entries[index].udata; }
		const std::pair<K, T> *operator->() const { return &ptr->entries[index].udata; }
		operator const_iterator() const { return const_iterator(ptr, index); }
	};

	constexpr dict()
	{
	}

	dict(const dict &other)
	{
		entries = other.entries;
		do_rehash();
	}

	dict(dict &&other)
	{
		swap(other);
	}

	dict &operator=(const dict &other) {
		entries = other.entries;
		do_rehash();
		return *this;
	}

	dict &operator=(dict &&other) {
		clear();
		swap(other);
		return *this;
	}

	dict(const std::initializer_list<std::pair<K, T>> &list)
	{
		for (auto &it : list)
			insert(it);
	}

	template<class InputIterator>
	dict(InputIterator first, InputIterator last)
	{
		insert(first, last);
	}

	template<class InputIterator>
	void insert(InputIterator first, InputIterator last)
	{
		for (; first != last; ++first)
			insert(*first);
	}

	std::pair<iterator, bool> insert(const K &key)
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(key, hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> insert(const std::pair<K, T> &value)
	{
		Hasher::hash_t hash = do_hash(value.first);
		int i = do_lookup(value.first, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(value, hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> insert(std::pair<K, T> &&rvalue)
	{
		Hasher::hash_t hash = do_hash(rvalue.first);
		int i = do_lookup(rvalue.first, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::forward<std::pair<K, T>>(rvalue), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> emplace(K const &key, T const &value)
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::make_pair(key, value), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> emplace(K const &key, T &&rvalue)
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::make_pair(key, std::forward<T>(rvalue)), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> emplace(K &&rkey, T const &value)
	{
		Hasher::hash_t hash = do_hash(rkey);
		int i = do_lookup(rkey, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::make_pair(std::forward<K>(rkey), value), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> emplace(K &&rkey, T &&rvalue)
	{
		Hasher::hash_t hash = do_hash(rkey);
		int i = do_lookup(rkey, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::make_pair(std::forward<K>(rkey), std::forward<T>(rvalue)), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	int erase(const K &key)
	{
		Hasher::hash_t hash = do_hash(key);
		int index = do_lookup(key, hash);
		return do_erase(index, hash);
	}

	iterator erase(iterator it)
	{
		Hasher::hash_t hash = do_hash(it->first);
		do_erase(it.index, hash);
		return ++it;
	}

	int count(const K &key) const
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		return i < 0 ? 0 : 1;
	}

	int count(const K &key, const_iterator it) const
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		return i < 0 || i > it.index ? 0 : 1;
	}

	iterator find(const K &key)
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return end();
		return iterator(this, i);
	}

	const_iterator find(const K &key) const
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return end();
		return const_iterator(this, i);
	}

	T& at(const K &key)
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			throw std::out_of_range("dict::at()");
		return entries[i].udata.second;
	}

	const T& at(const K &key) const
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			throw std::out_of_range("dict::at()");
		return entries[i].udata.second;
	}

	const T& at(const K &key, const T &defval) const
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return defval;
		return entries[i].udata.second;
	}

	T& operator[](const K &key)
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			i = do_insert(std::pair<K, T>(key, T()), hash);
		return entries[i].udata.second;
	}

	template<typename Compare = std::less<K>>
	void sort(Compare comp = Compare())
	{
		std::sort(entries.begin(), entries.end(), [comp](const entry_t &a, const entry_t &b){ return comp(b.udata.first, a.udata.first); });
		do_rehash();
	}

	void swap(dict &other)
	{
		hashtable.swap(other.hashtable);
		entries.swap(other.entries);
	}

	bool operator==(const dict &other) const {
		if (size() != other.size())
			return false;
		for (auto &it : entries) {
			auto oit = other.find(it.udata.first);
			if (oit == other.end() || !(oit->second == it.udata.second))
				return false;
		}
		return true;
	}

	bool operator!=(const dict &other) const {
		return !operator==(other);
	}

	[[nodiscard]] Hasher hash_into(Hasher h) const {
		for (auto &it : entries) {
			Hasher entry_hash;
			entry_hash.eat(it.udata.first);
			entry_hash.eat(it.udata.second);
			h.commutative_eat(entry_hash.yield());
		}
		h.eat(entries.size());
		return h;
	}

	void reserve(size_t n) { entries.reserve(n); }
	size_t size() const { return entries.size(); }
	bool empty() const { return entries.empty(); }
	void clear() { hashtable.clear(); entries.clear(); }

	iterator begin() { return iterator(this, int(entries.size())-1); }
	iterator element(int n) { return iterator(this, int(entries.size())-1-n); }
	iterator end() { return iterator(nullptr, -1); }

	const_iterator begin() const { return const_iterator(this, int(entries.size())-1); }
	const_iterator element(int n) const { return const_iterator(this, int(entries.size())-1-n); }
	const_iterator end() const { return const_iterator(nullptr, -1); }
};

template<typename K, typename OPS>
class pool
{
	template<typename, int, typename> friend class idict;

protected:
	struct entry_t
	{
		K udata;
		int next;

		entry_t() { }
		entry_t(const K &udata, int next) : udata(udata), next(next) { }
		entry_t(K &&udata, int next) : udata(std::move(udata)), next(next) { }
	};

	std::vector<int> hashtable;
	std::vector<entry_t> entries;
	OPS ops;

#ifdef NDEBUG
	static inline void do_assert(bool) { }
#else
	static inline void do_assert(bool cond) {
		if (!cond) throw std::runtime_error("pool<> assert failed.");
	}
#endif

	Hasher::hash_t do_hash(const K &key) const
	{
		Hasher::hash_t hash = 0;
		if (!hashtable.empty())
			hash = ops.hash(key).yield() % (unsigned int)(hashtable.size());
		return hash;
	}

	void do_rehash()
	{
		hashtable.clear();
		hashtable.resize(hashtable_size(entries.capacity() * hashtable_size_factor), -1);

		for (int i = 0; i < int(entries.size()); i++) {
			do_assert(-1 <= entries[i].next && entries[i].next < int(entries.size()));
			Hasher::hash_t hash = do_hash(entries[i].udata);
			entries[i].next = hashtable[hash];
			hashtable[hash] = i;
		}
	}

	int do_erase(int index, Hasher::hash_t hash)
	{
		do_assert(index < int(entries.size()));
		if (hashtable.empty() || index < 0)
			return 0;

		int k = hashtable[hash];
		if (k == index) {
			hashtable[hash] = entries[index].next;
		} else {
			while (entries[k].next != index) {
				k = entries[k].next;
				do_assert(0 <= k && k < int(entries.size()));
			}
			entries[k].next = entries[index].next;
		}

		int back_idx = entries.size()-1;

		if (index != back_idx)
		{
			Hasher::hash_t back_hash = do_hash(entries[back_idx].udata);

			k = hashtable[back_hash];
			if (k == back_idx) {
				hashtable[back_hash] = index;
			} else {
				while (entries[k].next != back_idx) {
					k = entries[k].next;
					do_assert(0 <= k && k < int(entries.size()));
				}
				entries[k].next = index;
			}

			entries[index] = std::move(entries[back_idx]);
		}

		entries.pop_back();

		if (entries.empty())
			hashtable.clear();

		return 1;
	}

	int do_lookup(const K &key, Hasher::hash_t &hash) const
	{
		if (hashtable.empty())
			return -1;

		if (entries.size() * hashtable_size_trigger > hashtable.size()) {
			((pool*)this)->do_rehash();
			hash = do_hash(key);
		}

		int index = hashtable[hash];

		while (index >= 0 && !ops.cmp(entries[index].udata, key)) {
			index = entries[index].next;
			do_assert(-1 <= index && index < int(entries.size()));
		}

		return index;
	}

	int do_insert(const K &value, Hasher::hash_t &hash)
	{
		if (hashtable.empty()) {
			entries.emplace_back(value, -1);
			do_rehash();
			hash = do_hash(value);
		} else {
			entries.emplace_back(value, hashtable[hash]);
			hashtable[hash] = entries.size() - 1;
		}
		return entries.size() - 1;
	}

	int do_insert(K &&rvalue, Hasher::hash_t &hash)
	{
		if (hashtable.empty()) {
			entries.emplace_back(std::forward<K>(rvalue), -1);
			do_rehash();
			hash = do_hash(rvalue);
		} else {
			entries.emplace_back(std::forward<K>(rvalue), hashtable[hash]);
			hashtable[hash] = entries.size() - 1;
		}
		return entries.size() - 1;
	}

public:
	class const_iterator
	{
		friend class pool;
	protected:
		const pool *ptr;
		int index;
		const_iterator(const pool *ptr, int index) : ptr(ptr), index(index) { }
	public:
		typedef std::forward_iterator_tag iterator_category;
		typedef K value_type;
		typedef ptrdiff_t difference_type;
		typedef K* pointer;
		typedef K& reference;
		const_iterator() { }
		const_iterator operator++() { index--; return *this; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const K &operator*() const { return ptr->entries[index].udata; }
		const K *operator->() const { return &ptr->entries[index].udata; }
	};

	class iterator
	{
		friend class pool;
	protected:
		pool *ptr;
		int index;
		iterator(pool *ptr, int index) : ptr(ptr), index(index) { }
	public:
		typedef std::forward_iterator_tag iterator_category;
		typedef K value_type;
		typedef ptrdiff_t difference_type;
		typedef K* pointer;
		typedef K& reference;
		iterator() { }
		iterator operator++() { index--; return *this; }
		bool operator==(const iterator &other) const { return index == other.index; }
		bool operator!=(const iterator &other) const { return index != other.index; }
		K &operator*() { return ptr->entries[index].udata; }
		K *operator->() { return &ptr->entries[index].udata; }
		const K &operator*() const { return ptr->entries[index].udata; }
		const K *operator->() const { return &ptr->entries[index].udata; }
		operator const_iterator() const { return const_iterator(ptr, index); }
	};

	constexpr pool()
	{
	}

	pool(const pool &other)
	{
		entries = other.entries;
		do_rehash();
	}

	pool(pool &&other)
	{
		swap(other);
	}

	pool &operator=(const pool &other) {
		entries = other.entries;
		do_rehash();
		return *this;
	}

	pool &operator=(pool &&other) {
		clear();
		swap(other);
		return *this;
	}

	pool(const std::initializer_list<K> &list)
	{
		for (auto &it : list)
			insert(it);
	}

	template<class InputIterator>
	pool(InputIterator first, InputIterator last)
	{
		insert(first, last);
	}

	template<class InputIterator>
	void insert(InputIterator first, InputIterator last)
	{
		for (; first != last; ++first)
			insert(*first);
	}

	std::pair<iterator, bool> insert(const K &value)
	{
		Hasher::hash_t hash = do_hash(value);
		int i = do_lookup(value, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(value, hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> insert(K &&rvalue)
	{
		Hasher::hash_t hash = do_hash(rvalue);
		int i = do_lookup(rvalue, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::forward<K>(rvalue), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	template<typename... Args>
	std::pair<iterator, bool> emplace(Args&&... args)
	{
		return insert(K(std::forward<Args>(args)...));
	}

	int erase(const K &key)
	{
		Hasher::hash_t hash = do_hash(key);
		int index = do_lookup(key, hash);
		return do_erase(index, hash);
	}

	iterator erase(iterator it)
	{
		Hasher::hash_t hash = do_hash(*it);
		do_erase(it.index, hash);
		return ++it;
	}

	int count(const K &key) const
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		return i < 0 ? 0 : 1;
	}

	int count(const K &key, const_iterator it) const
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		return i < 0 || i > it.index ? 0 : 1;
	}

	iterator find(const K &key)
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return end();
		return iterator(this, i);
	}

	const_iterator find(const K &key) const
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return end();
		return const_iterator(this, i);
	}

	bool operator[](const K &key)
	{
		Hasher::hash_t hash = do_hash(key);
		int i = do_lookup(key, hash);
		return i >= 0;
	}

	template<typename Compare = std::less<K>>
	void sort(Compare comp = Compare())
	{
		std::sort(entries.begin(), entries.end(), [comp](const entry_t &a, const entry_t &b){ return comp(b.udata, a.udata); });
		do_rehash();
	}

	K pop()
	{
		iterator it = begin();
		K ret = *it;
		erase(it);
		return ret;
	}

	void swap(pool &other)
	{
		hashtable.swap(other.hashtable);
		entries.swap(other.entries);
	}

	bool operator==(const pool &other) const {
		if (size() != other.size())
			return false;
		for (auto &it : entries)
			if (!other.count(it.udata))
				return false;
		return true;
	}

	bool operator!=(const pool &other) const {
		return !operator==(other);
	}

	[[nodiscard]] Hasher hash_into(Hasher h) const {
		for (auto &it : entries) {
			h.commutative_eat(ops.hash(it.udata).yield());
		}
		h.eat(entries.size());
		return h;
	}

	void reserve(size_t n) { entries.reserve(n); }
	size_t size() const { return entries.size(); }
	bool empty() const { return entries.empty(); }
	void clear() { hashtable.clear(); entries.clear(); }

	iterator begin() { return iterator(this, int(entries.size())-1); }
	iterator element(int n) { return iterator(this, int(entries.size())-1-n); }
	iterator end() { return iterator(nullptr, -1); }

	const_iterator begin() const { return const_iterator(this, int(entries.size())-1); }
	const_iterator element(int n) const { return const_iterator(this, int(entries.size())-1-n); }
	const_iterator end() const { return const_iterator(nullptr, -1); }
};

template<typename K, int offset, typename OPS>
class idict
{
	pool<K, OPS> database;

public:
	class const_iterator
	{
		friend class idict;
	protected:
		const idict &container;
		int index;
		const_iterator(const idict &container, int index) : container(container), index(index) { }
	public:
		typedef std::forward_iterator_tag iterator_category;
		typedef K value_type;
		typedef ptrdiff_t difference_type;
		typedef K* pointer;
		typedef K& reference;
		const_iterator() { }
		const_iterator operator++() { index++; return *this; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const K &operator*() const { return container[index]; }
		const K *operator->() const { return &container[index]; }
	};

	constexpr idict()
	{
	}

	int operator()(const K &key)
	{
		Hasher::hash_t hash = database.do_hash(key);
		int i = database.do_lookup(key, hash);
		if (i < 0)
			i = database.do_insert(key, hash);
		return i + offset;
	}

	int at(const K &key) const
	{
		Hasher::hash_t hash = database.do_hash(key);
		int i = database.do_lookup(key, hash);
		if (i < 0)
			throw std::out_of_range("idict::at()");
		return i + offset;
	}

	int at(const K &key, int defval) const
	{
		Hasher::hash_t hash = database.do_hash(key);
		int i = database.do_lookup(key, hash);
		if (i < 0)
			return defval;
		return i + offset;
	}

	int count(const K &key) const
	{
		Hasher::hash_t hash = database.do_hash(key);
		int i = database.do_lookup(key, hash);
		return i < 0 ? 0 : 1;
	}

	void expect(const K &key, int i)
	{
		int j = (*this)(key);
		if (i != j)
			throw std::out_of_range("idict::expect()");
	}

	const K &operator[](int index) const
	{
		return database.entries.at(index - offset).udata;
	}

	void swap(idict &other)
	{
		database.swap(other.database);
	}

	void reserve(size_t n) { database.reserve(n); }
	size_t size() const { return database.size(); }
	bool empty() const { return database.empty(); }
	void clear() { database.clear(); }

	const_iterator begin() const { return const_iterator(*this, offset); }
	const_iterator element(int n) const { return const_iterator(*this, n); }
	const_iterator end() const { return const_iterator(*this, offset + size()); }
};

/**
 * Union-find data structure with a promotion method
 * mfp stands for "merge, find, promote"
 * i-prefixed methods operate on indices in parents
*/
template<typename K, typename OPS>
class mfp
{
	mutable idict<K, 0, OPS> database;
	mutable std::vector<int> parents;

public:
	typedef typename idict<K, 0>::const_iterator const_iterator;

	constexpr mfp()
	{
	}

	// Finds a given element's index. If it isn't in the data structure,
	// it is added as its own set
	int operator()(const K &key) const
	{
		int i = database(key);
		// If the lookup caused the database to grow,
		// also add a corresponding entry in parents initialized to -1 (no parent)
		parents.resize(database.size(), -1);
		return i;
	}

	// Finds an element at given index
	const K &operator[](int index) const
	{
		return database[index];
	}

	int ifind(int i) const
	{
		int p = i, k = i;

		while (parents[p] != -1)
			p = parents[p];

		// p is now the representative of i
		// Now we traverse from i up to the representative again
		// and make p the parent of all the nodes along the way.
		// This is a side effect and doesn't affect the return value.
		// It speeds up future find operations
		while (k != p) {
			int next_k = parents[k];
			parents[k] = p;
			k = next_k;
		}

		return p;
	}

	// Merge sets if the given indices belong to different sets
	void imerge(int i, int j)
	{
		i = ifind(i);
		j = ifind(j);

		if (i != j)
			parents[i] = j;
	}

	void ipromote(int i)
	{
		int k = i;

		while (k != -1) {
			int next_k = parents[k];
			parents[k] = i;
			k = next_k;
		}

		parents[i] = -1;
	}

	int lookup(const K &a) const
	{
		return ifind((*this)(a));
	}

	const K &find(const K &a) const
	{
		int i = database.at(a, -1);
		if (i < 0)
			return a;
		return (*this)[ifind(i)];
	}

	void merge(const K &a, const K &b)
	{
		imerge((*this)(a), (*this)(b));
	}

	void promote(const K &a)
	{
		int i = database.at(a, -1);
		if (i >= 0)
			ipromote(i);
	}

	void swap(mfp &other)
	{
		database.swap(other.database);
		parents.swap(other.parents);
	}

	void reserve(size_t n) { database.reserve(n); }
	size_t size() const { return database.size(); }
	bool empty() const { return database.empty(); }
	void clear() { database.clear(); parents.clear(); }

	const_iterator begin() const { return database.begin(); }
	const_iterator element(int n) const { return database.element(n); }
	const_iterator end() const { return database.end(); }
};

} /* namespace hashlib */

#endif
