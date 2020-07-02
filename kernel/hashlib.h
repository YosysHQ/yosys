// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

// -------------------------------------------------------
// Written by Clifford Wolf <clifford@clifford.at> in 2014
// -------------------------------------------------------

#ifndef HASHLIB_H
#define HASHLIB_H

#include <stdexcept>
#include <algorithm>
#include <string>
#include <vector>

namespace hashlib {

const int hashtable_size_trigger = 2;
const int hashtable_size_factor = 3;

// The XOR version of DJB2
inline unsigned int mkhash(unsigned int a, unsigned int b) {
	return ((a << 5) + a) ^ b;
}

// traditionally 5381 is used as starting value for the djb2 hash
const unsigned int mkhash_init = 5381;

// The ADD version of DJB2
// (use this version for cache locality in b)
inline unsigned int mkhash_add(unsigned int a, unsigned int b) {
	return ((a << 5) + a) + b;
}

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

template<typename T> struct hash_ops {
	static inline bool cmp(const T &a, const T &b) {
		return a == b;
	}
	static inline unsigned int hash(const T &a) {
		return a.hash();
	}
};

struct hash_int_ops {
	template<typename T>
	static inline bool cmp(T a, T b) {
		return a == b;
	}
};

template<> struct hash_ops<int32_t> : hash_int_ops
{
	static inline unsigned int hash(int32_t a) {
		return a;
	}
};
template<> struct hash_ops<int64_t> : hash_int_ops
{
	static inline unsigned int hash(int64_t a) {
		return mkhash((unsigned int)(a), (unsigned int)(a >> 32));
	}
};

template<> struct hash_ops<std::string> {
	static inline bool cmp(const std::string &a, const std::string &b) {
		return a == b;
	}
	static inline unsigned int hash(const std::string &a) {
		unsigned int v = 0;
		for (auto c : a)
			v = mkhash(v, c);
		return v;
	}
};

template<typename P, typename Q> struct hash_ops<std::pair<P, Q>> {
	static inline bool cmp(std::pair<P, Q> a, std::pair<P, Q> b) {
		return a == b;
	}
	static inline unsigned int hash(std::pair<P, Q> a) {
		return mkhash(hash_ops<P>::hash(a.first), hash_ops<Q>::hash(a.second));
	}
};

template<typename... T> struct hash_ops<std::tuple<T...>> {
	static inline bool cmp(std::tuple<T...> a, std::tuple<T...> b) {
		return a == b;
	}
	template<size_t I = 0>
	static inline typename std::enable_if<I == sizeof...(T), unsigned int>::type hash(std::tuple<T...>) {
		return mkhash_init;
	}
	template<size_t I = 0>
	static inline typename std::enable_if<I != sizeof...(T), unsigned int>::type hash(std::tuple<T...> a) {
		typedef hash_ops<typename std::tuple_element<I, std::tuple<T...>>::type> element_ops_t;
		return mkhash(hash<I+1>(a), element_ops_t::hash(std::get<I>(a)));
	}
};

template<typename T> struct hash_ops<std::vector<T>> {
	static inline bool cmp(std::vector<T> a, std::vector<T> b) {
		return a == b;
	}
	static inline unsigned int hash(std::vector<T> a) {
		unsigned int h = mkhash_init;
		for (auto k : a)
			h = mkhash(h, hash_ops<T>::hash(k));
		return h;
	}
};

struct hash_cstr_ops {
	static inline bool cmp(const char *a, const char *b) {
		for (int i = 0; a[i] || b[i]; i++)
			if (a[i] != b[i])
				return false;
		return true;
	}
	static inline unsigned int hash(const char *a) {
		unsigned int hash = mkhash_init;
		while (*a)
			hash = mkhash(hash, *(a++));
		return hash;
	}
};

struct hash_ptr_ops {
	static inline bool cmp(const void *a, const void *b) {
		return a == b;
	}
	static inline unsigned int hash(const void *a) {
		return (uintptr_t)a;
	}
};

struct hash_obj_ops {
	static inline bool cmp(const void *a, const void *b) {
		return a == b;
	}
	template<typename T>
	static inline unsigned int hash(const T *a) {
		return a ? a->hash() : 0;
	}
};

template<typename T>
inline unsigned int mkhash(const T &v) {
	return hash_ops<T>().hash(v);
}

inline int hashtable_size(int min_size)
{
	static std::vector<int> zero_and_some_primes = {
		0, 23, 29, 37, 47, 59, 79, 101, 127, 163, 211, 269, 337, 431, 541, 677,
		853, 1069, 1361, 1709, 2137, 2677, 3347, 4201, 5261, 6577, 8231, 10289,
		12889, 16127, 20161, 25219, 31531, 39419, 49277, 61603, 77017, 96281,
		120371, 150473, 188107, 235159, 293957, 367453, 459317, 574157, 717697,
		897133, 1121423, 1401791, 1752239, 2190299, 2737937, 3422429, 4278037,
		5347553, 6684443, 8355563, 10444457, 13055587, 16319519, 20399411,
		25499291, 31874149, 39842687, 49803361, 62254207, 77817767, 97272239,
		121590311, 151987889, 189984863, 237481091, 296851369, 371064217
	};

	for (auto p : zero_and_some_primes)
		if (p >= min_size) return p;

	if (sizeof(int) == 4)
		throw std::length_error("hash table exceeded maximum size. use a ILP64 abi for larger tables.");

	for (auto p : zero_and_some_primes)
		if (100129 * p > min_size) return 100129 * p;

	throw std::length_error("hash table exceeded maximum size.");
}

template<typename K, typename T, typename OPS = hash_ops<K>> class dict;
template<typename K, int offset = 0, typename OPS = hash_ops<K>> class idict;
template<typename K, typename OPS = hash_ops<K>> class pool;
template<typename K, typename OPS = hash_ops<K>> class mfp;

template<typename K, typename T, typename OPS>
class dict
{
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

	int do_hash(const K &key) const
	{
		unsigned int hash = 0;
		if (!hashtable.empty())
			hash = ops.hash(key) % (unsigned int)(hashtable.size());
		return hash;
	}

	void do_rehash()
	{
		hashtable.clear();
		hashtable.resize(hashtable_size(entries.capacity() * hashtable_size_factor), -1);

		for (int i = 0; i < int(entries.size()); i++) {
			do_assert(-1 <= entries[i].next && entries[i].next < int(entries.size()));
			int hash = do_hash(entries[i].udata.first);
			entries[i].next = hashtable[hash];
			hashtable[hash] = i;
		}
	}

	int do_erase(int index, int hash)
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
			int back_hash = do_hash(entries[back_idx].udata.first);

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

	int do_lookup(const K &key, int &hash) const
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

	int do_insert(const K &key, int &hash)
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

	int do_insert(const std::pair<K, T> &value, int &hash)
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

	int do_insert(std::pair<K, T> &&rvalue, int &hash)
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
	class const_iterator : public std::iterator<std::forward_iterator_tag, std::pair<K, T>>
	{
		friend class dict;
	protected:
		const dict *ptr;
		int index;
		const_iterator(const dict *ptr, int index) : ptr(ptr), index(index) { }
	public:
		const_iterator() { }
		const_iterator operator++() { index--; return *this; }
		const_iterator operator+=(int amt) { index -= amt; return *this; }
		bool operator<(const const_iterator &other) const { return index > other.index; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const std::pair<K, T> &operator*() const { return ptr->entries[index].udata; }
		const std::pair<K, T> *operator->() const { return &ptr->entries[index].udata; }
	};

	class iterator : public std::iterator<std::forward_iterator_tag, std::pair<K, T>>
	{
		friend class dict;
	protected:
		dict *ptr;
		int index;
		iterator(dict *ptr, int index) : ptr(ptr), index(index) { }
	public:
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

	dict()
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
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(key, hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> insert(const std::pair<K, T> &value)
	{
		int hash = do_hash(value.first);
		int i = do_lookup(value.first, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(value, hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> insert(std::pair<K, T> &&rvalue)
	{
		int hash = do_hash(rvalue.first);
		int i = do_lookup(rvalue.first, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::forward<std::pair<K, T>>(rvalue), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> emplace(K const &key, T const &value)
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::make_pair(key, value), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> emplace(K const &key, T &&rvalue)
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::make_pair(key, std::forward<T>(rvalue)), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> emplace(K &&rkey, T const &value)
	{
		int hash = do_hash(rkey);
		int i = do_lookup(rkey, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::make_pair(std::forward<K>(rkey), value), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> emplace(K &&rkey, T &&rvalue)
	{
		int hash = do_hash(rkey);
		int i = do_lookup(rkey, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(std::make_pair(std::forward<K>(rkey), std::forward<T>(rvalue)), hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	int erase(const K &key)
	{
		int hash = do_hash(key);
		int index = do_lookup(key, hash);
		return do_erase(index, hash);
	}

	iterator erase(iterator it)
	{
		int hash = do_hash(it->first);
		do_erase(it.index, hash);
		return ++it;
	}

	int count(const K &key) const
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		return i < 0 ? 0 : 1;
	}

	int count(const K &key, const_iterator it) const
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		return i < 0 || i > it.index ? 0 : 1;
	}

	iterator find(const K &key)
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return end();
		return iterator(this, i);
	}

	const_iterator find(const K &key) const
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return end();
		return const_iterator(this, i);
	}

	T& at(const K &key)
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			throw std::out_of_range("dict::at()");
		return entries[i].udata.second;
	}

	const T& at(const K &key) const
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			throw std::out_of_range("dict::at()");
		return entries[i].udata.second;
	}

	const T& at(const K &key, const T &defval) const
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return defval;
		return entries[i].udata.second;
	}

	T& operator[](const K &key)
	{
		int hash = do_hash(key);
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

	unsigned int hash() const {
		unsigned int h = mkhash_init;
		for (auto &entry : entries) {
			h ^= hash_ops<K>::hash(entry.udata.first);
			h ^= hash_ops<T>::hash(entry.udata.second);
		}
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

	int do_hash(const K &key) const
	{
		unsigned int hash = 0;
		if (!hashtable.empty())
			hash = ops.hash(key) % (unsigned int)(hashtable.size());
		return hash;
	}

	void do_rehash()
	{
		hashtable.clear();
		hashtable.resize(hashtable_size(entries.capacity() * hashtable_size_factor), -1);

		for (int i = 0; i < int(entries.size()); i++) {
			do_assert(-1 <= entries[i].next && entries[i].next < int(entries.size()));
			int hash = do_hash(entries[i].udata);
			entries[i].next = hashtable[hash];
			hashtable[hash] = i;
		}
	}

	int do_erase(int index, int hash)
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
			int back_hash = do_hash(entries[back_idx].udata);

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

	int do_lookup(const K &key, int &hash) const
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

	int do_insert(const K &value, int &hash)
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

	int do_insert(K &&rvalue, int &hash)
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
	class const_iterator : public std::iterator<std::forward_iterator_tag, K>
	{
		friend class pool;
	protected:
		const pool *ptr;
		int index;
		const_iterator(const pool *ptr, int index) : ptr(ptr), index(index) { }
	public:
		const_iterator() { }
		const_iterator operator++() { index--; return *this; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const K &operator*() const { return ptr->entries[index].udata; }
		const K *operator->() const { return &ptr->entries[index].udata; }
	};

	class iterator : public std::iterator<std::forward_iterator_tag, K>
	{
		friend class pool;
	protected:
		pool *ptr;
		int index;
		iterator(pool *ptr, int index) : ptr(ptr), index(index) { }
	public:
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

	pool()
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
		int hash = do_hash(value);
		int i = do_lookup(value, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(value, hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	std::pair<iterator, bool> insert(K &&rvalue)
	{
		int hash = do_hash(rvalue);
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
		int hash = do_hash(key);
		int index = do_lookup(key, hash);
		return do_erase(index, hash);
	}

	iterator erase(iterator it)
	{
		int hash = do_hash(*it);
		do_erase(it.index, hash);
		return ++it;
	}

	int count(const K &key) const
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		return i < 0 ? 0 : 1;
	}

	int count(const K &key, const_iterator it) const
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		return i < 0 || i > it.index ? 0 : 1;
	}

	iterator find(const K &key)
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return end();
		return iterator(this, i);
	}

	const_iterator find(const K &key) const
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			return end();
		return const_iterator(this, i);
	}

	bool operator[](const K &key)
	{
		int hash = do_hash(key);
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

	bool hash() const {
		unsigned int hashval = mkhash_init;
		for (auto &it : entries)
			hashval ^= ops.hash(it.udata);
		return hashval;
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
	class const_iterator : public std::iterator<std::forward_iterator_tag, K>
	{
		friend class idict;
	protected:
		const idict &container;
		int index;
		const_iterator(const idict &container, int index) : container(container), index(index) { }
	public:
		const_iterator() { }
		const_iterator operator++() { index++; return *this; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const K &operator*() const { return container[index]; }
		const K *operator->() const { return &container[index]; }
	};

	int operator()(const K &key)
	{
		int hash = database.do_hash(key);
		int i = database.do_lookup(key, hash);
		if (i < 0)
			i = database.do_insert(key, hash);
		return i + offset;
	}

	int at(const K &key) const
	{
		int hash = database.do_hash(key);
		int i = database.do_lookup(key, hash);
		if (i < 0)
			throw std::out_of_range("idict::at()");
		return i + offset;
	}

	int at(const K &key, int defval) const
	{
		int hash = database.do_hash(key);
		int i = database.do_lookup(key, hash);
		if (i < 0)
			return defval;
		return i + offset;
	}

	int count(const K &key) const
	{
		int hash = database.do_hash(key);
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

template<typename K, typename OPS>
class mfp
{
	mutable idict<K, 0, OPS> database;
	mutable std::vector<int> parents;

public:
	typedef typename idict<K, 0, OPS>::const_iterator const_iterator;

	int operator()(const K &key) const
	{
		int i = database(key);
		parents.resize(database.size(), -1);
		return i;
	}

	const K &operator[](int index) const
	{
		return database[index];
	}

	int ifind(int i) const
	{
		int p = i, k = i;

		while (parents[p] != -1)
			p = parents[p];

		while (k != p) {
			int next_k = parents[k];
			parents[k] = p;
			k = next_k;
		}

		return p;
	}

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
