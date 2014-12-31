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

#include <stdexcept>
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
// (usunsigned int mkhashe this version for cache locality in b)
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
	bool cmp(const T &a, const T &b) const {
		return a == b;
	}
	unsigned int hash(const T &a) const {
		return a.hash();
	}
};

template<> struct hash_ops<int> {
	template<typename T>
	bool cmp(T a, T b) const {
		return a == b;
	}
	template<typename T>
	unsigned int hash(T a) const {
		return a;
	}
};

template<> struct hash_ops<std::string> {
	bool cmp(const std::string &a, const std::string &b) const {
		return a == b;
	}
	unsigned int hash(const std::string &a) const {
		unsigned int v = 0;
		for (auto c : a)
			v = mkhash(v, c);
		return v;
	}
};

template<typename P, typename Q> struct hash_ops<std::pair<P, Q>> {
	bool cmp(std::pair<P, Q> a, std::pair<P, Q> b) const {
		return a == b;
	}
	unsigned int hash(std::pair<P, Q> a) const {
		hash_ops<P> p_ops;
		hash_ops<Q> q_ops;
		return mkhash(p_ops.hash(a.first), q_ops.hash(a.second));
	}
};

template<typename T> struct hash_ops<std::vector<T>> {
	bool cmp(std::vector<T> a, std::vector<T> b) const {
		return a == b;
	}
	unsigned int hash(std::vector<T> a) const {
		hash_ops<T> t_ops;
		unsigned int h = mkhash_init;
		for (auto k : a)
			h = mkhash(h, t_ops.hash(k));
		return h;
	}
};

struct hash_cstr_ops {
	bool cmp(const char *a, const char *b) const {
		for (int i = 0; a[i] || b[i]; i++)
			if (a[i] != b[i])
				return false;
		return true;
	}
	unsigned int hash(const char *a) const {
		unsigned int hash = mkhash_init;
		while (*a)
			 hash = mkhash(hash, *(a++));
		 return hash;
	}
};

struct hash_ptr_ops {
	bool cmp(const void *a, const void *b) const {
		return a == b;
	}
	unsigned int hash(const void *a) const {
		return (unsigned long)a;
	}
};

struct hash_obj_ops {
	bool cmp(const void *a, const void *b) const {
		return a == b;
	}
	template<typename T>
	unsigned int hash(const T *a) const {
		return a->hash();
	}
};

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

template<typename K, typename T, typename OPS = hash_ops<K>>
class dict
{
	struct entry_t
	{
		std::pair<K, T> udata;
		int next;

		entry_t() { }
		entry_t(const std::pair<K, T> &udata, int next) : udata(udata), next(next) { }
	};

	std::vector<int> hashtable;
	std::vector<entry_t> entries;
	OPS ops;

#if 0
	static inline void do_assert(bool cond) {
		if (!cond) throw std::runtime_error("dict<> assert failed.");
	}
#else
	static inline void do_assert(bool) { }
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
		hashtable.resize(hashtable_size(entries.size() * hashtable_size_factor), -1);

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

	int do_insert(const std::pair<K, T> &value, int &hash)
	{
		if (hashtable.empty()) {
			entries.push_back(entry_t(value, -1));
			do_rehash();
			hash = do_hash(value.first);
		} else {
			entries.push_back(entry_t(value, hashtable[hash]));
			hashtable[hash] = entries.size() - 1;
		}
		return entries.size() - 1;
	}

public:
	class iterator
	{
		friend dict;
	protected:
		dict *ptr;
		int index;
	public:
		iterator() { }
		iterator(dict *ptr, int index) : ptr(ptr), index(index) { }
		iterator operator++() { index--; return *this; }
		bool operator==(const iterator &other) const { return index == other.index; }
		bool operator!=(const iterator &other) const { return index != other.index; }
		std::pair<K, T> &operator*() { return ptr->entries[index].udata; }
		std::pair<K, T> *operator->() { return &ptr->entries[index].udata; }
		const std::pair<K, T> &operator*() const { return ptr->entries[index].udata; }
		const std::pair<K, T> *operator->() const { return &ptr->entries[index].udata; }
	};

	class const_iterator
	{
		friend dict;
	protected:
		const dict *ptr;
		int index;
	public:
		const_iterator() { }
		const_iterator(const dict *ptr, int index) : ptr(ptr), index(index) { }
		const_iterator operator++() { index--; return *this; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const std::pair<K, T> &operator*() const { return ptr->entries[index].udata; }
		const std::pair<K, T> *operator->() const { return &ptr->entries[index].udata; }
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

	std::pair<iterator, bool> insert(const std::pair<K, T> &value)
	{
		int hash = do_hash(value.first);
		int i = do_lookup(value.first, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = do_insert(value, hash);
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

	T& operator[](const K &key)
	{
		int hash = do_hash(key);
		int i = do_lookup(key, hash);
		if (i < 0)
			i = do_insert(std::pair<K, T>(key, T()), hash);
		return entries[i].udata.second;
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
			if (oit == other.end() || oit->second != it.udata.second)
				return false;
		}
		return true;
	}

	bool operator!=(const dict &other) const {
		return !(*this == other);
	}

	size_t size() const { return entries.size(); }
	bool empty() const { return entries.empty(); }
	void clear() { hashtable.clear(); entries.clear(); }

	iterator begin() { return iterator(this, int(entries.size())-1); }
	iterator end() { return iterator(nullptr, -1); }

	const_iterator begin() const { return const_iterator(this, int(entries.size())-1); }
	const_iterator end() const { return const_iterator(nullptr, -1); }
};

// ********************************************************************************
// ********************************************************************************
// ********************************************************************************
// ********************************************************************************
// ********************************************************************************


template<typename K, typename OPS = hash_ops<K>>
class pool
{
	struct entry_t
	{
		K udata;
		int next;

		entry_t() { }
		entry_t(const K &udata, int next) : udata(udata), next(next) { }
	};

	std::vector<int> hashtable;
	std::vector<entry_t> entries;
	OPS ops;

#if 0
	static inline void do_assert(bool cond) {
		if (!cond) throw std::runtime_error("pool<> assert failed.");
	}
#else
	static inline void do_assert(bool) { }
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
		hashtable.resize(hashtable_size(entries.size() * hashtable_size_factor), -1);

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
			entries.push_back(entry_t(value, -1));
			do_rehash();
			hash = do_hash(value);
		} else {
			entries.push_back(entry_t(value, hashtable[hash]));
			hashtable[hash] = entries.size() - 1;
		}
		return entries.size() - 1;
	}

public:
	class iterator
	{
		friend pool;
	protected:
		pool *ptr;
		int index;
	public:
		iterator() { }
		iterator(pool *ptr, int index) : ptr(ptr), index(index) { }
		iterator operator++() { index--; return *this; }
		bool operator==(const iterator &other) const { return index == other.index; }
		bool operator!=(const iterator &other) const { return index != other.index; }
		const K &operator*() const { return ptr->entries[index].udata; }
		const K *operator->() const { return &ptr->entries[index].udata; }
	};

	class const_iterator
	{
		friend pool;
	protected:
		const pool *ptr;
		int index;
	public:
		const_iterator() { }
		const_iterator(const pool *ptr, int index) : ptr(ptr), index(index) { }
		const_iterator operator++() { index--; return *this; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const K &operator*() const { return ptr->entries[index].udata; }
		const K *operator->() const { return &ptr->entries[index].udata; }
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
		return !(*this == other);
	}

	size_t size() const { return entries.size(); }
	bool empty() const { return entries.empty(); }
	void clear() { hashtable.clear(); entries.clear(); }

	iterator begin() { return iterator(this, int(entries.size())-1); }
	iterator end() { return iterator(nullptr, -1); }

	const_iterator begin() const { return const_iterator(this, int(entries.size())-1); }
	const_iterator end() const { return const_iterator(nullptr, -1); }
};

} /* namespace hashlib */

#endif
