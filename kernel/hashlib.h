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

#define HASHLIB_SIZE_FACTOR 3

// The XOR version of DJB2
// (traditionally 5381 is used as starting value for the djb2 hash)
inline unsigned int mkhash(unsigned int a, unsigned int b) {
	return ((a << 5) + a) ^ b;
}

// The ADD version of DJB2
// (use this version for cache locality in b)
inline unsigned int mkhash_add(unsigned int a, unsigned int b) {
	return ((a << 5) + a) + b;
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
	unsigned int hash(unsigned int a) const {
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

struct hash_cstr_ops {
	bool cmp(const char *a, const char *b) const {
		for (int i = 0; a[i] || b[i]; i++)
			if (a[i] != b[i])
				return false;
		return true;
	}
	unsigned int hash(const char *a) const {
		unsigned int hash = 5381;
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

inline int hashtable_size(int old_size)
{
	// prime numbers, approx. in powers of two
	if (old_size <         53) return         53;
	if (old_size <        113) return        113;
	if (old_size <        251) return        251;
	if (old_size <        503) return        503;
	if (old_size <       1129) return       1129;
	if (old_size <       2503) return       2503;
	if (old_size <       5023) return       5023;
	if (old_size <      11299) return      11299;
	if (old_size <      25097) return      25097;
	if (old_size <      50291) return      50291;
	if (old_size <     112997) return     112997;
	if (old_size <     251003) return     251003;
	if (old_size <     503003) return     503003;
	if (old_size <    1129991) return    1129991;
	if (old_size <    2509993) return    2509993;
	if (old_size <    5029991) return    5029991;
	if (old_size <   11299997) return   11299997;
	if (old_size <   25099999) return   25099999;
	if (old_size <   50299999) return   50299999;
	if (old_size <  113000009) return  113000009;
	if (old_size <  250999999) return  250999999;
	if (old_size <  503000009) return  503000009;
	if (old_size < 1129999999) return 1129999999;
	throw std::length_error("hash table exceeded maximum size");
}

template<typename K, typename T, typename OPS = hash_ops<K>>
class dict
{
	struct entry_t
	{
		int link;
		std::pair<K, T> udata;

		entry_t() : link(-1) { }
		entry_t(const std::pair<K, T> &udata) : link(1), udata(udata) { }

		bool is_free() const { return link < 0; }
		int get_next() const { return (link > 0 ? link : -link) - 2; }
		bool get_last() const { return get_next() == -1; }
		void set_next_used(int next) { link = next + 2; }
		void set_next_free(int next) { link = -(next + 2); }
	};

	std::vector<int> hashtable;
	std::vector<entry_t> entries;
	int free_list, counter;
	OPS ops;

	void init()
	{
		free_list = -1;
		counter = 0;
	}

	void init_from(const dict<K, T, OPS> &other)
	{
		hashtable.clear();
		entries.clear();

		counter = other.size();
		int new_size = hashtable_size(HASHLIB_SIZE_FACTOR * counter);
		hashtable.resize(new_size);
		new_size = new_size / HASHLIB_SIZE_FACTOR + 1;
		entries.reserve(new_size);

		for (auto &it : other)
			entries.push_back(entry_t(it));
		entries.resize(new_size);
		rehash();
	}

	int mkhash(const K &key) const
	{
		unsigned int hash = 0;
		if (!hashtable.empty())
			hash = ops.hash(key) % (unsigned int)(hashtable.size());
		return hash;
	}

	void rehash()
	{
		free_list = -1;

		for (auto &h : hashtable)
			h = -1;

		for (int i = 0; i < int(entries.size()); i++)
			if (entries[i].is_free()) {
				entries[i].set_next_free(free_list);
				free_list = i;
			} else {
				int hash = mkhash(entries[i].udata.first);
				entries[i].set_next_used(hashtable[hash]);
				hashtable[hash] = i;
			}
	}

	void do_erase(const K &key, int hash)
	{
		int last_index = -1;
		int index = hashtable.empty() ? -1 : hashtable[hash];
		while (1) {
			if (index < 0)
				return;
			if (ops.cmp(entries[index].udata.first, key)) {
				if (last_index < 0)
					hashtable[hash] = entries[index].get_next();
				else
					entries[last_index].set_next_used(entries[index].get_next());
				entries[index].udata = std::pair<K, T>();
				entries[index].set_next_free(free_list);
				free_list = index;
				if (--counter == 0)
					init();
				return;
			}
			last_index = index;
			index = entries[index].get_next();
		}
	}

	int lookup_index(const K &key, int hash) const
	{
		int index = hashtable.empty() ? -1 : hashtable[hash];
		while (1) {
			if (index < 0)
				return -1;
			if (ops.cmp(entries[index].udata.first, key))
				return index;
			index = entries[index].get_next();
		}
	}

	int insert_at(const std::pair<K, T> &value, int hash)
	{
		if (free_list < 0)
		{
			int i = entries.size();
			int new_size = hashtable_size(HASHLIB_SIZE_FACTOR * entries.size());
			hashtable.resize(new_size);
			entries.resize(new_size / HASHLIB_SIZE_FACTOR + 1);
			entries[i].udata = value;
			entries[i].set_next_used(0);
			counter++;
			rehash();
			return i;
		}

		int i = free_list;
		free_list = entries[i].get_next();
		entries[i].udata = value;
		entries[i].set_next_used(hashtable[hash]);
		hashtable[hash] = i;
		counter++;
		return i;
	}

public:
	class iterator
	{
		dict<K, T, OPS> *ptr;
		int index;
	public:
		iterator() { }
		iterator(dict<K, T, OPS> *ptr, int index) : ptr(ptr), index(index) { }
		iterator operator++() { do index++; while (index != int(ptr->entries.size()) && ptr->entries[index].is_free()); return *this; }
		iterator operator--() { do index--; while (index != 0 && ptr->entries[index].is_free()); return *this; }
		bool operator==(const iterator &other) const { return index == other.index; }
		bool operator!=(const iterator &other) const { return index != other.index; }
		std::pair<K, T> &operator*() { return ptr->entries[index].udata; }
		std::pair<K, T> *operator->() { return &ptr->entries[index].udata; }
		const std::pair<K, T> &operator*() const { return ptr->entries[index].udata; }
		const std::pair<K, T> *operator->() const { return &ptr->entries[index].udata; }
	};

	class const_iterator
	{
		const dict<K, T, OPS> *ptr;
		int index;
	public:
		const_iterator() { }
		const_iterator(const dict<K, T, OPS> *ptr, int index) : ptr(ptr), index(index) { }
		const_iterator operator++() { do index++; while (index != int(ptr->entries.size()) && ptr->entries[index].is_free()); return *this; }
		const_iterator operator--() { do index--; while (index != 0 && ptr->entries[index].is_free()); return *this; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const std::pair<K, T> &operator*() const { return ptr->entries[index].udata; }
		const std::pair<K, T> *operator->() const { return &ptr->entries[index].udata; }
	};

	dict()
	{
		init();
	}

	dict(const dict<K, T, OPS> &other)
	{
		init_from(other);
	}

	dict(dict<K, T, OPS> &&other)
	{
		free_list = -1;
		counter = 0;
		swap(other);
	}

	dict<K, T, OPS> &operator=(const dict<K, T, OPS> &other) {
		clear();
		init_from(other);
		return *this;
	}

	dict<K, T, OPS> &operator=(dict<K, T, OPS> &&other) {
		clear();
		swap(other);
		return *this;
	}

	dict(const std::initializer_list<std::pair<K, T>> &list)
	{
		init();
		for (auto &it : list)
			insert(it);
	}

	template<class InputIterator>
	dict(InputIterator first, InputIterator last)
	{
		init();
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
		int hash = mkhash(value.first);
		int i = lookup_index(value.first, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = insert_at(value, hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	void erase(const K &key)
	{
		int hash = mkhash(key);
		do_erase(key, hash);
	}

	void erase(const iterator it)
	{
		int hash = mkhash(it->first);
		do_erase(it->first, hash);
	}

	int count(const K &key) const
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		return i < 0 ? 0 : 1;
	}

	iterator find(const K &key)
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		if (i < 0)
			return end();
		return iterator(this, i);
	}

	const_iterator find(const K &key) const
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		if (i < 0)
			return end();
		return const_iterator(this, i);
	}

	T& at(const K &key)
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		if (i < 0)
			throw std::out_of_range("dict::at()");
		return entries[i].udata.second;
	}

	const T& at(const K &key) const
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		if (i < 0)
			throw std::out_of_range("dict::at()");
		return entries[i].udata.second;
	}

	T& operator[](const K &key)
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		if (i < 0)
			i = insert_at(std::pair<K, T>(key, T()), hash);
		return entries[i].udata.second;
	}

	void swap(dict<K, T, OPS> &other)
	{
		hashtable.swap(other.hashtable);
		entries.swap(other.entries);
		std::swap(free_list, other.free_list);
		std::swap(counter, other.counter);
	}

	bool operator==(const dict<K, T, OPS> &other) const {
		if (counter != other.counter)
			return false;
		if (counter == 0)
			return true;
		if (entries.size() < other.entries.size())
			for (auto &it : *this) {
				auto oit = other.find(it.first);
				if (oit == other.end() || oit->second != it.second)
					return false;
			}
		else
			for (auto &oit : other) {
				auto it = find(oit.first);
				if (it == end() || it->second != oit.second)
					return false;
			}
		return true;
	}

	bool operator!=(const dict<K, T, OPS> &other) const {
		return !(*this == other);
	}

	size_t size() const { return counter; }
	bool empty() const { return counter == 0; }
	void clear() { hashtable.clear(); entries.clear(); init(); }

	iterator begin() { int index = 0; while (index != int(entries.size()) && entries[index].is_free()) index++; return iterator(this, index); }
	iterator end() { return iterator(this, entries.size()); }

	const_iterator begin() const { int index = 0; while (index != int(entries.size()) && entries[index].is_free()) index++; return const_iterator(this, index); }
	const_iterator end() const { return const_iterator(this, entries.size()); }
};

template<typename K, typename OPS = hash_ops<K>>
class pool
{
	struct entry_t
	{
		int link;
		K key;

		entry_t() : link(-1) { }
		entry_t(const K &key) : link(1), key(key) { }

		bool is_free() const { return link < 0; }
		int get_next() const { return (link > 0 ? link : -link) - 2; }
		bool get_last() const { return get_next() == -1; }
		void set_next_used(int next) { link = next + 2; }
		void set_next_free(int next) { link = -(next + 2); }
	};

	std::vector<int> hashtable;
	std::vector<entry_t> entries;
	int free_list, counter;
	OPS ops;

	void init()
	{
		free_list = -1;
		counter = 0;
	}

	void init_from(const pool<K, OPS> &other)
	{
		hashtable.clear();
		entries.clear();

		counter = other.size();
		int new_size = hashtable_size(HASHLIB_SIZE_FACTOR * counter);
		hashtable.resize(new_size);
		new_size = new_size / HASHLIB_SIZE_FACTOR + 1;
		entries.reserve(new_size);

		for (auto &it : other)
			entries.push_back(entry_t(it));
		entries.resize(new_size);
		rehash();
	}

	int mkhash(const K &key) const
	{
		unsigned int hash = 0;
		if (!hashtable.empty())
			hash = ops.hash(key) % (unsigned int)(hashtable.size());
		return hash;
	}

	void rehash()
	{
		free_list = -1;

		for (auto &h : hashtable)
			h = -1;

		for (int i = 0; i < int(entries.size()); i++)
			if (entries[i].is_free()) {
				entries[i].set_next_free(free_list);
				free_list = i;
			} else {
				int hash = mkhash(entries[i].key);
				entries[i].set_next_used(hashtable[hash]);
				hashtable[hash] = i;
			}
	}

	void do_erase(const K &key, int hash)
	{
		int last_index = -1;
		int index = hashtable.empty() ? -1 : hashtable[hash];
		while (1) {
			if (index < 0)
				return;
			if (ops.cmp(entries[index].key, key)) {
				if (last_index < 0)
					hashtable[hash] = entries[index].get_next();
				else
					entries[last_index].set_next_used(entries[index].get_next());
				entries[index].key = K();
				entries[index].set_next_free(free_list);
				free_list = index;
				if (--counter == 0)
					init();
				return;
			}
			last_index = index;
			index = entries[index].get_next();
		}
	}

	int lookup_index(const K &key, int hash) const
	{
		int index = hashtable.empty() ? -1 : hashtable[hash];
		while (1) {
			if (index < 0)
				return -1;
			if (ops.cmp(entries[index].key, key))
				return index;
			index = entries[index].get_next();
		}
	}

	int insert_at(const K &key, int hash)
	{
		if (free_list < 0)
		{
			int i = entries.size();
			int new_size = hashtable_size(HASHLIB_SIZE_FACTOR * entries.size());
			hashtable.resize(new_size);
			entries.resize(new_size / HASHLIB_SIZE_FACTOR + 1);
			entries[i].key = key;
			entries[i].set_next_used(0);
			counter++;
			rehash();
			return i;
		}

		int i = free_list;
		free_list = entries[i].get_next();
		entries[i].key = key;
		entries[i].set_next_used(hashtable[hash]);
		hashtable[hash] = i;
		counter++;
		return i;
	}

public:
	class iterator
	{
		pool<K, OPS> *ptr;
		int index;
	public:
		iterator() { }
		iterator(pool<K, OPS> *ptr, int index) : ptr(ptr), index(index) { }
		iterator operator++() { do index++; while (index != int(ptr->entries.size()) && ptr->entries[index].is_free()); return *this; }
		iterator operator--() { do index--; while (index != 0 && ptr->entries[index].is_free()); return *this; }
		bool operator==(const iterator &other) const { return index == other.index; }
		bool operator!=(const iterator &other) const { return index != other.index; }
		K &operator*() { return ptr->entries[index].key; }
		K *operator->() { return &ptr->entries[index].key; }
		const K &operator*() const { return ptr->entries[index].key; }
		const K *operator->() const { return &ptr->entries[index].key; }
	};

	class const_iterator
	{
		const pool<K, OPS> *ptr;
		int index;
	public:
		const_iterator() { }
		const_iterator(const pool<K, OPS> *ptr, int index) : ptr(ptr), index(index) { }
		const_iterator operator++() { do index++; while (index != int(ptr->entries.size()) && ptr->entries[index].is_free()); return *this; }
		const_iterator operator--() { do index--; while (index != 0 && ptr->entries[index].is_free()); return *this; }
		bool operator==(const const_iterator &other) const { return index == other.index; }
		bool operator!=(const const_iterator &other) const { return index != other.index; }
		const K &operator*() const { return ptr->entries[index].key; }
		const K *operator->() const { return &ptr->entries[index].key; }
	};

	pool()
	{
		init();
	}

	pool(const pool<K, OPS> &other)
	{
		init_from(other);
	}

	pool(pool<K, OPS> &&other)
	{
		free_list = -1;
		counter = 0;
		swap(other);
	}

	pool<K, OPS> &operator=(const pool<K, OPS> &other) {
		clear();
		init_from(other);
		return *this;
	}

	pool<K, OPS> &operator=(pool<K, OPS> &&other) {
		clear();
		swap(other);
		return *this;
	}

	pool(const std::initializer_list<K> &list)
	{
		init();
		for (auto &it : list)
			insert(it);
	}

	template<class InputIterator>
	pool(InputIterator first, InputIterator last)
	{
		init();
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
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		if (i >= 0)
			return std::pair<iterator, bool>(iterator(this, i), false);
		i = insert_at(key, hash);
		return std::pair<iterator, bool>(iterator(this, i), true);
	}

	void erase(const K &key)
	{
		int hash = mkhash(key);
		do_erase(key, hash);
	}

	void erase(const iterator it)
	{
		int hash = mkhash(*it);
		do_erase(*it, hash);
	}

	int count(const K &key) const
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		return i < 0 ? 0 : 1;
	}

	iterator find(const K &key)
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		if (i < 0)
			return end();
		return iterator(this, i);
	}

	const_iterator find(const K &key) const
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		if (i < 0)
			return end();
		return const_iterator(this, i);
	}

	bool operator[](const K &key) const
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		return i >= 0;
	}

	void swap(pool<K, OPS> &other)
	{
		hashtable.swap(other.hashtable);
		entries.swap(other.entries);
		std::swap(free_list, other.free_list);
		std::swap(counter, other.counter);
	}

	bool operator==(const pool<K, OPS> &other) const {
		if (counter != other.counter)
			return false;
		if (counter == 0)
			return true;
		if (entries.size() < other.entries.size())
			for (auto &it : *this) {
				auto oit = other.find(it.first);
				if (oit == other.end() || oit->second != it.second)
					return false;
			}
		else
			for (auto &oit : other) {
				auto it = find(oit.first);
				if (it == end() || it->second != oit.second)
					return false;
			}
		return true;
	}

	bool operator!=(const pool<K, OPS> &other) const {
		return !(*this == other);
	}

	size_t size() const { return counter; }
	bool empty() const { return counter == 0; }
	void clear() { hashtable.clear(); entries.clear(); init(); }

	iterator begin() { int index = 0; while (index != int(entries.size()) && entries[index].is_free()) index++; return iterator(this, index); }
	iterator end() { return iterator(this, entries.size()); }

	const_iterator begin() const { int index = 0; while (index != int(entries.size()) && entries[index].is_free()) index++; return const_iterator(this, index); }
	const_iterator end() const { return const_iterator(this, entries.size()); }
};

} /* namespace hashlib */

#endif
