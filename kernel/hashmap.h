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

#ifndef YOSYS_HASHMAP_H

#include <stdexcept>
#include <string>
#include <vector>

inline unsigned int mkhash(unsigned int a, unsigned int b) {
	return ((a << 5) + a) ^ b;
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
	bool cmp(int a, int b) const {
		return a == b;
	}
	unsigned int hash(int a) const {
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

struct hash_ptr_ops {
	bool cmp(const void *a, const void *b) const {
		return a == b;
	}
	unsigned int hash(const void *a) const {
		return (unsigned long)a;
	}
};

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
		int new_size = grow_size(counter);
		entries.reserve(new_size);

		for (auto &it : other)
			entries.push_back(entry_t(it));
		entries.resize(new_size);
		rehash();
	}

	size_t grow_size(size_t old_size)
	{
		if (old_size <         53) return         53;
		if (old_size <        113) return        113;
		if (old_size <        251) return        251;
		if (old_size <        503) return        503;
		if (old_size <       1130) return       1130;
		if (old_size <       2510) return       2510;
		if (old_size <       5030) return       5030;
		if (old_size <      11300) return      11300;
		if (old_size <      25100) return      25100;
		if (old_size <      50300) return      50300;
		if (old_size <     113000) return     113000;
		if (old_size <     251000) return     251000;
		if (old_size <     503000) return     503000;
		if (old_size <    1130000) return    1130000;
		if (old_size <    2510000) return    2510000;
		if (old_size <    5030000) return    5030000;
		if (old_size <   11300000) return   11300000;
		if (old_size <   25100000) return   25100000;
		if (old_size <   50300000) return   50300000;
		if (old_size <  113000000) return  113000000;
		if (old_size <  251000000) return  251000000;
		if (old_size <  503000000) return  503000000;
		if (old_size < 1130000000) return 1130000000;
		throw std::length_error("maximum size for dict reached");
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

		hashtable.resize(entries.size());
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
			entries.resize(grow_size(i));
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

	iterator insert(const std::pair<K, T> &value)
	{
		int hash = mkhash(value.first);
		int i = lookup_index(value.first, hash);
		if (i >= 0)
			return iterator(this, i);
		i = insert_at(value, hash);
		return iterator(this, i);
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

#endif
