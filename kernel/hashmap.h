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

#include <string>
#include <vector>

inline unsigned int mkhash(unsigned int a, unsigned int b) {
	return ((a << 5) + a) ^ b;
}

template<typename T> struct hash_ops {
	bool cmp(const T &a, const T &b) {
		return a == b;
	}
	unsigned int hash(const T &a) {
		return a.hash();
	}
};

template<> struct hash_ops<int> {
	bool cmp(int a, int b) {
		return a == b;
	}
	unsigned int hash(int a) {
		return a;
	}
};

template<> struct hash_ops<std::string> {
	bool cmp(const std::string &a, const std::string &b) {
		return a == b;
	}
	unsigned int hash(const std::string &a) {
		unsigned int v = 0;
		for (auto c : a)
			v = mkhash(v, c);
		return v;
	}
};

template<typename K, typename T, typename OPS = hash_ops<K>>
class new_dict
{
	struct entry_t
	{
		int link;
		std::pair<K, T> udata;
		entry_t() : link(-1) { }

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
		counter = 0;
		entries.resize(61);
		rehash();
	}

	int mkhash(const K &key)
	{
		return ops.hash(key) % int(hashtable.size());
	}

public:
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
		int index = hashtable[hash];
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
				counter--;
				return;
			}
			last_index = index;
			index = entries[index].get_next();
		}
	}

	int lookup_index(const K &key, int hash)
	{
		int index = hashtable[hash];
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
			entries.resize(2*entries.size());
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
		new_dict<K, T, OPS> *ptr;
		int index;
	public:
		iterator(new_dict<K, T, OPS> *ptr, int index) : ptr(ptr), index(index) { }
		iterator operator++() { do index++; while (index != int(ptr->entries.size()) && ptr->entries[index].is_free()); return *this; }
		iterator operator--() { do index--; while (index != 0 && ptr->entries[index].is_free()); return *this; }
		bool operator==(const iterator &other) const { return index == other.index; }
		bool operator!=(const iterator &other) const { return index != other.index; }
		std::pair<K, T> &operator*() { return ptr->entries[index].udata; }
	};

	new_dict()
	{
		init();
	}

	template<class InputIterator>
	new_dict(InputIterator first, InputIterator last)
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

	int count(const K &key)
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		return i < 0 ? 0 : 1;
	}

	T& operator[](const K &key)
	{
		int hash = mkhash(key);
		int i = lookup_index(key, hash);
		if (i < 0)
			i = insert_at(std::pair<K, T>(key, T()), hash);
		return entries[i].udata.second;
	}

	iterator begin() { int index = 0; while (index != int(entries.size()) && entries[index].is_free()) index++; return iterator(this, index); }
	iterator end() { return iterator(this, entries.size()); }
};

#endif
