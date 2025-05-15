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

// This file contains various c++ utility routines and helper classes that
// do not depend on any other components of yosys (except stuff like log_*).

#include "kernel/yosys.h"

#ifndef UTILS_H
#define UTILS_H

YOSYS_NAMESPACE_BEGIN

// ------------------------------------------------
// A map-like container, but you can save and restore the state
// ------------------------------------------------

template<typename Key, typename T>
struct stackmap
{
private:
	std::vector<dict<Key, T*>> backup_state;
	dict<Key, T> current_state;
	static T empty_tuple;

public:
	stackmap() { }
	stackmap(const dict<Key, T> &other) : current_state(other) { }

	template<typename Other>
	void operator=(const Other &other)
	{
		for (auto &it : current_state)
			if (!backup_state.empty() && backup_state.back().count(it.first) == 0)
				backup_state.back()[it.first] = new T(it.second);
		current_state.clear();

		for (auto &it : other)
			set(it.first, it.second);
	}

	bool has(const Key &k)
	{
		return current_state.count(k) != 0;
	}

	void set(const Key &k, const T &v)
	{
		if (!backup_state.empty() && backup_state.back().count(k) == 0)
			backup_state.back()[k] = current_state.count(k) ? new T(current_state.at(k)) : nullptr;
		current_state[k] = v;
	}

	void unset(const Key &k)
	{
		if (!backup_state.empty() && backup_state.back().count(k) == 0)
			backup_state.back()[k] = current_state.count(k) ? new T(current_state.at(k)) : nullptr;
		current_state.erase(k);
	}

	const T &get(const Key &k)
	{
		if (current_state.count(k) == 0)
			return empty_tuple;
		return current_state.at(k);
	}

	void reset(const Key &k)
	{
		for (int i = GetSize(backup_state)-1; i >= 0; i--)
			if (backup_state[i].count(k) != 0) {
				if (backup_state[i].at(k) == nullptr)
					current_state.erase(k);
				else
					current_state[k] = *backup_state[i].at(k);
				return;
			}
		current_state.erase(k);
	}

	const dict<Key, T> &stdmap()
	{
		return current_state;
	}

	void save()
	{
		backup_state.resize(backup_state.size()+1);
	}

	void restore()
	{
		log_assert(!backup_state.empty());
		for (auto &it : backup_state.back())
			if (it.second != nullptr) {
				current_state[it.first] = *it.second;
				delete it.second;
			} else
				current_state.erase(it.first);
		backup_state.pop_back();
	}

	~stackmap()
	{
		while (!backup_state.empty())
			restore();
	}
};


// ------------------------------------------------
// A simple class for topological sorting
// ------------------------------------------------

template <typename T, typename C = std::less<T>> class TopoSort
{
      public:
	// We use this ordering of the edges in the adjacency matrix for
	// exact compatibility with an older implementation.
	struct IndirectCmp {
                IndirectCmp(const std::vector<T> &nodes) : node_cmp_(), nodes_(nodes) {}
		bool operator()(int a, int b) const
		{
                        log_assert(static_cast<size_t>(a) < nodes_.size());
			log_assert(static_cast<size_t>(b) < nodes_.size());
			return node_cmp_(nodes_[a], nodes_[b]);
		}
		const C node_cmp_;
		const std::vector<T> &nodes_;
	};

	bool analyze_loops;
	std::map<T, int, C> node_to_index;
	std::vector<std::set<int, IndirectCmp>> edges;
	std::vector<T> sorted;
	std::set<std::vector<T>> loops;

	TopoSort() : indirect_cmp(nodes)
	{
		analyze_loops = true;
		found_loops = false;
	}

	int node(T n)
	{
                auto rv = node_to_index.emplace(n, static_cast<int>(nodes.size()));
                if (rv.second) {
      	              nodes.push_back(n);
		      edges.push_back(std::set<int, IndirectCmp>(indirect_cmp));
		}
		return rv.first->second;
	}

	void edge(int l_index, int r_index) { edges[r_index].insert(l_index); }

	void edge(T left, T right) { edge(node(left), node(right)); }

	bool has_node(const T &node) { return node_to_index.find(node) != node_to_index.end(); }

	bool sort()
	{
		log_assert(GetSize(node_to_index) == GetSize(edges));
		log_assert(GetSize(nodes) == GetSize(edges));

		loops.clear();
		sorted.clear();
		found_loops = false;

		std::vector<bool> marked_cells(edges.size(), false);
		std::vector<bool> active_cells(edges.size(), false);
		std::vector<int> active_stack;
		sorted.reserve(edges.size());

		for (const auto &it : node_to_index)
			sort_worker(it.second, marked_cells, active_cells, active_stack);

		log_assert(GetSize(sorted) == GetSize(nodes));

		return !found_loops;
	}

	// Build the more expensive representation of edges for
	// a few passes that use it directly.
	std::map<T, std::set<T, C>, C> get_database()
	{
		std::map<T, std::set<T, C>, C> database;
		for (size_t i = 0; i < nodes.size(); ++i) {
			std::set<T, C> converted_edge_set;
			for (int other_node : edges[i]) {
				converted_edge_set.insert(nodes[other_node]);
			}
			database.emplace(nodes[i], converted_edge_set);
		}
		return database;
	}

      private:
	bool found_loops;
	std::vector<T> nodes;
	const IndirectCmp indirect_cmp;

	void sort_worker(const int root_index, std::vector<bool> &marked_cells, std::vector<bool> &active_cells, std::vector<int> &active_stack)
	{
		if (active_cells[root_index]) {
			found_loops = true;
			if (analyze_loops) {
				std::vector<T> loop;
				for (int i = GetSize(active_stack) - 1; i >= 0; i--) {
					const int index = active_stack[i];
					loop.push_back(nodes[index]);
					if (index == root_index)
						break;
				}
				loops.insert(loop);
			}
			return;
		}

		if (marked_cells[root_index])
			return;

		if (!edges[root_index].empty()) {
			if (analyze_loops)
				active_stack.push_back(root_index);
			active_cells[root_index] = true;

			for (int left_n : edges[root_index])
				sort_worker(left_n, marked_cells, active_cells, active_stack);

			if (analyze_loops)
				active_stack.pop_back();
			active_cells[root_index] = false;
		}

		marked_cells[root_index] = true;
		sorted.push_back(nodes[root_index]);
	}
};

// this class is used for implementing operator-> on iterators that return values rather than references
// it's necessary because in C++ operator-> is called recursively until a raw pointer is obtained
template<class T>
struct arrow_proxy {
	T v;
	explicit arrow_proxy(T const & v) : v(v) {}
	T* operator->() { return &v; }
};

inline int ceil_log2(int x)
{
#if defined(__GNUC__)
        return x > 1 ? (8*sizeof(int)) - __builtin_clz(x-1) : 0;
#else
	if (x <= 0)
		return 0;
	for (int i = 0; i < 32; i++)
		if (((x-1) >> i) == 0)
			return i;
	log_abort();
#endif
}

YOSYS_NAMESPACE_END

#endif
