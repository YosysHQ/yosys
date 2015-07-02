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

// This file contains various c++ utility routines and helper classes that
// do not depend on any other components of yosys (except stuff like log_*).

#include "kernel/yosys.h"

#ifndef UTILS_H
#define UTILS_H

YOSYS_NAMESPACE_BEGIN

// ------------------------------------------------
// A map-like container, but you can save and restore the state
// ------------------------------------------------

template<typename Key, typename T, typename OPS = hash_ops<Key>>
struct stackmap
{
private:
	std::vector<dict<Key, T*, OPS>> backup_state;
	dict<Key, T, OPS> current_state;
	static T empty_tuple;

public:
	stackmap() { }
	stackmap(const dict<Key, T, OPS> &other) : current_state(other) { }

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

	const dict<Key, T, OPS> &stdmap()
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

template<typename T, typename C = std::less<T>>
struct TopoSort
{
	bool analyze_loops, found_loops;
	std::map<T, std::set<T, C>, C> database;
	std::set<std::set<T, C>> loops;
	std::vector<T> sorted;

	TopoSort()
	{
		analyze_loops = true;
		found_loops = false;
	}

	void node(T n)
	{
		if (database.count(n) == 0)
			database[n] = std::set<T, C>();
	}

	void edge(T left, T right)
	{
		node(left);
		database[right].insert(left);
	}

	void sort_worker(const T &n, std::set<T, C> &marked_cells, std::set<T, C> &active_cells, std::vector<T> &active_stack)
	{
		if (active_cells.count(n)) {
			found_loops = true;
			if (analyze_loops) {
				std::set<T, C> loop;
				for (int i = GetSize(active_stack)-1; i >= 0; i--) {
					loop.insert(active_stack[i]);
					if (active_stack[i] == n)
						break;
				}
				loops.insert(loop);
			}
			return;
		}

		if (marked_cells.count(n))
			return;

		if (!database.at(n).empty())
		{
			if (analyze_loops)
				active_stack.push_back(n);
			active_cells.insert(n);

			for (auto &left_n : database.at(n))
				sort_worker(left_n, marked_cells, active_cells, active_stack);

			if (analyze_loops)
				active_stack.pop_back();
			active_cells.erase(n);
		}

		marked_cells.insert(n);
		sorted.push_back(n);
	}

	bool sort()
	{
		loops.clear();
		sorted.clear();
		found_loops = false;

		std::set<T, C> marked_cells;
		std::set<T, C> active_cells;
		std::vector<T> active_stack;

		for (auto &it : database)
			sort_worker(it.first, marked_cells, active_cells, active_stack);

		log_assert(GetSize(sorted) == GetSize(database));
		return !found_loops;
	}
};

YOSYS_NAMESPACE_END

#endif
