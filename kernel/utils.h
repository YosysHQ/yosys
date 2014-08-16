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

#ifndef TOPOSORT_H
#define TOPOSORT_H

template<typename T>
struct TopoSort
{
	bool analyze_loops, found_loops;
	std::map<T, std::set<T>> database;
	std::set<std::set<T>> loops;
	std::vector<T> sorted;

	TopoSort()
	{
		analyze_loops = true;
		found_loops = false;
	}

	void node(T n)
	{
		if (database.count(n) == 0)
			database[n] = std::set<T>();
	}

	void edge(T left, T right)
	{
		node(left);
		database[right].insert(left);
	}

	void sort_worker(const T &n, std::set<T> &marked_cells, std::set<T> &active_cells, std::vector<T> &active_stack)
	{
		if (active_cells.count(n)) {
			found_loops = false;
			if (analyze_loops) {
				std::set<T> loop;
				for (int i = SIZE(active_stack)-1; i >= 0; i--) {
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

		std::set<T> marked_cells;
		std::set<T> active_cells;
		std::vector<T> active_stack;

		for (auto &it : database)
			sort_worker(it.first, marked_cells, active_cells, active_stack);

		log_assert(SIZE(sorted) == SIZE(database));
		return !found_loops;
	}
};

#endif
