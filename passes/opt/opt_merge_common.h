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

#ifndef OPT_MERGE_COMMON_H
#define OPT_MERGE_COMMON_H

#include "kernel/yosys.h"
#include "kernel/ffinit.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/hashlib.h"
#include <algorithm>
#include <utility>

YOSYS_NAMESPACE_BEGIN

namespace OptMergeCommon {

template <typename T, typename U>
inline Hasher hash_pair(const T &t, const U &u) { return hash_ops<std::pair<T, U>>::hash(t, u); }

// Shared cell hashing/comparison logic for opt_merge and opt_merge_inc.
// When apply_sigmap is true, signals are run through assign_map before hashing
// and comparison. When false, signals are used as-is (the caller is expected to
// have pre-normalized them, e.g. via design->sigNormalize).
struct CellHasher
{
	const SigMap &assign_map;
	const FfInitVals &initvals;
	bool apply_sigmap;

	CellHasher(const SigMap &assign_map, const FfInitVals &initvals, bool apply_sigmap)
		: assign_map(assign_map), initvals(initvals), apply_sigmap(apply_sigmap) {}

	SigSpec map_sig(const SigSpec &sig) const {
		return apply_sigmap ? assign_map(sig) : sig;
	}

	static Hasher hash_pmux_in(const SigSpec& sig_s, const SigSpec& sig_b, Hasher h)
	{
		int s_width = GetSize(sig_s);
		int width = GetSize(sig_b) / s_width;

		hashlib::commutative_hash comm;
		for (int i = 0; i < s_width; i++)
			comm.eat(hash_pair(sig_s[i], sig_b.extract(i*width, width)));

		return comm.hash_into(h);
	}

	static void sort_pmux_conn(dict<RTLIL::IdString, RTLIL::SigSpec> &conn)
	{
		const SigSpec &sig_s = conn.at(ID::S);
		const SigSpec &sig_b = conn.at(ID::B);

		int s_width = GetSize(sig_s);
		int width = GetSize(sig_b) / s_width;

		std::vector<std::pair<SigBit, SigSpec>> sb_pairs;
		for (int i = 0; i < s_width; i++)
			sb_pairs.push_back(std::pair<SigBit, SigSpec>(sig_s[i], sig_b.extract(i*width, width)));

		std::sort(sb_pairs.begin(), sb_pairs.end());

		conn[ID::S] = SigSpec();
		conn[ID::B] = SigSpec();

		for (auto &it : sb_pairs) {
			conn[ID::S].append(it.first);
			conn[ID::B].append(it.second);
		}
	}

	Hasher hash_cell_inputs(const RTLIL::Cell *cell, Hasher h) const
	{
		// TODO: when implemented, use celltypes to match:
		// (builtin || stdcell) && (unary || binary) && symmetrical
		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($add), ID($mul),
				ID($logic_and), ID($logic_or), ID($_AND_), ID($_OR_), ID($_XOR_))) {
			hashlib::commutative_hash comm;
			comm.eat(map_sig(cell->getPort(ID::A)));
			comm.eat(map_sig(cell->getPort(ID::B)));
			h = comm.hash_into(h);
		} else if (cell->type.in(ID($reduce_xor), ID($reduce_xnor))) {
			SigSpec a = map_sig(cell->getPort(ID::A));
			a.sort();
			h = a.hash_into(h);
		} else if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool))) {
			SigSpec a = map_sig(cell->getPort(ID::A));
			a.sort_and_unify();
			h = a.hash_into(h);
		} else if (cell->type == ID($pmux)) {
			SigSpec sig_s = map_sig(cell->getPort(ID::S));
			SigSpec sig_b = map_sig(cell->getPort(ID::B));
			h = hash_pmux_in(sig_s, sig_b, h);
			h = map_sig(cell->getPort(ID::A)).hash_into(h);
		} else {
			hashlib::commutative_hash comm;
			for (const auto& [port, sig] : cell->connections()) {
				if (cell->output(port))
					continue;
				comm.eat(hash_pair(port, map_sig(sig)));
			}
			h = comm.hash_into(h);
			if (cell->is_builtin_ff())
				h = initvals(cell->getPort(ID::Q)).hash_into(h);
		}
		return h;
	}

	static Hasher hash_cell_parameters(const RTLIL::Cell *cell, Hasher h)
	{
		hashlib::commutative_hash comm;
		for (const auto& param : cell->parameters) {
			comm.eat(param);
		}
		return comm.hash_into(h);
	}

	Hasher hash_cell_function(const RTLIL::Cell *cell, Hasher h) const
	{
		h.eat(cell->type);
		h = hash_cell_inputs(cell, h);
		h = hash_cell_parameters(cell, h);
		return h;
	}

	bool compare_cell_parameters_and_connections(const RTLIL::Cell *cell1, const RTLIL::Cell *cell2) const
	{
		if (cell1 == cell2) return true;
		if (cell1->type != cell2->type) return false;

		if (cell1->parameters != cell2->parameters)
			return false;
		if (cell1->connections_.size() != cell2->connections_.size())
			return false;
		for (const auto &it : cell1->connections_)
			if (!cell2->connections_.count(it.first))
				return false;

		decltype(RTLIL::Cell::connections_) conn1, conn2;
		conn1.reserve(cell1->connections_.size());
		conn2.reserve(cell1->connections_.size());

		for (const auto &it : cell1->connections_) {
			if (cell1->output(it.first)) {
				if (it.first == ID::Q && cell1->is_builtin_ff()) {
					// For the 'Q' output of state elements,
					//   use the (* init *) attribute value
					conn1[it.first] = initvals(it.second);
					conn2[it.first] = initvals(cell2->getPort(it.first));
				}
				else {
					conn1[it.first] = RTLIL::SigSpec();
					conn2[it.first] = RTLIL::SigSpec();
				}
			}
			else {
				conn1[it.first] = map_sig(it.second);
				conn2[it.first] = map_sig(cell2->getPort(it.first));
			}
		}

		if (cell1->type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($add), ID($mul),
				ID($logic_and), ID($logic_or), ID($_AND_), ID($_OR_), ID($_XOR_))) {
			if (conn1.at(ID::A) < conn1.at(ID::B)) {
				std::swap(conn1[ID::A], conn1[ID::B]);
			}
			if (conn2.at(ID::A) < conn2.at(ID::B)) {
				std::swap(conn2[ID::A], conn2[ID::B]);
			}
		} else
		if (cell1->type.in(ID($reduce_xor), ID($reduce_xnor))) {
			conn1[ID::A].sort();
			conn2[ID::A].sort();
		} else
		if (cell1->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool))) {
			conn1[ID::A].sort_and_unify();
			conn2[ID::A].sort_and_unify();
		} else
		if (cell1->type == ID($pmux)) {
			sort_pmux_conn(conn1);
			sort_pmux_conn(conn2);
		}

		return conn1 == conn2;
	}

	bool has_dont_care_initval(const RTLIL::Cell *cell) const
	{
		if (!cell->is_builtin_ff())
			return false;

		return !initvals(cell->getPort(ID::Q)).is_fully_def();
	}
};

} // namespace OptMergeCommon

YOSYS_NAMESPACE_END

#endif
