/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Akash Levy        <akash@silimate.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include <algorithm>
#include <cctype>
#include <map>
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static int clog2_int(int x)
{
	int r = 0;
	while ((1 << r) < x)
		r++;
	return r;
}

static bool is_power_of_two(int x)
{
	return x > 0 && (x & (x - 1)) == 0;
}

static Const packed_table_const(const vector<uint64_t> &values, int elem_width)
{
	vector<State> bits(values.size() * elem_width, State::S0);
	for (int i = 0; i < GetSize(values); i++)
		for (int b = 0; b < elem_width && b < 64; b++)
			if ((values[i] >> b) & 1ULL)
				bits[i * elem_width + b] = State::S1;
	return Const(bits);
}

static Const packed_valid_const(const vector<int> &valid)
{
	vector<State> bits(valid.size(), State::S0);
	for (int i = 0; i < GetSize(valid); i++)
		if (valid[i])
			bits[i] = State::S1;
	return Const(bits);
}

#include "passes/opt/cut_region.h"

struct OptArgmaxWorker : CutRegionWorker
{
	typedef BusCand InputBus;

	struct TestVector {
		vector<int> valid;
		vector<uint64_t> index;
		vector<uint64_t> values;
	};

	struct Candidate {
		SigSpec out_sig;
		std::string out_name;
		SigSpec valid_sig;
		SigSpec index_sig;
		SigSpec values_sig;
		std::string valid_name;
		std::string index_name;
		std::string values_name;
		bool identity_index = false;
		bool values_const = false;
		bool values_learned = false;
		vector<int> ok_index;
		int width = 0;
		int index_width = 0;
		int value_width = 0;
		Cell *anchor = nullptr;
		IdString anchor_port;
		pool<Cell *> cut_cells;
	};

	struct OutputCone {
		pool<Cell *> cells;
		pool<SigBit> leaves;
		bool saw_bmux = false;
		bool saw_lt = false;
	};

	struct Record {
		SigBit valid;
		SigSpec value;
		SigSpec index;
	};

	Cell *cell = nullptr;

	int min_width = 4;
	int max_width = 64;
	int max_select_lanes = 16;
	// Strict mode disables rewrites that rely on don't-care freedom (the
	// learned const-table mode diverges from the original netlist on
	// x-padded out-of-range table indices), so every emitted region is
	// provable with equiv_opt -assert. Enabled by the flow's formal mode.
	bool strict_mode = false;
	int regions_rewritten = 0;
	int cells_added = 0;

	// Per-root estimate of the cut cone size, used to charge the shared
	// eval budget for each fingerprint vector.
	int64_t cur_cone_est = 64;

	OptArgmaxWorker(Module *module) : CutRegionWorker(module)
	{
	}

	OutputCone summarize_output_cone(const pool<Cell *> &cone_cells, pool<SigBit> leaf_bits)
	{
		OutputCone cone;
		cone.cells = cone_cells;
		cone.leaves = std::move(leaf_bits);
		for (auto c : cone_cells) {
			cone.saw_bmux = cone.saw_bmux || c->type == ID($bmux);
			cone.saw_lt = cone.saw_lt || c->type == ID($lt);
		}
		return cone;
	}

	bool cone_has_required_shape(const OutputCone &cone, int value_width)
	{
		return cone.saw_bmux && (cone.saw_lt || value_width == 1);
	}

	pool<SigBit> candidate_input_bits(const Candidate &cand)
	{
		pool<SigBit> allowed;
		for (auto bit : sigmap(cand.valid_sig))
			if (bit.wire)
				allowed.insert(bit);
		if (!cand.identity_index)
			for (auto bit : sigmap(cand.index_sig))
				if (bit.wire)
					allowed.insert(bit);
		if (!cand.values_const)
			for (auto bit : sigmap(cand.values_sig))
				if (bit.wire)
					allowed.insert(bit);
		return allowed;
	}

	// The fingerprint drives each candidate bus bit independently, so the
	// buses must consist of distinct non-constant bits. Constant value
	// tables are not driven and are exempt.
	bool candidate_inputs_disjoint(const Candidate &cand)
	{
		pool<SigBit> seen_bits;
		for (auto bit : sigmap(cand.valid_sig))
			if (!bit.wire || !seen_bits.insert(bit).second)
				return false;
		if (!cand.identity_index)
			for (auto bit : sigmap(cand.index_sig))
				if (!bit.wire || !seen_bits.insert(bit).second)
					return false;
		if (!cand.values_const)
			for (auto bit : sigmap(cand.values_sig))
				if (!bit.wire || !seen_bits.insert(bit).second)
					return false;
		return true;
	}

	// Decode a constant value table (e.g. a lookup of fixed split sizes read
	// through $bmux) into per-entry integers; x bits decode as zero.
	vector<uint64_t> decode_const_table(const SigSpec &sig, int entries, int elem_width)
	{
		vector<uint64_t> table(entries, 0);
		for (int k = 0; k < entries; k++)
			for (int b = 0; b < elem_width && b < 64; b++)
				if (sig[k * elem_width + b] == State::S1)
					table[k] |= 1ULL << b;
		return table;
	}

	// The per-lane values may be produced by constant lookup logic baked
	// into the cone (e.g. mux trees over a fixed table, where no explicit
	// values bus exists). The induced order relation is observable from the
	// winner index alone: probing two valid lanes with indices (a, b) tells
	// whether T[a] < T[b]. The table is learned up to order isomorphism
	// (ranks) and then verified by the regular fingerprint.
	bool learn_const_table(const Candidate &cand, vector<uint64_t> &table)
	{
		int n = cand.width;
		ConstEval ce(module);
		SigSpec out_sig = sigmap(cand.out_sig);
		SigSpec valid_sig = sigmap(cand.valid_sig);
		SigSpec index_sig = sigmap(cand.index_sig);

		charge_eval((int64_t)n * n * cur_cone_est);
		vector<vector<bool>> lt_rel(n, vector<bool>(n, false));
		vector<vector<bool>> lt_known(n, vector<bool>(n, false));
		for (int a = 0; a < n; a++)
			for (int b = 0; b < n; b++) {
				if (a == b)
					continue;
				vector<int> valid(n, 0);
				valid[0] = 1;
				valid[1] = 1;
				vector<uint64_t> index(n, 0);
				index[0] = a;
				index[1] = b;
				ce.push();
				ce.set(valid_sig, packed_valid_const(valid));
				ce.set(index_sig, packed_table_const(index, cand.index_width));
				SigSpec out = out_sig;
				SigSpec undef;
				bool ok = ce.eval(out, undef);
				ce.pop();
				if (!ok || !out.is_fully_const())
					continue;
				int winner = out.as_const().as_int();
				if (winner != 0 && winner != 1)
					continue;
				lt_rel[a][b] = (winner == 1);
				lt_known[a][b] = true;
			}

		// The relation must form a strict weak order on the entries that the
		// table actually defines. Entries padded with x (out-of-range reads
		// of a short lookup table) are lowered under don't-care freedom and
		// may behave inconsistently; they are excluded from the table and
		// from the verification vectors (ok_index). The frontend already
		// lowers x freely (db_preserve_x 0), so diverging on those index
		// values keeps to the flow's don't-care semantics.
		vector<bool> consistent(n, true);
		auto compute_ranks = [&]() {
			vector<uint64_t> rk(n, 0);
			for (int a = 0; a < n; a++)
				for (int b = 0; b < n; b++)
					if (consistent[a] && consistent[b] && lt_rel[b][a])
						rk[a]++;
			return rk;
		};
		auto count_violations = [&](int x, const vector<uint64_t> &rk) {
			int v = 0;
			for (int b = 0; b < n; b++) {
				if (b == x || !consistent[b])
					continue;
				if (!lt_known[x][b] || lt_rel[x][b] != (rk[x] < rk[b]))
					v++;
				if (!lt_known[b][x] || lt_rel[b][x] != (rk[b] < rk[x]))
					v++;
			}
			return v;
		};

		vector<uint64_t> rank = compute_ranks();
		for (int round = 0; round < n; round++) {
			int worst = -1, worst_v = 0;
			for (int a = 0; a < n; a++) {
				if (!consistent[a])
					continue;
				int v = count_violations(a, rank);
				if (v > worst_v) {
					worst_v = v;
					worst = a;
				}
			}
			if (worst < 0)
				break;
			consistent[worst] = false;
			rank = compute_ranks();
		}

		ok_index.clear();
		for (int a = 0; a < n; a++)
			if (consistent[a])
				ok_index.push_back(a);
		if (GetSize(ok_index) < 2) {
			log_debug("    duel relation inconsistent beyond repair\n");
			return false;
		}
		table = rank;
		return true;
	}

	// Index values whose learned table entries behave consistently; the
	// fingerprint restricts its index test vectors to these (set by
	// learn_const_table, consumed via Candidate::ok_index).
	vector<int> ok_index;

	bool find_anchor_driver(const SigSpec &out_sig, Cell *&anchor, IdString &anchor_port)
	{
		for (auto bit : sigmap(out_sig)) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr)
				continue;
			for (auto &conn : drv->connections()) {
				if (!drv->output(conn.first))
					continue;
				for (auto out_bit : sigmap(conn.second)) {
					if (out_bit == bit) {
						anchor = drv;
						anchor_port = conn.first;
						return true;
					}
				}
			}
		}
		return false;
	}

	uint64_t value_mask(int width)
	{
		if (width >= 64)
			return ~0ULL;
		return (1ULL << width) - 1;
	}

	void add_vector(vector<TestVector> &vectors, const vector<int> &valid,
	                const vector<uint64_t> &index, const vector<uint64_t> &values)
	{
		vectors.push_back({valid, index, values});
	}

	vector<TestVector> make_test_vectors(int width, int value_width)
	{
		vector<TestVector> vectors;
		vector<uint64_t> identity(width), reverse(width), inc(width), dec(width), equal(width, 7);
		uint64_t mask = value_mask(value_width);
		for (int i = 0; i < width; i++) {
			identity[i] = i;
			reverse[i] = width - 1 - i;
			inc[i] = uint64_t(i + 1) & mask;
			dec[i] = uint64_t(width - i) & mask;
		}

		vector<int> valid(width, 0);
		add_vector(vectors, valid, identity, inc);

		for (int i = 0; i < width; i++) {
			valid.assign(width, 0);
			valid[i] = 1;
			add_vector(vectors, valid, identity, inc);
		}

		valid.assign(width, 1);
		add_vector(vectors, valid, identity, inc);
		add_vector(vectors, valid, identity, dec);
		add_vector(vectors, valid, identity, equal);
		add_vector(vectors, valid, reverse, inc);
		add_vector(vectors, valid, reverse, dec);

		for (int i = 0; i + 1 < width; i++) {
			vector<uint64_t> vals(width, 3);
			valid.assign(width, 0);
			valid[i] = 1;
			valid[i + 1] = 1;
			vals[i] = 1;
			vals[i + 1] = 9;
			add_vector(vectors, valid, identity, vals);
			vals[i] = 5;
			vals[i + 1] = 5;
			add_vector(vectors, valid, identity, vals);
		}

		if (width > 2) {
			vector<uint64_t> vals(width, 0);
			valid.assign(width, 0);
			valid[0] = 1;
			valid[width - 1] = 1;
			vals[0] = 2;
			vals[width - 1] = 11;
			add_vector(vectors, valid, identity, vals);
			vals[0] = 13;
			vals[width - 1] = 13;
			add_vector(vectors, valid, identity, vals);
		}

		return vectors;
	}

	int expected_argmax(const TestVector &tv, int width, int value_width, bool identity_index)
	{
		uint64_t mask = value_mask(value_width);
		int best_idx = 0;
		bool best_valid = tv.valid[0] != 0;
		uint64_t best_value = tv.values[identity_index ? 0 : tv.index[0]] & mask;

		for (int k = 1; k < width; k++) {
			bool cand_valid = tv.valid[k] != 0;
			uint64_t cand_value = tv.values[identity_index ? k : tv.index[k]] & mask;
			if (!best_valid && cand_valid) {
				best_idx = k;
				best_valid = true;
				best_value = cand_value;
			} else if (best_valid && cand_valid && best_value < cand_value) {
				best_idx = k;
				best_value = cand_value;
			}
		}

		return best_idx;
	}

	bool fingerprint(const Candidate &cand)
	{
		ConstEval ce(module);
		SigSpec out_sig = sigmap(cand.out_sig);
		SigSpec valid_sig = sigmap(cand.valid_sig);
		SigSpec index_sig = cand.identity_index ? SigSpec() : sigmap(cand.index_sig);
		SigSpec values_sig = sigmap(cand.values_sig);

		// Constant value tables are fixed circuit content rather than a
		// drivable cut: the expected function is checked against the table
		// entries themselves.
		vector<uint64_t> const_table;
		if (cand.values_const)
			const_table = decode_const_table(values_sig, cand.width, cand.value_width);

		vector<TestVector> vectors = make_test_vectors(cand.width, cand.value_width);
		charge_eval((int64_t)vectors.size() * cur_cone_est);
		for (auto &tv : vectors) {
			if (cand.values_const)
				tv.values = const_table;
			// Learned tables only define an order on the consistent index
			// values; restrict the index vectors to those.
			if (cand.values_learned && !cand.ok_index.empty())
				for (auto &iv : tv.index)
					iv = cand.ok_index[iv % cand.ok_index.size()];

			ce.push();
			ce.set(valid_sig, packed_valid_const(tv.valid));
			if (!cand.identity_index)
				ce.set(index_sig, packed_table_const(tv.index, cand.index_width));
			if (!cand.values_const)
				ce.set(values_sig, packed_table_const(tv.values, cand.value_width));

			SigSpec out = out_sig;
			SigSpec undef;
			bool ok = ce.eval(out, undef);
			ce.pop();
			if (!ok || !out.is_fully_const())
				return false;

			int actual = out.as_const().as_int();
			int expected = expected_argmax(tv, cand.width, cand.value_width, cand.identity_index);
			if (actual != expected)
				return false;
		}

		return true;
	}

	SigSpec zext(SigSpec sig, int width)
	{
		sig = sigmap(sig);
		if (GetSize(sig) > width)
			return sig.extract(0, width);
		while (GetSize(sig) < width)
			sig.append(State::S0);
		return sig;
	}

	SigSpec emit_not(Cell *anchor, SigSpec a)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Not(NEW_ID2_SUFFIX("argmax_not"), a);
	}

	SigSpec emit_and(Cell *anchor, SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->And(NEW_ID2_SUFFIX("argmax_and"), a, b);
	}

	SigSpec emit_or(Cell *anchor, SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Or(NEW_ID2_SUFFIX("argmax_or"), a, b);
	}

	SigSpec emit_lt(Cell *anchor, SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Lt(NEW_ID2_SUFFIX("argmax_lt"), a, b);
	}

	SigSpec emit_mux(Cell *anchor, SigSpec a, SigSpec b, SigSpec s)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Mux(NEW_ID2_SUFFIX("argmax_mux"), a, b, s);
	}

	SigSpec emit_bmux(Cell *anchor, SigSpec a, SigSpec s)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Bmux(NEW_ID2_SUFFIX("argmax_val"), a, s);
	}

	Record combine(Cell *anchor, const Record &lhs, const Record &rhs)
	{
		SigSpec lhs_invalid = emit_not(anchor, SigSpec(lhs.valid));
		SigSpec value_lt = emit_lt(anchor, lhs.value, rhs.value);
		SigSpec valid_and_lt = emit_and(anchor, SigSpec(lhs.valid), value_lt);
		SigSpec take_reason = emit_or(anchor, lhs_invalid, valid_and_lt);
		SigSpec take_rhs = emit_and(anchor, SigSpec(rhs.valid), take_reason);

		Record out;
		out.valid = emit_or(anchor, SigSpec(lhs.valid), SigSpec(rhs.valid))[0];
		out.value = emit_mux(anchor, lhs.value, rhs.value, take_rhs);
		out.index = emit_mux(anchor, lhs.index, rhs.index, take_rhs);
		return out;
	}

	Record emit_tree_rec(Cell *anchor, const vector<Record> &leaves, int begin, int end)
	{
		log_assert(begin < end);
		if (begin + 1 == end)
			return leaves[begin];

		int mid = begin + (end - begin) / 2;
		Record lhs = emit_tree_rec(anchor, leaves, begin, mid);
		Record rhs = emit_tree_rec(anchor, leaves, mid, end);
		return combine(anchor, lhs, rhs);
	}

	SigSpec emit_argmax(const Candidate &cand)
	{
		vector<Record> leaves;
		SigSpec valid = sigmap(cand.valid_sig);
		SigSpec index_map = cand.identity_index ? SigSpec() : sigmap(cand.index_sig);
		SigSpec values = sigmap(cand.values_sig);

		for (int k = 0; k < cand.width; k++) {
			SigSpec value;
			if (cand.identity_index)
				value = values.extract(k * cand.value_width, cand.value_width);
			else {
				SigSpec index = index_map.extract(k * cand.index_width, cand.index_width);
				value = emit_bmux(cand.anchor, values, index);
			}
			leaves.push_back({valid[k], value, SigSpec(Const(k, cand.index_width))});
		}

		Record root = emit_tree_rec(cand.anchor, leaves, 0, GetSize(leaves));
		return zext(root.index, cand.index_width);
	}

	void disconnect_old_output(const Candidate &cand)
	{
		disconnect_root(cand.out_sig, cand.anchor, "argmax_dangling");
	}

	bool check_candidate(Candidate &cand, const OutputCone &cone)
	{
		if (cand.width < min_width || cand.width > max_width)
			return false;
		if (!is_power_of_two(cand.width))
			return false;
		if (cand.index_width != clog2_int(cand.width))
			return false;
		if (cand.value_width <= 0 || cand.value_width > 62)
			return false;

		// Learned constant tables imply the compare logic was folded into
		// the cone, so the explicit $lt requirement does not apply.
		if (!cone_has_required_shape(cone, cand.values_learned ? 1 : cand.value_width))
			return false;
		if (!candidate_inputs_disjoint(cand)) {
			log_debug("  valid=%s index=%s values=%s: buses overlap\n",
			          cand.valid_name.c_str(), cand.index_name.c_str(), cand.values_name.c_str());
			return false;
		}
		pool<SigBit> allowed = candidate_input_bits(cand);
		if (!cut_cone_walk(cand.out_sig, allowed, GetSize(cone.cells) + 16, nullptr, &cand.cut_cells,
		                   nullptr, &cone.leaves, &cone.cells)) {
			log_debug("  valid=%s index=%s values=%s: cut not closed (%s)\n",
			          cand.valid_name.c_str(), cand.index_name.c_str(), cand.values_name.c_str(),
			          last_cut_fail.c_str());
			return false;
		}
		if (!find_anchor_driver(cand.out_sig, cand.anchor, cand.anchor_port))
			return false;

		fp_attempts++;
		if (!fingerprint(cand)) {
			log_debug("  valid=%s index=%s values=%s: fingerprint mismatch\n",
			          cand.valid_name.c_str(), cand.index_name.c_str(), cand.values_name.c_str());
			return false;
		}
		return true;
	}

	// ConstEval fingerprints are the expensive step of the candidate search
	// and get their own (smaller) per-root budget; cheap closure walks use
	// the larger trial budget.
	int fp_attempts = 0;

	bool is_compare_cell(Cell *c)
	{
		return c->type.in(ID($lt), ID($gt), ID($le), ID($ge), ID($sub));
	}

	// Argmax roots are index-width signals whose seed cones contain $bmux;
	// max-select roots are value-width signals whose seed cones contain
	// compare cells.
	vector<RootCand> collect_argmax_roots()
	{
		int max_w = clog2_int(max_width);
		return collect_root_candidates(
			[&](int w) { return w >= 2 && w <= max_w; },
			[&](const pool<Cell *> &cone) {
				for (auto c : cone)
					if (c->type == ID($bmux))
						return true;
				return false;
			},
			true, std::max(256, max_width * 96),
			max_width * (max_w + max_width) + max_width);
	}

	vector<RootCand> collect_max_select_roots()
	{
		return collect_root_candidates(
			[&](int w) { return w >= 2 && w <= 62; },
			[&](const pool<Cell *> &cone) {
				int cmps = 0;
				for (auto c : cone)
					if (is_compare_cell(c) && ++cmps >= min_width - 1)
						return true;
				return false;
			},
			true, std::max(256, max_width * 96),
			max_width * (62 + max_width) + max_width);
	}

	// --- Parallel max-select: out = max over N lanes of (zeroed ? 0 : v[n]).
	// Matches hand-written compare-select max trees (e.g. FP exponent max
	// stages) and replaces the serial compare levels with all pairwise
	// comparisons in parallel, a one-hot winner vector, and an AND-OR select.

	struct MaxCand {
		SigSpec out_sig;
		std::string out_name;
		SigSpec values_sig;
		std::string values_name;
		SigSpec mask_sig; // empty for the unmasked form
		std::string mask_name;
		bool zero_when_high = false; // lane forced to 0 when its mask bit is 1
		int lanes = 0;
		int value_width = 0;
		Cell *anchor = nullptr;
		IdString anchor_port;
		pool<Cell *> cut_cells;
	};

	int max_regions_rewritten = 0;

	bool fingerprint_max(const MaxCand &cand)
	{
		int n = cand.lanes;
		int vw = cand.value_width;
		uint64_t vmask = value_mask(vw);
		bool has_mask = !cand.mask_sig.empty();

		ConstEval ce(module);
		SigSpec out_sig = sigmap(cand.out_sig);
		SigSpec values_sig = sigmap(cand.values_sig);
		SigSpec mask_sig = sigmap(cand.mask_sig);

		// Value patterns paired with mask patterns (zeroing the running max
		// must reveal the runner-up, which kills near-miss structures).
		vector<std::pair<vector<uint64_t>, uint64_t>> vectors;
		auto add = [&](vector<uint64_t> vals, uint64_t mask) {
			for (auto &v : vals)
				v &= vmask;
			vectors.push_back({vals, mask});
		};

		vector<uint64_t> asc(n), desc(n), equal(n, 5);
		for (int i = 0; i < n; i++) {
			asc[i] = uint64_t(i + 1);
			desc[i] = uint64_t(n - i);
		}
		add(vector<uint64_t>(n, 0), 0);
		add(asc, 0);
		add(desc, 0);
		add(equal, 0);
		for (int i = 0; i < n; i++) {
			vector<uint64_t> single(n, 0);
			single[i] = vmask;
			add(single, 0);
		}
		if (has_mask) {
			uint64_t all = lowmask_u64(n);
			add(asc, all);
			add(desc, all);
			for (int i = 0; i < n; i++) {
				// Zero the maximal lane: result must become the runner-up.
				vector<uint64_t> vals = asc;
				vals[i] = vmask;
				add(vals, 1ULL << i);
				add(desc, 1ULL << i);
			}
		}
		uint64_t lfsr = 0x243f6a8885a308d3ULL;
		for (int r = 0; r < 24; r++) {
			vector<uint64_t> vals(n);
			for (int i = 0; i < n; i++) {
				lfsr ^= lfsr << 13;
				lfsr ^= lfsr >> 7;
				lfsr ^= lfsr << 17;
				vals[i] = lfsr;
			}
			lfsr ^= lfsr << 13;
			lfsr ^= lfsr >> 7;
			lfsr ^= lfsr << 17;
			add(vals, has_mask ? (lfsr & lowmask_u64(n)) : 0);
		}

		charge_eval((int64_t)vectors.size() * cur_cone_est);
		for (auto &tv : vectors) {
			uint64_t expected = 0;
			for (int i = 0; i < n; i++) {
				bool zeroed = has_mask &&
					((((tv.second >> i) & 1ULL) != 0) == cand.zero_when_high);
				uint64_t v = zeroed ? 0 : tv.first[i];
				expected = std::max(expected, v);
			}

			ce.push();
			ce.set(values_sig, packed_table_const(tv.first, vw));
			if (has_mask) {
				vector<int> mask_bits(n);
				for (int i = 0; i < n; i++)
					mask_bits[i] = (tv.second >> i) & 1ULL;
				ce.set(mask_sig, packed_valid_const(mask_bits));
			}
			SigSpec out = out_sig;
			SigSpec undef;
			bool ok = ce.eval(out, undef);
			ce.pop();
			if (!ok || !out.is_fully_const())
				return false;

			Const oc = out.as_const();
			uint64_t actual = 0;
			for (int i = 0; i < GetSize(oc) && i < 64; i++)
				if (oc[i] == State::S1)
					actual |= 1ULL << i;
			if (actual != expected)
				return false;
		}
		return true;
	}

	SigBit emit_ge(Cell *anchor, SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Ge(NEW_ID2_SUFFIX("maxsel_ge"), a, b)[0];
	}

	SigBit emit_reduce_and(Cell *anchor, SigSpec bits)
	{
		if (GetSize(bits) == 1)
			return bits[0];
		Cell *cell = anchor;
		cells_added++;
		return module->ReduceAnd(NEW_ID2_SUFFIX("maxsel_win"), bits)[0];
	}

	SigSpec emit_or_tree(Cell *anchor, const vector<SigSpec> &terms, int begin, int end)
	{
		log_assert(begin < end);
		if (begin + 1 == end)
			return terms[begin];
		int mid = begin + (end - begin) / 2;
		SigSpec lhs = emit_or_tree(anchor, terms, begin, mid);
		SigSpec rhs = emit_or_tree(anchor, terms, mid, end);
		return emit_or(anchor, lhs, rhs);
	}

	SigSpec emit_max_select(const MaxCand &cand)
	{
		int n = cand.lanes;
		int vw = cand.value_width;
		SigSpec values = sigmap(cand.values_sig);
		SigSpec mask = sigmap(cand.mask_sig);

		// Per-lane masked values.
		vector<SigSpec> m(n);
		for (int i = 0; i < n; i++) {
			m[i] = values.extract(i * vw, vw);
			if (!cand.mask_sig.empty()) {
				SigBit en = mask[i];
				if (cand.zero_when_high)
					en = emit_not(cand.anchor, SigSpec(en))[0];
				m[i] = emit_and(cand.anchor, m[i], SigSpec(en).repeat(vw));
			}
		}

		// All pairwise comparisons in parallel; the winner (lowest index on
		// ties) is the lane that is >= all later lanes and strictly above
		// all earlier ones.
		vector<vector<SigBit>> ge(n, vector<SigBit>(n));
		for (int i = 0; i < n; i++)
			for (int j = i + 1; j < n; j++)
				ge[i][j] = emit_ge(cand.anchor, m[i], m[j]);

		vector<SigSpec> gated(n);
		for (int i = 0; i < n; i++) {
			SigSpec win_terms;
			for (int j = i + 1; j < n; j++)
				win_terms.append(ge[i][j]);
			for (int j = 0; j < i; j++)
				win_terms.append(emit_not(cand.anchor, SigSpec(ge[j][i]))[0]);
			SigBit win = emit_reduce_and(cand.anchor, win_terms);
			gated[i] = emit_and(cand.anchor, m[i], SigSpec(win).repeat(vw));
		}

		return emit_or_tree(cand.anchor, gated, 0, n);
	}

	void run_max_select()
	{
		if (module->has_processes_warn())
			return;

		// Cheap module prefilter: a compare-select tree needs compares and
		// muxes.
		bool has_cmp = false, has_mux = false;
		for (auto c : module->cells()) {
			if (is_compare_cell(c))
				has_cmp = true;
			if (c->type.in(ID($mux), ID($pmux)))
				has_mux = true;
		}
		if (!has_cmp || !has_mux)
			return;

		const int max_lanes = std::min(max_width, max_select_lanes);

		vector<Wire *> inputs;
		for (auto w : module->wires())
			if (w->port_input)
				inputs.push_back(w);

		vector<MaxCand> rewrites;
		vector<RootCand> root_list = collect_max_select_roots();
		for (int ri = 0; ri < GetSize(root_list); ri++) {
			auto &root = root_list[ri];
			if (walk_exhausted() || eval_exhausted()) {
				note_budget("opt_argmax (max-select)", GetSize(root_list) - ri);
				break;
			}
			if (root_claimed(root.sig))
				continue;

			int vw = GetSize(root.sig);
			if (vw < 2 || vw > 62)
				continue;

			pool<Cell *> cone_cells;
			pool<SigBit> leaf_bits;
			vector<Cell *> order;
			int max_cone_cells = std::max(256, max_width * 96);
			int max_leaf_bits = max_width * (vw + max_width) + max_width;
			if (!get_cone(root.sig, cone_cells, leaf_bits,
			              max_cone_cells, max_leaf_bits, &order))
				continue;
			// A max-reduction tree over N >= min_width lanes has at least
			// N-1 compares, each steering a mux select; generic datapath
			// cones (compares and muxes that are not wired as
			// compare-select) are skipped before the expensive bus search.
			int cone_cmp_count = 0;
			pool<SigBit> mux_sel_bits;
			for (auto c : cone_cells) {
				if (is_compare_cell(c))
					cone_cmp_count++;
				if (c->type == ID($mux))
					for (auto bit : sigmap(c->getPort(ID::S)))
						if (bit.wire)
							mux_sel_bits.insert(bit);
			}
			bool cmp_feeds_mux_sel = false;
			for (auto c : cone_cells) {
				if (!is_compare_cell(c) || !c->hasPort(ID::Y))
					continue;
				for (auto bit : sigmap(c->getPort(ID::Y)))
					if (bit.wire && mux_sel_bits.count(bit)) {
						cmp_feeds_mux_sel = true;
						break;
					}
				if (cmp_feeds_mux_sel)
					break;
			}
			if (cone_cmp_count < min_width - 1 || !cmp_feeds_mux_sel)
				continue;
			cur_cone_est = GetSize(cone_cells);
			log_debug("max root %s (vw=%d): cone %d cells, %d leaf bits\n",
			          root.name.c_str(), vw, GetSize(cone_cells), GetSize(leaf_bits));

			// Bus candidates: ports first, then in-cone wire runs (longest
			// first), then internal cell connections shallowest-first.
			vector<InputBus> buses;
			pool<SigSpec> seen_buses;
			for (auto input : inputs) {
				SigSpec sig = sigmap(SigSpec(input));
				if (seen_buses.insert(sig).second)
					buses.push_back({sig, input->name.str(), 0, 0});
			}

			// Whole wires touching the cone, longest runs first.
			pool<SigBit> cone_sig_bits = cone_sig_bit_pool(cone_cells, leaf_bits);
			for (auto &run : collect_wire_run_buses(cone_sig_bits, 64)) {
				if (!seen_buses.insert(run.sig).second)
					continue;
				buses.push_back(run);
			}

			// Per-lane split wires ("exp_cmp[0]".."exp_cmp[N-1]") grouped
			// into lane-ordered buses, same as split ports / array FFs.
			{
				vector<Wire *> cone_wires;
				for (auto wb : module->wires()) {
					bool touches = false;
					for (auto bit : sigmap(SigSpec(wb)))
						if (bit.wire && cone_sig_bits.count(bit)) {
							touches = true;
							break;
						}
					if (touches)
						cone_wires.push_back(wb);
				}
				for (auto &bus : collect_split_buses(cone_wires)) {
					SigSpec sig = sigmap(bus.sig);
					if (seen_buses.insert(sig).second)
						buses.push_back({sig, bus.name, 0, 0});
				}
			}

			dict<Cell *, int> depths = compute_cone_depths(cone_cells);
			vector<Cell *> by_depth = order;
			std::stable_sort(by_depth.begin(), by_depth.end(),
			                 [&](Cell *a, Cell *b) {
			                     return depths.at(a, 1 << 30) < depths.at(b, 1 << 30);
			                 });
			int internal_buses = 0;
			for (auto c : by_depth) {
				if (internal_buses >= 32)
					break;
				for (auto &conn : c->connections()) {
					SigSpec sig = sigmap(conn.second);
					if (GetSize(sig) < 2 || !seen_buses.insert(sig).second)
						continue;
					if (!sig_fully_driven(sig))
						continue;
					buses.push_back({sig, stringf("%s.%s", log_id(c->name), log_id(conn.first)), 0, 0});
					internal_buses++;
				}
			}

			const int max_closure_attempts = 512;
			const int max_fp = 16;
			int closure_attempts = 0;
			int fps = 0;
			bool matched = false;
			MaxCand cand;

			for (auto &values : buses) {
				if (matched || closure_attempts >= max_closure_attempts || fps >= max_fp || walk_exhausted() || eval_exhausted())
					break;
				int total = GetSize(values.sig);
				if (total % vw != 0)
					continue;
				int n = total / vw;
				if (n < min_width || n > max_lanes)
					continue;

				pool<SigBit> value_bits;
				if (!sig_bits_unique(values.sig, value_bits))
					continue;

				cand = MaxCand();
				cand.out_sig = root.sig;
				cand.out_name = root.name;
				cand.values_sig = values.sig;
				cand.values_name = values.name;
				cand.lanes = n;
				cand.value_width = vw;
				if (!find_anchor_driver(root.sig, cand.anchor, cand.anchor_port))
					break;

				// Unmasked form first.
				closure_attempts++;
				if (cut_cone_walk(root.sig, value_bits, GetSize(cone_cells) + 16, nullptr, &cand.cut_cells,
				                  nullptr, &leaf_bits, &cone_cells) &&
				    GetSize(cand.cut_cells) >= 2 * (n - 1)) {
					fps++;
					if (fingerprint_max(cand)) {
						matched = true;
						break;
					}
					log_debug("  max values=%s: fingerprint mismatch\n", values.name.c_str());
				}

				// Masked form: a lane is forced to zero by its mask bit.
				for (auto &mask : buses) {
					if (matched || closure_attempts >= max_closure_attempts || fps >= max_fp || walk_exhausted() || eval_exhausted())
						break;
					if (GetSize(mask.sig) != n || mask.sig == values.sig)
						continue;
					pool<SigBit> allowed = value_bits;
					if (!sig_bits_unique(mask.sig, allowed))
						continue;
					closure_attempts++;
					if (!cut_cone_walk(root.sig, allowed, GetSize(cone_cells) + 16, nullptr, &cand.cut_cells,
					                   nullptr, &leaf_bits, &cone_cells)) {
						log_debug("  max values=%s mask=%s: cut not closed (%s)\n",
						          values.name.c_str(), mask.name.c_str(), last_cut_fail.c_str());
						continue;
					}
					if (GetSize(cand.cut_cells) < 2 * (n - 1))
						continue;
					cand.mask_sig = mask.sig;
					cand.mask_name = mask.name;
					fps++;
					cand.zero_when_high = true;
					if (fingerprint_max(cand)) {
						matched = true;
						break;
					}
					cand.zero_when_high = false;
					if (fingerprint_max(cand)) {
						matched = true;
						break;
					}
					log_debug("  max values=%s mask=%s: fingerprint mismatch\n",
					          values.name.c_str(), mask.name.c_str());
					cand.mask_sig = SigSpec();
					cand.mask_name = "";
				}
			}

			if (matched) {
				rewrites.push_back(cand);
				claim_region(root.sig, cand.cut_cells);
				log("  %s: %s <- max(values=%s%s%s) [N=%d, VW=%d]\n",
				    log_id(module), cand.out_name.c_str(), cand.values_name.c_str(),
				    cand.mask_sig.empty() ? "" : (cand.zero_when_high ? ", zero=" : ", valid="),
				    cand.mask_sig.empty() ? "" : cand.mask_name.c_str(),
				    cand.lanes, cand.value_width);
			}
		}

		for (auto &cand : rewrites) {
			cell = cand.anchor;
			SigSpec new_out = emit_max_select(cand);
			disconnect_root(cand.out_sig, cand.anchor, "argmax_dangling");
			module->connect(cand.out_sig, new_out);
			max_regions_rewritten++;
		}
	}

	void run()
	{
		if (module->has_processes_warn())
			return;

		bool module_has_bmux = false;
		for (auto c : module->cells())
			if (c->type == ID($bmux))
				module_has_bmux = true;
		if (!module_has_bmux)
			return;

		vector<Wire *> inputs;
		for (auto w : module->wires())
			if (w->port_input)
				inputs.push_back(w);
		vector<InputBus> split_buses = collect_split_buses(inputs);

		vector<Candidate> rewrites;
		vector<RootCand> root_list = collect_argmax_roots();
		for (int ri = 0; ri < GetSize(root_list); ri++) {
			auto &root = root_list[ri];
			if (walk_exhausted() || eval_exhausted()) {
				note_budget("opt_argmax", GetSize(root_list) - ri);
				break;
			}
			if (root_claimed(root.sig))
				continue;

			int out_width = GetSize(root.sig);
			int width = 1 << out_width;
			if (width < min_width || width > max_width)
				continue;

			pool<Cell *> cone_cells;
			pool<SigBit> leaf_bits;
			vector<Cell *> order;
			int max_cone_cells = std::max(256, max_width * 96);
			int max_leaf_bits = max_width * (out_width + max_width) + max_width;
			if (!get_cone(root.sig, cone_cells, leaf_bits,
			              max_cone_cells, max_leaf_bits, &order))
				continue;
			OutputCone cone = summarize_output_cone(cone_cells, std::move(leaf_bits));
			if (!cone.saw_bmux)
				continue;
			cur_cone_est = GetSize(cone.cells);
			log_debug("root %s (w=%d, N=%d): cone %d cells, %d leaf bits\n",
			          root.name.c_str(), out_width, width, GetSize(cone.cells), GetSize(cone.leaves));

			// Bus candidates: module input ports first (cheap, original
			// behavior), then internal cut signals from the root cone in
			// reverse BFS order (deepest first) to support pre-logic between
			// the ports and the rewritable region.
			vector<InputBus> valid_buses;
			vector<InputBus> index_buses;
			vector<InputBus> values_buses;
			auto classify_bus = [&](const SigSpec &sig, const std::string &name) {
				int sz = GetSize(sig);
				if (sz == width)
					valid_buses.push_back({sig, name, width, 1});
				if (sz == width * out_width)
					index_buses.push_back({sig, name, width, out_width});
				if (sz >= width && sz % width == 0 && sz / width <= 62)
					values_buses.push_back({sig, name, width, sz / width});
			};

			pool<SigSpec> seen_buses;
			for (auto input : inputs) {
				SigSpec sig = sigmap(SigSpec(input));
				if (seen_buses.insert(sig).second)
					classify_bus(sig, input->name.str());
			}
			for (auto &bus : split_buses) {
				if (!seen_buses.insert(sigmap(bus.sig)).second)
					continue;
				if (bus.entries == width && bus.elem_width == out_width)
					index_buses.push_back(bus);
				if (bus.entries == width)
					values_buses.push_back(bus);
				if (bus.entries == width && bus.elem_width == 1)
					valid_buses.push_back(bus);
			}

			// Whole wires touching the cone, longest runs first.
			pool<SigBit> cone_sig_bits = cone_sig_bit_pool(cone_cells, cone.leaves);
			for (auto &run : collect_wire_run_buses(cone_sig_bits, 64)) {
				if (!seen_buses.insert(run.sig).second)
					continue;
				classify_bus(run.sig, run.name);
			}

			// Per-lane split wires ("ids_q[0]".."ids_q[N]") grouped into
			// buses: array FFs are lowered into per-entry registers the same
			// way multi-dimensional ports are split.
			{
				vector<Wire *> cone_wires;
				for (auto wb : module->wires()) {
					bool touches = false;
					for (auto bit : sigmap(SigSpec(wb)))
						if (bit.wire && cone_sig_bits.count(bit)) {
							touches = true;
							break;
						}
					if (touches)
						cone_wires.push_back(wb);
				}
				for (auto &bus : collect_split_buses(cone_wires)) {
					if (!seen_buses.insert(sigmap(bus.sig)).second)
						continue;
					if (bus.entries == width && bus.elem_width == out_width)
						index_buses.push_back(bus);
					if (bus.entries == width)
						values_buses.push_back(bus);
					if (bus.entries == width && bus.elem_width == 1)
						valid_buses.push_back(bus);
					classify_bus(sigmap(bus.sig), bus.name);
				}
			}

			// Constant value tables read through $bmux/$shiftx (fixed lookup
			// tables, e.g. size classes selected by a per-lane id).
			for (auto c : cone_cells) {
				if (!c->type.in(ID($bmux), ID($shiftx)))
					continue;
				SigSpec sig = sigmap(c->getPort(ID::A));
				if (!sig.is_fully_const())
					continue;
				if (GetSize(sig) < width || GetSize(sig) % width != 0 || GetSize(sig) / width > 62)
					continue;
				if (!seen_buses.insert(sig).second)
					continue;
				values_buses.push_back({sig, stringf("%s.A<const>", log_id(c->name)),
				                        width, GetSize(sig) / width, true});
			}

			// Internal cut buses are taken from the shallowest cone cells
			// first (depth measured from the leaves), since the cut points
			// introduced by pre-logic sit right above the module inputs.
			const int max_internal_buses = 32;
			int internal_buses = 0;
			dict<Cell *, int> depths = compute_cone_depths(cone_cells);
			vector<Cell *> by_depth = order;
			std::stable_sort(by_depth.begin(), by_depth.end(),
			                 [&](Cell *a, Cell *b) {
			                     return depths.at(a, 1 << 30) < depths.at(b, 1 << 30);
			                 });
			for (auto c : by_depth) {
				if (internal_buses >= max_internal_buses)
					break;
				for (auto &conn : c->connections()) {
					SigSpec sig = sigmap(conn.second);
					if (GetSize(sig) < width || !seen_buses.insert(sig).second)
						continue;
					if (!sig_fully_driven(sig))
						continue;
					classify_bus(sig, stringf("%s.%s", log_id(c->name), log_id(conn.first)));
					internal_buses++;
				}
			}

			// Each matching mode gets its own budget pair so expensive
			// fingerprints in one mode cannot starve the others.
			const int max_attempts = 768;
			const int max_fp_attempts = 24;
			int attempts = 0;
			fp_attempts = 0;

			// Mode 1: identity-indexed values.
			for (auto &valid : valid_buses) {
				if (attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
					break;

				for (auto &values : values_buses) {
					if (attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
						break;
					if (values.sig == valid.sig)
						continue;
					// Identity-indexed constant values would make the winner
					// a constant function; only table mode uses const values.
					if (values.is_const)
						continue;
					Candidate cand;
					cand.out_sig = root.sig;
					cand.out_name = root.name;
					cand.valid_sig = valid.sig;
					cand.values_sig = values.sig;
					cand.valid_name = valid.name;
					cand.index_name = "<identity>";
					cand.values_name = values.name;
					cand.identity_index = true;
					cand.width = width;
					cand.index_width = out_width;
					cand.value_width = values.elem_width;
					attempts++;
					if (!check_candidate(cand, cone))
						continue;

					rewrites.push_back(cand);
					claim_region(root.sig, cand.cut_cells);
					log("  %s: %s <- argmax(valid=%s, index=<identity>, values=%s) [N=%d, IW=%d, VW=%d]\n",
					    log_id(module), cand.out_name.c_str(), valid.name.c_str(), values.name.c_str(),
					    cand.width, cand.index_width, cand.value_width);
					goto next_root;
				}
			}

			// Mode 2: table-indexed values (explicit or constant tables).
			attempts = 0;
			fp_attempts = 0;
			for (auto &valid : valid_buses) {
				if (attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
					break;

				for (auto &index : index_buses) {
					if (attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
						break;
					if (index.sig == valid.sig)
						continue;
					for (auto &values : values_buses) {
						if (attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
							break;
						if (index.sig == values.sig || values.sig == valid.sig)
							continue;
						Candidate cand;
						cand.out_sig = root.sig;
						cand.out_name = root.name;
						cand.valid_sig = valid.sig;
						cand.index_sig = index.sig;
						cand.values_sig = values.sig;
						cand.valid_name = valid.name;
						cand.index_name = index.name;
						cand.values_name = values.name;
						cand.identity_index = false;
						cand.values_const = values.is_const;
						cand.width = width;
						cand.index_width = out_width;
						cand.value_width = values.elem_width;
						attempts++;
						if (!check_candidate(cand, cone))
							continue;

						rewrites.push_back(cand);
						claim_region(root.sig, cand.cut_cells);
						log("  %s: %s <- argmax(valid=%s, index=%s, values=%s) [N=%d, IW=%d, VW=%d]\n",
						    log_id(module), cand.out_name.c_str(), valid.name.c_str(), index.name.c_str(),
						    values.name.c_str(), cand.width, cand.index_width, cand.value_width);
						goto next_root;
					}
				}
			}

			// Mode 3: table mode with the value table folded into the cone
			// as constant logic (no explicit values bus): learn the induced
			// order by probing two-lane duels, then verify the learned rank
			// table with the regular fingerprint. The learned table only
			// defines the order on consistently-behaving index values, so
			// the rewrite may diverge on x-padded table reads; strict mode
			// skips it to keep every rewrite formally provable.
			if (strict_mode)
				goto next_root;
			attempts = 0;
			fp_attempts = 0;
			for (auto &valid : valid_buses) {
				if (attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
					break;

				for (auto &index : index_buses) {
					if (attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
						break;
					if (index.sig == valid.sig || index.is_const)
						continue;
					Candidate cand;
					cand.out_sig = root.sig;
					cand.out_name = root.name;
					cand.valid_sig = valid.sig;
					cand.index_sig = index.sig;
					cand.valid_name = valid.name;
					cand.index_name = index.name;
					cand.values_name = "<learned>";
					cand.identity_index = false;
					cand.values_const = true;
					cand.values_learned = true;
					cand.width = width;
					cand.index_width = out_width;
					attempts++;

					if (!candidate_inputs_disjoint(cand))
						continue;
					pool<SigBit> allowed = candidate_input_bits(cand);
					if (!cut_cone_walk(cand.out_sig, allowed, GetSize(cone.cells) + 16, nullptr, &cand.cut_cells,
		                   nullptr, &cone.leaves, &cone.cells)) {
						log_debug("  valid=%s index=%s values=<learned>: cut not closed (%s)\n",
						          valid.name.c_str(), index.name.c_str(), last_cut_fail.c_str());
						continue;
					}

					vector<uint64_t> table;
					fp_attempts++;
					if (!learn_const_table(cand, table)) {
						log_debug("  valid=%s index=%s values=<learned>: order probe failed\n",
						          valid.name.c_str(), index.name.c_str());
						continue;
					}
					cand.ok_index = ok_index;
					cand.value_width = std::max(1, clog2_int(width));
					cand.values_sig = SigSpec(packed_table_const(table, cand.value_width));
					if (!check_candidate(cand, cone))
						continue;

					rewrites.push_back(cand);
					claim_region(root.sig, cand.cut_cells);
					log("  %s: %s <- argmax(valid=%s, index=%s, values=<learned>) [N=%d, IW=%d, VW=%d]\n",
					    log_id(module), cand.out_name.c_str(), valid.name.c_str(), index.name.c_str(),
					    cand.width, cand.index_width, cand.value_width);
					goto next_root;
				}
			}
next_root:
			;
		}

		for (auto &cand : rewrites) {
			cell = cand.anchor;
			SigSpec new_out = emit_argmax(cand);
			disconnect_old_output(cand);
			module->connect(cand.out_sig, new_out);
			regions_rewritten++;
		}
	}
};

struct OptArgmaxPass : public Pass
{
	OptArgmaxPass() : Pass("opt_argmax",
		"detect and rewrite masked argmax loops into balanced compare trees") {}

	void help() override
	{
		log("\n");
		log("    opt_argmax [options] [selection]\n");
		log("\n");
		log("Detect combinational masked argmax loops of the form used by\n");
		log("read-after dependency logic and replace the serial loop-carried\n");
		log("index/update cone with a balanced tree of {valid,value,index}\n");
		log("comparators. Ties preserve the lower candidate index, matching a\n");
		log("strict '<' update condition; all-invalid inputs return index zero.\n");
		log("\n");
		log("Regions are matched between cut signals (module ports, FF data pins,\n");
		log("or internal buses) and verified by ConstEval fingerprinting, so the\n");
		log("rewrites apply even when extra combinational logic surrounds the\n");
		log("region. Three argmax modes are tried per candidate root: identity\n");
		log("index, explicit index table, and a learned constant table (the value\n");
		log("lookup was folded into logic; its order is recovered by probing\n");
		log("two-lane duels). A fourth mode rewrites masked max-value reductions\n");
		log("(compare-select trees) into all-pairs parallel comparisons with a\n");
		log("one-hot select.\n");
		log("\n");
		log("    -max-width N, -max_width N\n");
		log("        maximum candidate count to consider (default 64).\n");
		log("\n");
		log("    -min-width N, -min_width N\n");
		log("        minimum candidate count to consider (default 4).\n");
		log("\n");
		log("    -max-lanes N, -max_lanes N\n");
		log("        maximum lane count for the parallel max-select rewrite\n");
		log("        (default 16; the all-pairs comparison area grows with N^2).\n");
		log("\n");
		log("    -strict\n");
		log("        disable rewrites that rely on don't-care freedom (the\n");
		log("        learned const-table mode may diverge on x-padded\n");
		log("        out-of-range table reads). With -strict every rewrite is\n");
		log("        provable with equiv_opt -assert; used by formal flows.\n");
		log("\n");
		log("    -walk-budget N, -eval-budget N, -attempt-budget N\n");
		log("        per-module work limits for the candidate search (defaults\n");
		log("        20000000 / 20000000 / 65536). When a budget is exhausted\n");
		log("        the remaining candidates are skipped and a note is logged.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_ARGMAX pass (masked argmax rewrite).\n");

		int max_width = 64;
		int min_width = 4;
		int max_lanes = 16;
		bool strict = false;
		int64_t walk_budget = -1, eval_budget = -1, attempt_budget = -1;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if ((args[argidx] == "-max-width" || args[argidx] == "-max_width") &&
			    argidx + 1 < args.size()) {
				max_width = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-min-width" || args[argidx] == "-min_width") &&
			    argidx + 1 < args.size()) {
				min_width = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-lanes" || args[argidx] == "-max_lanes") &&
			    argidx + 1 < args.size()) {
				max_lanes = std::stoi(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-strict") {
				strict = true;
				continue;
			}
			if ((args[argidx] == "-walk-budget" || args[argidx] == "-walk_budget") &&
			    argidx + 1 < args.size()) {
				walk_budget = std::stoll(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-eval-budget" || args[argidx] == "-eval_budget") &&
			    argidx + 1 < args.size()) {
				eval_budget = std::stoll(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-attempt-budget" || args[argidx] == "-attempt_budget") &&
			    argidx + 1 < args.size()) {
				attempt_budget = std::stoll(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0;
		int total_max_regions = 0;
		int total_cells_added = 0;
		for (auto module : design->selected_modules()) {
			OptArgmaxWorker worker(module);
			worker.max_width = max_width;
			worker.min_width = min_width;
			worker.max_select_lanes = max_lanes;
			worker.strict_mode = strict;
			if (walk_budget > 0)
				worker.walk_budget = walk_budget;
			if (eval_budget > 0)
				worker.eval_budget = eval_budget;
			if (attempt_budget > 0)
				worker.attempt_budget = attempt_budget;
			worker.run();
			worker.run_max_select();
			total_regions += worker.regions_rewritten;
			total_max_regions += worker.max_regions_rewritten;
			total_cells_added += worker.cells_added;
		}

		log("Rewrote %d argmax region(s) and %d max-select region(s); emitted %d new cell(s).\n",
		    total_regions, total_max_regions, total_cells_added);

		if (total_regions || total_max_regions)
			Yosys::run_pass("clean -purge");
	}
} OptArgmaxPass;

PRIVATE_NAMESPACE_END
