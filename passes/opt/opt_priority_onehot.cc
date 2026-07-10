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
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Pack a per-lane integer vector into a Const with elem_w bits per lane.
static Const pack_lanes(const vector<int> &vals, int elem_w)
{
	vector<State> bits(vals.size() * elem_w, State::S0);
	for (int k = 0; k < GetSize(vals); k++)
		for (int b = 0; b < elem_w && b < 31; b++)
			if ((vals[k] >> b) & 1)
				bits[k * elem_w + b] = State::S1;
	return Const(bits);
}

#include "passes/opt/cut_region.h"

struct OptPriorityOnehotWorker : CutRegionWorker {
	typedef BusCand InputBus;

	// One detected priority-onehot region ready to be rewritten.
	struct Candidate {
		SigSpec out_sig;            // one-hot output O (width W = 2^idx_w)
		std::string out_name;
		SigSpec valid_sig;          // N bits
		SigSpec field_sig;          // N * idx_w bits: concatenated per-lane index fields
		std::string valid_name;
		std::string index_name;
		int n = 0;                  // number of lanes
		int w = 0;                  // output width (power of two)
		int idx_w = 0;              // clog2(w) == per-lane field width
		bool msb_first = false;     // priority direction (false: lowest index wins)
		Cell *anchor = nullptr;     // a driver cell of O, used for naming/src
	};

	struct TestVector {
		vector<int> valid;
		vector<int> field;
	};

	Cell *cell = nullptr;

	int min_width = 4;
	int max_width = 64;
	int regions_rewritten = 0;
	int cells_added = 0;

	OptPriorityOnehotWorker(Module *module) : CutRegionWorker(module)
	{
	}

	// Discover the per-lane index field within candidate bus `d_sig_in`. The bus
	// is viewed as `n` lanes of stride `s = width/n`; each lane must contribute
	// exactly `idx_w` contiguous bits to the cone at a common within-lane offset
	// (handles packed fields, where s == idx_w, and sub-fields like id[*][4:1]).
	// `d_sig_in` may be a single flat input wire or a concatenation of per-lane
	// split-port wires (see collect_split_input_buses).
	bool infer_field(const SigSpec &d_sig_in, int n, int idx_w, int s,
	                 const pool<SigBit> &leaf_bits, SigSpec &field_sig)
	{
		SigSpec d_sig = sigmap(d_sig_in);
		dict<SigBit, int> d_offset;
		for (int i = 0; i < GetSize(d_sig); i++)
			if (d_sig[i].wire)
				d_offset[d_sig[i]] = i;

		vector<std::set<int>> lane_used(n);
		for (auto lb : leaf_bits) {
			auto it = d_offset.find(lb);
			if (it == d_offset.end())
				continue;
			int off = it->second;
			lane_used[off / s].insert(off % s);
		}

		int field_lo = -1;
		for (int k = 0; k < n; k++) {
			auto &used = lane_used[k];
			if (GetSize(used) != idx_w)
				return false;
			int lo = *used.begin();
			int expect = lo;
			for (int v : used) {
				if (v != expect)
					return false;
				expect++;
			}
			if (lo + idx_w > s)
				return false;
			if (field_lo < 0)
				field_lo = lo;
			else if (field_lo != lo)
				return false;
		}
		if (field_lo < 0)
			return false;

		field_sig = SigSpec();
		for (int k = 0; k < n; k++)
			field_sig.append(d_sig.extract(k * s + field_lo, idx_w));
		return true;
	}

	vector<TestVector> make_test_vectors(int n, int w)
	{
		vector<TestVector> vs;
		auto base_field = [&](int mul, int add) {
			vector<int> f(n);
			for (int k = 0; k < n; k++)
				f[k] = ((k * mul + add) % w + w) % w;
			return f;
		};

		// All invalid: output must be all-zero.
		{
			TestVector t;
			t.valid.assign(n, 0);
			t.field = base_field(1, 0);
			vs.push_back(t);
		}

		// Single valid lane: exercises every lane's field routing.
		for (int k = 0; k < n; k++) {
			TestVector t;
			t.valid.assign(n, 0);
			t.valid[k] = 1;
			t.field = base_field(1, 0);
			t.field[k] = k % w;
			vs.push_back(t);
			TestVector t2;
			t2.valid = t.valid;
			t2.field = base_field(3, 1);
			vs.push_back(t2);
		}

		// All valid: distinguishes priority direction.
		{
			TestVector t;
			t.valid.assign(n, 1);
			t.field = base_field(1, 0);
			vs.push_back(t);
		}
		{
			TestVector t;
			t.valid.assign(n, 1);
			t.field = base_field(-1, w - 1);
			vs.push_back(t);
		}

		// Prefix masks valid[k..n-1]: lowest-index winner is k (LSB-first).
		for (int k = 0; k < n; k++) {
			TestVector t;
			t.valid.assign(n, 0);
			for (int j = k; j < n; j++)
				t.valid[j] = 1;
			t.field = base_field(5, 2);
			vs.push_back(t);
		}

		// Suffix masks valid[0..k]: highest-index winner is k (MSB-first).
		for (int k = 0; k < n; k++) {
			TestVector t;
			t.valid.assign(n, 0);
			for (int j = 0; j <= k; j++)
				t.valid[j] = 1;
			t.field = base_field(7, 3);
			vs.push_back(t);
		}

		// Pairs with distinct fields: rejects OR-of-all and wrong direction.
		for (int i = 0; i < n; i++)
			for (int j = i + 1; j < n && j < i + 3; j++) {
				TestVector t;
				t.valid.assign(n, 0);
				t.valid[i] = 1;
				t.valid[j] = 1;
				t.field = base_field(2, 0);
				t.field[i] = (i + 1) % w;
				t.field[j] = (j + 5) % w;
				vs.push_back(t);
			}

		// Pseudo-random coverage.
		uint64_t lfsr = 0x1234567089abcdefULL;
		for (int r = 0; r < 32; r++) {
			lfsr ^= lfsr << 13;
			lfsr ^= lfsr >> 7;
			lfsr ^= lfsr << 17;
			TestVector t;
			t.valid.resize(n);
			t.field.resize(n);
			for (int k = 0; k < n; k++)
				t.valid[k] = (lfsr >> (k % 64)) & 1;
			uint64_t f = lfsr * 2654435761ULL;
			for (int k = 0; k < n; k++)
				t.field[k] = (int)((f >> ((k * 3) % 60)) % (uint64_t)w);
			vs.push_back(t);
		}

		return vs;
	}

	int expected_winner(const vector<int> &valid, int n, bool msb_first)
	{
		if (!msb_first) {
			for (int k = 0; k < n; k++)
				if (valid[k])
					return k;
		} else {
			for (int k = n - 1; k >= 0; k--)
				if (valid[k])
					return k;
		}
		return -1;
	}

	bool fingerprint(const Candidate &cand, bool msb_first)
	{
		ConstEval &ce = shared_ce();
		SigSpec out_sig = sigmap(cand.out_sig);
		SigSpec valid_sig = sigmap(cand.valid_sig);
		SigSpec field_sig = sigmap(cand.field_sig);

		vector<TestVector> vectors = make_test_vectors(cand.n, cand.w);
		for (auto &tv : vectors) {
			ce.push();
			ce.set(valid_sig, pack_lanes(tv.valid, 1));
			ce.set(field_sig, pack_lanes(tv.field, cand.idx_w));

			SigSpec out = out_sig;
			SigSpec undef;
			bool ok = ce.eval(out, undef);
			ce.pop();
			if (!ok || !out.is_fully_const())
				return false;

			Const oc = out.as_const();
			int winner = expected_winner(tv.valid, cand.n, msb_first);
			for (int p = 0; p < cand.w; p++) {
				bool expect = (winner >= 0) && (p == (tv.field[winner] % cand.w));
				bool actual = (p < GetSize(oc)) && (oc[p] == State::S1);
				if (expect != actual)
					return false;
			}
		}
		return true;
	}

	// The fingerprint drives each candidate bus bit independently, so the
	// buses must consist of distinct non-constant bits.
	bool candidate_inputs_disjoint(const Candidate &cand)
	{
		pool<SigBit> seen_bits;
		for (auto bit : sigmap(cand.valid_sig))
			if (!bit.wire || !seen_bits.insert(bit).second)
				return false;
		for (auto bit : sigmap(cand.field_sig))
			if (!bit.wire || !seen_bits.insert(bit).second)
				return false;
		return true;
	}

	bool check_candidate(Candidate &cand)
	{
		if (cand.n < min_width || cand.n > max_width)
			return false;
		if (!is_power_of_two(cand.w) || (1 << cand.idx_w) != cand.w)
			return false;
		if (!candidate_inputs_disjoint(cand))
			return false;
		if (!find_anchor_driver(cand.out_sig, cand.anchor))
			return false;
		if (fingerprint(cand, false)) {
			cand.msb_first = false;
			return true;
		}
		if (fingerprint(cand, true)) {
			cand.msb_first = true;
			return true;
		}
		log_debug("  reject %s (valid=%s index=%s): fingerprint mismatch (both directions)\n",
		          cand.out_name.c_str(), cand.valid_name.c_str(), cand.index_name.c_str());
		return false;
	}

	struct Record {
		SigBit valid;
		SigSpec index;
	};

	// Priority merge of two records: the left (higher-priority) record wins
	// unless it is invalid.
	Record combine(Cell *anchor, const Record &lhs, const Record &rhs)
	{
		Cell *cell = anchor;
		SigBit lhs_invalid = module->Not(NEW_ID2_SUFFIX("prionehot_ninv"), SigSpec(lhs.valid),
		                                  false, cell_src(anchor))[0];
		cells_added++;
		SigBit take_rhs = module->And(NEW_ID2_SUFFIX("prionehot_take"),
		                              SigSpec(lhs_invalid), SigSpec(rhs.valid),
		                              false, cell_src(anchor))[0];
		cells_added++;

		Record out;
		out.valid = module->Or(NEW_ID2_SUFFIX("prionehot_orv"),
		                       SigSpec(lhs.valid), SigSpec(rhs.valid),
		                       false, cell_src(anchor))[0];
		cells_added++;
		out.index = module->Mux(NEW_ID2_SUFFIX("prionehot_mux"), lhs.index, rhs.index,
		                        SigSpec(take_rhs), cell_src(anchor));
		cells_added++;
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

	// Log-depth binary decoder gated by `valid`: returns a w-bit one-hot where
	// bit p is set iff valid && index == p.
	SigSpec emit_decode(Cell *anchor, SigSpec index, SigBit valid, int w, int idx_w)
	{
		Cell *cell = anchor;
		vector<SigBit> cur;
		cur.push_back(valid);
		for (int b = 0; b < idx_w; b++) {
			SigSpec idx_bit(index[b]);
			SigBit idx_bit_n = module->Not(NEW_ID2_SUFFIX("prionehot_ndec"), idx_bit,
			                              false, cell_src(anchor))[0];
			cells_added++;
			int group = GetSize(cur);
			vector<SigBit> nxt(group * 2);
			for (int g = 0; g < group; g++) {
				nxt[g] = module->And(NEW_ID2_SUFFIX("prionehot_dec0"),
				                     SigSpec(cur[g]), SigSpec(idx_bit_n),
				                     false, cell_src(anchor))[0];
				cells_added++;
				nxt[g + group] = module->And(NEW_ID2_SUFFIX("prionehot_dec1"),
				                             SigSpec(cur[g]), idx_bit,
				                             false, cell_src(anchor))[0];
				cells_added++;
			}
			cur = std::move(nxt);
		}

		SigSpec out;
		for (int p = 0; p < w; p++)
			out.append(cur[p]);
		return out;
	}

	SigSpec emit_priority_onehot(const Candidate &cand)
	{
		vector<Record> leaves;
		for (int k = 0; k < cand.n; k++) {
			// Leftmost leaf has the highest priority.
			int lane = cand.msb_first ? (cand.n - 1 - k) : k;
			Record r;
			r.valid = cand.valid_sig[lane];
			r.index = cand.field_sig.extract(lane * cand.idx_w, cand.idx_w);
			leaves.push_back(r);
		}
		Record root = emit_tree_rec(cand.anchor, leaves, 0, GetSize(leaves));
		return emit_decode(cand.anchor, root.index, root.valid, cand.w, cand.idx_w);
	}

	vector<RootCand> collect_roots()
	{
		int max_cone_cells = std::max(256, max_width * 96);
		int max_leaf_bits = max_width * max_width + max_width * 64 + max_width;
		return collect_root_candidates(
			[&](int w) { return w >= 2 && is_power_of_two(w); },
			[&](const pool<Cell *> &) { return true; },
			true, max_cone_cells, max_leaf_bits, 64);
	}

	void run()
	{
		if (module->has_processes_warn())
			return;

		vector<Wire *> inputs;
		for (auto w : module->wires())
			if (w->port_input)
				inputs.push_back(w);

		// Per-lane split-port buses ("id[0]".."id[N-1]") are grouped once.
		vector<InputBus> split_buses = collect_split_buses(inputs);

		vector<Candidate> rewrites;
		vector<RootCand> root_list = collect_roots();
		for (int ri = 0; ri < GetSize(root_list); ri++) {
			auto &root = root_list[ri];
			if (walk_exhausted() || eval_exhausted()) {
				note_budget("opt_priority_onehot", GetSize(root_list) - ri);
				break;
			}
			if (root_claimed(root.sig))
				continue;

			int w = GetSize(root.sig);
			if (w < 2 || !is_power_of_two(w))
				continue;
			int idx_w = clog2_int(w);

			pool<Cell *> cone_cells;
			pool<SigBit> leaf_bits;
			vector<Cell *> order;
			int max_cone_cells = std::max(256, max_width * 96);
			int max_leaf_bits = max_width * max_width + max_width * w + max_width;
			if (!get_cone(root.sig, cone_cells, leaf_bits, max_cone_cells, max_leaf_bits, &order)) {
				log_debug("root %s (w=%d): cone exceeds size limits\n", root.name.c_str(), w);
				continue;
			}
			if (cone_cells.empty())
				continue;
			log_debug("root %s (w=%d, idx_w=%d): cone %d cells, %d leaf bits\n",
			          root.name.c_str(), w, idx_w, GetSize(cone_cells), GetSize(leaf_bits));

			// Bus candidates: module input ports first (cheap, original
			// behavior), then internal cut signals from the root cone in
			// reverse BFS order (deepest first) to support pre-logic between
			// the ports and the rewritable region.
			vector<InputBus> buses;
			for (auto input : inputs)
				buses.push_back({sigmap(SigSpec(input)), input->name.str(), 0, 0});
			for (auto &bus : split_buses)
				buses.push_back(bus);

			// Internal cut buses are taken from the shallowest cone cells
			// first (depth measured from the leaves), since the cut points
			// introduced by pre-logic sit right above the module inputs.
			const int max_internal_buses = 32;
			int internal_buses = 0;
			pool<SigSpec> seen_buses;
			for (auto &bus : buses)
				seen_buses.insert(bus.sig);
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
					if (GetSize(sig) < min_width || !seen_buses.insert(sig).second)
						continue;
					if (!sig_bus_ok(sig))
						continue;
					buses.push_back({sig, stringf("%s.%s", log_id(c->name), log_id(conn.first)), 0, 0});
					internal_buses++;
				}
			}

			// Whole wires touching the cone (outputs of cone cells or cone
			// leaves, e.g. FF-driven valid/index buses); constant edge bits
			// (never-written vector heads) are trimmed off as maximal runs.
			// Whole wires touching the cone, longest runs first.
			pool<SigBit> cone_sig_bits = cone_sig_bit_pool(cone_cells, leaf_bits);
			for (auto &run : collect_wire_run_buses(cone_sig_bits, 64)) {
				if (!seen_buses.insert(run.sig).second)
					continue;
				buses.push_back(run);
			}

			// Per-lane split wires grouped into buses (array FFs and
			// multi-dimensional nets are lowered into per-entry wires).
			for (auto &bus : collect_cone_split_buses(cone_sig_bits)) {
				SigSpec sig = sigmap(bus.sig);
				if (seen_buses.insert(sig).second)
					buses.push_back({sig, bus.name, bus.entries, bus.elem_width});
			}

			// Valid candidates: each bus as-is first (covers the simple
			// cases cheaply), then one-lane-short windows (regions often use
			// N of an N+1-entry vector, e.g. fits[N:1]).
			vector<InputBus> valid_views;
			for (auto &bus : buses) {
				int nv = GetSize(bus.sig);
				if (nv >= min_width && nv <= max_width)
					valid_views.push_back(bus);
			}
			for (auto &bus : buses) {
				int nv = GetSize(bus.sig);
				if (nv - 1 >= min_width && nv - 1 <= max_width) {
					valid_views.push_back({bus.sig.extract(0, nv - 1),
					                       stringf("%s[%d:0]", bus.name.c_str(), nv - 2), 0, 0});
					valid_views.push_back({bus.sig.extract(1, nv - 1),
					                       stringf("%s[%d:1]", bus.name.c_str(), nv - 1), 0, 0});
				}
			}
			// Power-of-two lane counts (the common region shape) and wider
			// buses first, so the attempt budget is not exhausted on junk
			// pairings in modules with many other wires.
			std::stable_sort(valid_views.begin(), valid_views.end(),
			                 [](const InputBus &a, const InputBus &b) {
			                     int na = GetSize(a.sig), nb = GetSize(b.sig);
			                     bool pa = is_power_of_two(na), pb = is_power_of_two(nb);
			                     if (pa != pb)
			                         return pa;
			                     return na > nb;
			                 });

			// Closure walks are cheap graph traversals; the full candidate
			// check (ConstEval fingerprint) gets its own smaller budget.
			const int max_attempts = 2048;
			const int max_fp_attempts = 24;
			int attempts = 0;
			int fp_attempts = 0;
			bool done = false;
			for (auto &valid : valid_views) {
				if (done || attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
					break;
				int n = GetSize(valid.sig);

				pool<SigBit> valid_bits;
				for (auto bit : sigmap(valid.sig))
					if (bit.wire)
						valid_bits.insert(bit);

				for (auto &src : buses) {
					if (done || attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
						break;
					if (src.sig == valid.sig)
						continue;
					int total = GetSize(src.sig);

					// Index source views: the bus split into n lanes, or n
					// contiguous lanes of an (n+1)-lane bus (e.g. ids[N:1]
					// of an [N:0] table).
					vector<std::pair<SigSpec, std::string>> src_views;
					if (total % n == 0 && total / n >= idx_w)
						src_views.push_back({src.sig, src.name});
					else if (total % (n + 1) == 0 && total / (n + 1) >= idx_w) {
						int s2 = total / (n + 1);
						src_views.push_back({src.sig.extract(0, n * s2),
						                     stringf("%s[lane0+]", src.name.c_str())});
						src_views.push_back({src.sig.extract(s2, n * s2),
						                     stringf("%s[lane1+]", src.name.c_str())});
					}

					for (auto &sv : src_views) {
						if (done || attempts >= max_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
							break;
						int s = GetSize(sv.first) / n;

						// Cut the root cone at valid+index bits: it must close
						// without reaching other inputs, and the index bits the
						// cone actually uses define the per-lane field layout.
						pool<SigBit> allowed = valid_bits;
						for (auto bit : sigmap(sv.first))
							if (bit.wire)
								allowed.insert(bit);
						pool<SigBit> hit_bits;
						pool<Cell *> cut_cells;
						attempts++;
						if (!cut_cone_walk(root.sig, allowed, GetSize(cone_cells) + 16, &hit_bits, &cut_cells,
						                   nullptr, &leaf_bits, &cone_cells)) {
							log_debug("  valid=%s index=%s: cut not closed (%s)\n",
							          valid.name.c_str(), sv.second.c_str(), last_cut_fail.c_str());
							continue;
						}

						SigSpec field_sig;
						if (!infer_field(sv.first, n, idx_w, s, hit_bits, field_sig)) {
							log_debug("  valid=%s index=%s (n=%d, s=%d): field layout inference failed\n",
							          valid.name.c_str(), sv.second.c_str(), n, s);
							continue;
						}

						// The fingerprint forces every valid+field bit, and
						// ConstEval caches whole cell outputs: no forced bit
						// may be driven by a cell inside the cut cone, even
						// one the cone never reads.
						bool forced_conflict = false;
						for (auto bit : sigmap(valid.sig)) {
							Cell *drv = bit.wire ? bit_to_driver.at(bit, nullptr) : nullptr;
							if (drv != nullptr && cut_cells.count(drv))
								forced_conflict = true;
						}
						for (auto bit : sigmap(field_sig)) {
							Cell *drv = bit.wire ? bit_to_driver.at(bit, nullptr) : nullptr;
							if (drv != nullptr && cut_cells.count(drv))
								forced_conflict = true;
						}
						if (forced_conflict) {
							log_debug("  valid=%s index=%s: forced bit driven inside cone\n",
							          valid.name.c_str(), sv.second.c_str());
							continue;
						}

						Candidate cand;
						cand.out_sig = root.sig;
						cand.out_name = root.name;
						cand.valid_sig = valid.sig;
						cand.field_sig = field_sig;
						cand.valid_name = valid.name;
						cand.index_name = sv.second;
						cand.n = n;
						cand.w = w;
						cand.idx_w = idx_w;
						fp_attempts++;
						if (!check_candidate(cand))
							continue;

						rewrites.push_back(cand);
						claim_region(root.sig, cut_cells);
						log("  %s: %s <- priority_onehot(valid=%s, index=%s) "
						    "[N=%d, W=%d, IDX_W=%d, %s]\n",
						    log_id(module), cand.out_name.c_str(), valid.name.c_str(), sv.second.c_str(),
						    cand.n, cand.w, cand.idx_w,
						    cand.msb_first ? "MSB-first" : "LSB-first");
						done = true;
						break;
					}
				}
			}
		}

		for (auto &cand : rewrites) {
			cell = cand.anchor;
			SigSpec new_out = emit_priority_onehot(cand);
			disconnect_root(cand.out_sig, cand.anchor, "prionehot_dangling");
			module->connect(cand.out_sig, new_out);
			regions_rewritten++;
		}
	}
};

struct OptPriorityOnehotPass : public Pass {
	OptPriorityOnehotPass() : Pass("opt_priority_onehot",
		"rewrite priority-select + one-hot index scatter into balanced trees") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_priority_onehot [options] [selection]\n");
		log("\n");
		log("This pass uses functional fingerprinting to detect combinational regions\n");
		log("that compute a priority (first-set) select of a per-lane index field and\n");
		log("scatter the winning field into a one-hot output, regardless of how the\n");
		log("RTL was written (unrolled for-loops, leading-one chains, |= scatter, etc.).\n");
		log("\n");
		log("Concretely, for a request/valid bus of N lanes and a per-lane index field,\n");
		log("the region computes:\n");
		log("\n");
		log("    winner = first lane with valid[lane] set (lowest index by default)\n");
		log("    out    = (winner exists) ? (1 << field[winner]) : 0\n");
		log("\n");
		log("where out has power-of-two width W = 2^idx_w and field is idx_w bits wide.\n");
		log("Each detected region is replaced with a balanced (log-depth) priority\n");
		log("selection tree feeding a log-depth one-hot decoder, replacing the\n");
		log("linear leading-one and scatter chains in the original RTL.\n");
		log("\n");
		log("The per-lane index field may be a sub-slice of a wider flat input bus\n");
		log("(e.g. id[*][4:1] of a packed [N][5] bus); the lane stride and field\n");
		log("offset are inferred from the fanin cone. Both LSB-first (lowest index\n");
		log("wins) and MSB-first priority directions are detected.\n");
		log("\n");
		log("    -max-width N, -max_width N\n");
		log("        maximum lane count to consider (default 64).\n");
		log("\n");
		log("    -min-width N, -min_width N\n");
		log("        minimum lane count to consider (default 4).\n");
		log("\n");
		log("    -walk-budget N, -eval-budget N, -attempt-budget N\n");
		log("        per-module work limits for the candidate search (defaults\n");
		log("        20000000 / 20000000 / 65536). When a budget is exhausted\n");
		log("        the remaining candidates are skipped and a note is logged.\n");
		log("\n");
		log("After rewriting, the original cone cells become unused and are removed\n");
		log("by the trailing 'clean -purge'.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_PRIORITY_ONEHOT pass (priority select + one-hot scatter).\n");

		int max_width = 64;
		int min_width = 4;
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
		int total_cells_added = 0;
		for (auto module : design->selected_modules()) {
			OptPriorityOnehotWorker worker(module);
			worker.max_width = max_width;
			worker.min_width = min_width;
			if (walk_budget > 0)
				worker.walk_budget = walk_budget;
			if (eval_budget > 0)
				worker.eval_budget = eval_budget;
			if (attempt_budget > 0)
				worker.attempt_budget = attempt_budget;
			worker.run();
			total_regions += worker.regions_rewritten;
			total_cells_added += worker.cells_added;
		}

		log("Rewrote %d region(s); emitted %d new cell(s).\n",
		    total_regions, total_cells_added);

		if (total_regions)
			Yosys::run_pass("clean -purge");
	}
} OptPriorityOnehotPass;

PRIVATE_NAMESPACE_END
