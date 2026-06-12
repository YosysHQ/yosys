/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.     <akash@silimate.com>
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
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static int ceil_log2_int(int v)
{
	int r = 0;
	int n = 1;
	while (n < v) {
		n <<= 1;
		r++;
	}
	return r;
}

#include "passes/opt/cut_region.h"

struct OptCompactPrefixWorker : CutRegionWorker
{
	// One matched compaction region ready to be rewritten. Kind 0 is the
	// forward dense pack (a = packed input), kind 1 the reverse suffix read
	// (a = disable, b = data), kind 2 the modulo decimation (a = en, b = n),
	// kind 3 the forward gather/compress (a = en, b = data).
	struct Rewrite {
		int kind = 0;
		SigSpec root;
		std::string root_name;
		SigSpec a, b;
		std::string a_name, b_name;
		int loop_width = 0;
		bool msb_first = false;
		int mod_offset = 0;
		Cell *anchor = nullptr;
		int cone_cells = 0;
	};

	int max_width;
	Cell *ref_cell = nullptr;

	int forward_rewrites = 0;
	int reverse_rewrites = 0;
	int modulo_rewrites = 0;
	int old_cells_removed = 0;
	int new_cells_emitted = 0;

	OptCompactPrefixWorker(Module *module, int max_width)
		: CutRegionWorker(module), max_width(max_width)
	{
	}

	// Cut buses only need to consist of wire bits; FF outputs (cone leaves)
	// are valid region boundaries even though they have no comb driver.
	bool sig_bus_ok(const SigSpec &sig)
	{
		for (auto bit : sigmap(sig))
			if (!bit.wire)
				return false;
		return true;
	}

	// Lane-ordered bus extraction: for unrolled scan loops the i-th output
	// bit is produced at the i-th loop step, so a boundary signal that first
	// influences root bit i (LSB-first scans; last, for MSB-first scans) is
	// that step's per-lane input. This recovers enable buses that are
	// permutations or replications of other signals and no longer exist as
	// wires or cell connections after elaboration.
	void lane_ordered_buses(const SigSpec &root, const pool<Cell *> &cone_cells,
	                        vector<BusCand> &buses, pool<SigSpec> &seen_buses)
	{
		int width = GetSize(root);
		if (width < 4 || width > 62)
			return;

		// Per root bit: boundary bits (not driven inside the cone) feed the
		// combinational-lane reconstruction; all visited bits additionally
		// feed the per-wire reconstruction (a bus may be an internal hub
		// signal, e.g. a decoder output read through wiring permutations).
		dict<SigBit, int> min_idx, max_idx;
		dict<SigBit, int> all_min_idx, all_max_idx;
		const int max_boundary = 8 * width + 64;
		const int max_tracked = 256 * width + 1024;
		bool track_all = true;
		if (walk_exhausted())
			return;
		for (int i = 0; i < width; i++) {
			SigBit rb = sigmap(root[i]);
			if (!rb.wire)
				return;
			pool<SigBit> visited;
			std::queue<SigBit> wl;
			visited.insert(rb);
			wl.push(rb);
			while (!wl.empty()) {
				SigBit bit = wl.front();
				wl.pop();
				charge_walk(1);
				Cell *drv = bit_to_driver.at(bit, nullptr);

				if (track_all) {
					if (all_min_idx.count(bit) == 0) {
						all_min_idx[bit] = i;
						all_max_idx[bit] = i;
					} else {
						all_min_idx[bit] = std::min(all_min_idx[bit], i);
						all_max_idx[bit] = std::max(all_max_idx[bit], i);
					}
					if (GetSize(all_min_idx) > max_tracked) {
						track_all = false;
						all_min_idx.clear();
						all_max_idx.clear();
					}
				}

				if (drv == nullptr || !cone_cells.count(drv)) {
					if (min_idx.count(bit) == 0) {
						min_idx[bit] = i;
						max_idx[bit] = i;
					} else {
						min_idx[bit] = std::min(min_idx[bit], i);
						max_idx[bit] = std::max(max_idx[bit], i);
					}
					continue;
				}
				for (auto &conn : drv->connections()) {
					if (!drv->input(conn.first))
						continue;
					for (auto in_bit : sigmap(conn.second)) {
						if (!in_bit.wire)
							continue;
						if (visited.insert(in_bit).second)
							wl.push(in_bit);
					}
				}
			}
			if (GetSize(min_idx) > max_boundary)
				return;
		}

		auto build = [&](const dict<SigBit, int> &idx_of, const char *tag) {
			vector<vector<SigBit>> lanes(width);
			for (auto &it : idx_of)
				lanes[it.second].push_back(it.first);

			// Every lane needs at least one bit; ambiguous lanes (shared
			// control like the modulus also lands in the first lane) are
			// expanded into a few alternative buses.
			long combos = 1;
			for (int i = 0; i < width; i++) {
				if (lanes[i].empty())
					return;
				combos *= GetSize(lanes[i]);
				if (combos > 8)
					return;
			}

			vector<SigSpec> cands(1, SigSpec());
			for (int i = 0; i < width; i++) {
				vector<SigSpec> next;
				for (auto &prefix : cands)
					for (auto bit : lanes[i]) {
						SigSpec ext = prefix;
						ext.append(bit);
						next.push_back(ext);
					}
				cands.swap(next);
			}
			for (int c = 0; c < GetSize(cands); c++)
				if (seen_buses.insert(cands[c]).second)
					buses.push_back({cands[c], stringf("<lanes-%s-%d>", tag, c)});
		};

		build(min_idx, "lsb");
		build(max_idx, "msb");

		// Per-wire lane buses: one wire contributing exactly one bit per
		// lane (in lane order) recovers buses that only exist as wiring
		// permutations of another signal.
		log_debug("  lanes: %d boundary bits, %d tracked bits (track_all=%d)\n",
		          GetSize(min_idx), GetSize(all_min_idx), track_all);
		auto build_per_wire = [&](const dict<SigBit, int> &idx_of, const char *tag) {
			dict<Wire *, vector<vector<SigBit>>> by_wire;
			for (auto &it : idx_of) {
				auto &lanes = by_wire[it.first.wire];
				if (lanes.empty())
					lanes.resize(width);
				lanes[it.second].push_back(it.first);
			}
			for (auto &it : by_wire) {
				SigSpec bus;
				bool ok = true;
				int covered = 0;
				for (int i = 0; i < width; i++) {
					if (GetSize(it.second[i]) == 1) {
						covered++;
						if (ok)
							bus.append(it.second[i][0]);
					} else {
						ok = false;
					}
				}
				if (covered >= width - 2 && !ok)
					log_debug("  wlanes-%s %s: %d/%d lanes covered\n",
					          tag, log_id(it.first->name), covered, width);
				if (ok && seen_buses.insert(bus).second)
					buses.push_back({bus, stringf("<wlanes-%s-%s>", tag, log_id(it.first->name))});
			}
		};

		build_per_wire(all_min_idx, "lsb");
		build_per_wire(all_max_idx, "msb");
	}

	// Learn the enable wiring of a gather given its data bus: with all
	// enable candidates forced to 1 the gather is the identity, and zeroing
	// one candidate u deletes exactly the scan positions gated by u (probed
	// with one-hot data). Returns the enable bus in scan order.
	bool learn_gather_enable(const SigSpec &root_sig, const SigSpec &data_sig,
	                         const pool<SigBit> &en_cands, SigSpec &en_bus)
	{
		int width = GetSize(root_sig);
		vector<SigBit> cand_bits;
		for (auto bit : en_cands)
			cand_bits.push_back(bit);

		ConstEval ce(module);
		SigSpec out_s = sigmap(root_sig);
		SigSpec data_s = sigmap(data_sig);
		SigSpec cand_s;
		for (auto bit : cand_bits)
			cand_s.append(bit);
		int nc = GetSize(cand_bits);

		// Prefilter: all candidates enabled must give the identity.
		uint64_t pattern = lowmask_u64(width) & 0xAAAAAAAAAAAAAAAAULL;
		uint64_t actual;
		if (!eval_with(ce, {{cand_s, const_u64(lowmask_u64(nc), nc)},
		                    {data_s, const_u64(pattern, width)}},
		               out_s, actual))
			return false;
		if (actual != pattern)
			return false;

		// Gating matrix: position i is gated by candidate u iff zeroing u
		// (alone) makes one-hot data at position i disappear.
		vector<int> gate_of(width, -1);
		for (int u = 0; u < nc; u++) {
			uint64_t en_val = lowmask_u64(nc) & ~(1ULL << u);
			for (int i = 0; i < width; i++) {
				if (!eval_with(ce, {{cand_s, const_u64(en_val, nc)},
				                    {data_s, const_u64(1ULL << i, width)}},
				               out_s, actual))
					return false;
				if (actual != 0)
					continue;
				if (gate_of[i] >= 0 && gate_of[i] != u)
					return false;
				gate_of[i] = u;
			}
		}
		for (int i = 0; i < width; i++)
			if (gate_of[i] < 0)
				return false;

		en_bus = SigSpec();
		for (int i = 0; i < width; i++)
			en_bus.append(cand_bits[gate_of[i]]);
		return true;
	}

	SigSpec zext(SigSpec sig, int width)
	{
		return zext_sig(sig, width);
	}

	SigSpec balanced_sum_rec(const vector<SigSpec> &terms, int begin, int end, int width)
	{
		if (begin >= end)
			return SigSpec(State::S0, width);
		if (begin + 1 == end)
			return zext(terms[begin], width);

		int mid = begin + (end - begin) / 2;
		SigSpec lhs = balanced_sum_rec(terms, begin, mid, width);
		SigSpec rhs = balanced_sum_rec(terms, mid, end, width);
		Cell *cell = ref_cell;
		log_assert(cell != nullptr);
		Wire *sum = module->addWire(NEW_ID2_SUFFIX("compact_sum"), width);
		module->addAdd(NEW_ID2_SUFFIX("compact_add"), lhs, rhs, sum);
		new_cells_emitted++;
		return SigSpec(sum);
	}

	SigSpec balanced_sum(const vector<SigSpec> &terms, int width)
	{
		return balanced_sum_rec(terms, 0, GetSize(terms), width);
	}

	SigBit emit_not(SigBit bit)
	{
		Cell *cell = ref_cell;
		log_assert(cell != nullptr);
		Wire *out = module->addWire(NEW_ID2_SUFFIX("compact_not"), 1);
		module->addNot(NEW_ID2_SUFFIX("compact_not_cell"), SigSpec(bit), out);
		new_cells_emitted++;
		return SigBit(out);
	}

	SigBit emit_and(SigBit a, SigBit b)
	{
		Cell *cell = ref_cell;
		log_assert(cell != nullptr);
		Wire *out = module->addWire(NEW_ID2_SUFFIX("compact_and"), 1);
		module->addAnd(NEW_ID2_SUFFIX("compact_and_cell"), SigSpec(a), SigSpec(b), out);
		new_cells_emitted++;
		return SigBit(out);
	}

	SigBit emit_eq(SigSpec a, int value, int width)
	{
		Cell *cell = ref_cell;
		log_assert(cell != nullptr);
		Wire *out = module->addWire(NEW_ID2_SUFFIX("compact_eq"), 1);
		module->addEq(NEW_ID2_SUFFIX("compact_eq_cell"), zext(a, width), Const(value, width), out);
		new_cells_emitted++;
		return SigBit(out);
	}

	SigBit emit_gt(SigSpec a, int value, int width)
	{
		Cell *cell = ref_cell;
		log_assert(cell != nullptr);
		Wire *out = module->addWire(NEW_ID2_SUFFIX("compact_gt"), 1);
		module->addGt(NEW_ID2_SUFFIX("compact_gt_cell"), zext(a, width), Const(value, width), out);
		new_cells_emitted++;
		return SigBit(out);
	}

	SigBit emit_reduce_or(SigSpec bits)
	{
		bits = sigmap(bits);
		if (GetSize(bits) == 0)
			return State::S0;
		if (GetSize(bits) == 1)
			return bits[0];

		Cell *cell = ref_cell;
		log_assert(cell != nullptr);
		Wire *out = module->addWire(NEW_ID2_SUFFIX("compact_or"), 1);
		module->addReduceOr(NEW_ID2_SUFFIX("compact_or_cell"), bits, out);
		new_cells_emitted++;
		return SigBit(out);
	}

	SigBit emit_bmux(SigSpec table, SigSpec sel)
	{
		Cell *cell = ref_cell;
		log_assert(cell != nullptr);
		Wire *out = module->addWire(NEW_ID2_SUFFIX("compact_div"), 1);
		module->addBmux(NEW_ID2_SUFFIX("compact_bmux"), table, sel, out);
		new_cells_emitted++;
		return SigBit(out);
	}

	// Per-root estimate of the cut cone size, used to charge the shared
	// eval budget for each fingerprint vector.
	int64_t cur_cone_est = 64;

	bool eval_with(ConstEval &ce, const vector<std::pair<SigSpec, Const>> &sets,
	               const SigSpec &out_sig, uint64_t &result)
	{
		return CutRegionWorker::eval_with(ce, sets, out_sig, result, cur_cone_est);
	}

	vector<uint64_t> make_value_set(int width)
	{
		uint64_t full = lowmask_u64(width);
		vector<uint64_t> vals;
		vals.push_back(0);
		vals.push_back(full);
		vals.push_back(full & 0x5555555555555555ULL);
		vals.push_back(full & 0xAAAAAAAAAAAAAAAAULL);
		for (int i = 0; i < width; i++)
			vals.push_back(1ULL << i);
		uint64_t lfsr = 0x1234567089abcdefULL;
		for (int r = 0; r < 32; r++) {
			lfsr ^= lfsr << 13;
			lfsr ^= lfsr >> 7;
			lfsr ^= lfsr << 17;
			vals.push_back(lfsr & full);
		}
		return vals;
	}

	// --- Forward dense pack: out = thermometer(popcount(in)). ---

	bool fingerprint_forward(const SigSpec &in_sig, const SigSpec &out_sig, int width)
	{
		if (width < 4 || width > 62)
			return false;
		ConstEval ce(module);
		SigSpec in_s = sigmap(in_sig);
		SigSpec out_s = sigmap(out_sig);

		for (uint64_t v : make_value_set(width)) {
			uint64_t actual;
			if (!eval_with(ce, {{in_s, const_u64(v, width)}}, out_s, actual))
				return false;
			uint64_t expected = lowmask_u64(__builtin_popcountll(v));
			if (actual != expected)
				return false;
		}
		return true;
	}

	// --- Reverse suffix read (MSB-first scan, cf. qor_spi_ra_sub_chain):
	//   indx = lw; for (I = lw; I > 0; I--)
	//     if (!disable[I-1]) { mask[I-1] = data[--indx]; } else mask[I-1] = 0;
	// Only the low `lw` bits of disable/data participate; high mask bits are 0.

	// `en_high` selects the disable-bus polarity: false means a set bit
	// disables the lane (the original form), true means a set bit enables it
	// (frontends often push the inversion into the muxes).
	uint64_t expected_reverse_mask(uint64_t dis, uint64_t data, int lw, bool en_high)
	{
		uint64_t mask = 0;
		int indx = lw;
		for (int I = lw; I > 0; I--) {
			int i = I - 1;
			bool enabled = (((dis >> i) & 1ULL) != 0) == en_high;
			if (enabled) {
				if ((data >> (indx - 1)) & 1ULL)
					mask |= 1ULL << i;
				indx--;
			}
		}
		return mask;
	}

	// The loop width is hidden state: probe with all lanes enabled and
	// data=all-ones, which yields mask = lowmask(loop_width). The
	// disable/data buses may be wider than the loop (e.g. 32-bit ports whose
	// loop only touches [15:0]) or exactly loop-sized (when the frontend
	// already narrowed pre-logic).
	bool derive_reverse_loop_width(const SigSpec &dis_s, const SigSpec &data_s,
	                               const SigSpec &out_s, int width, int &lw, bool &en_high)
	{
		int wd = GetSize(dis_s);
		int wt = GetSize(data_s);
		bool self = sigmap(dis_s) == sigmap(data_s);
		ConstEval ce(module);
		for (int pol = 0; pol < 2; pol++) {
			// A self-pair (data == disable bus) can only be probed with all
			// lanes enabled AND data all-ones, i.e. enable-high polarity.
			if (self && pol == 0)
				continue;
			uint64_t all_enabled = pol ? lowmask_u64(wd) : 0;
			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({dis_s, const_u64(all_enabled, wd)});
			if (!self)
				sets.push_back({data_s, const_u64(lowmask_u64(wt), wt)});
			uint64_t actual;
			if (!eval_with(ce, sets, out_s, actual))
				return false;
			int n = __builtin_popcountll(actual);
			if (n < 4 || n > width || n > wd || n > wt || actual != lowmask_u64(n))
				continue;
			if (n > max_width || n > 62)
				continue;
			lw = n;
			en_high = pol != 0;
			return true;
		}
		return false;
	}

	bool fingerprint_reverse(const SigSpec &dis_sig, const SigSpec &data_sig,
	                         const SigSpec &out_sig, int width, int lw, bool en_high)
	{
		int wd = GetSize(dis_sig);
		int wt = GetSize(data_sig);
		if (width < 4 || width > 62 || lw < 4 || lw > width)
			return false;
		if (lw > wd || lw > wt || wd > 62 || wt > 62)
			return false;
		ConstEval ce(module);
		SigSpec dis_s = sigmap(dis_sig);
		SigSpec data_s = sigmap(data_sig);
		SigSpec out_s = sigmap(out_sig);
		bool self = dis_s == data_s;

		vector<uint64_t> disvals = make_value_set(wd);
		uint64_t full = lowmask_u64(wt);
		vector<uint64_t> datavals;
		datavals.push_back(0);
		datavals.push_back(full);
		datavals.push_back(full & 0x5555555555555555ULL);
		datavals.push_back(full & 0xAAAAAAAAAAAAAAAAULL);
		uint64_t lfsr = 0xfedcba9876543210ULL;
		for (int r = 0; r < 6; r++) {
			lfsr ^= lfsr << 13;
			lfsr ^= lfsr >> 7;
			lfsr ^= lfsr << 17;
			datavals.push_back(lfsr & full);
		}

		for (uint64_t dv : disvals)
			for (uint64_t tv : datavals) {
				if (self)
					tv = dv;
				vector<std::pair<SigSpec, Const>> sets;
				sets.push_back({dis_s, const_u64(dv, wd)});
				if (!self)
					sets.push_back({data_s, const_u64(tv, wt)});
				uint64_t actual;
				if (!eval_with(ce, sets, out_s, actual))
					return false;
				if (actual != expected_reverse_mask(dv, tv, lw, en_high))
					return false;
				if (self)
					break; // data values collapse onto the disable values
			}
		return true;
	}

	// --- Modulo decimation: scanning the enable vector from one end, mark
	// every n-th enabled bit. Equivalent closed form:
	//   mask[I] = en[I] && n>0 && (inclusive_popcount(I) % n == 0)
	// where the popcount runs from the scan's leading end down to (incl.) I.

	// `offset` distinguishes "mark every n-th enabled bit" (offset 0, the
	// counter resets when it hits n-1) from "mark the first of each group of
	// n" (offset 1, the counter is checked against 0 before incrementing).
	uint64_t expected_modulo_mask(uint64_t en, uint64_t n, int width, bool msb_first, int offset)
	{
		if (n == 0)
			return 0;
		uint64_t mask = 0;
		for (int i = 0; i < width; i++) {
			if (!((en >> i) & 1ULL))
				continue;
			uint64_t v = 0;
			if (msb_first)
				for (int k = i; k < width; k++)
					v += (en >> k) & 1ULL;
			else
				for (int k = 0; k <= i; k++)
					v += (en >> k) & 1ULL;
			if ((v - offset) % n == 0)
				mask |= (1ULL << i);
		}
		return mask;
	}

	bool fingerprint_modulo(const SigSpec &en_sig, const SigSpec &n_sig,
	                        const SigSpec &mask_sig, int width, bool msb_first, int offset)
	{
		if (width <= 0 || width > 62)
			return false;
		// A 1-bit modulus degenerates the function to (n ? en : 0), which
		// also matches plain gating muxes; require a real counter range.
		if (GetSize(n_sig) < 2)
			return false;
		ConstEval ce(module);
		SigSpec en_s = sigmap(en_sig);
		SigSpec n_s = sigmap(n_sig);
		SigSpec mask_s = sigmap(mask_sig);
		int nw = GetSize(n_sig);

		vector<uint64_t> nvals;
		uint64_t nmax = (nw >= 64) ? ~0ULL : ((1ULL << nw) - 1);
		for (uint64_t v = 0; v <= (uint64_t)width + 1 && v <= nmax; v++)
			nvals.push_back(v);
		if (nmax > (uint64_t)width + 1)
			nvals.push_back(nmax);

		uint64_t full = lowmask_u64(width);
		vector<uint64_t> envals;
		envals.push_back(0);
		envals.push_back(full);
		envals.push_back(full & 0x5555555555555555ULL);
		envals.push_back(full & 0xAAAAAAAAAAAAAAAAULL);
		for (int i = 0; i < width; i++)
			envals.push_back(1ULL << i);
		uint64_t lfsr = 0x1234567089abcdefULL;
		for (int r = 0; r < 64; r++) {
			lfsr ^= lfsr << 13;
			lfsr ^= lfsr >> 7;
			lfsr ^= lfsr << 17;
			envals.push_back(lfsr & full);
		}

		for (uint64_t nv : nvals)
			for (uint64_t ev : envals) {
				uint64_t actual;
				if (!eval_with(ce, {{en_s, const_u64(ev, width)},
				                    {n_s, const_u64(nv, nw)}},
				               mask_s, actual))
					return false;
				if (actual != expected_modulo_mask(ev, nv, width, msb_first, offset))
					return false;
			}
		return true;
	}

	// --- Forward gather/compress: out[k] = data[i_k] where i_k is the
	// position of the (k+1)-th set bit of en; out bits beyond popcount(en)
	// are zero. The forward dense pack is the data==en special case.

	uint64_t expected_gather_mask(uint64_t en, uint64_t data, int width)
	{
		uint64_t out = 0;
		int indx = 0;
		for (int i = 0; i < width; i++)
			if ((en >> i) & 1ULL) {
				if ((data >> i) & 1ULL)
					out |= 1ULL << indx;
				indx++;
			}
		return out;
	}

	// The en/data buses may contain repeated bits (e.g. an enable vector
	// built by replicating a per-group mask bit across the group's lanes) or
	// share bits with each other. The fingerprint drives the distinct
	// underlying bits and expands each test value onto the bus patterns, so
	// the function is verified exactly on the reachable input subspace.
	bool fingerprint_gather(const SigSpec &en_sig, const SigSpec &data_sig,
	                        const SigSpec &out_sig, int width)
	{
		if (width < 4 || width > 62)
			return false;
		ConstEval ce(module);
		SigSpec en_s = sigmap(en_sig);
		SigSpec data_s = sigmap(data_sig);
		SigSpec out_s = sigmap(out_sig);

		dict<SigBit, int> unique_idx;
		SigSpec unique_sig;
		vector<int> en_map(width), data_map(width);
		for (int i = 0; i < width; i++) {
			auto it = unique_idx.find(en_s[i]);
			if (it == unique_idx.end()) {
				unique_idx[en_s[i]] = GetSize(unique_sig);
				unique_sig.append(en_s[i]);
			}
			en_map[i] = unique_idx.at(en_s[i]);
		}
		for (int i = 0; i < width; i++) {
			auto it = unique_idx.find(data_s[i]);
			if (it == unique_idx.end()) {
				unique_idx[data_s[i]] = GetSize(unique_sig);
				unique_sig.append(data_s[i]);
			}
			data_map[i] = unique_idx.at(data_s[i]);
		}
		int nu = GetSize(unique_sig);
		if (nu > 62)
			return false;

		auto expand = [&](uint64_t v, const vector<int> &map) {
			uint64_t r = 0;
			for (int i = 0; i < width; i++)
				if ((v >> map[i]) & 1ULL)
					r |= 1ULL << i;
			return r;
		};

		for (uint64_t v : make_value_set(nu)) {
			uint64_t actual;
			if (!eval_with(ce, {{unique_sig, const_u64(v, nu)}}, out_s, actual))
				return false;
			if (actual != expected_gather_mask(expand(v, en_map), expand(v, data_map), width))
				return false;
		}
		// A second value sweep decorrelates en from data when they share no
		// bits; with shared bits it simply adds more reachable patterns.
		uint64_t lfsr = 0x0f1e2d3c4b5a6978ULL;
		for (int r = 0; r < 48; r++) {
			lfsr ^= lfsr << 13;
			lfsr ^= lfsr >> 7;
			lfsr ^= lfsr << 17;
			uint64_t v = lfsr & lowmask_u64(nu);
			uint64_t actual;
			if (!eval_with(ce, {{unique_sig, const_u64(v, nu)}}, out_s, actual))
				return false;
			if (actual != expected_gather_mask(expand(v, en_map), expand(v, data_map), width))
				return false;
		}
		return true;
	}

	// --- Emission ---

	void apply_forward(const Rewrite &rw)
	{
		ref_cell = rw.anchor;
		int width = GetSize(rw.root);
		int count_width = ceil_log2_int(width + 1);
		SigSpec in_s = sigmap(rw.a);

		vector<SigSpec> bits;
		for (int i = 0; i < width; i++)
			bits.push_back(SigSpec(in_s[i]));

		SigSpec count = balanced_sum(bits, count_width);
		SigSpec packed;
		for (int i = 0; i < width; i++)
			packed.append(emit_gt(count, i, count_width));

		disconnect_root(rw.root, rw.anchor, "compact_dangling");
		module->connect(rw.root, packed);
		old_cells_removed += rw.cone_cells;

		log("  Forward dense pack: %s -> %s, width=%d, count_width=%d.\n",
		    rw.a_name.c_str(), rw.root_name.c_str(), width, count_width);
		forward_rewrites++;
	}

	void apply_reverse(const Rewrite &rw)
	{
		ref_cell = rw.anchor;
		int width = GetSize(rw.root);
		int loop_width = rw.loop_width;
		bool en_high = rw.msb_first; // polarity flag (see matching loop)
		int count_width = ceil_log2_int(loop_width + 1);
		SigSpec dis_s = sigmap(rw.a);
		SigSpec data_s = sigmap(rw.b);

		vector<SigBit> valid(loop_width);
		for (int i = 0; i < loop_width; i++)
			valid[i] = en_high ? dis_s[i] : emit_not(dis_s[i]);

		SigSpec out_bits;
		for (int j = 0; j < loop_width; j++) {
			vector<SigSpec> suffix_terms;
			for (int k = j + 1; k < loop_width; k++)
				suffix_terms.push_back(SigSpec(valid[k]));
			SigSpec suffix_count = balanced_sum(suffix_terms, count_width);

			SigSpec candidates;
			for (int k = 0; k < loop_width; k++) {
				int needed_count = loop_width - 1 - k;
				SigBit is_source = emit_eq(suffix_count, needed_count, count_width);
				SigBit gated_data = emit_and(data_s[k], is_source);
				candidates.append(gated_data);
			}

			SigBit selected = emit_reduce_or(candidates);
			out_bits.append(emit_and(valid[j], selected));
		}

		if (width > loop_width)
			out_bits.append(SigSpec(State::S0, width - loop_width));

		disconnect_root(rw.root, rw.anchor, "compact_dangling");
		module->connect(rw.root, out_bits);
		old_cells_removed += rw.cone_cells;

		log("  Reverse suffix read: %s/%s -> %s, loop_width=%d, count_width=%d.\n",
		    rw.a_name.c_str(), rw.b_name.c_str(), rw.root_name.c_str(),
		    loop_width, count_width);
		reverse_rewrites++;
	}

	void apply_modulo(const Rewrite &rw)
	{
		ref_cell = rw.anchor;
		int width = GetSize(rw.root);
		SigSpec en_s = sigmap(rw.a);
		SigSpec n_s = sigmap(rw.b);
		bool msb_first = rw.msb_first;

		int cnt_width = ceil_log2_int(width + 1);
		int table_size = 1 << cnt_width;
		int cmp_width = std::max(GetSize(n_s), cnt_width);

		// 1) Inclusive prefix popcount as a naive linear $add cascade. Each
		//    running sum is consumed below, so the downstream opt_parallel_prefix
		//    pass rebuilds the cascade into a shared log-depth prefix network.
		vector<SigSpec> popcount(width);
		Cell *cell = ref_cell;
		int start = msb_first ? width - 1 : 0;
		int step = msb_first ? -1 : 1;
		int last = msb_first ? 0 : width - 1;
		SigSpec acc = SigSpec(en_s[start]);
		popcount[start] = zext(acc, cnt_width);
		for (int i = start + step; i != last + step; i += step) {
			Wire *sum = module->addWire(NEW_ID2_SUFFIX("compact_pop"), cnt_width);
			module->addAdd(NEW_ID2_SUFFIX("compact_pop_add"), acc, SigSpec(en_s[i]), sum);
			new_cells_emitted++;
			acc = SigSpec(sum);
			popcount[i] = SigSpec(sum);
		}

		// 2) Decode the modulus once: eq_d = (n == d) for d in [1..width].
		vector<SigBit> eqd(width + 1, State::S0);
		for (int d = 1; d <= width; d++)
			eqd[d] = emit_eq(n_s, d, cmp_width);

		// 3) Divisibility per popcount value: div_k = OR_{d | k-offset} eq_d.
		//    n>0 and n>width fall out for free (no divisor in range matches),
		//    except k-offset == 0 which is divisible by any n > 0.
		vector<SigBit> divisible(table_size, State::S0);
		divisible[0] = State::S1; // gated away by en[]; defined to size the table
		for (int k = 1; k <= width; k++) {
			int target = k - rw.mod_offset;
			if (target == 0) {
				divisible[k] = emit_reduce_or(n_s);
				continue;
			}
			SigSpec terms;
			for (int d = 1; d <= target; d++)
				if (target % d == 0)
					terms.append(SigSpec(eqd[d]));
			divisible[k] = emit_reduce_or(terms);
		}

		// 4) Shared divisibility table; select per bit by its popcount value.
		SigSpec table;
		for (int k = 0; k < table_size; k++)
			table.append(SigSpec(divisible[k]));

		SigSpec out_bits;
		for (int i = 0; i < width; i++) {
			SigBit sel_divisible = emit_bmux(table, popcount[i]);
			out_bits.append(emit_and(en_s[i], sel_divisible));
		}

		disconnect_root(rw.root, rw.anchor, "compact_dangling");
		module->connect(rw.root, out_bits);
		old_cells_removed += rw.cone_cells;

		log("  Modulo decimation: en=%s, n=%s -> %s, width=%d, %s scan, offset=%d.\n",
		    rw.a_name.c_str(), rw.b_name.c_str(), rw.root_name.c_str(), width,
		    msb_first ? "MSB-first" : "LSB-first", rw.mod_offset);
		modulo_rewrites++;
	}

	void apply_gather(const Rewrite &rw)
	{
		ref_cell = rw.anchor;
		int width = GetSize(rw.root);
		int cnt_width = ceil_log2_int(width + 1);
		SigSpec en_s = sigmap(rw.a);
		SigSpec data_s = sigmap(rw.b);

		// Exclusive prefix popcount as a naive linear $add cascade (rebuilt
		// into a shared log-depth prefix network by opt_parallel_prefix).
		vector<SigSpec> prefix(width);
		Cell *cell = ref_cell;
		prefix[0] = SigSpec(Const(0, cnt_width));
		SigSpec acc = prefix[0];
		for (int i = 1; i < width; i++) {
			Wire *sum = module->addWire(NEW_ID2_SUFFIX("compact_pre"), cnt_width);
			module->addAdd(NEW_ID2_SUFFIX("compact_pre_add"), acc, SigSpec(en_s[i - 1]), sum);
			new_cells_emitted++;
			acc = SigSpec(sum);
			prefix[i] = acc;
		}

		SigSpec out_bits;
		for (int k = 0; k < width; k++) {
			SigSpec candidates;
			for (int i = k; i < width; i++) {
				SigBit is_source = emit_eq(prefix[i], k, cnt_width);
				SigBit gated = emit_and(emit_and(en_s[i], data_s[i]), is_source);
				candidates.append(gated);
			}
			out_bits.append(emit_reduce_or(candidates));
		}

		disconnect_root(rw.root, rw.anchor, "compact_dangling");
		module->connect(rw.root, out_bits);
		old_cells_removed += rw.cone_cells;

		log("  Forward gather: en=%s, data=%s -> %s, width=%d, count_width=%d.\n",
		    rw.a_name.c_str(), rw.b_name.c_str(), rw.root_name.c_str(), width, cnt_width);
		forward_rewrites++;
	}

	// --- Candidate enumeration ---

	// Candidate root signals: module output ports and FF data inputs are
	// seeds; internal signals inside seed cones are added so that regions
	// wrapped in extra combinational post-logic are still found.
	vector<RootCand> collect_roots()
	{
		int min_w = 4;
		int max_w = std::min(max_width, 62);
		return collect_root_candidates(
			[&](int w) { return w >= min_w && w <= max_w; },
			[&](const pool<Cell *> &) { return true; },
			true, std::max(256, max_width * 96), max_width * (max_width + 8));
	}

	void run()
	{
		if (module->has_processes_warn())
			return;

		// All three forms come from unrolled loops with conditional updates;
		// modules without muxes can be skipped cheaply.
		bool has_mux = false;
		for (auto c : module->cells())
			if (c->type.in(ID($mux), ID($pmux)))
				has_mux = true;
		if (!has_mux)
			return;

		vector<BusCand> port_buses;
		for (auto w : module->wires())
			if (w->port_input)
				port_buses.push_back({sigmap(SigSpec(w)), w->name.str()});

		vector<Rewrite> rewrites;
		pool<SigBit> claimed_bits;
		vector<RootCand> root_list = collect_roots();
		for (int ri = 0; ri < GetSize(root_list); ri++) {
			auto &root = root_list[ri];
			if (walk_exhausted() || eval_exhausted()) {
				note_budget("opt_compact_prefix", GetSize(root_list) - ri);
				break;
			}
			if (root_claimed(root.sig))
				continue;

			int width = GetSize(root.sig);
			if (width < 4 || width > max_width || width > 62)
				continue;

			pool<Cell *> cone_cells;
			pool<SigBit> leaf_bits;
			vector<Cell *> order;
			int max_cone_cells = std::max(256, max_width * 96);
			int max_leaf_bits = max_width * (max_width + 8);
			if (!get_cone(root.sig, cone_cells, leaf_bits, max_cone_cells, max_leaf_bits, &order))
				continue;
			if (cone_cells.empty())
				continue;
			cur_cone_est = GetSize(cone_cells);

			Rewrite rw;
			rw.root = root.sig;
			rw.root_name = root.name;
			rw.cone_cells = GetSize(cone_cells);
			if (!find_anchor_driver(root.sig, rw.anchor))
				continue;

			// Bus candidates: module input ports first, then internal cut
			// signals from the root cone ordered shallowest-first (depth
			// measured from the leaves), since the cut points introduced by
			// pre-logic sit right above the module inputs.
			vector<BusCand> buses = port_buses;
			const int max_internal_buses = 32;
			int internal_buses = 0;
			pool<SigSpec> seen_buses;
			for (auto &bus : port_buses)
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
					if (GetSize(sig) < 2 || !seen_buses.insert(sig).second)
						continue;
					if (!sig_bus_ok(sig))
						continue;
					buses.push_back({sig, stringf("%s.%s", log_id(c->name), log_id(conn.first))});
					internal_buses++;
				}
			}

			// Whole wires touching the cone (FF-driven masks etc.), longest
			// runs first, plus per-lane split wires grouped into buses
			// (regions written bit-by-bit only expose their buses as named
			// wires).
			pool<SigBit> cone_sig_bits = cone_sig_bit_pool(cone_cells, leaf_bits);
			for (auto &run : collect_wire_run_buses(cone_sig_bits, 64)) {
				if (!seen_buses.insert(run.sig).second)
					continue;
				buses.push_back({run.sig, run.name});
			}
			for (auto &bus : collect_cone_split_buses(cone_sig_bits)) {
				SigSpec sig = sigmap(bus.sig);
				if (seen_buses.insert(sig).second)
					buses.push_back({sig, bus.name});
			}

			// Width-targeted windows of slightly wider buses (the loop may
			// cover only part of a vector, e.g. actv[15:0] of a [W:0] bus).
			{
				vector<BusCand> windows;
				for (auto &bus : buses) {
					int sz = GetSize(bus.sig);
					if (sz <= width || sz - width > 4)
						continue;
					for (int off = 0; off + width <= sz; off++) {
						SigSpec slice = bus.sig.extract(off, width);
						if (!seen_buses.insert(slice).second)
							continue;
						windows.push_back({slice, stringf("%s[%d+:%d]", bus.name.c_str(), off, width)});
					}
				}
				for (auto &wnd : windows)
					buses.push_back(wnd);
			}

			// Lane-ordered buses recovered from the per-root-bit cones.
			lane_ordered_buses(root.sig, cone_cells, buses, seen_buses);

			// Buses overlapping the root would let the fingerprint force the
			// output it is checking; drop them up front.
			pool<SigBit> root_bits;
			for (auto bit : root.sig)
				if (bit.wire)
					root_bits.insert(bit);
			{
				vector<BusCand> filtered;
				for (auto &bus : buses) {
					bool overlap = false;
					for (auto bit : bus.sig)
						if (root_bits.count(bit)) {
							overlap = true;
							break;
						}
					if (!overlap)
						filtered.push_back(bus);
				}
				buses.swap(filtered);
			}

			// Closure walks are cheap graph traversals; ConstEval fingerprints
			// are the expensive step and get their own (smaller) budget.
			const int max_closure_attempts = 768;
			const int max_fp_attempts = 24;
			int closure_attempts = 0;
			int fp_attempts = 0;
			bool matched = false;
			pool<Cell *> matched_cone;

			log_debug("root %s (w=%d): cone %d cells, %d buses\n",
			          root.name.c_str(), width, GetSize(cone_cells), GetSize(buses));

			// 1) Forward dense pack: single input bus of the same width.
			for (auto &bus : buses) {
				if (closure_attempts >= max_closure_attempts || fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
					break;
				if (GetSize(bus.sig) != width)
					continue;
				pool<SigBit> allowed;
				if (!sig_bits_unique(bus.sig, allowed))
					continue;
				closure_attempts++;
				if (!cut_cone_walk(root.sig, allowed, GetSize(cone_cells) + 16, nullptr, &matched_cone,
					                   nullptr, &leaf_bits, &cone_cells)) {
					log_debug("  fwd %s: cut not closed\n", bus.name.c_str());
					continue;
				}
				fp_attempts++;
				if (!fingerprint_forward(bus.sig, root.sig, width)) {
					log_debug("  fwd %s: fingerprint mismatch\n", bus.name.c_str());
					continue;
				}
				rw.kind = 0;
				rw.a = bus.sig;
				rw.a_name = bus.name;
				matched = true;
				break;
			}

			// 1b) Forward gather/compress: en/data buses of the same width
			//     (the data==en special case is the forward pack above).
			//     Repeated or shared bits between the buses are allowed: the
			//     fingerprint drives the distinct underlying bits and checks
			//     the function on the reachable input subspace.
			if (!matched) {
				closure_attempts = 0;
				fp_attempts = 0;
				for (auto &en : buses) {
					if (matched || closure_attempts >= max_closure_attempts ||
					    fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
						break;
					if (GetSize(en.sig) != width)
						continue;
					for (auto &data : buses) {
						if (closure_attempts >= max_closure_attempts ||
						    fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
							break;
						if (GetSize(data.sig) != width || data.sig == en.sig)
							continue;
						bool en_const = false;
						bool data_const = false;
						pool<SigBit> allowed;
						for (auto bit : sigmap(en.sig)) {
							if (!bit.wire)
								en_const = true;
							else
								allowed.insert(bit);
						}
						if (en_const)
							break;
						for (auto bit : sigmap(data.sig)) {
							if (!bit.wire)
								data_const = true;
							else
								allowed.insert(bit);
						}
						if (data_const)
							continue;
						closure_attempts++;
						if (!cut_cone_walk(root.sig, allowed, GetSize(cone_cells) + 16, nullptr, &matched_cone,
					                   nullptr, &leaf_bits, &cone_cells)) {
							log_debug("  gat %s/%s: cut not closed\n", en.name.c_str(), data.name.c_str());
							continue;
						}
						// A real serial gather burns at least a mux and a
						// counter increment per lane; small cones are
						// degenerate matches (e.g. write-enable muxes) where
						// the rewrite would only add area.
						if (GetSize(matched_cone) < 2 * width) {
							log_debug("  gat %s/%s: cone too small (%d cells)\n",
							          en.name.c_str(), data.name.c_str(), GetSize(matched_cone));
							continue;
						}
						fp_attempts++;
						if (!fingerprint_gather(en.sig, data.sig, root.sig, width)) {
							log_debug("  gat %s/%s: fingerprint mismatch\n", en.name.c_str(), data.name.c_str());
							continue;
						}
						rw.kind = 3;
						rw.a = en.sig;
						rw.a_name = en.name;
						rw.b = data.sig;
						rw.b_name = data.name;
						matched = true;
						break;
					}
				}
			}

			// 1c) Forward gather with an implicit enable: the enable side of
			//     the gather may be arbitrary wiring (replication of a group
			//     mask, etc.) that exists neither as a wire nor as a cell
			//     connection. Once a data bus is known, the enable wiring is
			//     learned by probing and verified by the same fingerprint.
			if (!matched) {
				closure_attempts = 0;
				fp_attempts = 0;
				for (auto &data : buses) {
					if (matched || closure_attempts >= max_closure_attempts ||
					    fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
						break;
					if (GetSize(data.sig) != width)
						continue;
					// The probe drives one-hot patterns onto the data bus, so
					// its bits must be unique (the learned enable side is
					// what handles replicated wiring).
					bool data_const = false;
					pool<SigBit> data_bits;
					for (auto bit : sigmap(data.sig)) {
						if (!bit.wire)
							data_const = true;
						else
							data_bits.insert(bit);
					}
					if (data_const || GetSize(data_bits) != width)
						continue;

					closure_attempts++;
					pool<SigBit> en_cands;
					if (!cut_cone_extra_leaves(root.sig, data_bits, GetSize(cone_cells) + 16, en_cands, 24))
						continue;
					if (en_cands.empty())
						continue;

					// The closure check also guards against forced bits whose
					// drivers sit inside the cone (ConstEval conflicts), so it
					// must pass before any probing evaluates the cut.
					pool<SigBit> allowed = data_bits;
					for (auto bit : en_cands)
						allowed.insert(bit);
					if (!cut_cone_walk(root.sig, allowed, GetSize(cone_cells) + 16, nullptr, &matched_cone,
					                   nullptr, &leaf_bits, &cone_cells)) {
						log_debug("  gat <learned>/%s: cut not closed (%s)\n", data.name.c_str(),
						          last_cut_fail.c_str());
						continue;
					}
					// See the substantiality guard in the explicit gather
					// loop above: tiny cones are degenerate matches.
					if (GetSize(matched_cone) < 2 * width) {
						log_debug("  gat <learned>/%s: cone too small (%d cells)\n",
						          data.name.c_str(), GetSize(matched_cone));
						continue;
					}

					fp_attempts++;
					SigSpec en_bus;
					if (!learn_gather_enable(root.sig, data.sig, en_cands, en_bus)) {
						log_debug("  gat <learned>/%s: enable probe failed\n", data.name.c_str());
						continue;
					}
					if (!fingerprint_gather(en_bus, data.sig, root.sig, width)) {
						log_debug("  gat <learned>/%s: fingerprint mismatch\n", data.name.c_str());
						continue;
					}
					rw.kind = 3;
					rw.a = en_bus;
					rw.a_name = "<learned-enable>";
					rw.b = data.sig;
					rw.b_name = data.name;
					matched = true;
					break;
				}
			}

			// 2) Reverse suffix read: disable/data buses (the loop may cover
			//    only the low bits of wider buses, so widths are independent).
			if (!matched) {
				closure_attempts = 0;
				fp_attempts = 0;
				for (auto &dis : buses) {
					if (matched || closure_attempts >= max_closure_attempts ||
					    fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
						break;
					if (GetSize(dis.sig) < 4 || GetSize(dis.sig) > 62)
						continue;
					for (auto &data : buses) {
						if (closure_attempts >= max_closure_attempts ||
						    fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
							break;
						if (GetSize(data.sig) < 4 || GetSize(data.sig) > 62)
							continue;
						bool self = data.sig == dis.sig;
						pool<SigBit> allowed;
						if (!sig_bits_unique(dis.sig, allowed))
							break;
						if (!self && !sig_bits_unique(data.sig, allowed))
							continue;
						closure_attempts++;
						if (!cut_cone_walk(root.sig, allowed, GetSize(cone_cells) + 16, nullptr, &matched_cone,
					                   nullptr, &leaf_bits, &cone_cells)) {
							log_debug("  rev %s/%s: cut not closed (%s)\n", dis.name.c_str(), data.name.c_str(),
							          last_cut_fail.c_str());
							continue;
						}
						fp_attempts++;
						int lw = 0;
						bool en_high = false;
						if (!derive_reverse_loop_width(dis.sig, data.sig, root.sig, width, lw, en_high)) {
							log_debug("  rev %s/%s: loop width probe failed\n", dis.name.c_str(), data.name.c_str());
							continue;
						}
						if (!fingerprint_reverse(dis.sig, data.sig, root.sig, width, lw, en_high)) {
							log_debug("  rev %s/%s: fingerprint mismatch (lw=%d)\n", dis.name.c_str(), data.name.c_str(), lw);
							continue;
						}
						rw.kind = 1;
						rw.a = dis.sig;
						rw.a_name = dis.name;
						rw.b = data.sig;
						rw.b_name = data.name;
						rw.loop_width = lw;
						rw.msb_first = en_high; // reused as the polarity flag for reverse
						matched = true;
						break;
					}
				}
			}

			// 3) Modulo decimation: en bus of the same width plus a narrower
			//    modulus bus (the width mismatch also disambiguates from the
			//    reverse suffix read form).
			if (!matched) {
				closure_attempts = 0;
				fp_attempts = 0;
				for (auto &en : buses) {
					if (matched || closure_attempts >= max_closure_attempts ||
					    fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
						break;
					if (GetSize(en.sig) != width)
						continue;
					for (auto &n : buses) {
						if (closure_attempts >= max_closure_attempts ||
						    fp_attempts >= max_fp_attempts || walk_exhausted() || eval_exhausted())
							break;
						if (GetSize(n.sig) == width || GetSize(n.sig) > 62)
							continue;
						pool<SigBit> allowed;
						if (!sig_bits_unique(en.sig, allowed))
							break;
						if (!sig_bits_unique(n.sig, allowed))
							continue;
						closure_attempts++;
						if (!cut_cone_walk(root.sig, allowed, GetSize(cone_cells) + 16, nullptr, &matched_cone,
					                   nullptr, &leaf_bits, &cone_cells)) {
							log_debug("  mod %s/%s: cut not closed\n", en.name.c_str(), n.name.c_str());
							continue;
						}
						fp_attempts++;
						bool msb_first = false;
						int offset = -1;
						if (fingerprint_modulo(en.sig, n.sig, root.sig, width, true, 0)) {
							msb_first = true;
							offset = 0;
						} else if (fingerprint_modulo(en.sig, n.sig, root.sig, width, false, 0)) {
							msb_first = false;
							offset = 0;
						} else if (fingerprint_modulo(en.sig, n.sig, root.sig, width, false, 1)) {
							msb_first = false;
							offset = 1;
						} else if (fingerprint_modulo(en.sig, n.sig, root.sig, width, true, 1)) {
							msb_first = true;
							offset = 1;
						} else {
							log_debug("  mod %s/%s: fingerprint mismatch\n", en.name.c_str(), n.name.c_str());
							continue;
						}
						rw.kind = 2;
						rw.a = en.sig;
						rw.a_name = en.name;
						rw.b = n.sig;
						rw.b_name = n.name;
						rw.msb_first = msb_first;
						rw.mod_offset = offset;
						matched = true;
						break;
					}
				}
			}

			if (matched) {
				rw.cone_cells = GetSize(matched_cone);
				rewrites.push_back(rw);
				claim_region(root.sig, matched_cone);
			}
		}

		for (auto &rw : rewrites) {
			if (rw.kind == 0)
				apply_forward(rw);
			else if (rw.kind == 1)
				apply_reverse(rw);
			else if (rw.kind == 2)
				apply_modulo(rw);
			else
				apply_gather(rw);
		}
	}
};

struct OptCompactPrefixPass : public Pass
{
	OptCompactPrefixPass() : Pass("opt_compact_prefix",
		"rewrite monotonic compaction loops into balanced prefix/routing logic") {}

	void help() override
	{
		log("\n");
		log("    opt_compact_prefix [options] [selection]\n");
		log("\n");
		log("Recognize narrow monotonic compaction patterns produced by frontend\n");
		log("lowering of SystemVerilog loops and replace their long loop-carried\n");
		log("index/update cones with balanced prefix-count and routing logic.\n");
		log("\n");
		log("Currently this pass handles the dense bit-pack, reverse suffix-read,\n");
		log("and modulo-n decimation forms used by the qor_spi_ra_add_chain,\n");
		log("qor_spi_ra_sub_chain, and qor_spi_ra_add_chain2 regressions.\n");
		log("Non-matching modules are left unchanged.\n");
		log("\n");
		log("Matching is performed by functionally fingerprinting (ConstEval)\n");
		log("candidate regions between cut signals. Cut points include module\n");
		log("ports, FF data inputs, and internal signals, so the rewrites still\n");
		log("apply when extra combinational logic surrounds the compaction loop.\n");
		log("\n");
		log("The modulo decimation form (mark every n-th enabled bit while scanning\n");
		log("the enable vector) is lowered to a prefix-popcount plus divisor-decode\n");
		log("divisibility check. The popcount is emitted as a plain linear $add\n");
		log("cascade so a subsequent opt_parallel_prefix pass can rebuild it into a\n");
		log("shared log-depth network.\n");
		log("\n");
		log("    -max_width <n>\n");
		log("        Maximum compaction width to rewrite. Default: 64.\n");
		log("\n");
		log("    -walk-budget N, -eval-budget N, -attempt-budget N\n");
		log("        per-module work limits for the candidate search (defaults\n");
		log("        20000000 / 20000000 / 65536). When a budget is exhausted\n");
		log("        the remaining candidates are skipped and a note is logged.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_COMPACT_PREFIX pass (monotonic compaction rewrites).\n");

		int max_width = 64;
		int64_t walk_budget = -1, eval_budget = -1, attempt_budget = -1;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_width" && argidx + 1 < args.size()) {
				max_width = atoi(args[++argidx].c_str());
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

		int total_forward = 0;
		int total_reverse = 0;
		int total_modulo = 0;
		int total_removed = 0;
		int total_emitted = 0;

		for (auto module : design->selected_modules()) {
			OptCompactPrefixWorker worker(module, max_width);
			if (walk_budget > 0)
				worker.walk_budget = walk_budget;
			if (eval_budget > 0)
				worker.eval_budget = eval_budget;
			if (attempt_budget > 0)
				worker.attempt_budget = attempt_budget;
			worker.run();
			total_forward += worker.forward_rewrites;
			total_reverse += worker.reverse_rewrites;
			total_modulo += worker.modulo_rewrites;
			total_removed += worker.old_cells_removed;
			total_emitted += worker.new_cells_emitted;
		}

		log("Rewrote %d forward pack(s), %d reverse suffix read(s), %d modulo decimation(s); "
		    "removed %d old cell(s), emitted %d new cell(s).\n",
		    total_forward, total_reverse, total_modulo, total_removed, total_emitted);

		if (total_forward || total_reverse || total_modulo)
			Yosys::run_pass("clean -purge");
	}
} OptCompactPrefixPass;

PRIVATE_NAMESPACE_END
