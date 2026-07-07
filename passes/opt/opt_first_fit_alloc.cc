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
#include <cctype>
#include <map>
#include <queue>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static int clog2_int(int x)
{
	int r = 0;
	while ((1 << r) < x)
		r++;
	return r;
}

// Pack a per-lane integer vector into a Const with elem_w bits per lane,
// lane-major (lane k occupies bits [k*elem_w +: elem_w]).
static Const pack_lanes(const vector<int> &vals, int elem_w)
{
	// Lane values come from the small field widths above (<= max_attr_w), so a
	// 32-bit int always holds them. Assert rather than silently truncating, and
	// keep b < 32 so we never shift an int by >= its width (undefined behaviour).
	log_assert(elem_w < 32);
	vector<State> bits(vals.size() * elem_w, State::S0);
	for (int k = 0; k < GetSize(vals); k++)
		for (int b = 0; b < elem_w; b++)
			if ((vals[k] >> b) & 1)
				bits[k * elem_w + b] = State::S1;
	return Const(bits);
}

#include "passes/opt/cut_region.h"

struct OptFirstFitAllocWorker : CutRegionWorker {
	int min_n = 4;
	int max_n = 64;
	int max_field_w = 6;   // max index (dsel) element width
	int max_cat_w = 6;     // max category width c
	int max_attr_w = 8;    // max per-lane attr width for the xbar field gather

	int regions_rewritten = 0;
	int cells_added = 0;

	OptFirstFitAllocWorker(Module *module) : CutRegionWorker(module) {}

	// ----------------------------------------------------------------
	// Reference closed-form semantics of the greedy first-fit allocator.
	//
	// Lanes are processed in priority order (LSB-first here; the caller
	// reverses for MSB-first). A "leader" is the first enabled lane of each
	// category that is reached before its category's slot is taken; broadcast
	// (bc) lanes after the first leader are suppressed. Leaders take slots
	// 0,1,2,... in order; the per-lane rank (dsel) is the slot of the leader
	// matching that lane's category, except broadcast lanes which snap to the
	// last leader's slot. This is SAT-proven equivalent to the unrolled RTL
	// allocation loop (taken[]/done[] scan).
	// ----------------------------------------------------------------
	struct AllocResult {
		vector<int> dsel;     // per-lane rank
		vector<char> leader;  // 1 iff lane is a slot leader
		vector<int> slot;     // exclusive prefix count of leaders
		int M = 0;            // number of leaders
	};

	AllocResult compute_alloc(const vector<int> &en, const vector<int> &bc,
	                          const vector<int> &cat, int n) const
	{
		AllocResult r;
		r.dsel.assign(n, 0);
		r.leader.assign(n, 0);
		r.slot.assign(n, 0);

		vector<char> any_en_before(n, 0);
		int acc = 0;
		for (int i = 0; i < n; i++) {
			any_en_before[i] = acc ? 1 : 0;
			acc |= en[i];
		}
		int e0 = -1;
		for (int i = 0; i < n; i++)
			if (en[i] && !any_en_before[i]) { e0 = i; break; }
		int cat_e0 = (e0 >= 0) ? cat[e0] : 0;

		for (int i = 0; i < n; i++) {
			bool is_e0 = (i == e0);
			bool blocked_mid = false;
			for (int j = 0; j < i; j++)
				if (any_en_before[j] && en[j] && !bc[j] && cat[j] == cat[i]) {
					blocked_mid = true;
					break;
				}
			bool eq_e0 = (cat[i] == cat_e0);
			r.leader[i] = en[i] && (is_e0 || (!bc[i] && !eq_e0 && !blocked_mid));
		}

		int cnt = 0;
		for (int i = 0; i < n; i++) {
			r.slot[i] = cnt;
			if (r.leader[i])
				cnt++;
		}
		r.M = cnt;

		for (int k = 0; k < n; k++) {
			if (bc[k]) {
				r.dsel[k] = (r.M >= 1) ? (r.M - 1) : 0;
			} else if (en[k]) {
				for (int i = 0; i < n; i++)
					if (r.leader[i] && cat[i] == cat[k]) {
						r.dsel[k] = r.slot[i];
						break;
					}
			}
		}
		return r;
	}

	// Direction-aware wrapper: reverse inputs for MSB-first scans.
	AllocResult compute_alloc_dir(const vector<int> &en, const vector<int> &bc,
	                              const vector<int> &cat, int n, bool msb_first) const
	{
		if (!msb_first)
			return compute_alloc(en, bc, cat, n);
		vector<int> er(n), br(n), cr(n);
		for (int i = 0; i < n; i++) {
			er[i] = en[n - 1 - i];
			br[i] = bc[n - 1 - i];
			cr[i] = cat[n - 1 - i];
		}
		AllocResult rr = compute_alloc(er, br, cr, n);
		AllocResult r;
		r.dsel.assign(n, 0);
		r.leader.assign(n, 0);
		r.slot.assign(n, 0);
		r.M = rr.M;
		for (int i = 0; i < n; i++) {
			r.dsel[i] = rr.dsel[n - 1 - i];
			r.leader[i] = rr.leader[n - 1 - i];
			r.slot[i] = rr.slot[n - 1 - i];
		}
		return r;
	}

	// ----------------------------------------------------------------
	// Reference semantics of the "coalesce matrix" allocator variant.
	//
	// Leadership and slot assignment are identical to the greedy first-fit
	// above, but the per-lane rank does NOT depend on the lane's own enable:
	// every lane k (enabled or not) inherits the slot of the first leader at
	// or before k (in priority order) whose category matches cat[k]. This
	// models RTL that precomputes a per-leader "same_cat[i][k]" mask (gated
	// only on the leader's enable) and forward-coalesces into lane k without
	// re-checking en[k]. There is no broadcast lane in this variant.
	// ----------------------------------------------------------------
	AllocResult compute_alloc_coalesce(const vector<int> &en, const vector<int> &cat,
	                                   int n) const
	{
		AllocResult r = compute_alloc(en, vector<int>(n, 0), cat, n);
		for (int k = 0; k < n; k++) {
			r.dsel[k] = 0;
			for (int i = 0; i <= k; i++)
				if (r.leader[i] && cat[i] == cat[k]) {
					r.dsel[k] = r.slot[i];
					break;
				}
		}
		return r;
	}

	AllocResult compute_alloc_coalesce_dir(const vector<int> &en, const vector<int> &cat,
	                                       int n, bool msb_first) const
	{
		if (!msb_first)
			return compute_alloc_coalesce(en, cat, n);
		vector<int> er(n), cr(n);
		for (int i = 0; i < n; i++) {
			er[i] = en[n - 1 - i];
			cr[i] = cat[n - 1 - i];
		}
		AllocResult rr = compute_alloc_coalesce(er, cr, n);
		AllocResult r;
		r.dsel.assign(n, 0);
		r.leader.assign(n, 0);
		r.slot.assign(n, 0);
		r.M = rr.M;
		for (int i = 0; i < n; i++) {
			r.dsel[i] = rr.dsel[n - 1 - i];
			r.leader[i] = rr.leader[n - 1 - i];
			r.slot[i] = rr.slot[n - 1 - i];
		}
		return r;
	}

	// ----------------------------------------------------------------
	// Test vectors. `nval` is the number of distinct label values (2^c for
	// the category, 2^a for the xbar attribute). The vectors deliberately
	// include the all-distinct/all-enabled case so that an allocator whose
	// slot count is smaller than the number of distinct categories (i.e. one
	// that can overflow and diverge from the closed form) is rejected.
	// ----------------------------------------------------------------
	struct TestVector {
		vector<int> en;
		vector<int> bc;
		vector<int> label;
	};

	vector<TestVector> make_vectors(int n, int nval, bool with_bc) const
	{
		vector<TestVector> vs;
		auto lab = [&](int mul, int add) {
			vector<int> f(n);
			for (int k = 0; k < n; k++)
				f[k] = ((k * mul + add) % nval + nval) % nval;
			return f;
		};

		// All disabled.
		{ TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0); t.label = lab(1, 0); vs.push_back(t); }

		// Single enabled lane (each lane), no bc.
		for (int k = 0; k < n; k++) {
			TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
			t.en[k] = 1; t.label = lab(1, 0); vs.push_back(t);
		}

		// All enabled, all same category.
		{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.label.assign(n, 0); vs.push_back(t); }
		// All enabled, all distinct categories (overflow boundary).
		{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.label = lab(1, 0); vs.push_back(t); }
		{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.label = lab(3, 1); vs.push_back(t); }
		{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.label = lab(-1, nval - 1); vs.push_back(t); }

		// Prefix enable masks en[k..n-1].
		for (int k = 0; k < n; k++) {
			TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
			for (int j = k; j < n; j++) t.en[j] = 1;
			t.label = lab(5, 2); vs.push_back(t);
		}
		// Suffix enable masks en[0..k].
		for (int k = 0; k < n; k++) {
			TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
			for (int j = 0; j <= k; j++) t.en[j] = 1;
			t.label = lab(7, 3); vs.push_back(t);
		}

		// Pairs with distinct categories.
		for (int i = 0; i < n; i++)
			for (int j = i + 1; j < n && j < i + 3; j++) {
				TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
				t.en[i] = 1; t.en[j] = 1; t.label = lab(2, 0);
				t.label[i] = (i + 1) % nval; t.label[j] = (j + 5) % nval;
				vs.push_back(t);
			}

		// Broadcast corners.
		if (with_bc) {
			// One bc lane among several enabled lanes.
			for (int b = 0; b < n; b += std::max(1, n / 6)) {
				TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0);
				t.bc[b] = 1; t.label = lab(3, 0); vs.push_back(t);
			}
			// Leading bc lane (bc lane is E0).
			{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 0); t.bc[0] = 1; t.label = lab(1, 0); vs.push_back(t); }
			// bc lane not enabled.
			{ TestVector t; t.en.assign(n, 0); t.bc.assign(n, 0);
			  for (int j = 0; j < n; j += 2) t.en[j] = 1;
			  t.bc[1] = 1; t.bc[3 % n] = 1; t.label = lab(2, 1); vs.push_back(t); }
			// All bc, all enabled.
			{ TestVector t; t.en.assign(n, 1); t.bc.assign(n, 1); t.label = lab(1, 0); vs.push_back(t); }
		}

		// Pseudo-random coverage.
		uint64_t lfsr = 0x1234567089abcdefULL;
		for (int r = 0; r < 40; r++) {
			lfsr ^= lfsr << 13;
			lfsr ^= lfsr >> 7;
			lfsr ^= lfsr << 17;
			TestVector t; t.en.resize(n); t.bc.resize(n); t.label.resize(n);
			uint64_t f = lfsr * 2654435761ULL;
			// bc draws from an independently mixed word so en[k] and bc[j] never
			// share an LFSR bit (a shifted view of `lfsr` would alias them, e.g.
			// en[7] and bc[0] for n=8), keeping the random coverage independent.
			uint64_t g = lfsr * 0x9E3779B97F4A7C15ULL;
			for (int k = 0; k < n; k++) {
				t.en[k] = (lfsr >> (k % 64)) & 1;
				t.bc[k] = with_bc ? ((g >> (k % 64)) & 1) : 0;
				t.label[k] = (int)((f >> ((k * 3) % 60)) % (uint64_t)nval);
			}
			vs.push_back(t);
		}
		return vs;
	}

	// ----------------------------------------------------------------
	// Evaluate `out_sig` under input assignments, returning the full Const.
	// ----------------------------------------------------------------
	bool eval_root(ConstEval &ce, const vector<std::pair<SigSpec, Const>> &sets,
	               const SigSpec &out_sig, Const &result, int64_t cone_est)
	{
		charge_eval(cone_est);
		ce.push();
		for (auto &s : sets)
			ce.set(s.first, s.second);
		SigSpec out = out_sig;
		SigSpec undef;
		bool ok = ce.eval(out, undef);
		if (ok && out.is_fully_const())
			result = out.as_const();
		else
			ok = false;
		ce.pop();
		return ok;
	}

	static int lane_val(const Const &c, int lane, int elem_w)
	{
		int v = 0;
		for (int b = 0; b < elem_w; b++) {
			int p = lane * elem_w + b;
			if (p < GetSize(c) && c[p] == State::S1)
				v |= 1 << b;
		}
		return v;
	}

	// ----------------------------------------------------------------
	// Group a set of cone-leaf bits into per-lane fields of equal width,
	// using each bit's wire/offset and the wire's lane stride (width / n).
	// Returns a lane-major SigSpec (lane k -> bits [k*c +: c]) and the per-
	// lane width c, plus, for each cat key, the (wire,offset) identity so a
	// caller can locate the cat sub-field inside a wider attr field.
	// ----------------------------------------------------------------
	// A per-lane sub-field is identified by (source id, within-lane offset),
	// where the source is either a flat lane-strided bus (id = wire name) or
	// a group of per-lane indexed wires "base[i]" (id = base name). This lets
	// a category span several differently-laid-out buses (e.g. a flat set_q[]
	// plus per-lane bank_q[i][1:0] wires).
	struct FieldKey {
		std::string id;
		int offset;
		bool operator<(const FieldKey &o) const {
			if (id != o.id)
				return id < o.id;
			return offset < o.offset;
		}
		bool operator==(const FieldKey &o) const {
			return id == o.id && offset == o.offset;
		}
	};

	// Resolve a single cone-leaf bit to the lane it belongs to. Returns the
	// source `id` (flat bus wire name, or base name for per-lane "base[i]"
	// wires), the `lane` index in [0,n), and the bit's `offset` within that
	// lane's sub-field. Returns false if the bit has no wire or cannot be
	// assigned to one of the n lanes.
	bool lane_of_bit(SigBit bit, int n, std::string &id, int &lane, int &offset)
	{
		if (!bit.wire)
			return false;
		Wire *w = bit.wire;
		std::string base;
		int idx = -1;
		if (parse_indexed_port_name(w, base, idx)) {
			id = base;
			lane = idx;
			offset = bit.offset;
		} else {
			int width = GetSize(w);
			if (width % n != 0)
				return false;
			int stride = width / n;
			id = w->name.str();
			lane = bit.offset / stride;
			offset = bit.offset % stride;
		}
		return lane >= 0 && lane < n;
	}

	bool group_lane_field(const pool<SigBit> &bits, int n, SigSpec &field,
	                      int &c, vector<FieldKey> *keys_out = nullptr)
	{
		if (bits.empty() || n <= 0)
			return false;
		// Per-lane indexed wires may start at a non-zero base index; normalize
		// each source's lane numbering to start at its minimum.
		dict<std::string, int> src_min_lane;
		vector<std::tuple<std::string, int, int, SigBit>> recs; // id, lane, off, bit
		for (auto bit : bits) {
			std::string id;
			int lane, off;
			if (!lane_of_bit(bit, n, id, lane, off))
				return false;
			if (!src_min_lane.count(id) || lane < src_min_lane[id])
				src_min_lane[id] = lane;
			recs.push_back({id, lane, off, bit});
		}
		vector<std::map<FieldKey, SigBit>> per_lane(n);
		for (auto &r : recs) {
			std::string id = std::get<0>(r);
			int lane = std::get<1>(r) - src_min_lane[id];
			int off = std::get<2>(r);
			if (lane < 0 || lane >= n)
				return false;
			if (!per_lane[lane].emplace(FieldKey{id, off}, std::get<3>(r)).second)
				return false;
		}
		std::set<FieldKey> keys;
		for (auto &kv : per_lane[0])
			keys.insert(kv.first);
		if (keys.empty())
			return false;
		for (int k = 0; k < n; k++) {
			if (GetSize(per_lane[k]) != GetSize(keys))
				return false;
			for (auto &kv : per_lane[k])
				if (!keys.count(kv.first))
					return false;
		}
		c = GetSize(keys);
		field = SigSpec();
		vector<FieldKey> ordered(keys.begin(), keys.end());
		for (int k = 0; k < n; k++)
			for (auto &key : ordered)
				field.append(per_lane[k].at(key));
		if (keys_out != nullptr)
			*keys_out = ordered;
		return true;
	}

	// ----------------------------------------------------------------
	// A matched region: the shared (en,bc,cat) scan plus the dsel root.
	// ----------------------------------------------------------------
	struct Region {
		// dsel
		SigSpec dsel_sig;
		std::string dsel_name;
		int n = 0;
		int field_w = 0;
		SigSpec en_sig, bc_sig, cat_sig;
		bool has_bc = false;
		// Enable-independent forward coalescing: lanes inherit the slot of the
		// first same-category leader at or before them in priority order,
		// regardless of their own enable (the "same_cat matrix" RTL shape).
		bool coalesce = false;
		int c = 0;
		bool msb_first = false;
		Cell *anchor = nullptr;
		pool<Cell *> dsel_cut_cells;
		vector<FieldKey> cat_keys;
	};

	// ---- small emit helpers ----
	SigBit emit_not(Cell *anchor, SigBit a)
	{
		Cell *cell = anchor;
		SigBit o = module->Not(NEW_ID2_SUFFIX("ffa_not"), SigSpec(a))[0];
		cells_added++;
		return o;
	}
	SigBit emit_and(Cell *anchor, SigBit a, SigBit b)
	{
		Cell *cell = anchor;
		SigBit o = module->And(NEW_ID2_SUFFIX("ffa_and"), SigSpec(a), SigSpec(b))[0];
		cells_added++;
		return o;
	}
	SigBit emit_or(Cell *anchor, SigBit a, SigBit b)
	{
		Cell *cell = anchor;
		SigBit o = module->Or(NEW_ID2_SUFFIX("ffa_or"), SigSpec(a), SigSpec(b))[0];
		cells_added++;
		return o;
	}
	SigBit emit_reduce_or(Cell *anchor, SigSpec bits)
	{
		bits = sigmap(bits);
		if (GetSize(bits) == 0)
			return State::S0;
		if (GetSize(bits) == 1)
			return bits[0];
		Cell *cell = anchor;
		SigBit o = module->ReduceOr(NEW_ID2_SUFFIX("ffa_ror"), bits)[0];
		cells_added++;
		return o;
	}
	SigBit emit_eq_sig(Cell *anchor, SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		SigBit o = module->Eq(NEW_ID2_SUFFIX("ffa_eq"), a, b)[0];
		cells_added++;
		return o;
	}
	SigBit emit_eq_const(Cell *anchor, SigSpec a, int value, int width)
	{
		return emit_eq_sig(anchor, zext_sig(a, width), Const(value, width));
	}
	SigSpec emit_mux(Cell *anchor, SigSpec a, SigSpec b, SigBit s)
	{
		Cell *cell = anchor;
		SigSpec o = module->Mux(NEW_ID2_SUFFIX("ffa_mux"), a, b, SigSpec(s));
		cells_added++;
		return o;
	}
	SigSpec emit_bmux(Cell *anchor, SigSpec table, SigSpec sel, int width)
	{
		Cell *cell = anchor;
		Wire *o = module->addWire(NEW_ID2_SUFFIX("ffa_bmux"), width);
		module->addBmux(NEW_ID2_SUFFIX("ffa_bmux_cell"), table, sel, o);
		cells_added++;
		return SigSpec(o);
	}

	// Exclusive prefix-sum of `bits` as a linear $add cascade. Each running
	// sum is consumed downstream, so opt_parallel_prefix -arith later rebuilds
	// the cascade into a shared log-depth network. Returns slot[i] and the
	// total M (inclusive sum).
	void emit_prefix_count(Cell *anchor, const vector<SigBit> &bits, int cnt_w,
	                       vector<SigSpec> &slot, SigSpec &total)
	{
		Cell *cell = anchor;
		int n = GetSize(bits);
		slot.assign(n, SigSpec());
		SigSpec acc = Const(0, cnt_w);
		for (int i = 0; i < n; i++) {
			slot[i] = acc;
			Wire *sum = module->addWire(NEW_ID2_SUFFIX("ffa_pre"), cnt_w);
			module->addAdd(NEW_ID2_SUFFIX("ffa_pre_add"), acc, SigSpec(bits[i]), sum);
			cells_added++;
			acc = SigSpec(sum);
		}
		total = acc;
	}

	// Emit the shared leader/slot scan from (en,bc,cat). Fills leader[],
	// slot[] (cnt_w bits), total M, and the lane categories cat_lane[].
	void emit_scan(const Region &rg, vector<SigBit> &leader, vector<SigSpec> &slot,
	               SigSpec &total, int cnt_w, vector<SigSpec> &cat_lane)
	{
		Cell *anchor = rg.anchor;
		int n = rg.n, c = rg.c;
		SigSpec en = sigmap(rg.en_sig);
		SigSpec bc = rg.has_bc ? sigmap(rg.bc_sig) : SigSpec();
		SigSpec cat = sigmap(rg.cat_sig);

		// priority order: index p -> lane
		auto lane_of = [&](int p) { return rg.msb_first ? (n - 1 - p) : p; };

		vector<SigBit> en_p(n), bc_p(n);
		cat_lane.assign(n, SigSpec());
		for (int p = 0; p < n; p++) {
			int l = lane_of(p);
			en_p[p] = en[l];
			bc_p[p] = rg.has_bc ? bc[l] : SigBit(State::S0);
			cat_lane[p] = cat.extract(l * c, c);
		}

		// anyEnBefore[p] = OR_{q<p} en_p[q]
		vector<SigBit> any_before(n);
		for (int p = 0; p < n; p++) {
			SigSpec prev;
			for (int q = 0; q < p; q++)
				prev.append(en_p[q]);
			any_before[p] = emit_reduce_or(anchor, prev);
		}
		// isE0[p] = en_p[p] & ~anyEnBefore[p]
		vector<SigBit> is_e0(n);
		for (int p = 0; p < n; p++)
			is_e0[p] = emit_and(anchor, en_p[p], emit_not(anchor, any_before[p]));
		// catE0[b] = OR_p (isE0[p] & cat[p][b])
		SigSpec cat_e0;
		for (int b = 0; b < c; b++) {
			SigSpec terms;
			for (int p = 0; p < n; p++)
				terms.append(emit_and(anchor, is_e0[p], cat_lane[p][b]));
			cat_e0.append(emit_reduce_or(anchor, terms));
		}
		// eqE0[p] = (cat[p]==catE0)
		vector<SigBit> eq_e0(n);
		for (int p = 0; p < n; p++)
			eq_e0[p] = emit_eq_sig(anchor, cat_lane[p], cat_e0);

		// qual[p] = anyEnBefore[p] & en_p[p] & ~bc_p[p]
		vector<SigBit> qual(n);
		for (int p = 0; p < n; p++) {
			SigBit t = emit_and(anchor, any_before[p], en_p[p]);
			qual[p] = emit_and(anchor, t, emit_not(anchor, bc_p[p]));
		}
		// catEq[p][q] = (cat[p]==cat[q]) (only q<p needed for blockedMid)
		// blockedMid[p] = OR_{q<p} qual[q] & catEq[p][q]
		vector<SigBit> blocked_mid(n);
		for (int p = 0; p < n; p++) {
			SigSpec terms;
			for (int q = 0; q < p; q++) {
				SigBit eq = emit_eq_sig(anchor, cat_lane[p], cat_lane[q]);
				terms.append(emit_and(anchor, qual[q], eq));
			}
			blocked_mid[p] = emit_reduce_or(anchor, terms);
		}
		// leader[p] = en_p[p] & (isE0[p] | (~bc_p[p] & ~eqE0[p] & ~blockedMid[p]))
		vector<SigBit> leader_p(n);
		for (int p = 0; p < n; p++) {
			SigBit a = emit_and(anchor, emit_not(anchor, bc_p[p]), emit_not(anchor, eq_e0[p]));
			a = emit_and(anchor, a, emit_not(anchor, blocked_mid[p]));
			SigBit b = emit_or(anchor, is_e0[p], a);
			leader_p[p] = emit_and(anchor, en_p[p], b);
		}
		// slot[p] = exclusive prefix count
		vector<SigSpec> slot_p;
		emit_prefix_count(anchor, leader_p, cnt_w, slot_p, total);

		// map priority order back to lanes
		leader.assign(n, SigBit());
		slot.assign(n, SigSpec());
		for (int p = 0; p < n; p++) {
			int l = lane_of(p);
			leader[l] = leader_p[p];
			slot[l] = slot_p[p];
		}
	}

	// dsel gather. Returns lane-major SigSpec (lane k -> [k*field_w +: field_w]).
	SigSpec emit_dsel(const Region &rg, const vector<SigBit> &leader,
	                  const vector<SigSpec> &slot, SigSpec total, int cnt_w)
	{
		Cell *anchor = rg.anchor;
		int n = rg.n, c = rg.c, w = rg.field_w;
		SigSpec cat = sigmap(rg.cat_sig);

		// Enable-independent forward coalescing: lane k inherits the slot of the
		// unique same-category leader at or before k in priority order, with no
		// enable/broadcast gating. The priority position of a lane is a compile-
		// time constant, so the "leader at or before k" restriction is static.
		if (rg.coalesce) {
			auto pos = [&](int l) { return rg.msb_first ? (n - 1 - l) : l; };
			SigSpec out;
			for (int k = 0; k < n; k++) {
				SigSpec cat_k = cat.extract(k * c, c);
				vector<SigBit> g(n, SigBit(State::S0));
				for (int i = 0; i < n; i++) {
					if (pos(i) > pos(k))
						continue;
					SigBit eq = emit_eq_sig(anchor, cat.extract(i * c, c), cat_k);
					g[i] = emit_and(anchor, leader[i], eq);
				}
				SigSpec rank(Const(0, cnt_w));
				for (int b = 0; b < cnt_w; b++) {
					SigSpec terms;
					for (int i = 0; i < n; i++)
						if (pos(i) <= pos(k))
							terms.append(emit_and(anchor, g[i], slot[i][b]));
					rank[b] = emit_reduce_or(anchor, terms);
				}
				out.append(zext_sig(rank, w));
			}
			return out;
		}

		SigSpec en = sigmap(rg.en_sig);
		SigSpec bc = rg.has_bc ? sigmap(rg.bc_sig) : SigSpec();

		// bc rank: (M>=1) ? M-1 : 0
		SigBit any_leader = emit_reduce_or(anchor, total);
		Cell *cell = anchor;
		Wire *mm1w = module->addWire(NEW_ID2_SUFFIX("ffa_Mm1"), cnt_w);
		module->addSub(NEW_ID2_SUFFIX("ffa_Mm1_sub"), total, Const(1, cnt_w), mm1w);
		cells_added++;
		SigSpec bc_rank = emit_mux(anchor, Const(0, cnt_w), SigSpec(mm1w), any_leader);

		SigSpec out;
		for (int k = 0; k < n; k++) {
			SigSpec cat_k = cat.extract(k * c, c);
			// en rank: slot of the unique leader with cat==cat[k]
			vector<SigBit> g(n);
			for (int i = 0; i < n; i++) {
				SigBit eq = emit_eq_sig(anchor, cat.extract(i * c, c), cat_k);
				g[i] = emit_and(anchor, leader[i], eq);
			}
			SigSpec en_rank(Const(0, cnt_w));
			for (int b = 0; b < cnt_w; b++) {
				SigSpec terms;
				for (int i = 0; i < n; i++)
					terms.append(emit_and(anchor, g[i], slot[i][b]));
				en_rank[b] = emit_reduce_or(anchor, terms);
			}
			// dsel[k] = bc[k] ? bc_rank : (en[k] ? en_rank : 0)
			SigSpec sel_en = emit_mux(anchor, Const(0, cnt_w), en_rank, en[k]);
			SigSpec val = sel_en;
			if (rg.has_bc)
				val = emit_mux(anchor, sel_en, bc_rank, bc[k]);
			out.append(zext_sig(val, w));
		}
		return out;
	}

	// ----------------------------------------------------------------
	// xbar (per-slot field gather): xbar_slot[s] = (s<M) ? f(attr[leader at
	// slot s]) : 0, where f is learned by ConstEval (single-leader probe).
	// ----------------------------------------------------------------
	struct XbarCand {
		SigSpec sig;
		std::string name;
		int nb = 0;       // number of slots
		int slot_w = 0;   // bits per slot block
		SigSpec attr_sig; // lane-major attr
		int a = 0;        // attr width per lane
		vector<Const> ftab; // 2^a entries, slot_w bits each
		vector<FieldKey> attr_keys;
		Cell *anchor = nullptr;
		pool<Cell *> cut_cells;
	};

	SigSpec emit_xbar(const Region &rg, const XbarCand &xb, const vector<SigBit> &leader,
	                  const vector<SigSpec> &slot, int cnt_w)
	{
		Cell *anchor = rg.anchor;
		int n = rg.n, a = xb.a;
		SigSpec attr = sigmap(xb.attr_sig);

		// Build the function table as a flat Const for bmux.
		SigSpec table;
		for (int v = 0; v < (1 << a); v++)
			table.append(xb.ftab[v]);

		SigSpec out;
		for (int s = 0; s < xb.nb; s++) {
			// pick[i] = leader[i] && slot[i]==s
			vector<SigBit> pick(n);
			SigSpec valid_terms;
			for (int i = 0; i < n; i++) {
				SigBit eqs = emit_eq_const(anchor, slot[i], s, cnt_w);
				pick[i] = emit_and(anchor, leader[i], eqs);
				valid_terms.append(pick[i]);
			}
			// attrGather[s] = attr of the leader at slot s (one-hot select)
			SigSpec attr_gather(Const(0, a));
			for (int b = 0; b < a; b++) {
				SigSpec terms;
				for (int i = 0; i < n; i++)
					terms.append(emit_and(anchor, pick[i], attr[i * a + b]));
				attr_gather[b] = emit_reduce_or(anchor, terms);
			}
			SigBit valid = emit_reduce_or(anchor, valid_terms);
			SigSpec block = emit_bmux(anchor, table, attr_gather, xb.slot_w);
			SigSpec gated = emit_mux(anchor, Const(0, xb.slot_w), block, valid);
			out.append(gated);
		}
		return out;
	}

	// ----------------------------------------------------------------
	// Candidate bus collection for a root cone.
	// ----------------------------------------------------------------
	// Candidate enable/broadcast buses: width-N buses whose every bit is an
	// internal (cone-cell-output) signal. The enable/broadcast lanes are
	// computed signals (e.g. valid & format), not the leaf categories, so
	// restricting to internal bits sidesteps the flood of wide intermediate
	// nets that otherwise swamps a generic wire-run sweep.
	void collect_lane_buses(const pool<Cell *> &cone_cells, int n,
	                        vector<BusCand> &width_n_buses)
	{
		pool<SigBit> internal_bits;
		for (auto c : cone_cells)
			for (auto &conn : c->connections())
				if (c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							internal_bits.insert(bit);

		pool<SigSpec> seen;
		// Accept a bus bit if it is a cone-internal (computed) signal or a
		// primary input / undriven bit. The enable/broadcast lanes are usually
		// computed signals (e.g. valid & format), but some RTL drives the scan
		// straight from a top-level request port (e.g. lane_en), so input buses
		// must be admissible too. Inputs sort shallowest (depth 0) below, so they
		// survive the candidate cap ahead of the deep intermediate nets.
		auto all_internal_or_input = [&](const SigSpec &s) {
			for (auto bit : s)
				if (!bit.wire || (!internal_bits.count(bit) &&
				                  bit_to_driver.at(bit, nullptr) != nullptr))
					return false;
			return true;
		};
		auto add = [&](const SigSpec &sig, const std::string &nm) {
			SigSpec s = sigmap(sig);
			if (GetSize(s) != n || !sig_bus_ok(s) || !all_internal_or_input(s))
				return;
			if (!seen.insert(s).second)
				return;
			width_n_buses.push_back({s, nm, 0, 0});
		};

		for (auto w : module->wires())
			if (GetSize(w) == n)
				add(SigSpec(w), w->name.str());
		for (auto &bus : collect_cone_split_buses(internal_bits))
			if (bus.elem_width == 1 && bus.entries == n)
				add(bus.sig, bus.name);

		// Region inputs (enable/broadcast) sit just above the leaves; order
		// candidates shallowest-first so the deep intermediate nets of the
		// allocation network are only reached if the budget allows.
		dict<Cell *, int> depth = compute_cone_depths(cone_cells);
		auto bus_depth = [&](const SigSpec &s) {
			int d = 0;
			for (auto bit : s) {
				Cell *drv = bit_to_driver.at(bit, nullptr);
				if (drv != nullptr)
					d = std::max(d, depth.at(drv, 1 << 30));
			}
			return d;
		};
		std::stable_sort(width_n_buses.begin(), width_n_buses.end(),
		                 [&](const BusCand &a, const BusCand &b) {
		                     return bus_depth(a.sig) < bus_depth(b.sig);
		                 });
		const int max_en_bc = 24;
		if (GetSize(width_n_buses) > max_en_bc)
			width_n_buses.resize(max_en_bc);

		log_debug("    collect_lane_buses: %d width-%d internal bus(es) (capped)\n",
		          GetSize(width_n_buses), n);
		for (auto &b : width_n_buses)
			log_debug("      en/bc cand %s (depth %d)\n", b.name.c_str(), bus_depth(b.sig));
	}

	// ----------------------------------------------------------------
	// Try to match a dsel region rooted at `root_sig` (n lanes x field_w).
	// ----------------------------------------------------------------
	bool match_dsel(const SigSpec &root_sig, const std::string &root_name, int n, int field_w,
	                Region &out)
	{
		pool<Cell *> cone_cells;
		pool<SigBit> leaf_bits;
		int max_cone = std::max(512, max_n * 256);
		int max_leaf = max_n * max_n + max_n * 64 + max_n;
		if (!get_cone(root_sig, cone_cells, leaf_bits, max_cone, max_leaf))
			return false;
		if (cone_cells.empty())
			return false;

		log_debug("ffa: match_dsel root %s (n=%d, w=%d): cone %d cells, %d leaves\n",
		          root_name.c_str(), n, field_w, GetSize(cone_cells), GetSize(leaf_bits));

		vector<BusCand> lane_buses;
		collect_lane_buses(cone_cells, n, lane_buses);
		log_debug("  %d width-%d lane bus candidate(s)\n", GetSize(lane_buses), n);
		for (auto &b : lane_buses)
			log_debug("    lane bus %s\n", b.name.c_str());
		if (GetSize(lane_buses) < 1)
			return false;

		ConstEval ce(module);
		int64_t cone_est = GetSize(cone_cells) + 16;
		const int max_fp = 48;
		int fp = 0;

		for (auto &en_bus : lane_buses) {
			if (fp >= max_fp || walk_exhausted() || eval_exhausted())
				break;
			pool<SigBit> en_bits = sig_bit_pool(en_bus.sig);

			// bc options: none, or each other 1-bit/lane bus.
			vector<const BusCand *> bc_opts;
			bc_opts.push_back(nullptr);
			for (auto &b : lane_buses)
				if (b.sig != en_bus.sig)
					bc_opts.push_back(&b);

			for (auto bc_bus : bc_opts) {
				if (fp >= max_fp || walk_exhausted() || eval_exhausted())
					break;

				pool<SigBit> allowed_eb = en_bits;
				if (bc_bus)
					for (auto bit : sig_bit_pool(bc_bus->sig))
						allowed_eb.insert(bit);

				// Find the category leaves: cut at (en,bc), gather extras.
				pool<SigBit> extra;
				if (!cut_cone_extra_leaves(root_sig, allowed_eb, GetSize(cone_cells) + 32,
				                           extra, n * max_cat_w + 8)) {
					log_debug("  en=%s bc=%s: too many extra leaves\n", en_bus.name.c_str(),
					          bc_bus ? bc_bus->name.c_str() : "-");
					continue;
				}
				if (extra.empty())
					continue;

				SigSpec cat_sig;
				int c = 0;
				vector<FieldKey> cat_keys;
				if (!group_lane_field(extra, n, cat_sig, c, &cat_keys)) {
					log_debug("  en=%s bc=%s: cat grouping failed (%d extra leaves)\n",
					          en_bus.name.c_str(), bc_bus ? bc_bus->name.c_str() : "-", GetSize(extra));
					continue;
				}
				if (c < 1 || c > max_cat_w)
					continue;
				if ((1 << c) > (1 << field_w))  // need ranks to fit the field
					continue;
				log_debug("  en=%s bc=%s: cat=%dx%d candidate\n", en_bus.name.c_str(),
				          bc_bus ? bc_bus->name.c_str() : "-", n, c);

				// Confirm the cut closes at exactly (en,bc,cat).
				pool<SigBit> allowed = allowed_eb;
				for (auto bit : sig_bit_pool(cat_sig))
					allowed.insert(bit);
				pool<SigBit> hit;
				pool<Cell *> cut_cells;
				if (!cut_cone_walk(root_sig, allowed, GetSize(cone_cells) + 32, &hit, &cut_cells,
				                   &allowed, &leaf_bits, &cone_cells)) {
					log_debug("  en=%s bc=%s cat=%dx%d: cut not closed (%s)\n", en_bus.name.c_str(),
					          bc_bus ? bc_bus->name.c_str() : "-", n, c, last_cut_fail.c_str());
					continue;
				}

				// Forced inputs must not be driven inside the cut cone.
				bool forced_conflict = false;
				for (auto bit : allowed) {
					Cell *drv = bit_to_driver.at(bit, nullptr);
					if (drv != nullptr && cut_cells.count(drv)) {
						forced_conflict = true;
						break;
					}
				}
				if (forced_conflict)
					continue;

				// Fingerprint both scan directions.
				for (int dir = 0; dir < 2; dir++) {
					if (fp >= max_fp || eval_exhausted())
						break;
					bool msb_first = (dir == 1);
					fp++;
					bool fpm = fingerprint_dsel(ce, root_sig, n, field_w, en_bus.sig,
					                     bc_bus ? bc_bus->sig : SigSpec(), bc_bus != nullptr,
					                     cat_sig, c, msb_first, cone_est);
					// Standard first-fit failed: try the enable-independent
					// forward-coalescing variant (no broadcast lane).
					bool coalesce = false;
					if (!fpm && bc_bus == nullptr) {
						fpm = fingerprint_dsel(ce, root_sig, n, field_w, en_bus.sig,
						                       SigSpec(), false, cat_sig, c, msb_first,
						                       cone_est, /*coalesce=*/true);
						coalesce = fpm;
					}
					log_debug("  en=%s bc=%s cat=%dx%d %s: fingerprint %s%s\n", en_bus.name.c_str(),
					          bc_bus ? bc_bus->name.c_str() : "-", n, c,
					          msb_first ? "MSB" : "LSB", fpm ? "MATCH" : "no",
					          coalesce ? " (coalesce)" : "");
					if (fpm) {
						out.dsel_sig = root_sig;
						out.dsel_name = root_name;
						out.n = n;
						out.field_w = field_w;
						out.en_sig = en_bus.sig;
						out.bc_sig = (!coalesce && bc_bus) ? bc_bus->sig : SigSpec();
						out.has_bc = (!coalesce && bc_bus != nullptr);
						out.coalesce = coalesce;
						out.cat_sig = cat_sig;
						out.c = c;
						out.msb_first = msb_first;
						out.cat_keys = cat_keys;
						out.dsel_cut_cells = cut_cells;
						find_anchor_driver(root_sig, out.anchor);
						return true;
					}
				}
			}
		}
		return false;
	}

	// Functional fingerprint of a candidate dsel region: drive (en,bc,cat) with
	// each generated test vector, ConstEval the root, and compare every lane's
	// evaluated rank against the closed-form first-fit reference
	// (compute_alloc_dir). Returns true iff all lanes match on every vector,
	// i.e. the region implements the first-fit dsel for the given direction.
	// Any eval failure or single mismatch rejects the candidate.
	bool fingerprint_dsel(ConstEval &ce, const SigSpec &root, int n, int field_w,
	                      const SigSpec &en_sig, const SigSpec &bc_sig, bool has_bc,
	                      const SigSpec &cat_sig, int c, bool msb_first, int64_t cone_est,
	                      bool coalesce = false)
	{
		int nval = 1 << c;
		vector<TestVector> vs = make_vectors(n, nval, has_bc);
		SigSpec en_s = sigmap(en_sig);
		SigSpec bc_s = has_bc ? sigmap(bc_sig) : SigSpec();
		SigSpec cat_s = sigmap(cat_sig);

		for (auto &tv : vs) {
			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({en_s, pack_lanes(tv.en, 1)});
			if (has_bc)
				sets.push_back({bc_s, pack_lanes(tv.bc, 1)});
			sets.push_back({cat_s, pack_lanes(tv.label, c)});

			Const res;
			if (!eval_root(ce, sets, root, res, cone_est))
				return false;

			AllocResult ar = coalesce
			                     ? compute_alloc_coalesce_dir(tv.en, tv.label, n, msb_first)
			                     : compute_alloc_dir(tv.en, tv.bc, tv.label, n, msb_first);
			for (int k = 0; k < n; k++) {
				int got = lane_val(res, k, field_w);
				int exp = ar.dsel[k] & ((1 << field_w) - 1);
				if (got != exp)
					return false;
			}
		}
		return true;
	}

	// ----------------------------------------------------------------
	// Try to match the xbar per-slot field gather sharing the region scan.
	// ----------------------------------------------------------------
	bool match_xbar(const Region &rg, const BusCand &cand, XbarCand &out)
	{
		int total_bits = GetSize(cand.sig);
		int field_w = rg.field_w;
		int nb = 1 << field_w;          // slot count = 2^W
		if (nb < 2 || total_bits % nb != 0)
			return false;
		int slot_w = total_bits / nb;
		if (slot_w < 1 || slot_w > 64) {
			log_debug("  xbar %s: slot_w=%d out of range\n", cand.name.c_str(), slot_w);
			return false;
		}

		SigSpec root = sigmap(cand.sig);
		pool<Cell *> cone_cells;
		pool<SigBit> leaf_bits;
		int max_cone = std::max(512, max_n * 256);
		int max_leaf = max_n * max_n + max_n * 64 + max_n;
		if (!get_cone(root, cone_cells, leaf_bits, max_cone, max_leaf))
			return false;
		if (cone_cells.empty())
			return false;

		// Cut at (en,bc); the remaining leaves are the per-lane attr field.
		pool<SigBit> allowed_eb = sig_bit_pool(rg.en_sig);
		if (rg.has_bc)
			for (auto bit : sig_bit_pool(rg.bc_sig))
				allowed_eb.insert(bit);
		pool<SigBit> extra;
		if (!cut_cone_extra_leaves(root, allowed_eb, GetSize(cone_cells) + 32,
		                           extra, rg.n * max_attr_w + 8)) {
			log_debug("  xbar %s: too many extra leaves on (en,bc) cut\n", cand.name.c_str());
			return false;
		}
		if (extra.empty())
			return false;

		SigSpec attr_sig;
		int a = 0;
		vector<FieldKey> attr_keys;
		if (!group_lane_field(extra, rg.n, attr_sig, a, &attr_keys)) {
			log_debug("  xbar %s: attr grouping failed (%d extra leaves)\n",
			          cand.name.c_str(), GetSize(extra));
			return false;
		}
		if (a < rg.c || a > max_attr_w) {
			log_debug("  xbar %s: attr width %d out of range [%d,%d]\n",
			          cand.name.c_str(), a, rg.c, max_attr_w);
			return false;
		}
		log_debug("  xbar %s: nb=%d slot_w=%d attr=%dx%d\n", cand.name.c_str(), nb, slot_w, rg.n, a);

		// Confirm closure at (en,bc,attr).
		pool<SigBit> allowed = allowed_eb;
		for (auto bit : sig_bit_pool(attr_sig))
			allowed.insert(bit);
		pool<SigBit> hit;
		pool<Cell *> cut_cells;
		if (!cut_cone_walk(root, allowed, GetSize(cone_cells) + 32, &hit, &cut_cells,
		                   &allowed, &leaf_bits, &cone_cells)) {
			log_debug("  xbar %s: cut not closed (%s)\n", cand.name.c_str(), last_cut_fail.c_str());
			return false;
		}
		for (auto bit : allowed) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr && cut_cells.count(drv)) {
				log_debug("  xbar %s: forced bit driven inside cone\n", cand.name.c_str());
				return false;
			}
		}

		// The attr field must be a superset of the category field (so the
		// scan's leadership and the xbar gather see consistent lanes).
		// (cat keys identify wire/offset; verify each is present in attr.)
		// We do not strictly require this for correctness (the fingerprint
		// is authoritative), but it weeds out unrelated buses cheaply.

		ConstEval ce(module);
		int64_t cone_est = GetSize(cone_cells) + 16;

		// Learn f(v): force lane 0 (priority E0) the sole leader with attr=v.
		int e0_lane = rg.msb_first ? (rg.n - 1) : 0;
		vector<Const> ftab(1 << a);
		SigSpec en_s = sigmap(rg.en_sig);
		SigSpec bc_s = rg.has_bc ? sigmap(rg.bc_sig) : SigSpec();
		SigSpec attr_s = sigmap(attr_sig);
		SigSpec slot0 = root.extract(0, slot_w);
		for (int v = 0; v < (1 << a); v++) {
			vector<int> en(rg.n, 0), bc(rg.n, 0), attr(rg.n, 0);
			en[e0_lane] = 1;
			attr[e0_lane] = v;
			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({en_s, pack_lanes(en, 1)});
			if (rg.has_bc)
				sets.push_back({bc_s, pack_lanes(bc, 1)});
			sets.push_back({attr_s, pack_lanes(attr, a)});
			Const res;
			if (!eval_root(ce, sets, slot0, res, cone_est)) {
				log_debug("  xbar %s: ftab learn failed at v=%d\n", cand.name.c_str(), v);
				return false;
			}
			ftab[v] = res;
		}

		// Fingerprint the full xbar against the gather+table reference.
		int nval = 1 << a;
		vector<TestVector> vs = make_vectors(rg.n, nval, rg.has_bc);
		for (auto &tv : vs) {
			vector<std::pair<SigSpec, Const>> sets;
			sets.push_back({en_s, pack_lanes(tv.en, 1)});
			if (rg.has_bc)
				sets.push_back({bc_s, pack_lanes(tv.bc, 1)});
			sets.push_back({attr_s, pack_lanes(tv.label, a)});
			Const res;
			if (!eval_root(ce, sets, root, res, cone_est)) {
				log_debug("  xbar %s: eval failed during fingerprint\n", cand.name.c_str());
				return false;
			}

			// Derive cat labels from the attr labels via the cat keys' bit
			// positions inside attr.
			vector<int> catlab(rg.n);
			for (int k = 0; k < rg.n; k++)
				catlab[k] = cat_from_attr(tv.label[k], rg.cat_keys, attr_keys);
			AllocResult ar = compute_alloc_dir(tv.en, tv.bc, catlab, rg.n, rg.msb_first);

			// Expected per-slot block.
			for (int s = 0; s < nb; s++) {
				int leader_lane = -1;
				for (int i = 0; i < rg.n; i++)
					if (ar.leader[i] && ar.slot[i] == s) { leader_lane = i; break; }
				for (int b = 0; b < slot_w; b++) {
					bool got = (s * slot_w + b < GetSize(res)) && res[s * slot_w + b] == State::S1;
					bool exp;
					if (leader_lane < 0)
						exp = false;
					else {
						const Const &fv = ftab[tv.label[leader_lane]];
						exp = (b < GetSize(fv)) && fv[b] == State::S1;
					}
					if (got != exp) {
						log_debug("  xbar %s: fingerprint mismatch slot %d bit %d\n",
						          cand.name.c_str(), s, b);
						return false;
					}
				}
			}
		}
		log_debug("  xbar %s: MATCH\n", cand.name.c_str());

		out.sig = root;
		out.name = cand.name;
		out.nb = nb;
		out.slot_w = slot_w;
		out.attr_sig = attr_sig;
		out.a = a;
		out.ftab = ftab;
		out.attr_keys = attr_keys;
		out.cut_cells = cut_cells;
		find_anchor_driver(root, out.anchor);
		return true;
	}

	// Map an attr label value to its category label value, using the shared
	// (id,offset) keys: cat bit cb corresponds to the attr bit whose key
	// matches cat_keys[cb].
	int cat_from_attr(int attr_val, const vector<FieldKey> &cat_keys,
	                  const vector<FieldKey> &attr_keys)
	{
		int catval = 0;
		for (int cb = 0; cb < GetSize(cat_keys); cb++)
			for (int b = 0; b < GetSize(attr_keys); b++)
				if (attr_keys[b] == cat_keys[cb]) {
					if ((attr_val >> b) & 1)
						catval |= 1 << cb;
					break;
				}
		return catval;
	}

	// Drive `new_val` onto the cell-driven bits of `root` (bit-aligned),
	// leaving folded-constant / undriven bits untouched (they already hold
	// the correct value and are not on the deep path). Returns the number of
	// bits actually re-driven.
	int connect_driven(const SigSpec &root, const SigSpec &new_val, Cell *anchor,
	                   const char *suffix)
	{
		log_assert(GetSize(root) == GetSize(new_val));
		SigSpec lhs, rhs;
		for (int i = 0; i < GetSize(root); i++) {
			SigBit rb = sigmap(root[i]);
			if (rb.wire && bit_to_driver.at(rb, nullptr) != nullptr) {
				lhs.append(root[i]);
				rhs.append(new_val[i]);
			}
		}
		if (GetSize(lhs) == 0)
			return 0;
		disconnect_root(lhs, anchor, suffix);
		module->connect(lhs, rhs);
		return GetSize(lhs);
	}

	// ----------------------------------------------------------------
	// Collect root candidates: per-lane split buses (entries in range).
	// ----------------------------------------------------------------
	struct RootSplit {
		SigSpec sig;
		std::string name;
		int n, elem;
	};
	vector<RootSplit> collect_split_roots()
	{
		vector<RootSplit> roots;
		vector<Wire *> all;
		for (auto w : module->wires())
			all.push_back(w);
		for (auto &bus : collect_split_buses(all)) {
			if (bus.entries < min_n || bus.entries > max_n)
				continue;
			if (bus.elem_width < 1 || bus.elem_width > max_field_w)
				continue;
			// Keep the raw (un-sigmapped) wire bits so the root stays
			// drivable; some field bits may fold to constants (e.g. the
			// always-zero MSB of an xbar entry) and only the cell-driven
			// bits get re-driven later. So we do NOT require sig_bus_ok
			// (which would reject any constant-folded bit); the split-bus
			// bits are real wire bits by construction. We only require at
			// least one cell-driven bit so pure input ports are skipped.
			bool raw_ok = true;
			for (auto bit : bus.sig)
				if (!bit.wire) {
					raw_ok = false;
					break;
				}
			if (!raw_ok)
				continue;
			bool any_driven = false;
			for (auto bit : sigmap(bus.sig))
				if (bit.wire && bit_to_driver.at(bit, nullptr) != nullptr) {
					any_driven = true;
					break;
				}
			if (!any_driven)
				continue;
			roots.push_back({bus.sig, bus.name, bus.entries, bus.elem_width});
		}
		// widest fields first (real index buses are the deep ones)
		std::stable_sort(roots.begin(), roots.end(),
		                 [](const RootSplit &a, const RootSplit &b) { return a.n > b.n; });
		return roots;
	}

	void run()
	{
		if (module->has_processes_warn())
			return;

		vector<RootSplit> roots = collect_split_roots();
		log_debug("ffa: %d split-root candidate(s) in %s\n", GetSize(roots), log_id(module));
		for (auto &r : roots)
			log_debug("  cand root %s (n=%d, elem=%d)\n", r.name.c_str(), r.n, r.elem);

		for (auto &root : roots) {
			if (walk_exhausted() || eval_exhausted())
				break;
			if (root_claimed(root.sig))
				continue;

			Region rg;
			if (!match_dsel(root.sig, root.name, root.n, root.elem, rg))
				continue;

			// Find a sibling xbar root that shares this scan.
			XbarCand xb;
			bool have_xbar = false;
			for (auto &cand : roots) {
				if (cand.sig == rg.dsel_sig)
					continue;
				if (root_claimed(cand.sig))
					continue;
				// xbar bits must split evenly into 2^W per-slot blocks.
				if (GetSize(cand.sig) % (1 << rg.field_w) != 0)
					continue;
				log_debug("ffa: try xbar cand %s (%d bits) for region %s\n",
				          cand.name.c_str(), GetSize(cand.sig), rg.dsel_name.c_str());
				if (match_xbar(rg, BusCand{cand.sig, cand.name, cand.n, cand.elem}, xb)) {
					have_xbar = true;
					break;
				}
			}

			// Emit the shared scan once.
			int cnt_w = clog2_int(rg.n + 1);
			vector<SigBit> leader;
			vector<SigSpec> slot;
			SigSpec total;
			vector<SigSpec> cat_lane;
			emit_scan(rg, leader, slot, total, cnt_w, cat_lane);

			SigSpec new_dsel = emit_dsel(rg, leader, slot, total, cnt_w);
			connect_driven(rg.dsel_sig, new_dsel, rg.anchor, "ffa_dangling");
			claim_region(rg.dsel_sig, rg.dsel_cut_cells);
			regions_rewritten++;

			log("  %s: %s <- first_fit_alloc(en=%s%s, cat=%dx%d, %s%s)\n",
			    log_id(module), rg.dsel_name.c_str(),
			    log_signal(rg.en_sig),
			    rg.has_bc ? stringf(", bc=%s", log_signal(rg.bc_sig)).c_str() : "",
			    rg.n, rg.c, rg.msb_first ? "MSB-first" : "LSB-first",
			    rg.coalesce ? ", coalesce" : "");

			if (have_xbar) {
				SigSpec new_xbar = emit_xbar(rg, xb, leader, slot, cnt_w);
				int dn = connect_driven(xb.sig, new_xbar, xb.anchor, "ffa_xbar_dangling");
				claim_region(xb.sig, xb.cut_cells);
				log("    + xbar field gather: %s [slots=%d, slot_w=%d, attr=%dx%d, %d bit(s) re-driven]\n",
				    xb.name.c_str(), xb.nb, xb.slot_w, rg.n, xb.a, dn);
			}
		}
	}
};

struct OptFirstFitAllocPass : public Pass {
	OptFirstFitAllocPass() : Pass("opt_first_fit_alloc",
		"rewrite greedy first-fit resource allocators into log-depth scans") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_first_fit_alloc [options] [selection]\n");
		log("\n");
		log("This pass uses functional fingerprinting to detect combinational regions\n");
		log("that implement a greedy first-fit resource allocator: enabled request\n");
		log("lanes are scanned in priority order and the first lane of each category\n");
		log("(a 'leader') is assigned the next free slot, while later lanes of the\n");
		log("same category (and broadcast lanes) inherit that slot.\n");
		log("\n");
		log("The serial loop-carried taken[]/done[] scan produced by the RTL is\n");
		log("replaced with a log-depth network: a priority-encode of the first\n");
		log("enabled lane, an all-pairs category-equality leader test, a prefix-sum\n");
		log("slot assignment, and a rank gather. Where a per-slot field table (an\n");
		log("'xbar') is driven from the same allocation, it is rewritten as a shared\n");
		log("per-slot field gather driven from the same scan.\n");
		log("\n");
		log("The prefix-sums are emitted as linear $add cascades so a subsequent\n");
		log("opt_parallel_prefix pass rebuilds them into shared log-depth networks.\n");
		log("\n");
		log("    -min-width N, -max-width N\n");
		log("        lane-count range to consider (default 4..64).\n");
		log("\n");
		log("    -walk-budget N, -eval-budget N, -attempt-budget N\n");
		log("        per-module work limits for the candidate search.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_FIRST_FIT_ALLOC pass (greedy first-fit allocator rewrite).\n");

		int min_n = 4, max_n = 64;
		int64_t walk_budget = -1, eval_budget = -1, attempt_budget = -1;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if ((args[argidx] == "-min-width" || args[argidx] == "-min_width") && argidx + 1 < args.size()) {
				min_n = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-width" || args[argidx] == "-max_width") && argidx + 1 < args.size()) {
				max_n = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-walk-budget" || args[argidx] == "-walk_budget") && argidx + 1 < args.size()) {
				walk_budget = std::stoll(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-eval-budget" || args[argidx] == "-eval_budget") && argidx + 1 < args.size()) {
				eval_budget = std::stoll(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-attempt-budget" || args[argidx] == "-attempt_budget") && argidx + 1 < args.size()) {
				attempt_budget = std::stoll(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0;
		int total_cells = 0;
		for (auto module : design->selected_modules()) {
			OptFirstFitAllocWorker worker(module);
			worker.min_n = min_n;
			worker.max_n = max_n;
			if (walk_budget > 0)
				worker.walk_budget = walk_budget;
			if (eval_budget > 0)
				worker.eval_budget = eval_budget;
			if (attempt_budget > 0)
				worker.attempt_budget = attempt_budget;
			worker.run();
			total_regions += worker.regions_rewritten;
			total_cells += worker.cells_added;
		}

		log("Rewrote %d first-fit alloc region(s); emitted %d new cell(s).\n",
		    total_regions, total_cells);

		if (total_regions)
			Yosys::run_pass("clean -purge");
	}
} OptFirstFitAllocPass;

PRIVATE_NAMESPACE_END
