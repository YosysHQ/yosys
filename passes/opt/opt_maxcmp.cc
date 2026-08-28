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
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/cut_region.h"

// Predicate applied per lane: value <pred> threshold.
enum class Pred { GT, GE, LT, LE };

static const char *pred_name(Pred p)
{
	switch (p) {
	case Pred::GT: return "gt";
	case Pred::GE: return "ge";
	case Pred::LT: return "lt";
	default:       return "le";
	}
}

// opt_maxcmp: push a threshold comparison through a masked max/min reduction.
//
// A boolean `r = (max over enabled lanes of v_lane) CMP thr` (dually a min)
// is equivalent to a shallow reduction over per-lane comparisons:
//
//   max(v) >  thr  <=>  OR_lane(  en_lane & (v_lane >  thr) )
//   max(v) >= thr  <=>  OR_lane(  en_lane & (v_lane >= thr) )
//   min(v) <  thr  <=>  OR_lane(  en_lane & (v_lane <  thr) )
//   min(v) <= thr  <=>  OR_lane(  en_lane & (v_lane <= thr) )
//   max(v) <  thr  <=>  AND_lane( ~en_lane | (v_lane <  thr) )   (all-below)
//   min(v) >= thr  <=>  AND_lane( ~en_lane | (v_lane >= thr) )   (all-above)
//   ... and the other two conjunctive forms.
//
// RTL frequently builds the max/min with a serial structure (a one-hot
// `1<<idx` scatter followed by a leading-one priority encode, or a
// compare-select tree), giving a deep critical path; the rewrite collapses it
// to N parallel comparisons plus a log-depth reduction. The pass is anchored
// on magnitude-compare cells (bounded by their count) and every rewrite is
// verified by ConstEval fingerprinting, so it is agnostic to how the reduction
// was spelled and never depends on don't-care freedom.
struct OptMaxCmpWorker : CutRegionWorker
{
	typedef BusCand Bus;

	// Tunables (see Pass::execute).
	int min_lanes = 3;
	int max_lanes = 256;
	int max_value_width = 32;

	// Search caps per compare anchor.
	int max_value_buses = 24;
	int max_enable_buses = 24;

	int regions_rewritten = 0;
	int cells_added = 0;

	// Estimate of the current anchor cone size, charged per fingerprint eval.
	int64_t cur_cone_est = 64;

	// Emit anchor (drives NEW_ID2_SUFFIX / src attribution).
	Cell *anchor = nullptr;

	OptMaxCmpWorker(Module *module) : CutRegionWorker(module) {}

	// ---------------------------------------------------------------- emit
	SigSpec emit_not(SigSpec a)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Not(NEW_ID2_SUFFIX("maxcmp_not"), a, false, cell_src(anchor));
	}
	SigSpec emit_and(SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->And(NEW_ID2_SUFFIX("maxcmp_and"), a, b, false, cell_src(anchor));
	}
	SigSpec emit_or(SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Or(NEW_ID2_SUFFIX("maxcmp_or"), a, b, false, cell_src(anchor));
	}
	SigBit emit_cmp(Pred p, SigSpec a, SigSpec b, bool is_signed)
	{
		Cell *cell = anchor;
		cells_added++;
		switch (p) {
		case Pred::GT: return module->Gt(NEW_ID2_SUFFIX("maxcmp_cmp"), a, b, is_signed, cell_src(anchor))[0];
		case Pred::GE: return module->Ge(NEW_ID2_SUFFIX("maxcmp_cmp"), a, b, is_signed, cell_src(anchor))[0];
		case Pred::LT: return module->Lt(NEW_ID2_SUFFIX("maxcmp_cmp"), a, b, is_signed, cell_src(anchor))[0];
		default:       return module->Le(NEW_ID2_SUFFIX("maxcmp_cmp"), a, b, is_signed, cell_src(anchor))[0];
		}
	}
	SigBit emit_reduce(bool is_or, SigSpec bits)
	{
		if (GetSize(bits) == 1)
			return bits[0];
		Cell *cell = anchor;
		cells_added++;
		return is_or ? module->ReduceOr(NEW_ID2_SUFFIX("maxcmp_or"), bits, false, cell_src(anchor))[0]
		             : module->ReduceAnd(NEW_ID2_SUFFIX("maxcmp_and"), bits, false, cell_src(anchor))[0];
	}

	// -------------------------------------------------------------- models
	static int64_t sext_val(uint64_t v, int width)
	{
		if (width <= 0 || width >= 64)
			return (int64_t)v;
		uint64_t m = 1ULL << (width - 1);
		return (int64_t)((v ^ m) - m);
	}

	static bool pred_eval(Pred p, uint64_t v, uint64_t thr, bool is_signed, int width)
	{
		if (is_signed) {
			int64_t sv = sext_val(v, width), st = sext_val(thr, width);
			switch (p) {
			case Pred::GT: return sv > st;
			case Pred::GE: return sv >= st;
			case Pred::LT: return sv < st;
			default:       return sv <= st;
			}
		}
		switch (p) {
		case Pred::GT: return v > thr;
		case Pred::GE: return v >= thr;
		case Pred::LT: return v < thr;
		default:       return v <= thr;
		}
	}

	static Const pack_lanes(const vector<uint64_t> &vals, int vw)
	{
		vector<State> bits(GetSize(vals) * vw, State::S0);
		for (int i = 0; i < GetSize(vals); i++)
			for (int b = 0; b < vw && b < 64; b++)
				if ((vals[i] >> b) & 1ULL)
					bits[i * vw + b] = State::S1;
		return Const(bits);
	}

	static Const pack_bits(uint64_t mask, int m)
	{
		vector<State> bits(m, State::S0);
		for (int i = 0; i < m && i < 64; i++)
			if ((mask >> i) & 1ULL)
				bits[i] = State::S1;
		return Const(bits);
	}

	// --------------------------------------------------------------- candidate
	struct Cand {
		Cell *cmp = nullptr;   // anchor compare cell (its Y is the rewrite root)
		SigSpec root;          // sigmap'd Y
		SigSpec value_sig;     // N*vw wire bits (lane k = [k*vw +: vw])
		std::string value_name;
		SigSpec enable_sig;    // M wire bits, or empty for the always-enabled form
		std::string enable_name;
		SigSpec thr_sig;       // vw bits when the threshold is a signal (empty if const)
		Const thr_const;       // used when thr_sig is empty
		bool thr_is_const = false;
		int lanes = 0, vw = 0, mbits = 0;
		bool is_signed = false;
		Pred pred = Pred::GT;
		bool or_form = true;   // true: OR(en & cmp); false: AND(~en | cmp)
		vector<int> emap;      // per-lane enable bit index, or -1 = always on
		pool<Cell *> cut_cells;
	};

	bool is_compare(Cell *c)
	{
		return c->type.in(ID($lt), ID($le), ID($gt), ID($ge));
	}

	// Maps each 1-bit mux select to its mux, to spot min/max-select nodes.
	dict<SigBit, pool<Cell *>> sel_mux;

	void build_sel_index()
	{
		for (auto c : module->cells())
			if (c->type.in(ID($mux), ID($pmux)))
				for (auto b : sigmap(c->getPort(ID::S)))
					if (b.wire)
						sel_mux[b].insert(c);
	}

	// A compare-select (min/max) node: the compare's result selects a mux
	// between the very operands it compares (`(a<b) ? a : b`). These are
	// internal nodes of a max/min tree; rewriting them yields no depth win and
	// scales as O(N^2), so they are skipped. The threshold compare that
	// consumes the finished max/min (feeding an OR / output) is not a select
	// node and is still matched.
	bool is_minmax_select(Cell *cmp)
	{
		SigSpec cy = sigmap(cmp->getPort(ID::Y));
		if (GetSize(cy) < 1 || !cy[0].wire)
			return false;
		auto it = sel_mux.find(cy[0]);
		if (it == sel_mux.end())
			return false;
		SigSpec ca = sigmap(cmp->getPort(ID::A));
		SigSpec cb = sigmap(cmp->getPort(ID::B));
		for (auto m : it->second) {
			if (GetSize(m->getPort(ID::S)) != 1)
				continue;
			SigSpec ma = sigmap(m->getPort(ID::A));
			SigSpec mb = sigmap(m->getPort(ID::B));
			if ((ma == ca && mb == cb) || (ma == cb && mb == ca))
				return true;
		}
		return false;
	}

	// Evaluate the root under one assignment. Returns false if the cut does
	// not fully determine the (single-bit) output.
	bool eval_root(ConstEval &ce, const Cand &cand, const vector<uint64_t> &vals,
	               uint64_t enmask, uint64_t thrv, bool &out)
	{
		charge_eval(cur_cone_est);
		ce.push();
		ce.set(cand.value_sig, pack_lanes(vals, cand.vw));
		if (!cand.enable_sig.empty())
			ce.set(cand.enable_sig, pack_bits(enmask, cand.mbits));
		if (!cand.thr_is_const)
			ce.set(cand.thr_sig, pack_bits(thrv, cand.vw));
		SigSpec o = cand.root;
		SigSpec undef;
		bool ok = ce.eval(o, undef);
		ce.pop();
		if (!ok || !o.is_fully_const())
			return false;
		out = (o.as_const()[0] == State::S1);
		return true;
	}

	bool model(const Cand &cand, const vector<uint64_t> &vals, uint64_t enmask, uint64_t thrv)
	{
		if (cand.or_form) {
			for (int i = 0; i < cand.lanes; i++) {
				bool en = cand.emap[i] < 0 || ((enmask >> cand.emap[i]) & 1ULL);
				if (en && pred_eval(cand.pred, vals[i], thrv, cand.is_signed, cand.vw))
					return true;
			}
			return false;
		}
		for (int i = 0; i < cand.lanes; i++) {
			bool en = cand.emap[i] < 0 || ((enmask >> cand.emap[i]) & 1ULL);
			if (en && !pred_eval(cand.pred, vals[i], thrv, cand.is_signed, cand.vw))
				return false;
		}
		return true;
	}

	// Deterministic corner + pseudo-random vectors. thr varies only when it is
	// a signal (a constant threshold is fixed by the netlist).
	struct TV { vector<uint64_t> vals; uint64_t enmask; uint64_t thrv; };

	vector<TV> make_vectors(const Cand &cand)
	{
		int N = cand.lanes, M = cand.mbits, vw = cand.vw;
		uint64_t vmask = lowmask_u64(vw);
		uint64_t allen = lowmask_u64(std::max(M, 1));
		uint64_t thr0 = cand.thr_is_const ? cand.thr_const.as_int() : (vmask >> 1);
		vector<TV> vs;
		auto thr_set = [&]() -> vector<uint64_t> {
			if (cand.thr_is_const)
				return {thr0};
			return {thr0, 0, vmask, vmask >> 2, (vmask * 3) / 4 & vmask};
		};
		auto push = [&](vector<uint64_t> v, uint64_t en) {
			for (auto &x : v) x &= vmask;
			for (uint64_t t : thr_set())
				vs.push_back({v, en & allen, t & vmask});
		};
		push(vector<uint64_t>(N, 0), allen);
		push(vector<uint64_t>(N, vmask), allen);
		push(vector<uint64_t>(N, thr0), allen);
		if (M)
			push(vector<uint64_t>(N, vmask), 0);
		// Each lane solo-high (rest low), enables all-on and that lane's group off.
		for (int i = 0; i < N; i++) {
			vector<uint64_t> v(N, 0);
			v[i] = vmask;
			push(v, allen);
			vector<uint64_t> v2(N, vmask);
			v2[i] = 0;
			push(v2, allen);
		}
		// Random.
		uint64_t lfsr = 0x243f6a8885a308d3ULL ^ (uint64_t)(N * 131 + M * 17 + vw);
		auto rnd = [&]() { lfsr ^= lfsr << 13; lfsr ^= lfsr >> 7; lfsr ^= lfsr << 17; return lfsr; };
		int rounds = std::min(40, 8 + N);
		for (int r = 0; r < rounds; r++) {
			vector<uint64_t> v(N);
			for (int i = 0; i < N; i++) v[i] = rnd();
			push(v, M ? rnd() : allen);
		}
		return vs;
	}

	// Verify one fully-specified hypothesis (pred, form, emap). Early-outs on
	// the first mismatch or the first eval that the cut cannot resolve.
	bool fingerprint(ConstEval &ce, const Cand &cand)
	{
		for (auto &tv : make_vectors(cand)) {
			bool actual;
			if (!eval_root(ce, cand, tv.vals, tv.enmask, tv.thrv, actual))
				return false;
			if (actual != model(cand, tv.vals, tv.enmask, tv.thrv))
				return false;
			if (eval_exhausted())
				return false;
		}
		return true;
	}

	// Canonical lane->enable maps to try before giving up. Covers the common
	// physical shapes: 1:1, contiguous broadcast (en[i / (N/M)]) and
	// interleaved broadcast (en[i % M]). Any map that fails is simply skipped.
	vector<vector<int>> candidate_maps(int N, int M)
	{
		vector<vector<int>> maps;
		if (M == 0) {
			maps.push_back(vector<int>(N, -1));
			return maps;
		}
		// model() shifts enmask (a uint64_t) by the lane's enable index, so an
		// enable width past 64 is unrepresentable; refuse it rather than risk
		// shift-by->=64 UB (callers also cap M <= 64 before we reach here).
		if (M > 64)
			return maps;
		if (M == N) {
			vector<int> id(N);
			for (int i = 0; i < N; i++) id[i] = i;
			maps.push_back(id);
		}
		if (N % M == 0) {
			int g = N / M;
			vector<int> block(N), inter(N);
			for (int i = 0; i < N; i++) {
				block[i] = i / g;
				inter[i] = i % M;
			}
			maps.push_back(block);
			maps.push_back(inter);
		}
		return maps;
	}

	// Try every (pred, form, map) hypothesis for a fixed (value,enable,thr)
	// binding; the first that fingerprints fills `cand` and returns true.
	bool resolve(ConstEval &ce, Cand &cand)
	{
		static const Pred preds[4] = {Pred::GT, Pred::GE, Pred::LT, Pred::LE};
		auto maps = candidate_maps(cand.lanes, cand.mbits);
		for (Pred p : preds) {
			for (int form = 0; form < 2; form++) {
				for (auto &m : maps) {
					cand.pred = p;
					cand.or_form = (form == 0);
					cand.emap = m;
					if (fingerprint(ce, cand))
						return true;
					if (eval_exhausted() || walk_exhausted())
						return false;
				}
			}
		}
		return false;
	}

	// Cheap structural gate: a maskable max/min cone is mux/shift/reduce heavy.
	bool cone_looks_reducible(const pool<Cell *> &cone)
	{
		for (auto c : cone)
			if (c->type.in(ID($mux), ID($pmux), ID($shl), ID($shift), ID($shiftx),
			               ID($reduce_or), ID($reduce_and), ID($reduce_bool),
			               ID($or), ID($and)))
				return true;
		return false;
	}

	// Collect candidate buses inside the anchor cone. Every bus is offered both
	// as a value bus (split into lanes of the compare width) and as an enable
	// bus (M one-bit lanes); the width/divisibility filters in run() and the
	// fingerprint decide which role, if any, actually fits. This is why a
	// packed enable port (a plain wire run, e.g. `en[0+:8]`) is a valid enable
	// candidate and not just per-index split wires.
	void collect_buses(const pool<Cell *> &cone_cells, const pool<SigBit> &leaf_bits,
	                   vector<Bus> &value_buses, vector<Bus> &enable_buses)
	{
		(void)cone_cells;
		// Candidates are drawn from the cone LEAVES only (its actual inputs):
		// the value lanes and enables are primary inputs / register outputs, not
		// internal wires. Restricting to leaves keeps the candidate set small
		// (no `bits`/`$and` intermediates) and puts the real buses up front.
		pool<SigSpec> seen;
		auto add = [&](const SigSpec &sig, const std::string &name) {
			SigSpec s = sigmap(sig);
			if (GetSize(s) < 1 || !seen.insert(s).second)
				return;
			value_buses.push_back({s, name, 0, 0});
			enable_buses.push_back({s, name, GetSize(s), 1});
		};
		// Maximal leaf wire runs (covers packed value and enable ports).
		for (auto &run : collect_wire_run_buses(leaf_bits, 64))
			add(run.sig, run.name);
		// Per-index split leaf buses (array FFs / element wires).
		for (auto &bus : collect_cone_split_buses(leaf_bits))
			add(bus.sig, bus.name);
		// Whole single-bit leaf wires, so a broadcast (M==1) enable is reachable.
		// This runs per compare candidate, so it takes the width index rather
		// than re-walking every wire in the module each time; same wires, same
		// module order.
		for (auto w : wires_of_width(1)) {
			SigBit b = sigmap(SigSpec(w))[0];
			if (b.wire && leaf_bits.count(b))
				add(SigSpec(b), w->name.str());
		}
	}

	void run()
	{
		if (module->has_processes_warn())
			return;

		// Cheap module prefilter.
		bool has_cmp = false;
		for (auto c : module->cells())
			if (is_compare(c)) { has_cmp = true; break; }
		if (!has_cmp)
			return;

		ConstEval &ce = shared_ce();
		build_sel_index();

		vector<Cell *> compares;
		for (auto c : module->cells())
			if (is_compare(c) && !is_minmax_select(c))
				compares.push_back(c);

		vector<Cand> rewrites;
		for (int ci = 0; ci < GetSize(compares); ci++) {
			Cell *cmp = compares[ci];
			if (walk_exhausted() || eval_exhausted()) {
				note_budget("opt_maxcmp", GetSize(compares) - ci);
				break;
			}
			SigSpec y = sigmap(cmp->getPort(ID::Y));
			if (GetSize(y) < 1)
				continue;
			if (root_claimed(y))
				continue;
			bool is_signed = cmp->getParam(ID::A_SIGNED).as_bool() &&
			                 cmp->getParam(ID::B_SIGNED).as_bool();

			SigSpec A = sigmap(cmp->getPort(ID::A));
			SigSpec B = sigmap(cmp->getPort(ID::B));

			// Try both operand orientations: mval (the reduction side) is A or
			// B; the other operand is the threshold. resolve() brute-forces the
			// predicate/form, so orientation only selects which cone to search.
			bool matched = false;
			for (int orient = 0; orient < 2 && !matched; orient++) {
				SigSpec mval = orient == 0 ? A : B;
				SigSpec thr  = orient == 0 ? B : A;
				if (!sig_bus_ok(mval))
					continue;
				int vw = GetSize(mval);
				if (vw < 1 || vw > max_value_width)
					continue;

				pool<Cell *> cone_cells;
				pool<SigBit> leaf_bits;
				int max_cone_cells = std::max(256, max_lanes * 64);
				int max_leaf_bits = max_lanes * (vw + 4) + 64;
				if (!get_cone(mval, cone_cells, leaf_bits, max_cone_cells, max_leaf_bits))
					continue;
				if (GetSize(cone_cells) < 1 || !cone_looks_reducible(cone_cells))
					continue;
				cur_cone_est = GetSize(cone_cells);

				// Threshold: constant, or a signal whose bits sit outside mval's
				// value lanes. Extract its value/handle at compare width.
				bool thr_const = thr.is_fully_const();

				// A non-constant threshold is driven into ConstEval as a word of vw
				// bits, so the fingerprint only makes sense when the compare's two
				// operands are the same width. RTLIL permits them to differ, and any
				// upstream pass that narrows one operand on its own produces exactly
				// that -- so check rather than assume.
				if (!thr_const && GetSize(thr) != vw)
					continue;

				vector<Bus> value_buses, enable_buses;
				collect_buses(cone_cells, leaf_bits, value_buses, enable_buses);

				int vb_tried = 0;
				for (auto &vb : value_buses) {
					if (matched || vb_tried >= max_value_buses)
						break;
					if (walk_exhausted() || eval_exhausted())
						break;
					int total = GetSize(vb.sig);
					if (total < vw || total % vw != 0)
						continue;
					int N = total / vw;
					if (N < min_lanes || N > max_lanes)
						continue;
					pool<SigBit> vbits;
					if (!sig_bits_unique(vb.sig, vbits))
						continue;
					vb_tried++;

					// Enable options: none first, then 1-bit-lane buses whose
					// width evenly maps onto the lanes.
					int eb_tried = 0;
					for (int e = -1; e < GetSize(enable_buses); e++) {
						if (matched || eb_tried >= max_enable_buses)
							break;
						if (walk_exhausted() || eval_exhausted())
							break;
						Cand cand;
						cand.cmp = cmp;
						cand.root = y;
						cand.value_sig = vb.sig;
						cand.value_name = vb.name;
						cand.lanes = N;
						cand.vw = vw;
						cand.is_signed = is_signed;
						cand.thr_is_const = thr_const;
						if (thr_const)
							cand.thr_const = thr.as_const();
						else
							cand.thr_sig = thr;

						pool<SigBit> allowed = vbits;
						if (!thr_const)
							if (!sig_bits_unique(thr, allowed))
								continue;
						if (e >= 0) {
							auto &eb = enable_buses[e];
							int M = GetSize(eb.sig);
							// Enable fingerprinting models the mask in a single
							// uint64_t, so cap the enable width at 64 bits; wider
							// buses would shift by >=64 in model() (UB) and be
							// truncated in pack_bits.
							if (M < 1 || M > 64 || (M != N && N % M != 0))
								continue;
							if (eb.sig == vb.sig)
								continue;
							pool<SigBit> ebits;
							if (!sig_bits_unique(eb.sig, ebits))
								continue;
							bool overlap = false;
							for (auto b : ebits)
								if (allowed.count(b)) { overlap = true; break; }
							if (overlap)
								continue;
							for (auto b : ebits)
								allowed.insert(b);
							cand.enable_sig = eb.sig;
							cand.enable_name = eb.name;
							cand.mbits = M;
							eb_tried++;
						} else {
							cand.mbits = 0;
						}

						pool<Cell *> cut_cells;
						if (!cut_cone_walk(mval, allowed, GetSize(cone_cells) + 16, nullptr,
						                   &cut_cells, nullptr, &leaf_bits, &cone_cells))
							continue;
						cand.cut_cells = cut_cells;

						if (!resolve(ce, cand))
							continue;

						rewrites.push_back(cand);
						claim_region(y, cut_cells);
						log("  %s: %s <- %s(values=%s%s%s, thr=%s) [N=%d, VW=%d, %s]\n",
						    log_id(module), log_signal(y), cand.or_form ? "any" : "all",
						    cand.value_name.c_str(),
						    cand.enable_sig.empty() ? "" : ", en=",
						    cand.enable_sig.empty() ? "" : cand.enable_name.c_str(),
						    cand.thr_is_const ? "const" : "sig",
						    N, vw, pred_name(cand.pred));
						matched = true;
						break;
					}
				}
			}
		}

		for (auto &cand : rewrites) {
			anchor = cand.cmp;
			SigSpec value = sigmap(cand.value_sig);
			SigSpec enable = cand.enable_sig.empty() ? SigSpec() : sigmap(cand.enable_sig);
			SigSpec thr = cand.thr_is_const ? SigSpec(cand.thr_const) : sigmap(cand.thr_sig);

			SigSpec terms;
			for (int i = 0; i < cand.lanes; i++) {
				SigSpec v = value.extract(i * cand.vw, cand.vw);
				SigBit c = emit_cmp(cand.pred, v, thr, cand.is_signed);
				SigBit term = c;
				if (cand.emap[i] >= 0) {
					SigBit en = enable[cand.emap[i]];
					if (cand.or_form)
						term = emit_and(SigSpec(en), SigSpec(c))[0];
					else
						term = emit_or(emit_not(SigSpec(en)), SigSpec(c))[0];
				}
				terms.append(term);
			}
			SigBit reduced = emit_reduce(cand.or_form, terms);
			SigSpec new_y = zext_sig(SigSpec(reduced), GetSize(cand.root));
			disconnect_root(cand.root, cand.cmp, "maxcmp_dangling");
			module->connect(cand.root, new_y);
			regions_rewritten++;
		}
	}
};

struct OptMaxCmpPass : public Pass
{
	OptMaxCmpPass() : Pass("opt_maxcmp",
		"push threshold comparisons through masked max/min reductions") {}

	void help() override
	{
		log("\n");
		log("    opt_maxcmp [options] [selection]\n");
		log("\n");
		log("Detect a boolean that compares a masked max/min reduction against a\n");
		log("threshold, e.g. (max over enabled lanes of v) > thr, and replace it\n");
		log("with a shallow reduction over per-lane comparisons:\n");
		log("\n");
		log("    max(v) > thr   ==>   |(en_lane & (v_lane > thr))\n");
		log("    min(v) < thr   ==>   |(en_lane & (v_lane < thr))\n");
		log("    max(v) < thr   ==>   &(~en_lane | (v_lane < thr))\n");
		log("\n");
		log("The reduction is commonly built as a one-hot scatter plus leading-one\n");
		log("priority encode or a compare-select tree, which has a deep critical\n");
		log("path; the rewrite exposes N parallel comparisons and a log-depth OR/AND\n");
		log("instead. The pass is anchored on magnitude-compare cells and every\n");
		log("region is verified by ConstEval fingerprinting (max/min, >/>=/</<=,\n");
		log("signed/unsigned, constant or signal threshold, and 1:1, broadcast, or\n");
		log("absent per-lane enables), so it applies regardless of how the RTL was\n");
		log("written and never relies on don't-care freedom.\n");
		log("\n");
		log("    -min-lanes N, -min_lanes N\n");
		log("        minimum lane count to consider (default 3).\n");
		log("\n");
		log("    -max-lanes N, -max_lanes N\n");
		log("        maximum lane count to consider (default 256).\n");
		log("\n");
		log("    -max-value-width N, -max_value_width N\n");
		log("        maximum per-lane / threshold width to consider (default 32).\n");
		log("\n");
		log("    -walk-budget N, -eval-budget N, -attempt-budget N\n");
		log("        per-module work limits for the candidate search (defaults\n");
		log("        20000000 / 20000000 / 65536). When a budget is exhausted the\n");
		log("        remaining compare anchors are skipped and a note is logged.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MAXCMP pass (masked max/min threshold rewrite).\n");

		int min_lanes = 3;
		int max_lanes = 256;
		int max_value_width = 32;
		int64_t walk_budget = -1, eval_budget = -1, attempt_budget = -1;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if ((args[argidx] == "-min-lanes" || args[argidx] == "-min_lanes") &&
			    argidx + 1 < args.size()) {
				min_lanes = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-lanes" || args[argidx] == "-max_lanes") &&
			    argidx + 1 < args.size()) {
				max_lanes = std::stoi(args[++argidx]);
				continue;
			}
			if ((args[argidx] == "-max-value-width" || args[argidx] == "-max_value_width") &&
			    argidx + 1 < args.size()) {
				max_value_width = std::stoi(args[++argidx]);
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
			OptMaxCmpWorker worker(module);
			worker.min_lanes = min_lanes;
			worker.max_lanes = max_lanes;
			worker.max_value_width = max_value_width;
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

		log("Rewrote %d max/min-compare region(s); emitted %d new cell(s).\n",
		    total_regions, total_cells_added);

		if (total_regions)
			Yosys::run_pass("clean -purge");
	}
} OptMaxCmpPass;

PRIVATE_NAMESPACE_END
