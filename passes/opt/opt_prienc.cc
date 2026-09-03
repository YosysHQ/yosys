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
#include <functional>
#include <memory>
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/rewrite_utils.h"

// Priority-encoder variants the pass recognises. The CLO/CTO forms count a
// leading/trailing run of ONES; by De Morgan they are CLZ/CTZ of ~x, so they
// share the whole fingerprint deck and emit network with one extra $not.
enum class PEVariant { NONE, CLZ_FULL, CLZ_SHORT, CTZ_FULL, CTZ_SHORT,
                       CLO_FULL, CLO_SHORT, CTO_FULL, CTO_SHORT };

static const char* variant_name(PEVariant v) {
	switch (v) {
		case PEVariant::CLZ_FULL:  return "clz_full";
		case PEVariant::CLZ_SHORT: return "clz_short";
		case PEVariant::CTZ_FULL:  return "ctz_full";
		case PEVariant::CTZ_SHORT: return "ctz_short";
		case PEVariant::CLO_FULL:  return "clo_full";
		case PEVariant::CLO_SHORT: return "clo_short";
		case PEVariant::CTO_FULL:  return "cto_full";
		case PEVariant::CTO_SHORT: return "cto_short";
		default: return "none";
	}
}

// Leading (MSB-side) scan vs trailing (LSB-side) scan.
static bool variant_is_leading(PEVariant v) {
	return v == PEVariant::CLZ_FULL || v == PEVariant::CLZ_SHORT ||
	       v == PEVariant::CLO_FULL || v == PEVariant::CLO_SHORT;
}

// Counts a run of ones (CLO/CTO) rather than a run of zeros (CLZ/CTZ).
static bool variant_counts_ones(PEVariant v) {
	return v == PEVariant::CLO_FULL || v == PEVariant::CLO_SHORT ||
	       v == PEVariant::CTO_FULL || v == PEVariant::CTO_SHORT;
}

// The emitted network is fixed by the run's polarity and direction alone, so
// FULL and SHORT of the same variant share one network and differ only in the
// out_width truncation applied after the lookup.
static int variant_net_key(PEVariant v) {
	return (variant_counts_ones(v) ? 1 : 0) | (variant_is_leading(v) ? 2 : 0);
}

// FULL pins the saturating input's result too, so the emitted output is the
// exact count. Only then does the thermometer mask agree with it bit for bit.
static bool variant_is_full(PEVariant v) {
	return v == PEVariant::CLZ_FULL || v == PEVariant::CTZ_FULL ||
	       v == PEVariant::CLO_FULL || v == PEVariant::CTO_FULL;
}

// A candidate bus rarely stays a clean vector of distinct free nets: tie-offs,
// const propagation and boundary optimization leave constant bits behind, and
// resizing can repeat one net in several positions. Those bits are not free
// inputs -- they narrow the bus's reachable domain -- so record which positions
// ConstEval may pin and which are fixed by the netlist itself.
struct PinnedBus {
	SigSpec sig;            // the bus as it appears in the netlist
	SigSpec free_bits;      // distinct variable bits, first-occurrence order
	std::vector<int> slot;  // bus position -> free_bits index, -1 when constant
	bool ok = false;        // usable: no x/z bit, at least one free bit
	bool pinned = false;    // at least one constant or repeated position
};

static PinnedBus make_pinned_bus(const SigSpec& sig) {
	PinnedBus pb;
	pb.sig = sig;
	pb.slot.assign(GetSize(sig), -1);
	dict<SigBit, int> first;
	for (int i = 0; i < GetSize(sig); i++) {
		SigBit b = sig[i];
		if (!b.wire) {
			// x/z makes the reachable domain undefined; refuse to reason about it.
			if (b != State::S0 && b != State::S1) return pb;
			pb.pinned = true;
			continue;
		}
		auto it = first.find(b);
		if (it == first.end()) {
			pb.slot[i] = GetSize(pb.free_bits);
			first[b] = pb.slot[i];
			pb.free_bits.append(b);
		} else {
			pb.slot[i] = it->second;
			pb.pinned = true;
		}
	}
	pb.ok = GetSize(pb.free_bits) > 0;
	return pb;
}

// Materialise the bus from an assignment of its free bits.
static Const realize_free(const PinnedBus& pb, const Const& fv) {
	auto fb = fv.to_bits();
	std::vector<State> bits(GetSize(pb.sig), State::S0);
	for (int i = 0; i < GetSize(pb.sig); i++) {
		int k = pb.slot[i];
		bits[i] = (k < 0) ? pb.sig[i].data : fb[k];
	}
	return Const(bits);
}

// Project a wanted test pattern onto the bus: pinned positions keep their
// netlist value and repeats follow their first occurrence. Every vector the
// deck produces is therefore reachable, so a pinned bus loses discriminating
// power instead of being rejected outright.
static Const project_vector(const PinnedBus& pb, const Const& want, Const& free_out) {
	auto wb = want.to_bits();
	std::vector<State> fv(GetSize(pb.free_bits), State::Sx);
	for (int i = 0; i < GetSize(pb.sig); i++) {
		int k = pb.slot[i];
		if (k < 0 || fv[k] != State::Sx) continue;
		fv[k] = (i < GetSize(wb) && wb[i] == State::S1) ? State::S1 : State::S0;
	}
	free_out = Const(fv);
	return realize_free(pb, free_out);
}

// Index of the highest bit of `c` equal to `want`, or -1 if there is none.
// Bits past the end of `c` read as S0 (Const may be shorter than N).
static int const_msb(const Const& c, int N, State want) {
	auto bits = c.to_bits();
	for (int i = N - 1; i >= 0; i--) {
		State s = i < (int)bits.size() ? bits[i] : State::S0;
		if (s == want) return i;
	}
	return -1;
}

// Index of the lowest bit of `c` equal to `want`, or -1 if there is none.
static int const_lsb(const Const& c, int N, State want) {
	auto bits = c.to_bits();
	for (int i = 0; i < N; i++) {
		State s = i < (int)bits.size() ? bits[i] : State::S0;
		if (s == want) return i;
	}
	return -1;
}

// MSB-side suffix-OR: M[i] = OR of x[j] for all j >= i. That is the
// "round up to 2^n - 1" mask: one leading one, then ones down to the LSB.
static Const software_smear(const Const& c, int N) {
	auto bits = c.to_bits();
	std::vector<State> m(N, State::S0);
	State run = State::S0;
	for (int i = N - 1; i >= 0; i--) {
		State b = i < (int)bits.size() ? bits[i] : State::S0;
		if (b == State::S1) run = State::S1;
		m[i] = run;
	}
	return Const(m);
}

// msb_index(x)+1, and 0 when x is 0. Equals cto_full(smear(x)).
static int software_leadone(const Const& c, int N) {
	int msb = const_msb(c, N, State::S1);
	return msb < 0 ? 0 : msb + 1;
}

struct OptPriEncWorker {
	Module* module;
	SigMap sigmap;
	Cell* cell = nullptr;

	// Bit-level driver map (combinational drivers only).
	dict<SigBit, Cell*> bit_to_driver;
	pool<SigBit> input_port_bits;
	pool<Cell*> sequential_cells;

	// Configuration.
	bool detect_clz = true;
	bool detect_ctz = true;
	bool detect_clo = true;
	bool detect_cto = true;
	bool detect_rr = true;
	bool enable_smear = false;
	bool allow_partial_cone = false;
	int max_input_width = 256;
	int min_input_width = 4;
	// 2^8 evals, paid only by a pinned bus that already survived the deck.
	int max_exhaustive_free_bits = 8;

	// Stats.
	int regions_rewritten = 0;
	int roundtrips_collapsed = 0;
	int smears_collapsed = 0;
	int compares_narrowed = 0;
	int cells_added = 0;

	// Valid only during the pre-mutation fingerprint window in run().
	ConstEval* ce = nullptr;
	// M -> x when M is the MSB suffix-OR smear of x; misses recorded separately.
	dict<SigSpec, SigSpec> smear_hit;
	pool<SigSpec> smear_miss;
	// Remaining mux peels while emitting I1, so a clamp/pad tree can still
	// retarget a smear arm after hoisting stops at an intermediate leaf.
	int smear_peel = 3;

	struct Rewrite {
		Wire* S_wire;
		Wire* T_wire;
		int N;
		int Wbits;
		PEVariant variant;
		Cell* sole_driver;
		IdString out_port;
		SigSpec driven;        // the bits of S the driver actually produces
		vector<int> driven_pos; // their positions within S
		bool cone_partial;     // discovery walk was truncated (see -partial-cone)
	};

	// Networks already emitted per (input bus, variant_net_key) pair, so matched
	// outputs sharing a bus -- and repeated arms of a hoisted mux tree -- pull
	// from one instantiation instead of duplicating the log-depth tree.
	dict<std::pair<SigSpec, int>, SigSpec> pe_sig_cache;
	dict<SigSpec, SigSpec> inverted_cache;
	dict<std::pair<Wire*, int>, SigSpec> pe_prefix_cache;
	dict<SigSpec, SigSpec> leadone_cache;

	OptPriEncWorker(Module* m) : module(m), sigmap(m) { build_indexes(); }

	void build_indexes() {
		for (auto cell : module->cells()) {
			if (is_sequential(cell)) {
				sequential_cells.insert(cell);
				continue;
			}
			for (auto& conn : cell->connections()) {
				if (!cell->output(conn.first)) continue;
				for (auto bit : sigmap(conn.second))
					if (bit.wire) bit_to_driver[bit] = cell;
			}
		}
		for (auto wire : module->wires()) {
			if (!wire->port_input) continue;
			for (auto bit : sigmap(wire))
				input_port_bits.insert(bit);
		}
	}

	// Compute the combinational fanin cone of `from`. Outputs the set of cells
	// in the cone (cells whose output is reached by BFS) and the "leaf" bits
	// (port-input bits or bits driven by sequential cells / undriven).
	// Returns 1 on success, 0 if the cone is empty/unusable, -1 if it exceeded
	// the size caps (caller may retry with a larger cap / budget).
	int get_cone(SigSpec from, pool<Cell*>& cone_cells, pool<SigBit>& leaf_bits,
	             int max_cone_cells, int max_leaf_bits) {
		cone_cells.clear();
		leaf_bits.clear();
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		for (auto bit : sigmap(from)) {
			if (!bit.wire) continue;
			if (visited.insert(bit).second) worklist.push(bit);
		}
		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();
			if (input_port_bits.count(bit)) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits) return -1;
				continue;
			}
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits) return -1;
				continue;
			}
			Cell* drv = it->second;
			if (sequential_cells.count(drv)) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits) return -1;
				continue;
			}
			if (!cone_cells.insert(drv).second) continue;
			if (GetSize(cone_cells) > max_cone_cells) return -1;
			for (auto& conn : drv->connections()) {
				if (!drv->input(conn.first)) continue;
				for (auto in_bit : sigmap(conn.second)) {
					if (!in_bit.wire) continue;
					if (visited.insert(in_bit).second) worklist.push(in_bit);
				}
			}
		}
		return cone_cells.empty() ? 0 : 1;
	}

	// Inverted index: sigmap bit -> wires that contain it. Built once per run()
	// so candidate T/req/start discovery is O(|cone_bits|) instead of O(|wires|).
	dict<SigBit, vector<Wire*>> bit_to_cand_wires;
	dict<Wire*, int> wire_uniq_bit_count;
	dict<Wire*, vector<SigBit>> wire_sig_bits;
	pool<Wire*> wire_has_const;

	void build_wire_index(const vector<Wire*>& wires) {
		bit_to_cand_wires.clear();
		wire_uniq_bit_count.clear();
		wire_sig_bits.clear();
		wire_has_const.clear();
		for (Wire* w : wires) {
			SigSpec ss = sigmap(SigSpec(w));
			vector<SigBit> bits;
			bits.reserve(GetSize(ss));
			pool<SigBit> uniq;
			for (auto bit : ss) {
				bits.push_back(bit);
				if (!bit.wire) { wire_has_const.insert(w); continue; }
				if (uniq.insert(bit).second)
					bit_to_cand_wires[bit].push_back(w);
			}
			wire_sig_bits[w] = std::move(bits);
			// Counts the bits ConstEval can pin; const positions are covered
			// by the netlist, so they never need to be found in the cone.
			wire_uniq_bit_count[w] = GetSize(uniq);
		}
	}

	// Wires whose sigmap bits are all inside `cone_bits` (and pass `keep`).
	// Buses carrying constant bits are only offered when `allow_const`, since
	// only the PE fingerprint knows how to hold those positions fixed.
	vector<Wire*> wires_in_cone(const pool<SigBit>& cone_bits,
	                            std::function<bool(Wire*)> keep,
	                            bool allow_const = false) {
		dict<Wire*, int> cover;
		dict<Wire*, bool> keep_cache;
		auto keep_cached = [&](Wire* w) -> bool {
			auto it = keep_cache.find(w);
			if (it != keep_cache.end()) return it->second;
			bool ok = keep(w);
			keep_cache[w] = ok;
			return ok;
		};
		for (auto bit : cone_bits) {
			auto it = bit_to_cand_wires.find(bit);
			if (it == bit_to_cand_wires.end()) continue;
			for (Wire* w : it->second) {
				if (!keep_cached(w)) continue;
				cover[w]++;
			}
		}
		vector<Wire*> out;
		for (auto& it : cover) {
			Wire* w = it.first;
			if (!allow_const && wire_has_const.count(w)) continue;
			auto uit = wire_uniq_bit_count.find(w);
			if (uit == wire_uniq_bit_count.end()) continue;
			if (it.second == uit->second)
				out.push_back(w);
		}
		return out;
	}

	// Collect wires whose bits are entirely within the cone frontier of S.
	// Prefer wider candidates: more fingerprint constraints, fewer false positives.
	vector<Wire*> find_candidate_Ts(Wire* S_wire,
	                                const pool<SigBit>& cone_bits,
	                                const pool<SigBit>& control_bits,
	                                int Wbits) {
		vector<Wire*> out = wires_in_cone(cone_bits, [&](Wire* w) {
			if (w == S_wire) return false;
			if (w->width < min_input_width || w->width > max_input_width) return false;
			// Same "too narrow to be worth it" floor, applied to the bits that
			// are actually free once tie-offs and repeats are discounted.
			auto uit = wire_uniq_bit_count.find(w);
			if (uit == wire_uniq_bit_count.end() || uit->second < min_input_width)
				return false;
			int W_full = clog2_int(w->width + 1);
			int W_short = clog2_int(w->width);
			if (W_full != Wbits && W_short != Wbits) return false;
			auto sit = wire_sig_bits.find(w);
			if (sit == wire_sig_bits.end()) return false;
			for (auto bit : sit->second)
				if (control_bits.count(bit)) return true;
			return false;
		}, /*allow_const=*/true);
		std::sort(out.begin(), out.end(), [](Wire* a, Wire* b) {
			return a->width > b->width;
		});
		return out;
	}

	// Multi-bit confirmation patterns only (no zero / one-hots). Shared by PE
	// and RR fingerprint decks so callers that already swept one-hots do not
	// rebuild and discard them.
	vector<Const> gen_multibit_test_vectors(int N, bool dense_small_n) {
		vector<Const> vs;
		auto push_prefix = [&](int k) {
			if (k < 1 || k > N) return;
			std::vector<State> bits(N, State::S0);
			for (int i = 0; i < k; i++) bits[i] = State::S1;
			vs.push_back(Const(bits));
		};
		auto push_suffix_clear = [&](int k) {
			if (k < 0 || k >= N) return;
			std::vector<State> bits(N, State::S1);
			for (int i = 0; i < k; i++) bits[i] = State::S0;
			vs.push_back(Const(bits));
		};
		if (dense_small_n && N <= 16) {
			for (int k = 1; k <= N; k++) push_prefix(k);
			for (int k = 0; k < N; k++) push_suffix_clear(k);
		} else {
			push_prefix(2);
			push_prefix(N / 4);
			push_prefix(N / 2);
			push_prefix(N - 1);
			push_prefix(N);
			push_suffix_clear(1);
			push_suffix_clear(N / 4);
			push_suffix_clear(N / 2);
			push_suffix_clear(N - 1);
		}
		if (N >= 4) {
			std::vector<State> aa(N, State::S0), fivefive(N, State::S0), e8(N, State::S0);
			for (int i = 0; i < N; i++) {
				if (i & 1) aa[i] = State::S1; else fivefive[i] = State::S1;
			}
			vs.push_back(Const(aa));
			vs.push_back(Const(fivefive));
			e8[0] = State::S1;
			if (N > 1) e8[N - 1] = State::S1;
			vs.push_back(Const(e8));
		}
		return vs;
	}

	// Full start sweep for small N; capped sample for large N (still includes
	// corners / midpoints that distinguish rotation from fixed priority).
	static vector<int> rr_start_samples(int N) {
		vector<int> out;
		if (N <= 16) {
			out.reserve(N);
			for (int s = 0; s < N; s++) out.push_back(s);
			return out;
		}
		pool<int> sset;
		auto add = [&](int s) { if (s >= 0 && s < N) sset.insert(s); };
		add(0); add(1); add(2);
		add(N - 1); add(N - 2); add(N - 3);
		add(N / 4); add(N / 2); add((3 * N) / 4);
		int target = std::min(N, 16);
		for (int i = 0; GetSize(sset) < target && i < N; i++)
			add((i * 7) % N);
		out.assign(sset.begin(), sset.end());
		std::sort(out.begin(), out.end());
		return out;
	}

	// Sole-driver type gate before get_cone: skip wires driven by cells that
	// never root a PE/RR region (avoids BFS on every narrow misc wire).
	static bool driver_looks_interesting(Cell* d) {
		return d->type.in(ID($mux), ID($pmux), ID($add), ID($sub), ID($or), ID($and),
		                  ID($xor), ID($xnor), ID($not), ID($logic_not), ID($logic_and), ID($logic_or),
		                  ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($reduce_xor),
		                  ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge),
		                  ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx),
		                  ID($mod), ID($modfloor), ID($neg), ID($pos));
	}

	// Cheap structural gate before ConstEval: PE cones are mux/compare/shift heavy.
	static bool cone_looks_like_pe(const pool<Cell*>& cells) {
		for (Cell* c : cells)
			if (c->type.in(ID($mux), ID($pmux), ID($eq), ID($ne), ID($lt), ID($le),
			               ID($gt), ID($ge), ID($logic_and), ID($logic_or), ID($logic_not),
			               ID($reduce_or), ID($reduce_bool), ID($reduce_and),
			               ID($and), ID($or), ID($xor), ID($not),
			               ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx),
			               ID($add), ID($sub)))
				return true;
		return false;
	}

	// RR RTL dynamic-indexes req[idx] ($shiftx/$shift) or uses mod wrap.
	// Do NOT treat $shl/$shr as RR-like: CLZ/CTZ for-loop scans use those and
	// would otherwise pay for pointless RR fingerprinting on huge PE cones.
	static bool cone_looks_like_rr(const pool<Cell*>& cells) {
		int muxes = 0;
		for (Cell* c : cells) {
			if (c->type.in(ID($shiftx), ID($shift), ID($mod), ID($modfloor)))
				return true;
			if (c->type.in(ID($mux), ID($pmux))) muxes++;
		}
		return muxes >= 8;
	}

	// ConstEval::set() requires every (sigmap-canonical) bit it pins to be a
	// distinct free wire bit. Real designs can tie parts of a bus to constants
	// or alias nets together, so guard the fingerprint inputs: reject signals
	// containing constant or repeated bits, and (across the whole set) any
	// overlap between them. This prevents a ConstEval assertion; skipping an
	// unclean candidate only forgoes a possible rewrite, never yields a wrong
	// one.
	static bool clean_set_signals(std::initializer_list<const SigSpec*> sigs) {
		pool<SigBit> seen;
		for (const SigSpec* sp : sigs)
			for (auto bit : *sp) {
				if (bit.wire == nullptr) return false;
				if (!seen.insert(bit).second) return false;
			}
		return true;
	}

	// A set of signals is a valid ConstEval "cut" to pin as free inputs only if
	// pinning them can never collide with a value ConstEval derives while
	// evaluating the cone. ConstEval::eval() re-computes and re-set()s the FULL
	// output of any combinational cell it needs: so if a pinned bit is a
	// combinational-cell output and a *sibling* output bit of that same cell
	// lies outside the cut (and is pulled into the cone), evaluating the sibling
	// re-sets the pinned bit to the cell's real value, which contradicts the
	// free value we pinned -> the ConstEval assertion in set() fires.
	//
	// A bit is a safe leaf when it is a primary input, sequential-cell output or
	// undriven (all absent from bit_to_driver, which holds combinational drivers
	// only). A combinational-cell output is safe only if that cell's entire
	// output lies within the cut. `cut` must be the union of every signal pinned
	// together before a shared eval.
	bool is_valid_consteval_cut(const SigSpec& cut) {
		pool<SigBit> cut_bits;
		for (auto bit : cut)
			if (bit.wire) cut_bits.insert(bit);
		for (auto bit : cut) {
			if (bit.wire == nullptr) return false;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) continue;   // safe leaf
			Cell* d = it->second;
			for (auto& conn : d->connections()) {
				if (!d->output(conn.first)) continue;
				for (auto ob : sigmap(conn.second))
					if (ob.wire && !cut_bits.count(ob))
						return false;
			}
		}
		return true;
	}

	// Same hazard, scoped to the cells evaluating S actually reaches (the walk
	// stops at cut bits, which already read as constants). A driver of a cut
	// bit that is never evaluated cannot clobber what we pinned, so a bus whose
	// unused sibling bits went elsewhere is still a usable cut.
	bool cut_survives_eval(const SigSpec& cut, const pool<Cell*>& evaluated) {
		for (auto bit : cut) {
			if (bit.wire == nullptr) return false;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) continue;   // safe leaf
			if (evaluated.count(it->second)) return false;
		}
		return true;
	}

	// Run candidate test vectors through a shared ConstEval. Zero + one-hots
	// lead the deck so non-PEs bail before denser patterns. For large N the
	// one-hot sweep is sampled; once a single variant remains we return early.
	PEVariant fingerprint(ConstEval& ce, const PinnedBus& pb, SigSpec S_sig, int N, int Wbits,
	                      int care_mask, const pool<Cell*>& evaluated) {
		bool full_w = (Wbits == clog2_int(N + 1));
		// SHORT infers that the saturating input is a don't-care. That is only
		// justified when the narrower width physically cannot hold the count N
		// (power-of-2 N); otherwise the RTL's value there is a real choice, and
		// dropping the high bit in emit_pe would corrupt large counts anyway.
		bool short_w = (clog2_int(N) < clog2_int(N + 1)) && (Wbits == clog2_int(N));
		bool clz_full_ok = detect_clz && full_w;
		bool ctz_full_ok = detect_ctz && full_w;
		bool clz_short_ok = detect_clz && short_w;
		bool ctz_short_ok = detect_ctz && short_w;
		bool clo_full_ok = detect_clo && full_w;
		bool cto_full_ok = detect_cto && full_w;
		bool clo_short_ok = detect_clo && short_w;
		bool cto_short_ok = detect_cto && short_w;

		auto survivors = [&]() {
			return (int)clz_full_ok + (int)ctz_full_ok + (int)clz_short_ok + (int)ctz_short_ok +
			       (int)clo_full_ok + (int)cto_full_ok + (int)clo_short_ok + (int)cto_short_ok;
		};
		auto ones_alive = [&]() {
			return clo_full_ok || cto_full_ok || clo_short_ok || cto_short_ok;
		};

		if (survivors() == 0)
			return PEVariant::NONE;

		if (!pb.ok || !cut_survives_eval(pb.free_bits, evaluated))
			return PEVariant::NONE;

		// Pinned positions cut the reachable domain, so the deck below cannot
		// see every count. When the whole domain is small, confirm the survivor
		// by enumerating it instead of trusting the thinned deck.
		bool exhaustive = pb.pinned && GetSize(pb.free_bits) <= max_exhaustive_free_bits;

		// Prefer FULL: it also pins the all-zero / all-ones result, so it is the
		// stronger contract when both widths coincide (non-power-of-2 N).
		auto finish = [&]() -> PEVariant {
			if (clz_full_ok)  return PEVariant::CLZ_FULL;
			if (ctz_full_ok)  return PEVariant::CTZ_FULL;
			if (clo_full_ok)  return PEVariant::CLO_FULL;
			if (cto_full_ok)  return PEVariant::CTO_FULL;
			if (clz_short_ok) return PEVariant::CLZ_SHORT;
			if (ctz_short_ok) return PEVariant::CTZ_SHORT;
			if (clo_short_ok) return PEVariant::CLO_SHORT;
			if (cto_short_ok) return PEVariant::CTO_SHORT;
			return PEVariant::NONE;
		};

		auto check_realized = [&](const Const& v, const Const& fv) -> bool {
			ce.push();
			ce.set(pb.free_bits, fv);
			SigSpec out = S_sig;
			SigSpec undef;
			bool ok = ce.eval(out, undef);
			// Belt and braces for the cut analysis above: if evaluation somehow
			// recomputed a pinned bit, the reading is not the one we asked for.
			if (ok && pb.pinned && ce.values_map(pb.free_bits) != SigSpec(fv))
				ok = false;
			ce.pop();
			auto kill_all = [&]() {
				clz_full_ok = ctz_full_ok = clz_short_ok = ctz_short_ok = false;
				clo_full_ok = cto_full_ok = clo_short_ok = cto_short_ok = false;
			};
			if (!ok || !out.is_fully_const()) {
				kill_all();
				return false;
			}
			// A care position that evaluates to x is a real mismatch: only
			// slots that are x in every state are don't-cares.
			int outval = 0;
			for (int i = 0; i < GetSize(out); i++) {
				if (!(care_mask & (1 << i))) continue;
				if (out[i] == State::S1) outval |= 1 << i;
				else if (out[i] != State::S0) { kill_all(); return false; }
			}

			int msb_set = const_msb(v, N, State::S1);
			int lsb_set = const_lsb(v, N, State::S1);
			int msb_clr = const_msb(v, N, State::S0);
			int lsb_clr = const_lsb(v, N, State::S0);
			bool zero = (msb_set < 0);
			bool ones = (msb_clr < 0);

			int e_clz = zero ? N : (N - 1 - msb_set);
			int e_ctz = zero ? N : lsb_set;
			int e_clo = ones ? N : (N - 1 - msb_clr);
			int e_cto = ones ? N : lsb_clr;

			e_clz &= care_mask; e_ctz &= care_mask;
			e_clo &= care_mask; e_cto &= care_mask;

			// SHORT leaves its saturating input (all-zero for CLZ/CTZ, all-ones
			// for CLO/CTO) unconstrained, so it skips that vector.
			if (clz_full_ok && outval != e_clz) clz_full_ok = false;
			if (ctz_full_ok && outval != e_ctz) ctz_full_ok = false;
			if (clz_short_ok && !zero && outval != e_clz) clz_short_ok = false;
			if (ctz_short_ok && !zero && outval != e_ctz) ctz_short_ok = false;
			if (clo_full_ok && outval != e_clo) clo_full_ok = false;
			if (cto_full_ok && outval != e_cto) cto_full_ok = false;
			if (clo_short_ok && !ones && outval != e_clo) clo_short_ok = false;
			if (cto_short_ok && !ones && outval != e_cto) cto_short_ok = false;
			return survivors() > 0;
		};

		auto check_vec = [&](const Const& want) -> bool {
			Const fv;
			Const realized = project_vector(pb, want, fv);
			return check_realized(realized, fv);
		};

		// One-hots: full sweep for small N; corners+stride sample for large N.
		pool<int> pos;
		auto addp = [&](int k) { if (k >= 0 && k < N) pos.insert(k); };
		if (N <= 32) {
			for (int k = 0; k < N; k++) addp(k);
		} else {
			for (int k = 0; k < 4; k++) { addp(k); addp(N - 1 - k); }
			int stride = std::max(1, N / 16);
			for (int k = 0; k < N; k += stride) addp(k);
		}
		vector<int> pv(pos.begin(), pos.end());
		std::sort(pv.begin(), pv.end());

		vector<Const> vs;
		vs.push_back(const_u64(0, N));
		// All-ones leads too: it is what separates a ones-run count from the
		// many cones that read as 0 across zero + one-hots, so without it those
		// would all drag a CLO/CTO candidate through the whole deck.
		if (ones_alive())
			vs.push_back(Const(std::vector<State>(N, State::S1)));
		for (int k : pv) {
			std::vector<State> bits(N, State::S0);
			bits[k] = State::S1;
			vs.push_back(Const(bits));
		}
		size_t base_end = vs.size();

		int n_checked = 0;
		int onehot_end = GetSize(vs); // zero + all-ones + one-hots
		int early_at = std::min(onehot_end, 1 + std::min(GetSize(pv), 8));
		size_t ones_deck_end = 0;
		for (size_t i = 0; i < vs.size(); i++) {
			if (!check_vec(vs[i])) return PEVariant::NONE;
			n_checked++;
			// Unique survivor after zero + a handful of one-hots is enough --
			// but one-hots barely exercise a run of ONES, so a surviving CLO/CTO
			// must first face the whole ones-domain deck.
			bool ones_checked = ones_deck_end != 0 && i + 1 >= ones_deck_end;
			if (n_checked >= early_at && survivors() == 1 &&
			    (ones_checked || !ones_alive())) {
				// A pinned bus only gets to stop early if the exhaustive proof
				// below will run; otherwise it owes the rest of the deck.
				if (!pb.pinned || exhaustive) break;
			}
			if (i + 1 != base_end) continue;

			// One-colds are the ones-domain mirror of the one-hot sweep; only pay
			// for them if a CLO/CTO candidate is still alive.
			if (ones_alive())
				for (int k : pv) {
					std::vector<State> bits(N, State::S1);
					bits[k] = State::S0;
					vs.push_back(Const(bits));
				}
			ones_deck_end = vs.size();
			// Multi-bit confirmation vectors (no zero/one-hot rebuild).
			auto multi = gen_multibit_test_vectors(N, /*dense_small_n=*/true);
			vs.insert(vs.end(), multi.begin(), multi.end());
		}

		// Only reached on a survivor, so the enumeration never runs on the
		// non-matching cones the deck already rejected in a handful of evals.
		if (exhaustive && survivors() > 0) {
			int nf = GetSize(pb.free_bits);
			for (int m = 0; m < (1 << nf); m++) {
				std::vector<State> fb(nf);
				for (int j = 0; j < nf; j++)
					fb[j] = ((m >> j) & 1) ? State::S1 : State::S0;
				Const fv(fb);
				if (!check_realized(realize_free(pb, fv), fv))
					return PEVariant::NONE;
			}
		}
		return finish();
	}

	// True iff M is the MSB suffix-OR of x (M[i] = OR_{j>=i} x[j]) on every
	// vector in the deck. x may be an internal wire; ConstEval stops at it.
	bool fingerprint_smear(const PinnedBus& pb, SigSpec M_sig, int N,
	                       const pool<Cell*>& evaluated) {
		if (!pb.ok || ce == nullptr) return false;
		if (!cut_survives_eval(pb.free_bits, evaluated)) return false;
		if (GetSize(M_sig) != N) return false;

		auto check = [&](const Const& v, const Const& fv) -> bool {
			ce->push();
			ce->set(pb.free_bits, fv);
			SigSpec out = M_sig;
			SigSpec undef;
			bool ok = ce->eval(out, undef);
			if (ok && pb.pinned && ce->values_map(pb.free_bits) != SigSpec(fv))
				ok = false;
			ce->pop();
			if (!ok || !out.is_fully_const()) return false;
			Const want = software_smear(v, N);
			auto wb = want.to_bits();
			for (int i = 0; i < N; i++) {
				State got = out[i].data;
				State exp = i < (int)wb.size() ? wb[i] : State::S0;
				if (got != exp) return false;
			}
			return true;
		};
		auto check_vec = [&](const Const& want) -> bool {
			Const fv;
			Const realized = project_vector(pb, want, fv);
			return check(realized, fv);
		};

		if (!check_vec(const_u64(0, N))) return false;
		if (!check_vec(Const(std::vector<State>(N, State::S1)))) return false;
		int stride = (N <= 32) ? 1 : std::max(1, N / 16);
		for (int k = 0; k < N; k += stride) {
			std::vector<State> bits(N, State::S0);
			bits[k] = State::S1;
			if (!check_vec(Const(bits))) return false;
		}
		if (N > 32) {
			for (int k : {0, 1, N - 2, N - 1}) {
				if (k < 0 || k >= N) continue;
				std::vector<State> bits(N, State::S0);
				bits[k] = State::S1;
				if (!check_vec(Const(bits))) return false;
			}
		}
		for (auto& v : gen_multibit_test_vectors(N, N <= 16))
			if (!check_vec(v)) return false;
		// Prefixes and one-hots miss adjacent two-hots such as 8'b00000110,
		// which still distinguish a true suffix-OR from a near-miss.
		for (int i = 0; i + 1 < N; i++) {
			std::vector<State> bits(N, State::S0);
			bits[i] = State::S1;
			bits[i + 1] = State::S1;
			if (!check_vec(Const(bits))) return false;
		}
		if (pb.pinned && GetSize(pb.free_bits) <= max_exhaustive_free_bits) {
			int nf = GetSize(pb.free_bits);
			for (int m = 0; m < (1 << nf); m++) {
				std::vector<State> fb(nf);
				for (int j = 0; j < nf; j++)
					fb[j] = ((m >> j) & 1) ? State::S1 : State::S0;
				Const fv(fb);
				if (!check(realize_free(pb, fv), fv)) return false;
			}
		}
		return true;
	}

	// x such that M = smear(x), or empty. Memoized per bus; bounded tries.
	SigSpec find_smear_source(SigSpec M_sig) {
		M_sig = sigmap(M_sig);
		if (!enable_smear || ce == nullptr) return SigSpec();
		if (smear_hit.count(M_sig)) return smear_hit.at(M_sig);
		if (smear_miss.count(M_sig)) return SigSpec();
		int N = GetSize(M_sig);
		auto miss = [&]() {
			smear_miss.insert(M_sig);
			return SigSpec();
		};
		if (N < min_input_width || N > max_input_width) return miss();

		pool<Cell*> cone_cells;
		pool<SigBit> leaf_bits;
		int st = get_cone(M_sig, cone_cells, leaf_bits,
		                  std::max(128, max_input_width * 16),
		                  max_input_width + 16);
		if (st <= 0) return miss();

		pool<SigBit> cone_bits = leaf_bits;
		for (Cell* c : cone_cells)
			for (auto& conn : c->connections())
				if (c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire) cone_bits.insert(bit);

		vector<Wire*> cands = wires_in_cone(cone_bits, [&](Wire* w) {
			if (w->width != N) return false;
			if (sigmap(SigSpec(w)) == M_sig) return false;
			return true;
		}, /*allow_const=*/true);
		// Sequential / port sources first: those are the unsmeared datapath.
		std::sort(cands.begin(), cands.end(), [&](Wire* a, Wire* b) {
			auto rank = [&](Wire* w) {
				SigSpec s = sigmap(SigSpec(w));
				bool seq = false;
				for (auto bit : s) {
					auto it = bit_to_driver.find(bit);
					if (it != bit_to_driver.end() && sequential_cells.count(it->second))
						seq = true;
				}
				if (w->port_input || seq) return 0;
				return 1;
			};
			int ra = rank(a), rb = rank(b);
			if (ra != rb) return ra < rb;
			return a->name.str() < b->name.str();
		});

		const int max_tries = 24;
		int tried = 0;
		for (Wire* w : cands) {
			if (++tried > max_tries) break;
			SigSpec x = sigmap(SigSpec(w));
			pool<SigBit> x_bits;
			for (auto bit : x)
				if (bit.wire) x_bits.insert(bit);
			if (x_bits.empty()) continue;
			pool<Cell*> evaluated;
			if (!cone_depends_only_on_T(M_sig, x_bits, &evaluated)) continue;
			PinnedBus pb = make_pinned_bus(x);
			if (!fingerprint_smear(pb, M_sig, N, evaluated)) continue;
			smear_hit[M_sig] = x;
			log("  %s: smear [%d] <- suffix-or(%s)\n",
			    log_id(module), N, log_id(w));
			return x;
		}
		return miss();
	}

	// Split `sig` through a $mux that drives its variable bits. Returns false
	// when there is no such mux or the bit mapping is incomplete.
	bool split_mux(SigSpec sig, SigBit& sel, SigSpec& sa, SigSpec& sb) {
		std::vector<int> vp;
		for (int i = 0; i < GetSize(sig); i++)
			if (sig[i].wire) vp.push_back(i);
		if (vp.empty()) return false;
		SigSpec var;
		for (int i : vp) var.append(sig[i]);
		Cell* d = sole_driver_of(var);
		if (!d) return false;
		// $pmux with a single select bit is $mux (A default, B the S=1 arm).
		if (d->type == ID($pmux) && GetSize(sigmap(d->getPort(ID::S))) != 1)
			return false;
		if (!d->type.in(ID($mux), ID($pmux))) return false;
		SigSpec Y = sigmap(d->getPort(ID::Y));
		SigSpec A = sigmap(d->getPort(ID::A)), B = sigmap(d->getPort(ID::B));
		if (GetSize(A) != GetSize(Y) || GetSize(B) != GetSize(Y)) return false;
		dict<SigBit, int> y_pos;
		for (int i = GetSize(Y) - 1; i >= 0; i--)
			if (Y[i].wire) y_pos[Y[i]] = i;
		sa = sig; sb = sig;
		for (int k = 0; k < GetSize(vp); k++) {
			auto it = y_pos.find(var[k]);
			if (it == y_pos.end()) return false;
			sa[vp[k]] = A[it->second];
			sb[vp[k]] = B[it->second];
		}
		sel = sigmap(d->getPort(ID::S))[0];
		return true;
	}

	// Walk mux layers so a clamp/pad tree does not hide a smear arm from I1.
	void hunt_smear(SigSpec sig, int budget = 16) {
		sig = sigmap(sig);
		if (GetSize(sig) < min_input_width) return;
		if (smear_hit.count(sig)) return;
		if (!smear_miss.count(sig) && GetSize(find_smear_source(sig))) return;
		if (budget <= 0) return;
		SigBit sel;
		SigSpec sa, sb;
		if (!split_mux(sig, sel, sa, sb)) return;
		hunt_smear(sa, budget - 1);
		hunt_smear(sb, budget - 1);
	}

	bool subtree_has_smear(SigSpec sig, int budget) {
		sig = sigmap(sig);
		if (smear_hit.count(sig)) return true;
		if (budget <= 0) return false;
		SigBit sel;
		SigSpec sa, sb;
		if (!split_mux(sig, sel, sa, sb)) return false;
		return subtree_has_smear(sa, budget - 1) || subtree_has_smear(sb, budget - 1);
	}

	// Const-folding wrappers: the sentinel padding below feeds constants deep
	// into the recursion, and folding them here keeps the emitted netlist small.
	SigBit emit_not(SigBit a) {
		if (!a.wire) return a == State::S1 ? State::S0 : State::S1;
		cells_added++;
		return module->Not(NEW_ID2_SUFFIX("clznot"), SigSpec(a), false, cell_src(cell));
	}

	SigSpec emit_mux(SigSpec a, SigSpec b, SigBit s) {
		if (!s.wire) return s == State::S1 ? b : a;
		if (a == b) return a;
		cells_added++;
		return module->Mux(NEW_ID2_SUFFIX("clzmux"), a, b, SigSpec(s), cell_src(cell));
	}

	SigBit emit_and(SigBit a, SigBit b) {
		if (!a.wire) return a == State::S1 ? b : SigBit(State::S0);
		if (!b.wire) return b == State::S1 ? a : SigBit(State::S0);
		cells_added++;
		return module->And(NEW_ID2_SUFFIX("peand"), SigSpec(a), SigSpec(b), false, cell_src(cell))[0];
	}

	// Recursive CLZ on a power-of-2-width input. Returns a (log2(N)+1)-bit
	// SigSpec whose MSB is 1 iff T == 0 and whose lower bits are the leading-
	// zeros count for nonzero T.
	SigSpec emit_clz_pow2(SigSpec T, int N) {
		log_assert(N >= 1 && (N & (N - 1)) == 0);
		if (N == 1)
			return SigSpec(emit_not(T[0]));
		int N2 = N / 2;
		SigSpec hi = T.extract(N2, N2);
		SigSpec lo = T.extract(0, N2);
		SigSpec clz_hi = emit_clz_pow2(hi, N2);
		SigSpec clz_lo = emit_clz_pow2(lo, N2);
		int W1 = GetSize(clz_hi);
		SigBit hi_zero = clz_hi[W1 - 1];
		SigBit lo_zero = clz_lo[W1 - 1];

		// pad_clz_hi (W bits): {1'b0, clz_hi}. When the mux selects this arm
		// (hi != 0), clz_hi's MSB is guaranteed 0, so the top two bits of the
		// result are 0.
		SigSpec pad_clz_hi = clz_hi;
		pad_clz_hi.append(SigSpec(State::S0));

		// pad_clz_lo (W bits): logical equivalent of N/2 + clz_lo. The MSB
		// becomes lo_zero (= 1 iff x == 0); the next bit becomes ~lo_zero (=
		// 1 iff lo != 0, signalling result in [N/2, N-1]); the remaining bits
		// are clz_lo[W1-2:0].
		SigBit lo_nonzero = emit_not(lo_zero);

		SigSpec pad_clz_lo;
		if (W1 >= 2)
			pad_clz_lo.append(clz_lo.extract(0, W1 - 1));
		pad_clz_lo.append(lo_nonzero);
		pad_clz_lo.append(lo_zero);

		// $mux: Y = S ? B : A. We want Y = hi_zero ? pad_clz_lo : pad_clz_hi.
		return emit_mux(pad_clz_hi, pad_clz_lo, hi_zero);
	}

	// msb_index(T)+1 on a power-of-2-width input (0 when T is 0). Result
	// width is log2(N)+1, covering the saturating value N.
	SigSpec emit_leadone_pow2(SigSpec T, int N) {
		log_assert(N >= 1 && (N & (N - 1)) == 0);
		if (N == 1)
			return SigSpec(T[0]);
		int N2 = N / 2;
		SigSpec c_hi = emit_leadone_pow2(T.extract(N2, N2), N2);
		SigSpec c_lo = emit_leadone_pow2(T.extract(0, N2), N2);
		int W1 = GetSize(c_hi);
		SigBit hi_nz;
		{
			// OR-reduce: any bit of c_hi set means the high half is nonzero.
			SigSpec red = c_hi;
			cells_added++;
			hi_nz = module->ReduceOr(NEW_ID2_SUFFIX("lonz"), red, false, cell_src(cell));
		}
		int W = W1 + 1;
		SigSpec lo_pad = c_lo;
		lo_pad.append(SigSpec(State::S0));
		SigSpec hi_pad = c_hi;
		hi_pad.append(SigSpec(State::S0));
		SigSpec hi_sum = module->Add(NEW_ID2_SUFFIX("loadd"), hi_pad,
		                             SigSpec(Const(N2, W)), false, cell_src(cell));
		cells_added++;
		return emit_mux(lo_pad, hi_sum, hi_nz);
	}

	// msb_index(T)+1 for arbitrary width, clog2(N+1) bits. Pad MSBs with 0
	// so a non-power-of-2 T keeps the same count (no subtract on the path).
	SigSpec emit_leadone_full(SigSpec T, int N) {
		T = sigmap(T);
		auto it = leadone_cache.find(T);
		if (it != leadone_cache.end()) return it->second;
		int Np = 1;
		while (Np < N) Np *= 2;
		SigSpec padded = T;
		while (GetSize(padded) < Np)
			padded.append(SigSpec(State::S0));
		SigSpec full = emit_leadone_pow2(padded, Np);
		int W = clog2_int(N + 1);
		if (GetSize(full) > W)
			full = full.extract(0, W);
		while (GetSize(full) < W)
			full.append(SigSpec(State::S0));
		leadone_cache[T] = full;
		return full;
	}

	// CLZ of arbitrary-width T, returning a (clog2(N+1))-bit result.
	SigSpec emit_clz_full(SigSpec T, int N) {
		int Np = 1;
		while (Np < N) Np *= 2;
		int pad_amount = Np - N;
		SigSpec padded;
		// Pad *below* T with a sentinel 1 at the top of the pad: an all-zero T
		// then reads back as exactly N leading zeros, so no "- pad" subtract
		// (a full ripple on the critical path) is needed.
		for (int i = 0; i + 1 < pad_amount; i++)
			padded.append(SigSpec(State::S0));
		if (pad_amount > 0)
			padded.append(SigSpec(State::S1));
		padded.append(T);
		SigSpec clz_padded = emit_clz_pow2(padded, Np); // log2(Np)+1 bits
		int W = clog2_int(N + 1);
		if (GetSize(clz_padded) >= W)
			return clz_padded.extract(0, W);
		SigSpec out = clz_padded;
		while (GetSize(out) < W) out.append(SigSpec(State::S0));
		return out;
	}

	// CTZ via bit-reversal of T followed by CLZ.
	SigSpec emit_ctz_full(SigSpec T, int N) {
		SigSpec rev;
		for (int i = N - 1; i >= 0; i--)
			rev.append(T[i]);
		return emit_clz_full(rev, N);
	}

	// ~T, shared by every CLO/CTO network built on the same bus (const bits fold).
	SigSpec emit_inv(SigSpec T) {
		auto it = inverted_cache.find(T);
		if (it != inverted_cache.end()) return it->second;
		SigSpec inv;
		for (auto bit : T) inv.append(SigSpec(emit_not(bit)));
		inverted_cache[T] = inv;
		return inv;
	}

	SigSpec emit_pe_sig(PEVariant v, SigSpec T_sig, int N, int out_width) {
		T_sig = sigmap(T_sig);
		// I1: cto_full(smear(x)) == msb_index(x)+1, and clz_full(smear(x)) ==
		// clz_full(x). Looked up from the pre-mutation cache so ConstEval is
		// not consulted after the netlist starts changing.
		if (enable_smear && smear_hit.count(T_sig)) {
			SigSpec x = smear_hit.at(T_sig);
			int Nx = GetSize(x);
			if (Nx == N) {
				SigSpec full;
				if (v == PEVariant::CTO_FULL || v == PEVariant::CTO_SHORT) {
					full = emit_leadone_full(x, N);
					smears_collapsed++;
				} else if (v == PEVariant::CLZ_FULL || v == PEVariant::CLZ_SHORT) {
					full = emit_clz_full(x, N);
					smears_collapsed++;
				}
				if (GetSize(full)) {
					if (GetSize(full) > out_width)
						full = full.extract(0, out_width);
					while (GetSize(full) < out_width)
						full.append(SigSpec(State::S0));
					return full;
				}
			}
		}

		auto key = std::make_pair(T_sig, variant_net_key(v));
		SigSpec full;
		auto it = pe_sig_cache.find(key);
		if (it != pe_sig_cache.end()) {
			full = it->second;
		} else if (enable_smear && smear_peel > 0 && subtree_has_smear(T_sig, smear_peel)) {
			// Hoisting may stop at a clamp/pad mux; peel so a smear arm still
			// takes the I1 path while the other arm keeps a normal encoder.
			SigBit sel;
			SigSpec sa, sb;
			if (split_mux(T_sig, sel, sa, sb)) {
				smear_peel--;
				SigSpec ea = emit_pe_sig(v, sa, N, out_width);
				SigSpec eb = emit_pe_sig(v, sb, N, out_width);
				smear_peel++;
				full = emit_mux(ea, eb, sel);
				pe_sig_cache[key] = full;
			}
		}
		if (GetSize(full) == 0) {
			if (it == pe_sig_cache.end()) {
				SigSpec run = variant_counts_ones(v) ? emit_inv(T_sig) : T_sig;
				full = variant_is_leading(v) ? emit_clz_full(run, N) : emit_ctz_full(run, N);
				pe_sig_cache[key] = full;
			}
		}

		// Truncation covers the SHORT variants: their narrower width only ever
		// drops the saturating value's high bit. Explicitly dropping the MSB
		// would be wrong for non-power-of-2 N, where SHORT and FULL are equally
		// wide and every value needs all the bits.
		if (GetSize(full) > out_width)
			full = full.extract(0, out_width);
		while (GetSize(full) < out_width)
			full.append(SigSpec(State::S0));
		return full;
	}

	SigSpec emit_pe(PEVariant v, Wire* T_wire, int N, int out_width) {
		return emit_pe_sig(v, sigmap(SigSpec(T_wire)), N, out_width);
	}

	// ------------------------------------------------------------------
	// Thermometer domain: the same run that the encoder counts, kept as a
	// mask instead of a binary code. run_prefix[i] = "bit i is still inside the
	// scanned run" = (i < count), built by a log-depth Kogge-Stone prefix-AND.
	// This is what lets shift consumers of the count bypass the encoder.
	// ------------------------------------------------------------------
	SigSpec emit_run_prefix(PEVariant v, Wire* T_wire, int N) {
		auto key = std::make_pair(T_wire, (int)v);
		auto it = pe_prefix_cache.find(key);
		if (it != pe_prefix_cache.end()) return it->second;

		// CLO/CTO scan a run of ones, CLZ/CTZ a run of zeros; CL* scan from MSB.
		SigSpec T = sigmap(SigSpec(T_wire));
		SigSpec src = variant_counts_ones(v) ? T : emit_inv(T);
		std::vector<SigBit> cur(N);
		for (int j = 0; j < N; j++)
			cur[j] = variant_is_leading(v) ? src[N - 1 - j] : src[j];
		for (int d = 1; d < N; d *= 2) {
			std::vector<SigBit> next = cur;
			for (int j = d; j < N; j++)
				next[j] = emit_and(cur[j], cur[j - d]);
			cur.swap(next);
		}
		SigSpec out;
		for (int j = 0; j < N; j++) out.append(SigSpec(cur[j]));
		pe_prefix_cache[key] = out;
		return out;
	}

	// mask[i] = (i < count), zero-extended past the input width (count <= N).
	SigSpec emit_pe_mask(PEVariant v, Wire* T_wire, int N, int W) {
		SigSpec pre = emit_run_prefix(v, T_wire, N);
		SigSpec mask;
		for (int i = 0; i < W; i++)
			mask.append(i < N ? SigSpec(pre[i]) : SigSpec(State::S0));
		return mask;
	}

	// (1 << count)[i] == (count == i) == mask[i-1] & ~mask[i], with mask[-1] = 1.
	SigSpec emit_pe_onehot(PEVariant v, Wire* T_wire, int N, int W) {
		SigSpec pre = emit_run_prefix(v, T_wire, N);
		SigSpec oh;
		for (int i = 0; i < W; i++) {
			SigBit lo = (i == 0) ? SigBit(State::S1)
			                     : (i - 1 < N ? SigBit(pre[i - 1]) : SigBit(State::S0));
			SigBit hi = (i < N) ? SigBit(pre[i]) : SigBit(State::S0);
			oh.append(SigSpec(emit_and(lo, emit_not(hi))));
		}
		return oh;
	}

	// ------------------------------------------------------------------
	// Encode/decode round-trip collapse.
	//
	// Once `count` is a matched CLZ/CTZ/CLO/CTO, shifting by it just decodes
	// what the encoder encoded. With mask = (1 << count) - 1 taken straight
	// from the thermometer above, for W-bit truncating arithmetic:
	//
	//   (a >> count) << count        ==  a & ~mask     (align down)
	//   ((a >> count) + 1) << count  ==  (a | mask) + 1 (align up)
	//   1 << count                   ==  one-hot(count)
	//
	// All three hold for every count (including count >= W, where mask is all
	// ones), so no range side condition is needed. They keep the critical path
	// in the mask domain: two barrel shifters plus the binary encode collapse
	// to a prefix-AND and one bitwise op.
	// ------------------------------------------------------------------

	dict<SigBit, pool<Cell*>> bit_to_readers;
	bool readers_indexed = false;

	void build_reader_index() {
		if (readers_indexed) return;
		readers_indexed = true;
		for (auto c : module->cells())
			for (auto& conn : c->connections()) {
				if (!c->input(conn.first)) continue;
				for (auto bit : sigmap(conn.second))
					if (bit.wire) bit_to_readers[bit].insert(c);
			}
	}

	// Sole cell whose full output is exactly `sig` (nullptr if none).
	Cell* whole_driver(const SigSpec& sig) {
		pool<Cell*> drivers;
		for (auto bit : sig) {
			if (!bit.wire) return nullptr;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) return nullptr;
			drivers.insert(it->second);
		}
		if (GetSize(drivers) != 1) return nullptr;
		Cell* d = *drivers.begin();
		for (auto& conn : d->connections())
			if (d->output(conn.first))
				return sigmap(conn.second) == sig ? d : nullptr;
		return nullptr;
	}

	// Sole cell driving every bit of `sig`; unlike whole_driver its output may
	// be wider (unused high bits pruned off a mux, resized buses).
	Cell* sole_driver_of(const SigSpec& sig) {
		Cell* d = nullptr;
		for (auto bit : sig) {
			if (!bit.wire) return nullptr;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) return nullptr;
			if (d && d != it->second) return nullptr;
			d = it->second;
		}
		return d;
	}

	static bool is_unsigned_shift(Cell* c, IdString type, int W) {
		return c->type == type &&
		       !c->getParam(ID::A_SIGNED).as_bool() && !c->getParam(ID::B_SIGNED).as_bool() &&
		       c->getParam(ID::A_WIDTH).as_int() == W && c->getParam(ID::Y_WIDTH).as_int() == W;
	}

	static bool is_const_one(const SigSpec& s) {
		if (!s.is_fully_const()) return false;
		Const c = s.as_const();
		if (!c.is_fully_def()) return false;
		auto bits = c.to_bits();
		for (int i = 0; i < GetSize(bits); i++)
			if (bits[i] != (i == 0 ? State::S1 : State::S0)) return false;
		return GetSize(bits) > 0;
	}

	// Replace `c`'s output with `repl` by re-pointing its Y to a fresh wire.
	void steal_output(Cell* c, IdString port, const SigSpec& out, const SigSpec& repl) {
		Wire* dangling = module->addWire(NEW_ID2_SUFFIX("dangling"), GetSize(out));
		c->setPort(port, dangling);
		module->connect(out, repl);
	}

	bool has_live_reader(Wire* S_wire, const pool<Cell*>& dead) {
		build_reader_index();
		if (S_wire->port_output) return true;
		for (auto bit : sigmap(SigSpec(S_wire))) {
			auto it = bit_to_readers.find(bit);
			if (it == bit_to_readers.end()) continue;
			for (Cell* c : it->second)
				if (!dead.count(c)) return true;
		}
		return false;
	}

	void collapse_roundtrips(const Rewrite& r, pool<Cell*>& dead_readers) {
		build_reader_index();
		SigSpec S_sig = sigmap(SigSpec(r.S_wire));
		pool<Cell*> readers;
		for (auto bit : S_sig) {
			auto it = bit_to_readers.find(bit);
			if (it != bit_to_readers.end())
				for (Cell* c : it->second) readers.insert(c);
		}
		vector<Cell*> shls;
		for (Cell* c : readers)
			if (c->type == ID($shl)) shls.push_back(c);
		std::sort(shls.begin(), shls.end(),
		          [](Cell* a, Cell* b) { return a->name.str() < b->name.str(); });

		for (Cell* shl : shls) {
			if (shl->getParam(ID::A_SIGNED).as_bool() || shl->getParam(ID::B_SIGNED).as_bool())
				continue;
			if (sigmap(shl->getPort(ID::B)) != S_sig) continue;
			int W = shl->getParam(ID::Y_WIDTH).as_int();
			SigSpec shl_A = sigmap(shl->getPort(ID::A));
			SigSpec shl_Y = sigmap(shl->getPort(ID::Y));
			cell = shl;

			if (is_const_one(shl_A)) {
				steal_output(shl, ID::Y, shl_Y, emit_pe_onehot(r.variant, r.T_wire, r.N, W));
				log("  %s: 1 << %s -> one-hot(%s) [decode of %s]\n", log_id(module),
				    log_id(r.S_wire), log_id(r.T_wire), variant_name(r.variant));
				dead_readers.insert(shl);
				roundtrips_collapsed++;
				continue;
			}
			if (shl->getParam(ID::A_WIDTH).as_int() != W) continue;

			// Peel an optional "+ 1" between the two shifts (align-up form).
			SigSpec base = shl_A;
			bool plus_one = false;
			Cell* add = whole_driver(base);
			if (add && add->type == ID($add) &&
			    !add->getParam(ID::A_SIGNED).as_bool() && !add->getParam(ID::B_SIGNED).as_bool() &&
			    add->getParam(ID::A_WIDTH).as_int() == W &&
			    add->getParam(ID::B_WIDTH).as_int() == W &&
			    add->getParam(ID::Y_WIDTH).as_int() == W) {
				SigSpec aa = sigmap(add->getPort(ID::A)), bb = sigmap(add->getPort(ID::B));
				if (is_const_one(bb)) { base = aa; plus_one = true; }
				else if (is_const_one(aa)) { base = bb; plus_one = true; }
			}

			Cell* shr = whole_driver(base);
			if (!shr || !is_unsigned_shift(shr, ID($shr), W)) continue;
			if (sigmap(shr->getPort(ID::B)) != S_sig) continue;

			SigSpec a = sigmap(shr->getPort(ID::A));
			SigSpec mask = emit_pe_mask(r.variant, r.T_wire, r.N, W);
			SigSpec repl;
			if (plus_one) {
				SigSpec ored = module->Or(NEW_ID2_SUFFIX("peupor"), a, mask, false, cell_src(cell));
				repl = module->Add(NEW_ID2_SUFFIX("peupinc"), ored, SigSpec(Const(1, W)), false, cell_src(cell));
				cells_added += 2;
			} else {
				SigSpec nmask = module->Not(NEW_ID2_SUFFIX("pedninv"), mask, false, cell_src(cell));
				repl = module->And(NEW_ID2_SUFFIX("pednand"), a, nmask, false, cell_src(cell));
				cells_added += 2;
			}
			steal_output(shl, ID::Y, shl_Y, repl);
			log("  %s: align-%s round-trip on %s -> mask(%s) [%s]\n", log_id(module),
			    plus_one ? "up" : "down", log_id(r.S_wire), log_id(r.T_wire),
			    variant_name(r.variant));
			// Best-effort liveness hint only (they may have other readers).
			dead_readers.insert(shl);
			dead_readers.insert(shr);
			roundtrips_collapsed++;
		}
	}

	// Off the combinational path: every bit is const, a port, or sequential.
	bool is_offpath_operand(SigSpec s) {
		s = sigmap(s);
		if (s.is_fully_const()) return true;
		for (auto bit : s) {
			if (!bit.wire) continue;
			if (input_port_bits.count(bit)) continue;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) continue;
			if (sequential_cells.count(it->second)) continue;
			return false;
		}
		return true;
	}

	static bool pred_u(IdString t, uint64_t a, uint64_t b) {
		if (t == ID($lt)) return a < b;
		if (t == ID($le)) return a <= b;
		if (t == ID($gt)) return a > b;
		if (t == ID($ge)) return a >= b;
		return false;
	}

	static uint64_t const_low(const Const& c, int N) {
		uint64_t v = 0;
		auto bits = c.to_bits();
		int n = std::min(N, 64);
		for (int i = 0; i < n; i++)
			if (i < (int)bits.size() && bits[i] == State::S1)
				v |= 1ull << i;
		return v;
	}

	static uint64_t smear_u(int m) {
		if (m <= 0) return 0;
		if (m >= 64) return ~0ull;
		return (1ull << m) - 1;
	}

	SigSpec emit_pred(IdString t, SigSpec a, SigSpec b) {
		cells_added++;
		if (t == ID($lt)) return module->Lt(NEW_ID2_SUFFIX("smearcmp"), a, b, false, cell_src(cell));
		if (t == ID($le)) return module->Le(NEW_ID2_SUFFIX("smearcmp"), a, b, false, cell_src(cell));
		if (t == ID($gt)) return module->Gt(NEW_ID2_SUFFIX("smearcmp"), a, b, false, cell_src(cell));
		return module->Ge(NEW_ID2_SUFFIX("smearcmp"), a, b, false, cell_src(cell));
	}

	// Search a (predicate, const threshold) pair that agrees with orig_pred
	// on every smear of an N-bit x. Returns true and writes new_pred / t.
	bool find_const_threshold(IdString orig_pred, uint64_t k, int N,
	                          IdString& new_pred, int& t_out) {
		for (IdString np : {ID($lt), ID($le), ID($gt), ID($ge)}) {
			for (int t = 0; t <= N + 1; t++) {
				bool ok = true;
				for (int m = 0; m <= N && ok; m++)
					if (pred_u(orig_pred, smear_u(m), k) != pred_u(np, (uint64_t)m, (uint64_t)t))
						ok = false;
				if (ok) { new_pred = np; t_out = t; return true; }
			}
		}
		return false;
	}

	// leadone(x) vs leadone(K) with some predicate, checked on the deck.
	bool find_reg_threshold(IdString orig_pred, const PinnedBus& pb_x, int Nx,
	                        const PinnedBus& pb_k, int Nk, IdString& new_pred) {
		auto check_pair = [&](const Const& xv, const Const& kv, IdString np) {
			int m = software_leadone(xv, Nx);
			int mk = software_leadone(kv, Nk);
			return pred_u(orig_pred, smear_u(m), const_low(kv, Nk))
			    == pred_u(np, (uint64_t)m, (uint64_t)mk);
		};
		auto deck = [&](int n) {
			vector<Const> vs;
			vs.push_back(const_u64(0, n));
			vs.push_back(Const(std::vector<State>(n, State::S1)));
			int stride = (n <= 16) ? 1 : std::max(1, n / 8);
			for (int i = 0; i < n; i += stride) {
				std::vector<State> bits(n, State::S0);
				bits[i] = State::S1;
				vs.push_back(Const(bits));
			}
			for (auto& v : gen_multibit_test_vectors(n, n <= 12))
				vs.push_back(v);
			return vs;
		};
		auto xs = deck(Nx), ks = deck(Nk);
		for (IdString np : {ID($lt), ID($le), ID($gt), ID($ge)}) {
			bool ok = true;
			for (auto& xv0 : xs) {
				Const fx;
				Const xv = project_vector(pb_x, xv0, fx);
				for (auto& kv0 : ks) {
					Const fk;
					Const kv = project_vector(pb_k, kv0, fk);
					if (!check_pair(xv, kv, np)) { ok = false; break; }
				}
				if (!ok) break;
			}
			if (ok) { new_pred = np; return true; }
		}
		return false;
	}

	// Emit smear(x) ? K as leadone(x) ? t(K), after the software identity
	// search agrees on every m in 0..N (const K) or the hypothesized deck
	// (register K). Returns empty when no equivalent pair exists.
	SigSpec emit_narrow_smear_cmp(IdString orig, bool a_smear, SigSpec x, SigSpec k) {
		int Nx = GetSize(x);
		int Nk = GetSize(k);
		if (Nx < 1 || Nx > 64 || Nk > 64) return SigSpec();
		IdString np;
		int t = 0;
		bool k_const = k.is_fully_const();
		if (k_const) {
			if (!find_const_threshold(orig, const_low(k.as_const(), Nk), Nx, np, t))
				return SigSpec();
		} else {
			PinnedBus pb_x = make_pinned_bus(x);
			PinnedBus pb_k = make_pinned_bus(k);
			if (!pb_x.ok || !pb_k.ok) return SigSpec();
			if (!clean_set_signals({&pb_x.free_bits, &pb_k.free_bits})) return SigSpec();
			if (!find_reg_threshold(orig, pb_x, Nx, pb_k, Nk, np)) return SigSpec();
		}
		SigSpec n_x = emit_leadone_full(x, Nx);
		SigSpec n_k = k_const ? SigSpec(Const(t, GetSize(n_x)))
		                      : emit_leadone_full(k, Nk);
		int W = std::max(GetSize(n_x), GetSize(n_k));
		while (GetSize(n_x) < W) n_x.append(SigSpec(State::S0));
		while (GetSize(n_k) < W) n_k.append(SigSpec(State::S0));
		SigSpec lhs = a_smear ? n_x : n_k;
		SigSpec rhs = a_smear ? n_k : n_x;
		return emit_pred(np, lhs, rhs);
	}

	struct CmpRewrite { SigSpec y; bool narrowed; };

	// Narrow a smear operand, or peel a mux so a smear arm underneath can be.
	CmpRewrite rewrite_smear_cmp(IdString orig, SigSpec A, SigSpec B, int budget) {
		A = sigmap(A);
		B = sigmap(B);
		SigSpec xA = smear_hit.count(A) ? smear_hit.at(A) : SigSpec();
		SigSpec xB = smear_hit.count(B) ? smear_hit.at(B) : SigSpec();
		bool a_smear = GetSize(xA) > 0;
		bool b_smear = GetSize(xB) > 0;
		if (a_smear != b_smear) {
			SigSpec x = a_smear ? xA : xB;
			SigSpec k = a_smear ? B : A;
			// Const K is muxpush's job and a leadone tree on a const-compare
			// arm has been a net loss on the clamp-floor family. Register/port
			// K cannot be pushed, so that is the I2 case that pays.
			if (is_offpath_operand(k) && !k.is_fully_const()) {
				SigSpec y = emit_narrow_smear_cmp(orig, a_smear, x, k);
				if (GetSize(y)) return {y, true};
			}
		}
		if (budget <= 0) return {SigSpec(), false};
		// Muxpush already distributes const-K compares; peeling those here
		// only duplicates them. Register/port K cannot be pushed, so peel
		// just far enough to reach a smear arm.
		SigBit sel;
		SigSpec sa, sb;
		if (!B.is_fully_const() && is_offpath_operand(B) &&
		    split_mux(A, sel, sa, sb) && subtree_has_smear(A, budget)) {
			CmpRewrite ta = rewrite_smear_cmp(orig, sa, B, budget - 1);
			CmpRewrite tb = rewrite_smear_cmp(orig, sb, B, budget - 1);
			if (!ta.narrowed && !tb.narrowed) return {SigSpec(), false};
			if (!GetSize(ta.y)) ta.y = emit_pred(orig, sa, B);
			if (!GetSize(tb.y)) tb.y = emit_pred(orig, sb, B);
			return {emit_mux(ta.y, tb.y, sel), true};
		}
		if (!A.is_fully_const() && is_offpath_operand(A) &&
		    split_mux(B, sel, sa, sb) && subtree_has_smear(B, budget)) {
			CmpRewrite ta = rewrite_smear_cmp(orig, A, sa, budget - 1);
			CmpRewrite tb = rewrite_smear_cmp(orig, A, sb, budget - 1);
			if (!ta.narrowed && !tb.narrowed) return {SigSpec(), false};
			if (!GetSize(ta.y)) ta.y = emit_pred(orig, A, sa);
			if (!GetSize(tb.y)) tb.y = emit_pred(orig, A, sb);
			return {emit_mux(ta.y, tb.y, sel), true};
		}
		return {SigSpec(), false};
	}

	void collapse_smear_compares(pool<Cell*>& dead_readers) {
		if (!enable_smear) return;
		build_reader_index();
		vector<Cell*> cmps;
		for (auto c : module->cells()) {
			if (!c->type.in(ID($lt), ID($le), ID($gt), ID($ge))) continue;
			if (c->getParam(ID::A_SIGNED).as_bool() || c->getParam(ID::B_SIGNED).as_bool())
				continue;
			cmps.push_back(c);
		}
		std::sort(cmps.begin(), cmps.end(),
		          [](Cell* a, Cell* b) { return a->name.str() < b->name.str(); });

		for (Cell* cmp : cmps) {
			SigSpec A = sigmap(cmp->getPort(ID::A));
			SigSpec B = sigmap(cmp->getPort(ID::B));
			SigSpec Y = sigmap(cmp->getPort(ID::Y));
			hunt_smear(A);
			hunt_smear(B);
			cell = cmp;
			CmpRewrite rw = rewrite_smear_cmp(cmp->type, A, B, 4);
			if (!rw.narrowed || !GetSize(rw.y)) continue;
			steal_output(cmp, ID::Y, Y, rw.y);
			log("  %s: %s via smear narrowed to encoded-domain compare\n",
			    log_id(module), log_id(cmp->type));
			dead_readers.insert(cmp);
			compares_narrowed++;
		}
	}

	// ------------------------------------------------------------------
	// Encode before select.
	//
	// pe(mux(s, a, b)) == mux(s, pe(a), pe(b)) for any pe, so when the select is
	// itself computed *from* the mux data (a compare / clamp that feeds back
	// into the select), the encoder can run on the early arms in parallel with
	// the select instead of queueing behind it. Constant arms fold to constants,
	// so clamp-to-literal trees mostly disappear. The push only pays off in that
	// data-dependent-select case, hence the cone check, and it duplicates the
	// encoder per arm, hence the arm cap.
	// ------------------------------------------------------------------

	struct MuxArm {
		bool is_leaf = true;
		SigSpec leaf;
		SigBit sel;
		std::shared_ptr<MuxArm> a, b;   // a = sel 0 arm, b = sel 1 arm
	};

	std::shared_ptr<MuxArm> build_mux_arms(SigSpec sig, int& split_budget,
	                                       pool<SigBit>& sel_bits, pool<SigBit>& leaf_bits_out) {
		auto n = std::make_shared<MuxArm>();
		if (split_budget > 0) {
			std::vector<int> vp;
			for (int i = 0; i < GetSize(sig); i++)
				if (sig[i].wire) vp.push_back(i);
			SigSpec var;
			for (int i : vp) var.append(sig[i]);
			Cell* d = vp.empty() ? nullptr : sole_driver_of(var);
			if (d && d->type == ID($mux)) {
				// Track each arm bit through the mux's own output positions, so
				// a mux whose extra output bits went elsewhere still splits.
				SigSpec Y = sigmap(d->getPort(ID::Y));
				SigSpec A = sigmap(d->getPort(ID::A)), B = sigmap(d->getPort(ID::B));
				dict<SigBit, int> y_pos;
				for (int i = GetSize(Y) - 1; i >= 0; i--)
					if (Y[i].wire) y_pos[Y[i]] = i;
				bool ok = GetSize(A) == GetSize(Y) && GetSize(B) == GetSize(Y);
				SigSpec sa = sig, sb = sig;
				for (int k = 0; ok && k < GetSize(vp); k++) {
					auto it = y_pos.find(var[k]);
					if (it == y_pos.end()) { ok = false; break; }
					sa[vp[k]] = A[it->second];
					sb[vp[k]] = B[it->second];
				}
				if (ok) {
					split_budget--;
					n->is_leaf = false;
					n->sel = sigmap(d->getPort(ID::S))[0];
					sel_bits.insert(n->sel);
					n->a = build_mux_arms(sa, split_budget, sel_bits, leaf_bits_out);
					n->b = build_mux_arms(sb, split_budget, sel_bits, leaf_bits_out);
					return n;
				}
			}
		}
		n->leaf = sig;
		for (auto bit : sig)
			if (bit.wire) leaf_bits_out.insert(bit);
		return n;
	}

	// Bounded backward reachability from `from` to any bit in `targets`.
	bool cone_reaches(const SigSpec& from, const pool<SigBit>& targets, int budget) {
		pool<SigBit> visited;
		std::queue<SigBit> q;
		for (auto bit : sigmap(from))
			if (bit.wire && visited.insert(bit).second) q.push(bit);
		while (!q.empty()) {
			if (budget-- <= 0) return false;
			SigBit bit = q.front();
			q.pop();
			if (targets.count(bit)) return true;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) continue;
			Cell* d = it->second;
			if (sequential_cells.count(d)) continue;
			for (auto& conn : d->connections()) {
				if (!d->input(conn.first)) continue;
				for (auto in_bit : sigmap(conn.second))
					if (in_bit.wire && visited.insert(in_bit).second) q.push(in_bit);
			}
		}
		return false;
	}

	SigSpec emit_pe_arms(const std::shared_ptr<MuxArm>& n, PEVariant v, int N, int out_width) {
		if (n->is_leaf) return emit_pe_sig(v, n->leaf, N, out_width);
		return emit_mux(emit_pe_arms(n->a, v, N, out_width),
		                emit_pe_arms(n->b, v, N, out_width), n->sel);
	}

	void discover_smear_leaves(const std::shared_ptr<MuxArm>& n) {
		if (!n) return;
		if (n->is_leaf) {
			hunt_smear(n->leaf);
			return;
		}
		discover_smear_leaves(n->a);
		discover_smear_leaves(n->b);
	}

	int max_push_arms = 24;

	// Returns the pushed encoder, or an empty SigSpec when the push does not apply.
	SigSpec try_push_encoder(const Rewrite& r) {
		// The arm cap below is the only guard on the duplication, and the cone
		// walk is how the arms behind the bus get measured at all. A truncated
		// walk overran on exactly that logic, so there is nothing to weigh the
		// copies against: hoist only above a select tree walked in full.
		if (r.cone_partial) return SigSpec();
		// Every arm gets its own encoder, so bound the duplicated bit count too.
		int arm_cap = std::min(max_push_arms, std::max(2, 512 / std::max(r.N, 1)));
		if (arm_cap < 2) return SigSpec();
		int split_budget = arm_cap - 1;
		pool<SigBit> sel_bits, leaf_bits;
		auto root = build_mux_arms(sigmap(SigSpec(r.T_wire)), split_budget, sel_bits, leaf_bits);
		if (root->is_leaf) return SigSpec();

		SigSpec sels;
		for (auto bit : sel_bits) sels.append(SigSpec(bit));
		if (!cone_reaches(sels, leaf_bits, 4096)) return SigSpec();

		int before = cells_added;
		SigSpec pushed = emit_pe_arms(root, r.variant, r.N, r.Wbits);
		log("  %s: %s hoisted above %d mux select(s) on %s (+%d cell(s))\n",
		    log_id(module), variant_name(r.variant), arm_cap - 1 - split_budget,
		    log_id(r.T_wire), cells_added - before);
		return pushed;
	}

	// ------------------------------------------------------------------
	// Round-robin (rotated priority) detection + rewrite.
	//
	// A round-robin arbiter grants the first set request bit scanning
	// *upward* (increasing index, wrapping) starting just after a stored
	// pointer `s` (= idx_last):
	//
	//   grant    = anyreq ? (first set bit at index > s, else first set
	//                        bit overall) : 0
	//   idx_next = anyreq ? grant : s
	//
	// RTL usually spells this as a DEPTH-iteration loop that walks `idx`
	// downward from idx_last with wraparound and keeps the last hit, which
	// elaborates into a serial mux/shift chain of depth ~DEPTH. The rewrite
	// below is log-depth:
	//
	//   above[i] = (i > s)          (per-bit threshold mask)
	//   mask_hi  = req & above
	//   grant    = anyreq ? (|mask_hi ? ctz(mask_hi) : ctz(req)) : 0
	//
	// where ctz() reuses the log-depth CTZ network. For power-of-2 DEPTH the
	// rewrite is fully combinationally equivalent for every pointer value;
	// for non-power-of-2 DEPTH it is equivalent for every *reachable* pointer
	// (idx_last only ever holds a valid index in [0,DEPTH)), which is the
	// range the fingerprint checks. Detection therefore sweeps s over
	// [0,DEPTH) only.
	// ------------------------------------------------------------------

	// kind: 0 = grant, 1 = idx_next.
	int rr_expected(const Const& reqv, int s, int N, int W, int kind) {
		auto bits = reqv.to_bits();
		int lo_all = -1, lo_hi = -1;
		for (int i = 0; i < N; i++) {
			bool set = (i < (int)bits.size() && bits[i] == State::S1);
			if (!set) continue;
			if (lo_all < 0) lo_all = i;
			if (i > s && lo_hi < 0) lo_hi = i;
		}
		bool anyreq = (lo_all >= 0);
		int gsel = (lo_hi >= 0) ? lo_hi : (lo_all >= 0 ? lo_all : 0);
		int val = kind == 0 ? (anyreq ? gsel : 0)
		                    : (anyreq ? gsel : s);
		return val & ((W >= 31) ? -1 : ((1 << W) - 1));
	}

	// Returns matched kind (0 grant, 1 idx_next), or -1 for no match.
	// Empty/multi-bit vectors are swept over sampled starts (rotation matters);
	// one-hots are s-independent so they run once at s=0 only.
	int fingerprint_rr(ConstEval& ce, SigSpec req_sig, SigSpec start_sig, SigSpec S_sig,
	                   int N, int W) {
		if (!clean_set_signals({&req_sig, &start_sig}))
			return -1;
		SigSpec cut = req_sig;
		cut.append(start_sig);
		if (!is_valid_consteval_cut(cut))
			return -1;

		bool ok0 = true, ok1 = true;
		auto starts = rr_start_samples(N);
		int checks = 0;

		auto check = [&](const Const& rv, int s) -> bool {
			ce.push();
			ce.set(req_sig, rv);
			ce.set(start_sig, Const(s, W));
			SigSpec out = S_sig, undef;
			bool ok = ce.eval(out, undef);
			ce.pop();
			if (!ok || !out.is_fully_const()) return false;
			int ov = out.as_const().as_int();
			if (ok0 && ov != rr_expected(rv, s, N, W, 0)) ok0 = false;
			if (ok1 && ov != rr_expected(rv, s, N, W, 1)) ok1 = false;
			checks++;
			return ok0 || ok1;
		};

		// Phase 1: empty req × starts — idx_next must track s; grant stays 0.
		Const z = const_u64(0, N);
		for (int s : starts)
			if (!check(z, s)) return -1;

		// Phase 2: one-hots at a single start (result is independent of s).
		for (int k = 0; k < N; k++) {
			std::vector<State> bits(N, State::S0);
			bits[k] = State::S1;
			if (!check(Const(bits), 0)) return -1;
		}

		// Phase 3: sparse multi-bit patterns × starts (rotation-sensitive).
		auto multi = gen_multibit_test_vectors(N, /*dense_small_n=*/false);
		for (auto& rv : multi) {
			for (int s : starts)
				if (!check(rv, s)) return -1;
		}

		// Require empty×starts plus at least one one-hot (phases 1+2).
		if (checks < GetSize(starts) + 1) return -1;
		if (ok0) return 0;
		if (ok1) return 1;
		return -1;
	}

	// Emit the log-depth round-robin network. Shared subexpressions across
	// the grant / idx_next pair for the same (req, start) inputs are cached.
	dict<std::pair<Wire*, Wire*>, std::tuple<SigSpec, SigSpec, SigBit>> rr_core_cache;

	SigSpec emit_rr(Wire* req_wire, Wire* start_wire, int N, int W, int kind) {
		SigSpec req = sigmap(SigSpec(req_wire));
		SigSpec s = sigmap(SigSpec(start_wire));

		SigSpec gsel;
		SigBit anyreq;
		auto key = std::make_pair(req_wire, start_wire);
		auto it = rr_core_cache.find(key);
		if (it != rr_core_cache.end()) {
			SigSpec cached_gsel;
			std::tie(cached_gsel, std::ignore, anyreq) = it->second;
			gsel = cached_gsel;
		} else {
			SigSpec above;
			for (int i = 0; i < N; i++) {
				above.append(module->Lt(NEW_ID2_SUFFIX("rrabove"), s, SigSpec(Const(i, W)), false, cell_src(cell)));
				cells_added++;
			}
			SigSpec mask_hi = module->And(NEW_ID2_SUFFIX("rrmask"), req, above, false, cell_src(cell));
			cells_added++;

			SigSpec cz_hi = emit_ctz_full(mask_hi, N);
			SigSpec cz_all = emit_ctz_full(req, N);
			auto low_w = [&](SigSpec x) {
				if (GetSize(x) > W) return x.extract(0, W);
				while (GetSize(x) < W) x.append(SigSpec(State::S0));
				return x;
			};
			cz_hi = low_w(cz_hi);
			cz_all = low_w(cz_all);

			SigBit any_hi = module->ReduceOr(NEW_ID2_SUFFIX("rranyhi"), mask_hi, false, cell_src(cell));
			cells_added++;
			anyreq = module->ReduceOr(NEW_ID2_SUFFIX("rranyreq"), req, false, cell_src(cell));
			cells_added++;
			// any_hi ? cz_hi : cz_all
			gsel = module->Mux(NEW_ID2_SUFFIX("rrgsel"), cz_all, cz_hi, any_hi, cell_src(cell));
			cells_added++;
			rr_core_cache[key] = std::make_tuple(gsel, SigSpec(), anyreq);
		}

		SigSpec fallback = (kind == 0) ? SigSpec(Const(0, W)) : s;
		// anyreq ? gsel : fallback
		SigSpec res = module->Mux(NEW_ID2_SUFFIX("rrsel"), fallback, gsel, anyreq, cell_src(cell));
		cells_added++;
		return res;
	}

	// Generalisation of cone_depends_only_on_T to a set of allowed leaf bits.
	bool cone_depends_only_on_set(SigSpec S_sig, const pool<SigBit>& allowed) {
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		for (auto bit : sigmap(S_sig)) {
			if (!bit.wire) continue;
			if (visited.insert(bit).second) worklist.push(bit);
		}
		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();
			if (allowed.count(bit)) continue;
			if (input_port_bits.count(bit)) return false;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) return false;
			Cell* drv = it->second;
			if (sequential_cells.count(drv)) return false;
			for (auto& conn : drv->connections()) {
				if (!drv->input(conn.first)) continue;
				for (auto in_bit : sigmap(conn.second)) {
					if (!in_bit.wire) continue;
					if (visited.insert(in_bit).second) worklist.push(in_bit);
				}
			}
		}
		return true;
	}

	struct RRRewrite {
		Wire* S_wire;
		Wire* req_wire;
		Wire* start_wire;
		int N;
		int W;
		int kind;
		Cell* sole_driver;
		IdString out_port;
	};

	// One per (potential) candidate, lazily filled before fingerprinting.
	struct Candidate {
		Wire* S_wire;
		pool<Cell*> cone_cells;
		pool<SigBit> leaf_bits;
		pool<SigBit> cone_bits;
		pool<SigBit> control_bits;
		Cell* sole_driver;
		IdString out_port;
		SigSpec driven;
		vector<int> driven_pos;
		bool cone_partial;
	};

	// Positions of S that constrain the count: driven bits and hard 0/1 ties.
	// A structural x is a slot the RTL never commits to (an unreachable casez
	// arm, a pruned high bit), so it is dropped from the comparison instead of
	// failing it -- and left untouched by the rewrite.
	static int care_mask_of(const SigSpec& S_sig) {
		int mask = 0;
		for (int i = 0; i < GetSize(S_sig) && i < 30; i++) {
			SigBit b = S_sig[i];
			if (b.wire || b == State::S0 || b == State::S1) mask |= 1 << i;
		}
		return mask;
	}

	static int count_care_bits(int mask) {
		int n = 0;
		for (; mask; mask &= mask - 1) n++;
		return n;
	}

	// A count whose top values became unreachable loses its high bits to
	// constants, so the driver only produces part of the word. Match on the
	// driven part and keep the tied positions as context for the fingerprint.
	bool get_sole_whole_wire_driver(Wire* S_wire, Cell*& sole_driver, IdString& out_port,
	                                SigSpec& driven, vector<int>& driven_pos) {
		driven = SigSpec();
		driven_pos.clear();
		SigSpec S_sig = sigmap(SigSpec(S_wire));
		pool<Cell*> drivers;
		for (int i = 0; i < GetSize(S_sig); i++) {
			SigBit bit = S_sig[i];
			if (!bit.wire) continue;
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) return false;
			drivers.insert(it->second);
			driven.append(bit);
			driven_pos.push_back(i);
		}
		if (GetSize(driven) < 2) return false;
		if (GetSize(drivers) != 1) return false;
		sole_driver = *drivers.begin();

		SigSpec out_sig;
		for (auto& conn : sole_driver->connections()) {
			if (sole_driver->output(conn.first)) {
				out_port = conn.first;
				out_sig = sigmap(conn.second);
				break;
			}
		}
		return out_sig == driven;
	}

	bool is_control_input(Cell* c, IdString port) {
		if (c->type.in(ID($mux), ID($pmux)))
			return port == ID::S;
		return c->type.in(
			ID($eq), ID($ne), ID($eqx), ID($nex), ID($lt), ID($le), ID($gt), ID($ge),
			ID($logic_not), ID($logic_and), ID($logic_or),
			ID($reduce_bool), ID($reduce_or), ID($reduce_and),
			ID($and), ID($or), ID($xor), ID($xnor), ID($not));
	}

	// Cheap structural prefilter for a candidate S=f(T). ConstEval will only
	// assign T, so any other variable leaf in the fanin cone guarantees the
	// fingerprint will fail. Stop traversal at T bits to allow T to be an
	// internal wire produced by logic outside the PE region.
	bool cone_depends_only_on_T(SigSpec S_sig, const pool<SigBit>& T_bits,
	                            pool<Cell*>* evaluated = nullptr) {
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		for (auto bit : sigmap(S_sig)) {
			if (!bit.wire) continue;
			if (visited.insert(bit).second) worklist.push(bit);
		}

		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();

			if (T_bits.count(bit)) continue;
			if (input_port_bits.count(bit)) return false;

			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) return false;

			Cell* drv = it->second;
			if (sequential_cells.count(drv)) return false;
			if (evaluated) evaluated->insert(drv);

			for (auto& conn : drv->connections()) {
				if (!drv->input(conn.first)) continue;
				for (auto in_bit : sigmap(conn.second)) {
					if (!in_bit.wire) continue;
					if (visited.insert(in_bit).second) worklist.push(in_bit);
				}
			}
		}

		return true;
	}

	void run() {
		vector<Wire*> wires_snapshot(module->wires().begin(), module->wires().end());
		build_wire_index(wires_snapshot);
		// One ConstEval for the whole module: ctor indexes every cell once.
		// Fingerprints only run before we mutate the netlist.
		ConstEval ce_store(module);
		ce = &ce_store;

		// Stage 1: build candidate set with cones, filter by driver/width.
		// Probe with a small cone cap first; only a budgeted number of wires
		// that overflow get a full-size rewalk (unrolled N=64 loops otherwise
		// make every intermediate encoder wire pay for a full BFS).
		vector<Candidate> candidates;
		int max_W = clog2_int(max_input_width + 1);
		int max_cone_cells = std::max(128, max_input_width * 16);
		int probe_cone_cells = std::min(64, max_cone_cells);
		int large_cone_budget = 24;
		// req[N]+start[W] leaves for RR, plus a little slack for aliases/opt junk.
		int max_leaf_bits = max_input_width + max_W + max_input_width / 4 + 16;

		struct SCand { Wire* w; Cell* drv; IdString port; int rank;
		               SigSpec driven; vector<int> driven_pos; };
		vector<SCand> s_cands;
		for (Wire* S_wire : wires_snapshot) {
			if (S_wire->port_input) continue;
			int Wbits = S_wire->width;
			if (Wbits < 2 || Wbits > max_W) continue;
			Cell* sole_driver = nullptr;
			IdString out_port;
			SigSpec driven;
			vector<int> driven_pos;
			if (!get_sole_whole_wire_driver(S_wire, sole_driver, out_port, driven, driven_pos))
				continue;
			if (!driver_looks_interesting(sole_driver)) continue;
			int rank = 2;
			if (S_wire->port_output) rank = 0;
			else if (sole_driver->type.in(ID($mux), ID($pmux), ID($add), ID($sub), ID($and), ID($or)))
				rank = 1;
			s_cands.push_back({S_wire, sole_driver, out_port, rank,
			                   std::move(driven), std::move(driven_pos)});
		}
		std::sort(s_cands.begin(), s_cands.end(), [](const SCand& a, const SCand& b) {
			if (a.rank != b.rank) return a.rank < b.rank;
			if (a.w->width != b.w->width) return a.w->width > b.w->width;
			// Deterministic across platforms (wire iteration order is not).
			return a.w->name.str() < b.w->name.str();
		});

		for (auto& sc : s_cands) {
			Wire* S_wire = sc.w;
			Cell* sole_driver = sc.drv;
			IdString out_port = sc.port;

			pool<Cell*> cone_cells;
			pool<SigBit> leaf_bits;
			bool cone_partial = false;
			int st = get_cone(SigSpec(S_wire), cone_cells, leaf_bits,
			                  probe_cone_cells, max_leaf_bits);
			if (st < 0) {
				// Rank 0/1 (ports + mux/add/and tails) always get a full rewalk;
				// only lower-priority wires consume the shared budget.
				if (sc.rank >= 2) {
					if (large_cone_budget <= 0) continue;
					large_cone_budget--;
				}
				st = get_cone(SigSpec(S_wire), cone_cells, leaf_bits,
				              max_cone_cells, max_leaf_bits);
				// Overrunning even the full budget leaves a breadth-first prefix
				// of the cone, which is all discovery needs: candidate T wires
				// come from the frontier nearest S, and each one is re-proved
				// against S by cone_depends_only_on_T plus the fingerprint. An
				// encoder reading a mux tree has leaves tracking arms x arm
				// width rather than bus width, so dropping the whole candidate
				// here loses the match on a bus that is itself perfectly clean.
				if (st < 0 && allow_partial_cone && !cone_cells.empty()) {
					st = 1;
					cone_partial = true;
				}
			}
			if (st <= 0) continue;
			if (!cone_looks_like_pe(cone_cells)) continue;

			pool<SigBit> cone_bits = leaf_bits;
			pool<SigBit> control_bits;
			for (Cell* c : cone_cells) {
				for (auto& conn : c->connections()) {
					if (c->output(conn.first)) {
						for (auto bit : sigmap(conn.second))
							if (bit.wire) cone_bits.insert(bit);
					}
					if (c->input(conn.first) && is_control_input(c, conn.first)) {
						for (auto bit : sigmap(conn.second))
							if (bit.wire) control_bits.insert(bit);
					}
				}
			}
			if (control_bits.empty()) continue;
			candidates.push_back({S_wire, std::move(cone_cells), std::move(leaf_bits),
			                      std::move(cone_bits), std::move(control_bits),
			                      sole_driver, out_port, sc.driven, sc.driven_pos,
			                      cone_partial});
		}

		// Stage 2: process candidates in order of cone size (LARGEST first).
		// Verific-style lowerings often expose several wires along the same
		// chain that all fingerprint as a PE on the same input bus (e.g. a
		// "found ? chain_out : default" wrapper mux plus the raw chain tail
		// plus a downstream mask & enc-merge). Rewriting only one of them
		// leaves the chain alive feeding the others, so we rewrite each
		// match independently and de-duplicate the emitted log-depth
		// network through the per-input clz/ctz cache.
		// Cone size alone is not a total order: a lowering routinely exposes
		// several chain wires with byte-identical (cells, bits) counts. std::sort
		// is not stable, so those ties resolve differently under libc++ and
		// libstdc++, and since a candidate claims its output and driver
		// exclusively, whichever of a tied pair runs first changes the netlist.
		// Break the tie explicitly, as candidate discovery above already does.
		// Public before private, so a tie between a port and the $0\... proc
		// temporary feeding it still reports (and claims) the named wire.
		std::sort(candidates.begin(), candidates.end(),
		          [](const Candidate& a, const Candidate& b) {
		              if (GetSize(a.cone_cells) != GetSize(b.cone_cells))
		                  return GetSize(a.cone_cells) > GetSize(b.cone_cells);
		              if (GetSize(a.cone_bits) != GetSize(b.cone_bits))
		                  return GetSize(a.cone_bits) > GetSize(b.cone_bits);
		              if (a.S_wire->name.isPublic() != b.S_wire->name.isPublic())
		                  return a.S_wire->name.isPublic();
		              return a.S_wire->name.str() < b.S_wire->name.str();
		          });

		vector<Rewrite> rewrites;
		pool<Wire*> claimed_outputs;
		pool<Cell*> claimed_drivers;

		for (auto& cand : candidates) {
			if (claimed_outputs.count(cand.S_wire)) continue;
			if (claimed_drivers.count(cand.sole_driver)) continue;

			int Wbits = cand.S_wire->width;
			SigSpec S_sig = sigmap(SigSpec(cand.S_wire));

			vector<Wire*> Ts = find_candidate_Ts(cand.S_wire, cand.cone_bits,
			                                     cand.control_bits, Wbits);
			for (Wire* T_wire : Ts) {
				int N = T_wire->width;
				SigSpec T_sig = sigmap(SigSpec(T_wire));
				pool<SigBit> T_bits;
				for (auto bit : T_sig)
					if (bit.wire) T_bits.insert(bit);
				pool<Cell*> evaluated;
				if (!cone_depends_only_on_T(S_sig, T_bits, &evaluated)) continue;

				PinnedBus pb = make_pinned_bus(T_sig);
				if (!pb.ok) continue;

				// Each don't-care slot drops a bit from every comparison, so
				// allow only the one an unreachable saturating value prunes;
				// a mostly-x word would be matched on far too little evidence.
				int care_mask = care_mask_of(S_sig);
				if (count_care_bits(care_mask) < Wbits - 1) continue;

				PEVariant variant = fingerprint(ce_store, pb, S_sig, N, Wbits,
				                                care_mask, evaluated);
				if (variant == PEVariant::NONE) continue;

				log("  %s: %s <- %s(%s) [N=%d, W=%d]\n",
				    log_id(module), log_id(cand.S_wire), variant_name(variant),
				    log_id(T_wire), N, Wbits);

				rewrites.push_back({cand.S_wire, T_wire, N, Wbits, variant,
				                    cand.sole_driver, cand.out_port,
				                    cand.driven, cand.driven_pos,
				                    cand.cone_partial});
				claimed_outputs.insert(cand.S_wire);
				claimed_drivers.insert(cand.sole_driver);
				break;
			}
		}

		// Stage 3: round-robin (rotated priority) detection. Reuses the same
		// candidate cones; an output S is grant/idx_next of a round-robin
		// arbiter over a wide request bus `req` and a same-width-as-S pointer
		// `start`, both bottoming out the cone.
		vector<RRRewrite> rr_rewrites;
		if (detect_rr) {
			const int max_pairs = 64;
			for (auto& cand : candidates) {
				if (claimed_outputs.count(cand.S_wire)) continue;
				if (claimed_drivers.count(cand.sole_driver)) continue;
				if (!cone_looks_like_rr(cand.cone_cells)) continue;
				// RR emits a whole pointer word; a partly tied S is not one.
				if (GetSize(cand.driven) != cand.S_wire->width) continue;

				int W = cand.S_wire->width;
				if (W < 2 || W > max_W) continue;
				SigSpec S_sig = sigmap(SigSpec(cand.S_wire));

				vector<Wire*> in_cone = wires_in_cone(cand.cone_bits, [&](Wire* w) {
					return w != cand.S_wire;
				});
				vector<Wire*> req_cands, start_cands;
				for (Wire* w : in_cone) {
					int wn = w->width;
					if (wn >= min_input_width && wn <= max_input_width &&
					    clog2_int(wn) == W)
						req_cands.push_back(w);
					if (wn == W)
						start_cands.push_back(w);
				}
				std::sort(req_cands.begin(), req_cands.end(),
				          [](Wire* a, Wire* b) { return a->width > b->width; });

				bool matched = false;
				for (Wire* req_wire : req_cands) {
					if (matched) break;
					int N = req_wire->width;
					SigSpec req_sig = sigmap(SigSpec(req_wire));
					pool<SigBit> req_bits;
					for (auto bit : req_sig)
						if (bit.wire) req_bits.insert(bit);
					// Per-req_wire fingerprint budget: a start-candidate-heavy
					// first req size must not exhaust a shared budget and starve
					// later (narrower) req sizes.
					int pairs = 0;
					for (Wire* start_wire : start_cands) {
						if (start_wire == req_wire) continue;
						if (++pairs > max_pairs) break;
						SigSpec start_sig = sigmap(SigSpec(start_wire));
						pool<SigBit> allowed = req_bits;
						for (auto bit : start_sig)
							if (bit.wire) allowed.insert(bit);
						if (!cone_depends_only_on_set(S_sig, allowed)) continue;

						int kind = fingerprint_rr(ce_store, req_sig, start_sig, S_sig, N, W);
						if (kind < 0) continue;

						log("  %s: %s <- round_robin_%s(req=%s, start=%s) [N=%d, W=%d]\n",
						    log_id(module), log_id(cand.S_wire),
						    kind == 0 ? "grant" : "next",
						    log_id(req_wire), log_id(start_wire), N, W);
						rr_rewrites.push_back({cand.S_wire, req_wire, start_wire, N, W,
						                       kind, cand.sole_driver, cand.out_port});
						claimed_outputs.insert(cand.S_wire);
						claimed_drivers.insert(cand.sole_driver);
						matched = true;
						break;
					}
				}
			}
		}

		// Apply rewrites. We collected first to avoid the index growing stale
		// while we add new cells/wires.
		// Smear discovery and compare narrowing must run before any mutation:
		// they consult ConstEval. Round-trip collapse then takes shift
		// consumers off S's fanout, so the emit below can tell whether the
		// binary code is still live.
		if (enable_smear) {
			for (auto& r : rewrites) {
				hunt_smear(sigmap(SigSpec(r.T_wire)));
				int arm_cap = std::min(max_push_arms, std::max(2, 512 / std::max(r.N, 1)));
				if (arm_cap < 2) continue;
				int split_budget = arm_cap - 1;
				pool<SigBit> sel_bits, leaf_bits;
				auto root = build_mux_arms(sigmap(SigSpec(r.T_wire)), split_budget,
				                           sel_bits, leaf_bits);
				discover_smear_leaves(root);
			}
		}
		pool<Cell*> dead_readers;
		collapse_smear_compares(dead_readers);
		ce = nullptr;
		for (auto& r : rewrites)
			if (variant_is_full(r.variant))
				collapse_roundtrips(r, dead_readers);

		for (auto& r : rewrites) {
			cell = r.sole_driver;
			SigSpec new_S;
			// A fully collapsed encode is dead anyway; do not pay to hoist it.
			if (has_live_reader(r.S_wire, dead_readers))
				new_S = try_push_encoder(r);
			if (GetSize(new_S) == 0)
				new_S = emit_pe(r.variant, r.T_wire, r.N, r.Wbits);
			// Only the driven positions get re-connected; tied bits of S keep
			// their constant, which the fingerprint already checked against.
			SigSpec repl;
			for (int i : r.driven_pos)
				repl.append(new_S[i]);
			// Disconnect the old driver by re-pointing its Y to a fresh wire.
			Wire* dangling = module->addWire(NEW_ID2_SUFFIX("dangling"), GetSize(r.driven));
			r.sole_driver->setPort(r.out_port, dangling);
			module->connect(r.driven, repl);
			regions_rewritten++;
		}
		for (auto& r : rr_rewrites) {
			cell = r.sole_driver;
			SigSpec new_S = emit_rr(r.req_wire, r.start_wire, r.N, r.W, r.kind);
			Wire* dangling = module->addWire(NEW_ID2_SUFFIX("dangling"), r.W);
			r.sole_driver->setPort(r.out_port, dangling);
			module->connect(SigSpec(r.S_wire), new_S);
			regions_rewritten++;
		}
	}
};

struct OptPriEncPass : public Pass {
	OptPriEncPass() : Pass("opt_prienc",
		"detect and rewrite priority-encoder / CLZ / CTZ regions") {}

	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_prienc [options] [selection]\n");
		log("\n");
		log("This pass uses functional fingerprinting to detect combinational logic\n");
		log("regions that implement a priority encoder, count-leading/trailing-zeros\n");
		log("(CLZ/CTZ) or count-leading/trailing-ones (CLO/CTO) on a single contiguous\n");
		log("input wire, regardless of how the RTL was written (unrolled for-loops,\n");
		log("casez priority lists, pmux chains, etc.). Each detected region is replaced\n");
		log("with a log-depth network built from $mux/$not cells.\n");
		log("\n");
		log("Detected variants:\n");
		log("\n");
		log("    clz_full  : result = N when input is 0, else N-1 - msb_set_pos.\n");
		log("                Output width = ceil(log2(N+1)).\n");
		log("    clz_short : result = N-1 - msb_set_pos for nonzero input; the\n");
		log("                output for input==0 is unconstrained. Output width =\n");
		log("                ceil(log2(N)), and only considered for power-of-2 N,\n");
		log("                where that width cannot hold N in the first place.\n");
		log("    ctz_full  : symmetric to clz_full from the LSB side.\n");
		log("    ctz_short : symmetric to clz_short from the LSB side.\n");
		log("    clo_full  : leading-ONES count; = clz_full of ~input, so result = N\n");
		log("                when the input is all ones. Widths as for clz_full.\n");
		log("    clo_short : leading-ONES count with all-ones input unconstrained.\n");
		log("    cto_full  : trailing-ONES count; = ctz_full of ~input.\n");
		log("    cto_short : trailing-ONES count with all-ones input unconstrained.\n");
		log("\n");
		log("Buses need not be vectors of distinct free nets. Positions that the\n");
		log("netlist pins to a constant (tie-offs, const propagation, boundary\n");
		log("optimization) or that repeat another net are held at their real value\n");
		log("while fingerprinting, so they narrow the reachable domain instead of\n");
		log("rejecting the candidate; when the remaining free space is small enough\n");
		log("the surviving variant is then confirmed by enumerating it. On the\n");
		log("output side a count slot that is x in every state is a don't-care: it\n");
		log("is left out of the comparison and left untouched by the rewrite.\n");
		log("\n");
		log("For the *_full variants the pass also collapses encode/decode round\n");
		log("trips on the matched count: shifting by a count that was just encoded\n");
		log("from a run only decodes it again, so with mask = (1 << count) - 1 taken\n");
		log("straight from the log-depth run thermometer,\n");
		log("\n");
		log("    (a >> count) << count        ->  a & ~mask       (align down)\n");
		log("    ((a >> count) + 1) << count  ->  (a | mask) + 1  (align up)\n");
		log("    1 << count                   ->  one-hot(count)\n");
		log("\n");
		log("This keeps the critical path in the thermometer domain: two barrel\n");
		log("shifters plus the binary encode become a prefix-AND and one bitwise op.\n");
		log("Only shifts whose amount is exactly the matched count are touched, so a\n");
		log("genuinely binary-encoded variable shift is never collapsed.\n");
		log("\n");
		log("    -smear\n");
		log("        recognise an MSB suffix-OR ('round up to 2^n-1') feeding a\n");
		log("        matched encoder or a magnitude compare. Off by default.\n");
		log("        cto_full(smear(x)) is rewritten as msb_index(x)+1, so the\n");
		log("        smear cone leaves the encoder path; a compare whose other\n");
		log("        operand is sequential or a port is narrowed into the\n");
		log("        same encoded domain after a software identity search\n");
		log("        confirms the threshold. Constant other operands are left\n");
		log("        to muxpush.\n");
		log("\n");
		log("In addition, the pass detects round-robin (rotated priority)\n");
		log("arbiters: grant / idx_next = first set request bit scanning upward\n");
		log("(wrapping) from just after a stored pointer idx_last. RTL typically\n");
		log("spells this as a DEPTH-iteration idx-- loop over req[idx], which\n");
		log("elaborates into a serial chain; it is replaced with a log-depth\n");
		log("threshold-mask + CTZ network. For power-of-2 DEPTH the rewrite is\n");
		log("equivalent for every pointer value; for other widths it is\n");
		log("equivalent for every reachable pointer (idx_last in [0,DEPTH)).\n");
		log("\n");
		log("    -clz, -ctz, -clo, -cto\n");
		log("        detect only the named variant(s); may be combined. Any of\n");
		log("        these also disables round-robin detection.\n");
		log("\n");
		log("    -no-ones\n");
		log("        disable the CLO/CTO (leading/trailing ONES) variants.\n");
		log("\n");
		log("    -max-push-arms N\n");
		log("        cap on mux arms the encoder may be hoisted above when the\n");
		log("        mux select is computed from the mux data (default 24, further\n");
		log("        limited so arms*input_width stays bounded; 0/1 disables it).\n");
		log("\n");
		log("    -partial-cone\n");
		log("        keep a candidate whose cone walk runs out of budget, using\n");
		log("        the breadth-first prefix reached so far. Off by default.\n");
		log("        The walk only proposes candidate input buses; each one is\n");
		log("        then proved against the output on its own, so a truncated\n");
		log("        cone costs recall, not soundness. It matters when the\n");
		log("        encoder input is itself a wide select: the leaf count then\n");
		log("        tracks arms x arm width instead of bus width, and a clean\n");
		log("        narrow bus is rejected for the size of the logic behind it.\n");
		log("        Such a match emits the plain log-depth network and is never\n");
		log("        hoisted into the mux arms, since the truncated walk is\n");
		log("        exactly the evidence that those arms were not measured.\n");
		log("\n");
		log("    -no-rr\n");
		log("        disable round-robin / rotated-priority detection.\n");
		log("\n");
		log("    -max-width N\n");
		log("        maximum input bus width to consider (default 64).\n");
		log("\n");
		log("    -min-width N\n");
		log("        minimum input bus width to consider (default 4). Smaller\n");
		log("        inputs are too easy to alias and rarely worth rewriting.\n");
		log("\n");
		log("This pass is not invoked by the default 'opt' script; users opt in.\n");
		log("After rewriting, the original cone cells become unused and are removed\n");
		log("by the trailing 'clean -purge'.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_PRIENC pass (priority encoder / CLZ / CTZ).\n");

		bool sel_clz = false, sel_ctz = false, sel_clo = false, sel_cto = false;
		bool no_ones = false;
		bool no_rr = false;
		bool enable_smear = false;
		bool partial_cone = false;
		int max_width = 64;
		int min_width = 4;
		int max_push_arms = 24;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-clz") { sel_clz = true; continue; }
			if (args[argidx] == "-ctz") { sel_ctz = true; continue; }
			if (args[argidx] == "-clo") { sel_clo = true; continue; }
			if (args[argidx] == "-cto") { sel_cto = true; continue; }
			if (args[argidx] == "-no-ones") { no_ones = true; continue; }
			if (args[argidx] == "-no-rr") { no_rr = true; continue; }
			if (args[argidx] == "-smear") { enable_smear = true; continue; }
			if (args[argidx] == "-partial-cone") { partial_cone = true; continue; }
			if (args[argidx] == "-max-push-arms" && argidx + 1 < args.size()) {
				max_push_arms = std::stoi(args[++argidx]); continue;
			}
			if (args[argidx] == "-max-width" && argidx + 1 < args.size()) {
				max_width = std::stoi(args[++argidx]); continue;
			}
			if (args[argidx] == "-min-width" && argidx + 1 < args.size()) {
				min_width = std::stoi(args[++argidx]); continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		// -clz / -ctz / -clo / -cto restrict detection to the named variants and
		// disable round-robin (which is a CTZ-based secondary pattern).
		bool any_sel = sel_clz || sel_ctz || sel_clo || sel_cto;
		if (any_sel) no_rr = true;

		int total_regions = 0;
		int total_roundtrips = 0;
		int total_smears = 0;
		int total_cmps = 0;
		int total_cells_added = 0;
		for (auto module : design->selected_modules()) {
			OptPriEncWorker worker(module);
			worker.detect_clz = any_sel ? sel_clz : true;
			worker.detect_ctz = any_sel ? sel_ctz : true;
			worker.detect_clo = (any_sel ? sel_clo : true) && !no_ones;
			worker.detect_cto = (any_sel ? sel_cto : true) && !no_ones;
			worker.detect_rr = !no_rr;
			worker.enable_smear = enable_smear;
			worker.allow_partial_cone = partial_cone;
			worker.max_input_width = max_width;
			worker.min_input_width = min_width;
			worker.max_push_arms = max_push_arms;
			worker.run();
			total_regions += worker.regions_rewritten;
			total_roundtrips += worker.roundtrips_collapsed;
			total_smears += worker.smears_collapsed;
			total_cmps += worker.compares_narrowed;
			total_cells_added += worker.cells_added;
		}

		log("Rewrote %d region(s); emitted %d new cell(s).\n",
		    total_regions, total_cells_added);
		log("Collapsed %d encode/decode round-trip(s) into mask logic.\n",
		    total_roundtrips);
		if (enable_smear)
			log("Collapsed %d smear/encoder round-trip(s); narrowed %d compare(s).\n",
			    total_smears, total_cmps);

		Yosys::run_pass("clean -purge");
	}
} OptPriEncPass;

PRIVATE_NAMESPACE_END
