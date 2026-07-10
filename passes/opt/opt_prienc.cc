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
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/rewrite_utils.h"

// Priority-encoder variants the pass recognises.
enum class PEVariant { NONE, CLZ_FULL, CLZ_SHORT, CTZ_FULL, CTZ_SHORT };

static const char* variant_name(PEVariant v) {
	switch (v) {
		case PEVariant::CLZ_FULL:  return "clz_full";
		case PEVariant::CLZ_SHORT: return "clz_short";
		case PEVariant::CTZ_FULL:  return "ctz_full";
		case PEVariant::CTZ_SHORT: return "ctz_short";
		default: return "none";
	}
}

// Return the index of the highest set bit (MSB) of `c`, or -1 if all zero.
static int const_msb_set(const Const& c, int N) {
	auto bits = c.to_bits();
	for (int i = N - 1; i >= 0; i--)
		if (i < (int)bits.size() && bits[i] == State::S1) return i;
	return -1;
}

// Return the index of the lowest set bit (LSB) of `c`, or -1 if all zero.
static int const_lsb_set(const Const& c, int N) {
	auto bits = c.to_bits();
	for (int i = 0; i < N; i++)
		if (i < (int)bits.size() && bits[i] == State::S1) return i;
	return -1;
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
	bool detect_rr = true;
	int max_input_width = 256;
	int min_input_width = 4;

	// Stats.
	int regions_rewritten = 0;
	int cells_added = 0;

	// Cache of full-width CLZ/CTZ networks already emitted for a given input
	// wire, so that several matched output wires sharing the same input bus
	// pull from a single instantiation instead of materialising duplicate
	// log-depth trees.
	dict<Wire*, SigSpec> clz_full_cache;
	dict<Wire*, SigSpec> ctz_full_cache;

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

	void build_wire_index(const vector<Wire*>& wires) {
		bit_to_cand_wires.clear();
		wire_uniq_bit_count.clear();
		wire_sig_bits.clear();
		for (Wire* w : wires) {
			SigSpec ss = sigmap(SigSpec(w));
			vector<SigBit> bits;
			bits.reserve(GetSize(ss));
			pool<SigBit> uniq;
			bool has_const = false;
			for (auto bit : ss) {
				bits.push_back(bit);
				if (!bit.wire) { has_const = true; continue; }
				if (uniq.insert(bit).second)
					bit_to_cand_wires[bit].push_back(w);
			}
			wire_sig_bits[w] = std::move(bits);
			// Wires with const bits can never be clean ConstEval cuts.
			if (!has_const)
				wire_uniq_bit_count[w] = GetSize(uniq);
		}
	}

	// Wires whose sigmap bits are all inside `cone_bits` (and pass `keep`).
	vector<Wire*> wires_in_cone(const pool<SigBit>& cone_bits,
	                            std::function<bool(Wire*)> keep) {
		dict<Wire*, int> cover;
		for (auto bit : cone_bits) {
			auto it = bit_to_cand_wires.find(bit);
			if (it == bit_to_cand_wires.end()) continue;
			for (Wire* w : it->second) {
				if (!keep(w)) continue;
				cover[w]++;
			}
		}
		vector<Wire*> out;
		for (auto& it : cover) {
			Wire* w = it.first;
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
			int W_full = clog2_int(w->width + 1);
			int W_short = clog2_int(w->width);
			if (W_full != Wbits && W_short != Wbits) return false;
			auto sit = wire_sig_bits.find(w);
			if (sit == wire_sig_bits.end()) return false;
			for (auto bit : sit->second)
				if (control_bits.count(bit)) return true;
			return false;
		});
		std::sort(out.begin(), out.end(), [](Wire* a, Wire* b) {
			return a->width > b->width;
		});
		return out;
	}

	// PE deck: zero + one-hots first (reject most non-PEs immediately), then
	// denser patterns that separate full vs short / CLZ vs CTZ. For large N the
	// prefix/suffix sweeps are sparsified — one-hots already pin every position.
	vector<Const> gen_test_vectors(int N) {
		vector<Const> vs;
		vs.push_back(const_u64(0, N));
		for (int k = 0; k < N; k++) {
			std::vector<State> bits(N, State::S0);
			bits[k] = State::S1;
			vs.push_back(Const(bits));
		}
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
		if (N <= 16) {
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

	// Leaner RR deck: empty + one-hots + a sparse multi-bit set. One-hots are
	// s-independent (sanity); multi-bit + empty×s catch rotation dependence.
	vector<Const> gen_rr_test_vectors(int N) {
		vector<Const> vs;
		vs.push_back(const_u64(0, N));
		for (int k = 0; k < N; k++) {
			std::vector<State> bits(N, State::S0);
			bits[k] = State::S1;
			vs.push_back(Const(bits));
		}
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
		push_prefix(2);
		push_prefix(N / 2);
		push_prefix(N - 1);
		push_prefix(N);
		push_suffix_clear(1);
		push_suffix_clear(N / 2);
		push_suffix_clear(N - 1);
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

	// Run candidate test vectors through a shared ConstEval. Zero + one-hots
	// lead the deck so non-PEs bail before denser patterns. For large N the
	// one-hot sweep is sampled; once a single variant remains we return early.
	PEVariant fingerprint(ConstEval& ce, SigSpec T_sig, SigSpec S_sig, int N, int Wbits) {
		bool clz_full_ok = detect_clz && (Wbits == clog2_int(N + 1));
		bool ctz_full_ok = detect_ctz && (Wbits == clog2_int(N + 1));
		bool clz_short_ok = detect_clz && (Wbits == clog2_int(N));
		bool ctz_short_ok = detect_ctz && (Wbits == clog2_int(N));

		if (!clz_full_ok && !ctz_full_ok && !clz_short_ok && !ctz_short_ok)
			return PEVariant::NONE;

		if (!clean_set_signals({&T_sig}))
			return PEVariant::NONE;

		if (!is_valid_consteval_cut(T_sig))
			return PEVariant::NONE;

		auto finish = [&]() -> PEVariant {
			if (clz_full_ok)  return PEVariant::CLZ_FULL;
			if (ctz_full_ok)  return PEVariant::CTZ_FULL;
			if (clz_short_ok) return PEVariant::CLZ_SHORT;
			if (ctz_short_ok) return PEVariant::CTZ_SHORT;
			return PEVariant::NONE;
		};
		auto survivors = [&]() {
			return (int)clz_full_ok + (int)ctz_full_ok + (int)clz_short_ok + (int)ctz_short_ok;
		};

		auto check_vec = [&](const Const& v) -> bool {
			ce.push();
			ce.set(T_sig, v);
			SigSpec out = S_sig;
			SigSpec undef;
			bool ok = ce.eval(out, undef);
			ce.pop();
			if (!ok || !out.is_fully_const()) {
				clz_full_ok = ctz_full_ok = clz_short_ok = ctz_short_ok = false;
				return false;
			}
			int outval = out.as_const().as_int();

			int msb_set = const_msb_set(v, N);
			int lsb_set = const_lsb_set(v, N);
			bool zero = (msb_set < 0);

			int e_clz = zero ? N : (N - 1 - msb_set);
			int e_ctz = zero ? N : lsb_set;

			if (clz_full_ok && outval != e_clz) clz_full_ok = false;
			if (ctz_full_ok && outval != e_ctz) ctz_full_ok = false;
			if (clz_short_ok && !zero && outval != e_clz) clz_short_ok = false;
			if (ctz_short_ok && !zero && outval != e_ctz) ctz_short_ok = false;
			return survivors() > 0;
		};

		vector<Const> vs;
		vs.push_back(const_u64(0, N));

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
		for (int k : pv) {
			std::vector<State> bits(N, State::S0);
			bits[k] = State::S1;
			vs.push_back(Const(bits));
		}

		// Multi-bit confirmation vectors (sparse for any N via gen_test_vectors tail).
		{
			auto tail = gen_test_vectors(N);
			for (auto& v : tail) {
				int pop = 0;
				auto b = v.to_bits();
				for (int i = 0; i < N && i < (int)b.size(); i++)
					if (b[i] == State::S1) pop++;
				if (pop <= 1) continue;
				vs.push_back(v);
			}
		}

		int n_checked = 0;
		int onehot_end = 1 + GetSize(pv); // zero + one-hots
		int early_at = std::min(onehot_end, 1 + std::min(GetSize(pv), 8));
		for (auto& v : vs) {
			if (!check_vec(v)) return PEVariant::NONE;
			n_checked++;
			// Unique survivor after zero + a handful of one-hots is enough.
			if (n_checked >= early_at && survivors() == 1)
				return finish();
		}
		return finish();
	}

	// Recursive CLZ on a power-of-2-width input. Returns a (log2(N)+1)-bit
	// SigSpec whose MSB is 1 iff T == 0 and whose lower bits are the leading-
	// zeros count for nonzero T.
	SigSpec emit_clz_pow2(SigSpec T, int N) {
		log_assert(N >= 1 && (N & (N - 1)) == 0);
		if (N == 1) {
			cells_added++;
			return module->Not(NEW_ID2_SUFFIX("clznot"), T, false, cell_src(cell));
		}
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
		SigSpec lo_nonzero_spec = module->Not(NEW_ID2_SUFFIX("clz_lonz"), SigSpec(lo_zero), false, cell_src(cell));
		cells_added++;
		SigBit lo_nonzero = lo_nonzero_spec[0];

		SigSpec pad_clz_lo;
		if (W1 >= 2)
			pad_clz_lo.append(clz_lo.extract(0, W1 - 1));
		pad_clz_lo.append(lo_nonzero);
		pad_clz_lo.append(lo_zero);

		// $mux: Y = S ? B : A. We want Y = hi_zero ? pad_clz_lo : pad_clz_hi.
		cells_added++;
		return module->Mux(NEW_ID2_SUFFIX("clzmux"), pad_clz_hi, pad_clz_lo, SigSpec(hi_zero), cell_src(cell));
	}

	// CLZ of arbitrary-width T, returning a (clog2(N+1))-bit result.
	SigSpec emit_clz_full(SigSpec T, int N) {
		int Np = 1;
		while (Np < N) Np *= 2;
		int pad_amount = Np - N;
		SigSpec padded = T;
		for (int i = 0; i < pad_amount; i++)
			padded.append(SigSpec(State::S0));
		SigSpec clz_padded = emit_clz_pow2(padded, Np); // log2(Np)+1 bits
		if (pad_amount == 0)
			return clz_padded;
		// result = clz_padded - pad_amount, truncated to W = clog2(N+1) bits.
		int W = clog2_int(N + 1);
		SigSpec sub = module->Sub(NEW_ID2_SUFFIX("clzsub"), clz_padded, SigSpec(Const(pad_amount, GetSize(clz_padded))), false, cell_src(cell));
		cells_added++;
		if (GetSize(sub) >= W)
			return sub.extract(0, W);
		SigSpec out = sub;
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

	SigSpec emit_pe(PEVariant v, Wire* T_wire, int N, int out_width) {
		bool is_clz = (v == PEVariant::CLZ_FULL || v == PEVariant::CLZ_SHORT);
		auto& cache = is_clz ? clz_full_cache : ctz_full_cache;

		SigSpec full;
		auto it = cache.find(T_wire);
		if (it != cache.end()) {
			full = it->second;
		} else {
			SigSpec T_sig = sigmap(SigSpec(T_wire));
			full = is_clz ? emit_clz_full(T_sig, N) : emit_ctz_full(T_sig, N);
			cache[T_wire] = full;
		}

		if (v == PEVariant::CLZ_SHORT || v == PEVariant::CTZ_SHORT) {
			if (GetSize(full) > 0)
				full = full.extract(0, GetSize(full) - 1);
		}
		// Match the user-visible output width.
		if (GetSize(full) > out_width)
			full = full.extract(0, out_width);
		while (GetSize(full) < out_width)
			full.append(SigSpec(State::S0));
		return full;
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
		auto multi = gen_rr_test_vectors(N);
		for (auto& rv : multi) {
			// Skip empty + one-hots already covered above.
			int pop = 0;
			auto b = rv.to_bits();
			for (int i = 0; i < N && i < (int)b.size(); i++)
				if (b[i] == State::S1) pop++;
			if (pop <= 1) continue;
			for (int s : starts)
				if (!check(rv, s)) return -1;
		}

		if (checks < 2 * GetSize(starts)) return -1;
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

	struct Rewrite {
		Wire* S_wire;
		Wire* T_wire;
		int N;
		int Wbits;
		PEVariant variant;
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
	};

	bool get_sole_whole_wire_driver(Wire* S_wire, Cell*& sole_driver, IdString& out_port) {
		SigSpec S_sig = sigmap(SigSpec(S_wire));
		pool<Cell*> drivers;
		for (auto bit : S_sig) {
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) return false;
			drivers.insert(it->second);
		}
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
		return out_sig == S_sig;
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
	bool cone_depends_only_on_T(SigSpec S_sig, const pool<SigBit>& T_bits) {
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
		ConstEval ce(module);

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

		struct SCand { Wire* w; Cell* drv; IdString port; int rank; };
		vector<SCand> s_cands;
		for (Wire* S_wire : wires_snapshot) {
			if (S_wire->port_input) continue;
			int Wbits = S_wire->width;
			if (Wbits < 2 || Wbits > max_W) continue;
			Cell* sole_driver = nullptr;
			IdString out_port;
			if (!get_sole_whole_wire_driver(S_wire, sole_driver, out_port)) continue;
			if (!driver_looks_interesting(sole_driver)) continue;
			int rank = 2;
			if (S_wire->port_output) rank = 0;
			else if (sole_driver->type.in(ID($mux), ID($pmux), ID($add), ID($sub), ID($and), ID($or)))
				rank = 1;
			s_cands.push_back({S_wire, sole_driver, out_port, rank});
		}
		std::sort(s_cands.begin(), s_cands.end(), [](const SCand& a, const SCand& b) {
			if (a.rank != b.rank) return a.rank < b.rank;
			return a.w->width > b.w->width;
		});

		for (auto& sc : s_cands) {
			Wire* S_wire = sc.w;
			Cell* sole_driver = sc.drv;
			IdString out_port = sc.port;

			pool<Cell*> cone_cells;
			pool<SigBit> leaf_bits;
			int st = get_cone(SigSpec(S_wire), cone_cells, leaf_bits,
			                  probe_cone_cells, max_leaf_bits);
			if (st < 0) {
				if (large_cone_budget <= 0) continue;
				large_cone_budget--;
				st = get_cone(SigSpec(S_wire), cone_cells, leaf_bits,
				              max_cone_cells, max_leaf_bits);
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
			                      sole_driver, out_port});
		}

		// Stage 2: process candidates in order of cone size (LARGEST first).
		// Verific-style lowerings often expose several wires along the same
		// chain that all fingerprint as a PE on the same input bus (e.g. a
		// "found ? chain_out : default" wrapper mux plus the raw chain tail
		// plus a downstream mask & enc-merge). Rewriting only one of them
		// leaves the chain alive feeding the others, so we rewrite each
		// match independently and de-duplicate the emitted log-depth
		// network through the per-input clz/ctz cache.
		std::sort(candidates.begin(), candidates.end(),
		          [](const Candidate& a, const Candidate& b) {
		              if (GetSize(a.cone_cells) != GetSize(b.cone_cells))
		                  return GetSize(a.cone_cells) > GetSize(b.cone_cells);
		              return GetSize(a.cone_bits) > GetSize(b.cone_bits);
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
				if (!cone_depends_only_on_T(S_sig, T_bits)) continue;

				PEVariant variant = fingerprint(ce, T_sig, S_sig, N, Wbits);
				if (variant == PEVariant::NONE) continue;

				log("  %s: %s <- %s(%s) [N=%d, W=%d]\n",
				    log_id(module), log_id(cand.S_wire), variant_name(variant),
				    log_id(T_wire), N, Wbits);

				rewrites.push_back({cand.S_wire, T_wire, N, Wbits, variant,
				                    cand.sole_driver, cand.out_port});
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

						int kind = fingerprint_rr(ce, req_sig, start_sig, S_sig, N, W);
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
		for (auto& r : rewrites) {
			cell = r.sole_driver;
			SigSpec new_S = emit_pe(r.variant, r.T_wire, r.N, r.Wbits);
			// Disconnect the old driver by re-pointing its Y to a fresh wire.
			Wire* dangling = module->addWire(NEW_ID2_SUFFIX("dangling"), r.Wbits);
			r.sole_driver->setPort(r.out_port, dangling);
			module->connect(SigSpec(r.S_wire), new_S);
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
		log("regions that implement a priority encoder, count-leading-zeros (CLZ), or\n");
		log("count-trailing-zeros (CTZ) on a single contiguous input wire, regardless\n");
		log("of how the RTL was written (unrolled for-loops, casez priority lists,\n");
		log("pmux chains, etc.). Each detected region is replaced with a log-depth\n");
		log("network built from $mux/$not/$sub cells.\n");
		log("\n");
		log("Detected variants:\n");
		log("\n");
		log("    clz_full  : result = N when input is 0, else N-1 - msb_set_pos.\n");
		log("                Output width = ceil(log2(N+1)).\n");
		log("    clz_short : result = N-1 - msb_set_pos for nonzero input; the\n");
		log("                output for input==0 is unconstrained. Output width =\n");
		log("                ceil(log2(N)).\n");
		log("    ctz_full  : symmetric to clz_full from the LSB side.\n");
		log("    ctz_short : symmetric to clz_short from the LSB side.\n");
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
		log("    -clz\n");
		log("        detect CLZ patterns only (also disables round-robin).\n");
		log("\n");
		log("    -ctz\n");
		log("        detect CTZ patterns only (also disables round-robin).\n");
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

		bool only_clz = false;
		bool only_ctz = false;
		bool no_rr = false;
		int max_width = 64;
		int min_width = 4;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-clz") { only_clz = true; continue; }
			if (args[argidx] == "-ctz") { only_ctz = true; continue; }
			if (args[argidx] == "-no-rr") { no_rr = true; continue; }
			if (args[argidx] == "-max-width" && argidx + 1 < args.size()) {
				max_width = std::stoi(args[++argidx]); continue;
			}
			if (args[argidx] == "-min-width" && argidx + 1 < args.size()) {
				min_width = std::stoi(args[++argidx]); continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		// -clz / -ctz select a single leading/trailing variant and disable
		// round-robin detection unless the user re-enables it explicitly.
		if (only_clz || only_ctz) no_rr = true;

		int total_regions = 0;
		int total_cells_added = 0;
		for (auto module : design->selected_modules()) {
			OptPriEncWorker worker(module);
			worker.detect_clz = !only_ctz;
			worker.detect_ctz = !only_clz;
			worker.detect_rr = !no_rr;
			worker.max_input_width = max_width;
			worker.min_input_width = min_width;
			worker.run();
			total_regions += worker.regions_rewritten;
			total_cells_added += worker.cells_added;
		}

		log("Rewrote %d region(s); emitted %d new cell(s).\n",
		    total_regions, total_cells_added);

		Yosys::run_pass("clean -purge");
	}
} OptPriEncPass;

PRIVATE_NAMESPACE_END
