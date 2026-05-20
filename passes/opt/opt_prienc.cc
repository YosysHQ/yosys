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
#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

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

static int clog2_int(int x) {
	int r = 0;
	while ((1 << r) < x) r++;
	return r;
}

// Build an N-bit Const from a uint64_t pattern. Bit i set in `pattern` -> bit i
// of the result. Bits beyond 64 are zero.
static Const u64_const(uint64_t pattern, int N) {
	std::vector<State> bits(N, State::S0);
	for (int i = 0; i < N && i < 64; i++)
		if ((pattern >> i) & 1ULL) bits[i] = State::S1;
	return Const(bits);
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

	bool is_sequential(Cell* c) {
		return c->type.in(
			ID($ff), ID($dff), ID($dffe), ID($adff), ID($adffe),
			ID($sdff), ID($sdffe), ID($sdffce), ID($dffsr), ID($dffsre),
			ID($_DFF_P_), ID($_DFF_N_),
			ID($_DFFE_PP_), ID($_DFFE_PN_), ID($_DFFE_NP_), ID($_DFFE_NN_),
			ID($_DFF_PP0_), ID($_DFF_PP1_), ID($_DFF_PN0_), ID($_DFF_PN1_),
			ID($_DFF_NP0_), ID($_DFF_NP1_), ID($_DFF_NN0_), ID($_DFF_NN1_),
			ID($dlatch), ID($adlatch), ID($dlatchsr),
			ID($mem), ID($mem_v2), ID($meminit), ID($meminit_v2),
			ID($memrd), ID($memrd_v2), ID($memwr), ID($memwr_v2),
			ID($fsm),
			ID($assert), ID($assume), ID($cover), ID($live), ID($fair),
			ID($print), ID($check),
			ID($anyconst), ID($anyseq), ID($allconst), ID($allseq),
			ID($initstate));
	}

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
	// Returns false if the cone touches anything we don't want to drive a PE.
	bool get_cone(SigSpec from, pool<Cell*>& cone_cells, pool<SigBit>& leaf_bits) {
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		for (auto bit : sigmap(from)) {
			if (!bit.wire) continue;
			if (visited.insert(bit).second) worklist.push(bit);
		}
		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();
			if (input_port_bits.count(bit)) { leaf_bits.insert(bit); continue; }
			auto it = bit_to_driver.find(bit);
			if (it == bit_to_driver.end()) { leaf_bits.insert(bit); continue; }
			Cell* drv = it->second;
			if (sequential_cells.count(drv)) { leaf_bits.insert(bit); continue; }
			if (!cone_cells.insert(drv).second) continue;
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

	// Collect all wires in the module whose bits are entirely within the
	// (leaf_bits + cone-driven bits) frontier of S's cone. These are
	// candidates for the input bus T -- either a leaf wire bottoming out the
	// cone (ports / FF outputs) or an internal wire produced by a cone cell.
	// Wires with a valid power-of-2-friendly width are preferred but we let
	// the fingerprint be the final arbiter.
	vector<Wire*> find_candidate_Ts(Wire* S_wire,
	                                const pool<Cell*>& cone_cells,
	                                const pool<SigBit>& leaf_bits) {
		pool<SigBit> cone_bits = leaf_bits;
		for (Cell* c : cone_cells) {
			for (auto& conn : c->connections()) {
				if (!c->output(conn.first)) continue;
				for (auto bit : sigmap(conn.second))
					if (bit.wire) cone_bits.insert(bit);
			}
		}
		vector<Wire*> out;
		for (Wire* w : module->wires()) {
			if (w == S_wire) continue;
			if (w->width < min_input_width || w->width > max_input_width) continue;
			bool all_in = true;
			for (auto bit : sigmap(SigSpec(w))) {
				if (!cone_bits.count(bit)) { all_in = false; break; }
			}
			if (all_in) out.push_back(w);
		}
		// Try wider candidates first: the more bits the fingerprint constrains,
		// the lower the chance of false positives, and longer chains usually
		// imply a more substantial detection target.
		std::sort(out.begin(), out.end(), [](Wire* a, Wire* b) {
			return a->width > b->width;
		});
		return out;
	}

	// Build the test-vector deck for an N-bit input.
	vector<Const> gen_test_vectors(int N) {
		vector<Const> vs;
		vs.push_back(u64_const(0, N));
		for (int k = 0; k < N; k++) {
			std::vector<State> bits(N, State::S0);
			bits[k] = State::S1;
			vs.push_back(Const(bits));
		}
		for (int k = 1; k <= N; k++) {
			std::vector<State> bits(N, State::S0);
			for (int i = 0; i < k; i++) bits[i] = State::S1;
			vs.push_back(Const(bits));
		}
		for (int k = 0; k < N; k++) {
			std::vector<State> bits(N, State::S1);
			for (int i = 0; i < k; i++) bits[i] = State::S0;
			vs.push_back(Const(bits));
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

	// Run all candidate test vectors through ConstEval and try to match each of
	// the four PE variants against the recorded outputs. Returns the matched
	// variant, or NONE.
	PEVariant fingerprint(SigSpec T_sig, SigSpec S_sig, int N, int Wbits) {
		ConstEval ce(module);

		bool clz_full_ok = detect_clz && (Wbits == clog2_int(N + 1));
		bool ctz_full_ok = detect_ctz && (Wbits == clog2_int(N + 1));
		bool clz_short_ok = detect_clz && (Wbits == clog2_int(N));
		bool ctz_short_ok = detect_ctz && (Wbits == clog2_int(N));

		if (!clz_full_ok && !ctz_full_ok && !clz_short_ok && !ctz_short_ok)
			return PEVariant::NONE;

		auto vs = gen_test_vectors(N);
		for (auto& v : vs) {
			ce.push();
			ce.set(T_sig, v);
			SigSpec out = S_sig;
			SigSpec undef;
			bool ok = ce.eval(out, undef);
			ce.pop();
			if (!ok || !out.is_fully_const()) return PEVariant::NONE;
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

			if (!clz_full_ok && !ctz_full_ok && !clz_short_ok && !ctz_short_ok)
				return PEVariant::NONE;
		}

		// Prefer the most specific match (full > short; CLZ before CTZ tie-breaker).
		if (clz_full_ok)  return PEVariant::CLZ_FULL;
		if (ctz_full_ok)  return PEVariant::CTZ_FULL;
		if (clz_short_ok) return PEVariant::CLZ_SHORT;
		if (ctz_short_ok) return PEVariant::CTZ_SHORT;
		return PEVariant::NONE;
	}

	// Recursive CLZ on a power-of-2-width input. Returns a (log2(N)+1)-bit
	// SigSpec whose MSB is 1 iff T == 0 and whose lower bits are the leading-
	// zeros count for nonzero T.
	SigSpec emit_clz_pow2(SigSpec T, int N) {
		log_assert(N >= 1 && (N & (N - 1)) == 0);
		if (N == 1) {
			cells_added++;
			return module->Not(NEW_ID2_SUFFIX("clznot"), T);
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
		SigSpec lo_nonzero_spec = module->Not(NEW_ID2_SUFFIX("clz_lonz"), SigSpec(lo_zero));
		cells_added++;
		SigBit lo_nonzero = lo_nonzero_spec[0];

		SigSpec pad_clz_lo;
		if (W1 >= 2)
			pad_clz_lo.append(clz_lo.extract(0, W1 - 1));
		pad_clz_lo.append(lo_nonzero);
		pad_clz_lo.append(lo_zero);

		// $mux: Y = S ? B : A. We want Y = hi_zero ? pad_clz_lo : pad_clz_hi.
		cells_added++;
		return module->Mux(NEW_ID2_SUFFIX("clzmux"), pad_clz_hi, pad_clz_lo, SigSpec(hi_zero));
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
		SigSpec sub = module->Sub(NEW_ID2_SUFFIX("clzsub"), clz_padded, SigSpec(Const(pad_amount, GetSize(clz_padded))));
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
		Cell* sole_driver;
		IdString out_port;
	};

	void run() {
		vector<Wire*> wires_snapshot(module->wires().begin(), module->wires().end());

		// Stage 1: build candidate set with cones, filter by driver/width.
		vector<Candidate> candidates;
		int max_W = clog2_int(max_input_width + 1);
		for (Wire* S_wire : wires_snapshot) {
			if (S_wire->port_input) continue;
			int Wbits = S_wire->width;
			if (Wbits < 2 || Wbits > max_W) continue;

			pool<Cell*> cone_cells;
			pool<SigBit> leaf_bits;
			if (!get_cone(SigSpec(S_wire), cone_cells, leaf_bits)) continue;
			if (cone_cells.empty()) continue;

			SigSpec S_sig = sigmap(SigSpec(S_wire));
			pool<Cell*> drivers;
			for (auto bit : S_sig) {
				auto it = bit_to_driver.find(bit);
				if (it == bit_to_driver.end()) { drivers.clear(); break; }
				drivers.insert(it->second);
			}
			if (GetSize(drivers) != 1) continue;
			Cell* sole_driver = *drivers.begin();
			IdString out_port;
			SigSpec out_sig;
			for (auto& conn : sole_driver->connections()) {
				if (sole_driver->output(conn.first)) {
					out_port = conn.first;
					out_sig = sigmap(conn.second);
					break;
				}
			}
			if (out_sig != S_sig) continue;

			pool<SigBit> cone_bits = leaf_bits;
			for (Cell* c : cone_cells) {
				for (auto& conn : c->connections()) {
					if (!c->output(conn.first)) continue;
					for (auto bit : sigmap(conn.second))
						if (bit.wire) cone_bits.insert(bit);
				}
			}
			candidates.push_back({S_wire, std::move(cone_cells), std::move(leaf_bits),
			                      std::move(cone_bits), sole_driver, out_port});
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

			vector<Wire*> Ts = find_candidate_Ts(cand.S_wire, cand.cone_cells, cand.leaf_bits);
			for (Wire* T_wire : Ts) {
				int N = T_wire->width;
				int W_full = clog2_int(N + 1);
				int W_short = clog2_int(N);
				if (Wbits != W_full && Wbits != W_short) continue;

				SigSpec T_sig = sigmap(SigSpec(T_wire));
				PEVariant variant = fingerprint(T_sig, S_sig, N, Wbits);
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
		log("    -clz\n");
		log("        detect CLZ patterns only.\n");
		log("\n");
		log("    -ctz\n");
		log("        detect CTZ patterns only.\n");
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
		int max_width = 64;
		int min_width = 4;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-clz") { only_clz = true; continue; }
			if (args[argidx] == "-ctz") { only_ctz = true; continue; }
			if (args[argidx] == "-max-width" && argidx + 1 < args.size()) {
				max_width = std::stoi(args[++argidx]); continue;
			}
			if (args[argidx] == "-min-width" && argidx + 1 < args.size()) {
				min_width = std::stoi(args[++argidx]); continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0;
		int total_cells_added = 0;
		for (auto module : design->selected_modules()) {
			OptPriEncWorker worker(module);
			worker.detect_clz = !only_ctz;
			worker.detect_ctz = !only_clz;
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
