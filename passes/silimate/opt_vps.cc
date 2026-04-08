/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2025  Silimate Inc.     <akash@silimate.com>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptVpsWorker
{
	struct PmuxInfo {
		Cell *cell;
		int window_start;
	};

	struct FeedbackInfo {
		Cell *feedback_mux;
		Cell *and_gate;
		SigBit q_bit;
	};

	Module *module;
	SigMap sigmap;
	dict<SigBit, Cell *> bit_drivers;
	dict<SigBit, pool<Cell *>> bit_consumers;
	int groups_optimized = 0;
	int pmux_replaced = 0;
	int reduce_or_replaced = 0;
	int feedback_collapsed = 0;
	int vps_reads_replaced = 0;
	int min_stride;
	pool<Cell *> vps_shr_cells;

	OptVpsWorker(Module *module, int min_stride)
		: module(module), sigmap(module), min_stride(min_stride)
	{
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					for (int i = 0; i < GetSize(conn.second); i++) {
						SigBit bit = sigmap(conn.second[i]);
						bit_drivers[bit] = cell;
					}
				else
					for (int i = 0; i < GetSize(conn.second); i++) {
						SigBit bit = sigmap(conn.second[i]);
						if (bit.wire)
							bit_consumers[bit].insert(cell);
					}
	}

	Cell *find_sole_consumer(SigBit bit)
	{
		auto it = bit_consumers.find(sigmap(bit));
		if (it == bit_consumers.end() || it->second.size() != 1)
			return nullptr;
		return *(it->second.begin());
	}

	bool is_decoder_shl(Cell *cell)
	{
		if (cell->type != ID($shl))
			return false;
		SigSpec a = cell->getPort(ID::A);
		if (!a.is_fully_const())
			return false;
		Const a_val = a.as_const();
		if (GetSize(a_val) < 1 || a_val[0] != State::S1)
			return false;
		for (int i = 1; i < GetSize(a_val); i++)
			if (a_val[i] != State::S0)
				return false;
		return true;
	}

	// Trace an S-port bit back through an optional AND gate to find
	// which decoder output position it comes from.  Returns -1 on failure.
	// If overflow_cond is non-null, stores the non-decoder input of the
	// AND gate (the overflow mask bit), or State::S1 if direct.
	int trace_to_decoder_pos(SigBit bit, SigSpec &decoder_y,
				 SigBit *overflow_cond = nullptr)
	{
		SigBit mapped = sigmap(bit);

		for (int i = 0; i < GetSize(decoder_y); i++)
			if (sigmap(decoder_y[i]) == mapped) {
				if (overflow_cond)
					*overflow_cond = State::S1;
				return i;
			}

		Cell *driver = bit_drivers.at(mapped, nullptr);
		if (!driver)
			return -1;

		if (driver->type == ID($and)) {
			SigSpec port_a = driver->getPort(ID::A);
			SigSpec port_b = driver->getPort(ID::B);
			if (GetSize(port_a) == 1 && GetSize(port_b) == 1) {
				SigBit a = sigmap(port_a[0]);
				SigBit b = sigmap(port_b[0]);
				for (int i = 0; i < GetSize(decoder_y); i++) {
					SigBit dy = sigmap(decoder_y[i]);
					if (dy == a) {
						if (overflow_cond) *overflow_cond = b;
						return i;
					}
					if (dy == b) {
						if (overflow_cond) *overflow_cond = a;
						return i;
					}
				}
			}
		}

		if (driver->type == ID($_AND_)) {
			SigBit a = sigmap(driver->getPort(ID::A));
			SigBit b = sigmap(driver->getPort(ID::B));
			for (int i = 0; i < GetSize(decoder_y); i++) {
				SigBit dy = sigmap(decoder_y[i]);
				if (dy == a) {
					if (overflow_cond) *overflow_cond = b;
					return i;
				}
				if (dy == b) {
					if (overflow_cond) *overflow_cond = a;
					return i;
				}
			}
		}

		return -1;
	}

	// Extract the constant addend from a binary_index signal.
	// If binary_index = $add(dynamic, C) or $add(C, dynamic),
	// return C.  Otherwise return 0.  Handles chains of
	// $add/$sub up to 8 levels deep.
	// Evaluate a signal assuming all primary inputs are 0.
	// Uses recursive constant propagation through the driver
	// graph.  Handles $add, $sub, $not, $and, $or, $xor, $shl,
	// $shr, $neg and pass-through (no driver → 0).
	int eval_at_zero(SigSpec sig)
	{
		dict<SigBit, int> cache;
		int result = 0;
		for (int i = 0; i < GetSize(sig); i++) {
			int v = eval_bit_at_zero(sigmap(sig[i]), cache, 0);
			result |= (v << i);
		}
		return result;
	}

	int eval_bit_at_zero(SigBit b, dict<SigBit, int> &cache, int depth)
	{
		if (b == State::S0) return 0;
		if (b == State::S1) return 1;
		if (!b.wire) return 0;

		auto it = cache.find(b);
		if (it != cache.end()) return it->second;
		if (depth > 64) return 0;

		cache[b] = 0;

		Cell *drv = bit_drivers.at(b, nullptr);
		if (!drv) return 0;

		if (!drv->hasPort(ID::Y) || !drv->hasPort(ID::A))
			return 0;

		int bit_pos = -1;
		SigSpec dy = drv->getPort(ID::Y);
		for (int j = 0; j < GetSize(dy); j++)
			if (sigmap(dy[j]) == b) { bit_pos = j; break; }
		if (bit_pos < 0) return 0;

		int64_t av = 0, bv = 0;
		SigSpec pa = drv->getPort(ID::A);
		SigSpec pb = drv->hasPort(ID::B) ? drv->getPort(ID::B) : SigSpec();
		for (int i = 0; i < GetSize(pa) && i < 62; i++)
			av |= ((int64_t)eval_bit_at_zero(sigmap(pa[i]), cache,
							  depth+1) << i);
		for (int i = 0; i < GetSize(pb) && i < 62; i++)
			bv |= ((int64_t)eval_bit_at_zero(sigmap(pb[i]), cache,
							  depth+1) << i);

		int64_t rv = 0;
		if (drv->type == ID($add)) rv = av + bv;
		else if (drv->type == ID($sub)) rv = av - bv;
		else if (drv->type == ID($mul)) rv = av * bv;
		else if (drv->type == ID($and) || drv->type == ID($_AND_)) rv = av & bv;
		else if (drv->type == ID($or) || drv->type == ID($_OR_)) rv = av | bv;
		else if (drv->type == ID($xor) || drv->type == ID($_XOR_)) rv = av ^ bv;
		else if (drv->type == ID($not) || drv->type == ID($_NOT_)) rv = ~av;
		else if (drv->type == ID($neg)) rv = -av;
		else if (drv->type == ID($shl) || drv->type == ID($sshl)) rv = av << bv;
		else if (drv->type == ID($shr) || drv->type == ID($sshr)) rv = av >> bv;
		else if (drv->type == ID($mux)) {
			SigSpec sp = drv->getPort(ID::S);
			int sv = eval_bit_at_zero(sigmap(sp[0]), cache, depth+1);
			rv = sv ? bv : av;
		} else {
			cache[b] = 0;
			return 0;
		}

		int val = (rv >> bit_pos) & 1;
		cache[b] = val;
		return val;
	}

	// Trace a signal back through the driver graph to find the
	// set of root bits (primary inputs / FF outputs) that
	// influence it.  Returns them as a sorted SigSpec.
	SigSpec trace_input_roots(SigSpec sig)
	{
		pool<SigBit> roots, visited;
		std::vector<SigBit> worklist;
		for (auto bit : sig)
			worklist.push_back(sigmap(bit));
		while (!worklist.empty()) {
			SigBit b = worklist.back();
			worklist.pop_back();
			if (!visited.insert(b).second)
				continue;
			Cell *drv = bit_drivers.at(b, nullptr);
			if (!drv) {
				if (b.wire)
					roots.insert(b);
				continue;
			}
			for (auto &conn : drv->connections())
				if (!drv->output(conn.first))
					for (auto bit2 : conn.second)
						worklist.push_back(sigmap(bit2));
		}
		SigSpec result;
		for (auto b : roots)
			result.append(b);
		result.sort();
		return result;
	}

	void run()
	{
		std::vector<Cell *> decoders;
		for (auto cell : module->selected_cells())
			if (is_decoder_shl(cell))
				decoders.push_back(cell);

		// --- Cross-decoder VPS read merge ---
		// Collect stride-1 VPS read candidates across ALL decoders.
		// Group by the underlying SOURCE REGISTER (identified by the
		// wire of the first reconstructed source bit).  When multiple
		// reads extract adjacent byte lanes from the same register
		// with verified data overlap, merge them into one wider
		// barrel shifter.

		struct XReadCandidate {
			Cell *decoder;
			Cell *pmux;
			int W;
			int base;
			int valid_n;
			std::vector<int> s_indices;
			Wire *src_wire;    // register wire (from first source bit)
			int src_offset;    // offset of first source bit in that wire
			int idx_const;     // constant part of decoder binary_index
			SigSpec idx_roots; // primary input bits influencing decoder
		};

		std::vector<XReadCandidate> all_reads;

		for (auto decoder : decoders) {
			SigSpec decoder_y = decoder->getPort(ID::Y);

			for (auto cell : module->selected_cells()) {
				if (cell->type != ID($pmux))
					continue;
				int W = cell->getParam(ID::WIDTH).as_int();
				if (W <= 1) continue;
				SigSpec sig_a = cell->getPort(ID::A);
				if (!sig_a.is_fully_zero()) continue;

				SigSpec sig_s = cell->getPort(ID::S);
				SigSpec sig_b = cell->getPort(ID::B);
				int N = GetSize(sig_s);

				std::vector<int> dec_positions, s_indices;
				for (int i = 0; i < N; i++) {
					SigBit sb = sigmap(sig_s[i]);
					if (sb == State::S0) continue;
					int pos = trace_to_decoder_pos(sig_s[i], decoder_y);
					if (pos < 0) break;
					dec_positions.push_back(pos);
					s_indices.push_back(i);
				}
				if (GetSize(dec_positions) < 2) continue;

				bool contiguous = true;
				for (int i = 1; i < GetSize(dec_positions); i++)
					if (dec_positions[i] != dec_positions[0] + i)
						{ contiguous = false; break; }
				if (!contiguous) continue;

				int sliding_n = 1;
				for (int k = 0; k < GetSize(s_indices) - 1; k++) {
					int si_cur = s_indices[k], si_nxt = s_indices[k + 1];
					bool ok = true;
					for (int j = 1; j < W && ok; j++)
						if (sigmap(sig_b[si_cur * W + j]) !=
						    sigmap(sig_b[si_nxt * W + (j - 1)]))
							ok = false;
					if (!ok) break;
					sliding_n = k + 2;
				}
				if (sliding_n < 2) continue;

				int base = dec_positions[0];

				// Find first source bit with a valid wire (skip
				// don't-care bits that arise when base < W-1)
				Wire *reg_wire = nullptr;
				int reg_offset = -1;
				for (int k = 0; k < sliding_n + W - 1 && !reg_wire; k++) {
					int idx = std::min(k, sliding_n - 1);
					int si = s_indices[idx];
					int j = k - idx;
					if (j >= W) break;
					SigBit sb = sigmap(sig_b[si * W + j]);
					if (sb.wire) {
						reg_wire = sb.wire;
						reg_offset = sb.offset - k;
					}
				}
				if (!reg_wire) continue;

				SigSpec binary_idx = decoder->getPort(ID::B);
				SigSpec roots = trace_input_roots(binary_idx);
				int idx_c = eval_at_zero(binary_idx);

				all_reads.push_back({decoder, cell, W, base, sliding_n,
					{s_indices.begin(), s_indices.begin() + sliding_n},
					reg_wire, reg_offset, idx_c, roots});
			}
		}

		// Group by (source wire, width, index root bits)
		struct SrcKey {
			Wire *wire;
			int W;
			SigSpec roots;
			bool operator<(const SrcKey &o) const {
				if (wire != o.wire) return wire < o.wire;
				if (W != o.W) return W < o.W;
				return roots < o.roots;
			}
		};
		std::map<SrcKey, std::vector<int>> src_groups;
		for (int i = 0; i < GetSize(all_reads); i++)
			src_groups[{all_reads[i].src_wire, all_reads[i].W,
				    all_reads[i].idx_roots}].push_back(i);

		// Compute effective register offset: for reads sharing
		// the same data port but using different decoders with
		// different constant offsets in binary_index, the
		// effective offset = src_offset + idx_const.  This lets
		// reads like source[(n+31)-:32] and source[(n+63)-:32]
		// be recognized as accessing adjacent 32-bit windows.
		auto eff_offset = [&](const XReadCandidate &r) -> int {
			return r.src_offset + r.idx_const;
		};

		for (auto &[key, indices] : src_groups) {
			if (GetSize(indices) < 2) continue;
			int W0 = key.W;

			// Sort by effective offset (data position in register)
			std::sort(indices.begin(), indices.end(),
				[&](int a, int b) {
					return eff_offset(all_reads[a]) < eff_offset(all_reads[b]);
				});

			

			// Find maximal contiguous runs where effective offset
			// values differ by exactly W
			int run_start = 0;
			while (run_start < GetSize(indices)) {
				int run_end = run_start + 1;
				while (run_end < GetSize(indices) &&
				       eff_offset(all_reads[indices[run_end]]) ==
				       eff_offset(all_reads[indices[run_end-1]]) + W0)
					run_end++;

				int run_len = run_end - run_start;
				if (run_len < 2) {
					run_start = run_end;
					continue;
				}

				// Check if reads come from different decoders
				bool different_decoders = false;
				for (int ri = run_start + 1; ri < run_end; ri++)
					if (all_reads[indices[ri]].idx_const !=
					    all_reads[indices[run_start]].idx_const)
						{ different_decoders = true; break; }

				auto &lowest = all_reads[indices[run_start]];
				int combined_W = W0 * run_len;

				if (different_decoders) {
					// Different decoders: build source from
					// the register wire directly and compute
					// shift from the dynamic part of binary_index.
					Wire *reg = lowest.src_wire;
					int lowest_eff = eff_offset(lowest);

					// The source covers the register range
					// needed by all reads across all dynamic
					// index values.  valid_n gives the decoder
					// range; combined_W is the output width.
					int src_start = std::max(0, lowest_eff);
					int src_end = std::min(GetSize(reg) - 1,
						lowest_eff + lowest.valid_n +
						combined_W - 2);
					if (src_end < src_start) {
						run_start = run_end;
						continue;
					}
					SigSpec source = SigSpec(reg, src_start,
						src_end - src_start + 1);

					// Shift amount: the dynamic part.  For
					// binary_index = n + idx_const and VPS
					// [idx -: W], the register position of
					// output bit 0 is idx - W + 1 = n +
					// idx_const - W + 1.  The lowest eff_offset
					// is src_offset + idx_const_lowest, and
					// register bit at eff_offset is at source
					// position eff_offset - src_start.  So
					// shift = (n + idx_const - W + 1 -
					// src_offset) - src_start.  Since
					// eff_offset = src_offset + idx_const,
					// shift = n - W + 1 + eff_offset -
					// src_start = n - W + 1 + lowest_eff -
					// src_start.
					//
					// Equivalently, shift = binary_index -
					// (W - 1) - src_offset - src_start.  Since
					// binary_index = decoder B port and
					// src_offset = lowest.src_offset:
					SigSpec binary_index = lowest.decoder->getPort(ID::B);
					int base_sub = (W0 - 1) + src_start;

					SigSpec raw_idx;
					if (base_sub != 0) {
						Wire *sub_w = module->addWire(
							NEW_ID_SUFFIX("vps_merge_idx"),
							GetSize(binary_index));
						module->addSub(NEW_ID_SUFFIX("vps_merge_sub"),
							binary_index,
							Const(base_sub, GetSize(binary_index)),
							sub_w);
						raw_idx = SigSpec(sub_w);
					} else {
						raw_idx = binary_index;
					}

					// Detect alignment: look for constant
					// lower bits in the shift expression,
					// tracing through $add/$sub if needed
					// (mirrors process_vps_reads).
					auto count_const_lower = [&](SigSpec sig) -> std::pair<int, int> {
						int count = 0, value = 0;
						for (int i = 0; i < GetSize(sig); i++) {
							SigBit b = sigmap(sig[i]);
							if (b == State::S0) count++;
							else if (b == State::S1) { value |= (1 << i); count++; }
							else break;
						}
						return {count, value};
					};

					int log2_align = 0;
					int fixed_lower = 0;
					{
						auto [n0, v0] = count_const_lower(binary_index);
						if (n0 > 0) { log2_align = n0; fixed_lower = v0; }
						if (log2_align == 0) {
							Cell *drv = nullptr;
							for (int i = 0; i < GetSize(binary_index); i++) {
								Cell *d = bit_drivers.at(sigmap(binary_index[i]), nullptr);
								if (!d) { drv = nullptr; break; }
								if (!drv) drv = d;
								else if (drv != d) { drv = nullptr; break; }
							}
							if (drv && (drv->type == ID($add) || drv->type == ID($sub))) {
								SigSpec aa = drv->getPort(ID::A);
								SigSpec ab = drv->getPort(ID::B);
								SigSpec non_const;
								int offset = 0;
								bool is_sub = (drv->type == ID($sub));
								if (aa.is_fully_const()) { offset = aa.as_int(); non_const = ab; }
								else if (ab.is_fully_const()) { offset = ab.as_int(); non_const = aa; }
								if (GetSize(non_const) > 0) {
									auto [nc, nv] = count_const_lower(non_const);
									if (nc > 0) {
										log2_align = nc;
										int mask = (1 << nc) - 1;
										if (is_sub) {
											if (non_const == ab)
												fixed_lower = ((offset & mask) - nv) & mask;
											else
												fixed_lower = (nv - (offset & mask)) & mask;
										} else {
											fixed_lower = (nv + (offset & mask)) & mask;
										}
									}
								}
							}
						}
					}

					SigSpec shift_amount;
					if (log2_align > 0) {
						int adj_lower = (fixed_lower - (base_sub & ((1 << log2_align) - 1)))
								& ((1 << log2_align) - 1);
						for (int i = 0; i < log2_align; i++)
							shift_amount.append((adj_lower >> i) & 1 ? State::S1 : State::S0);
						shift_amount.append(raw_idx.extract(
							log2_align, GetSize(raw_idx) - log2_align));
					} else {
						shift_amount = raw_idx;
					}

					Wire *merged_y = module->addWire(
						NEW_ID_SUFFIX("vps_merge_y"), combined_W);
					Cell *shr = module->addShr(NEW_ID_SUFFIX("vps_merge_shr"),
						source, shift_amount, SigSpec(merged_y));
					shr->add_strpool_attribute(ID::src,
						lowest.pmux->get_strpool_attribute(ID::src));
					vps_shr_cells.insert(shr);

					int lowest_eff_off = eff_offset(lowest);
					for (int i = 0; i < run_len; i++) {
						auto &r = all_reads[indices[run_start + i]];
						SigSpec pmux_y = r.pmux->getPort(ID::Y);
						int byte_offset = eff_offset(r) - lowest_eff_off;
						module->connect(pmux_y,
							SigSpec(merged_y, byte_offset, r.W));

						log("  VPS xread merge: pmux %s (W=%d, eff=%d)"
						    " -> merged $shr [%d:%d]\n",
						    log_id(r.pmux->name), r.W, eff_offset(r),
						    byte_offset + r.W - 1, byte_offset);

						module->remove(r.pmux);
						pmux_replaced++;
						vps_reads_replaced++;
					}

					log("  VPS merged %d cross-decoder reads -> $shr"
					    " WIDTH=%d, src=%d, align=%d\n",
					    run_len, combined_W, GetSize(source),
					    log2_align > 0 ? (1 << log2_align) : 1);
					groups_optimized++;
					run_start = run_end;
					continue;
				}

				// Same decoder: verify data overlap between
				// adjacent reads.
				// source[k] = sig_b[s_indices[min(k,vn-1)] * W + k - min(k,vn-1)]
				bool overlap_ok = true;
				for (int ri = run_start; ri < run_end - 1 && overlap_ok; ri++) {
					auto &rA = all_reads[indices[ri]];
					auto &rB = all_reads[indices[ri + 1]];
					SigSpec bA = rA.pmux->getPort(ID::B);
					SigSpec bB = rB.pmux->getPort(ID::B);
					int check_len = std::min(W0,
						std::min(rA.valid_n, rB.valid_n));
					for (int c = 0; c < check_len && overlap_ok; c++) {
						int posA = c + W0;
						int idxA = std::min(posA, rA.valid_n - 1);
						int jA = posA - idxA;
						int idxB = std::min(c, rB.valid_n - 1);
						int jB = c - idxB;
						if (jA >= W0 || jB >= W0) break;
						if (sigmap(bA[rA.s_indices[idxA] * W0 + jA]) !=
						    sigmap(bB[rB.s_indices[idxB] * W0 + jB]))
							overlap_ok = false;
					}
				}

				if (!overlap_ok) {
					log("    Run [%d..%d]: overlap check failed\n",
					    run_start, run_end - 1);
					run_start = run_end;
					continue;
				}

				// --- Merge this run into one wider barrel shifter ---
				int lowest_base = lowest.base;

				Cell *ref_pmux = lowest.pmux;
				SigSpec ref_sig_b = ref_pmux->getPort(ID::B);
				int ref_valid_n = lowest.valid_n;
				int source_width = ref_valid_n + combined_W - 1;
				SigSpec source;
				for (int k = 0; k < source_width; k++) {
					int idx = std::min(k, ref_valid_n - 1);
					int si = lowest.s_indices[idx];
					int j = k - idx;
					if (j < W0)
						source.append(sigmap(ref_sig_b[si * W0 + j]));
					else {
						int extra = j - W0;
						int next_ri = run_start + 1 + extra / W0;
						if (next_ri < run_end) {
							auto &rN = all_reads[indices[next_ri]];
							SigSpec bN = rN.pmux->getPort(ID::B);
							int siN = rN.s_indices[std::min(idx, rN.valid_n - 1)];
							int jN = extra % W0;
							source.append(sigmap(bN[siN * W0 + jN]));
						} else {
							source.append(State::S0);
						}
					}
				}

				// Truncate to actual register range
				Wire *merge_reg = nullptr;
				for (int i = 0; i < GetSize(source); i++) {
					SigBit b = source[i];
					if (b.wire) { merge_reg = b.wire; break; }
				}
				if (merge_reg) {
					int first_reg = -1, last_reg = -1;
					for (int i = 0; i < GetSize(source); i++) {
						SigBit b = source[i];
						if (b.wire == merge_reg) {
							if (first_reg < 0) first_reg = i;
							last_reg = i;
						}
					}
					if (first_reg > 0 || last_reg < GetSize(source) - 1) {
						int new_len = last_reg - first_reg + 1;
						source = source.extract(first_reg, new_len);
						lowest_base += first_reg;
					}
				}

				SigSpec binary_index = lowest.decoder->getPort(ID::B);
				SigSpec shift_amount;
				SigSpec raw_idx = binary_index;
				if (lowest_base > 0) {
					Wire *sub_w = module->addWire(
						NEW_ID_SUFFIX("vps_merge_idx"),
						GetSize(binary_index));
					module->addSub(NEW_ID_SUFFIX("vps_merge_sub"),
						binary_index,
						Const(lowest_base, GetSize(binary_index)),
						sub_w);
					raw_idx = SigSpec(sub_w);
				}

				auto count_const_lower = [&](SigSpec sig) -> std::pair<int, int> {
					int count = 0, value = 0;
					for (int i = 0; i < GetSize(sig); i++) {
						SigBit b = sigmap(sig[i]);
						if (b == State::S0) count++;
						else if (b == State::S1) { value |= (1 << i); count++; }
						else break;
					}
					return {count, value};
				};

				int log2_align = 0;
				int fixed_lower = 0;
				{
					auto [n0, v0] = count_const_lower(binary_index);
					if (n0 > 0) { log2_align = n0; fixed_lower = v0; }
					if (log2_align == 0) {
						Cell *drv = nullptr;
						for (int i = 0; i < GetSize(binary_index); i++) {
							Cell *d = bit_drivers.at(sigmap(binary_index[i]), nullptr);
							if (!d) { drv = nullptr; break; }
							if (!drv) drv = d;
							else if (drv != d) { drv = nullptr; break; }
						}
						if (drv && (drv->type == ID($add) || drv->type == ID($sub))) {
							SigSpec aa = drv->getPort(ID::A);
							SigSpec ab = drv->getPort(ID::B);
							SigSpec non_const;
							int offset = 0;
							bool is_sub = (drv->type == ID($sub));
							if (aa.is_fully_const()) { offset = aa.as_int(); non_const = ab; }
							else if (ab.is_fully_const()) { offset = ab.as_int(); non_const = aa; }
							if (GetSize(non_const) > 0) {
								auto [nc, nv] = count_const_lower(non_const);
								if (nc > 0) {
									log2_align = nc;
									int mask = (1 << nc) - 1;
									if (is_sub) {
										if (non_const == ab)
											fixed_lower = ((offset & mask) - nv) & mask;
										else
											fixed_lower = (nv - (offset & mask)) & mask;
									} else {
										fixed_lower = (nv + (offset & mask)) & mask;
									}
								}
							}
						}
					}
				}

				if (log2_align > 0) {
					int adj_lower = (fixed_lower - (lowest_base & ((1 << log2_align) - 1)))
							& ((1 << log2_align) - 1);
					for (int i = 0; i < log2_align; i++)
						shift_amount.append((adj_lower >> i) & 1 ? State::S1 : State::S0);
					shift_amount.append(raw_idx.extract(
						log2_align, GetSize(binary_index) - log2_align));
				} else {
					shift_amount = raw_idx;
				}

				Wire *merged_y = module->addWire(
					NEW_ID_SUFFIX("vps_merge_y"), combined_W);
				Cell *shr = module->addShr(NEW_ID_SUFFIX("vps_merge_shr"),
					source, shift_amount, SigSpec(merged_y));
				shr->add_strpool_attribute(ID::src,
					ref_pmux->get_strpool_attribute(ID::src));
				vps_shr_cells.insert(shr);

				int lowest_eff_off = eff_offset(lowest);
				for (int i = 0; i < run_len; i++) {
					auto &r = all_reads[indices[run_start + i]];
					SigSpec pmux_y = r.pmux->getPort(ID::Y);
					int byte_offset = eff_offset(r) - lowest_eff_off;
					module->connect(pmux_y,
						SigSpec(merged_y, byte_offset, r.W));

					log("  VPS read merge: pmux %s (WIDTH=%d, base=%d)"
					    " -> merged $shr [%d:%d]\n",
					    log_id(r.pmux->name), r.W, r.base,
					    byte_offset + r.W - 1, byte_offset);

					module->remove(r.pmux);
					pmux_replaced++;
					vps_reads_replaced++;
				}

				log("  VPS merged %d reads (WIDTH=%d each) -> $shr WIDTH=%d%s\n",
				    run_len, W0, combined_W,
				    log2_align > 0 ?
				      stringf(", align=%d", 1 << log2_align).c_str() : "");
				groups_optimized++;

				run_start = run_end;
			}
		}

		// Process remaining decoders normally (for VPS writes and
		// unmerged VPS reads — merged reads' $pmux cells were
		// already removed, so they won't be found again)
		for (auto decoder : decoders)
			process_decoder(decoder);

		// --- Shared barrel shifter merge ---
		// After all VPS reads have been converted to $shr cells,
		// find groups that access the same register with byte-aligned
		// shifts sharing the same dynamic index variable.  Replace
		// each group with a single barrel shifter whose output feeds
		// all reads via simple wire slices.
		merge_shared_barrel_shifters();
	}

	void merge_shared_barrel_shifters()
	{
		// Rebuild bit_drivers to include cells created during
		// process_vps_reads (e.g. $sub cells for index adjustment)
		bit_drivers.clear();
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					for (int i = 0; i < GetSize(conn.second); i++) {
						SigBit bit = sigmap(conn.second[i]);
						bit_drivers[bit] = cell;
					}

		struct ShrInfo {
			Cell *shr;
			Wire *reg_wire;
			int reg_offset;       // bit offset of read within register
			int output_width;
			SigSpec shift_variable; // the variable (non-constant) upper shift bits
			int const_shift_lower; // constant value of lower shift bits
			int shift_align;       // number of constant lower shift bits
		};

		std::vector<ShrInfo> shr_infos;
		for (auto *shr : vps_shr_cells) {
			if (!shr->type.in(ID($shr)))
				continue;

			SigSpec source = shr->getPort(ID::A);
			SigSpec shift = shr->getPort(ID::B);
			SigSpec output = shr->getPort(ID::Y);
			int out_w = GetSize(output);

			// Find the register wire: all source bits must
			// come from the same wire
			Wire *reg_wire = nullptr;
			bool single_wire = true;
			for (auto b : source) {
				if (!b.wire) continue;
				if (!reg_wire) reg_wire = b.wire;
				else if (b.wire != reg_wire) { single_wire = false; break; }
			}
			if (!reg_wire || !single_wire)
				continue;

			// Determine the register bit offset: position of
			// output bit 0 relative to the register when the
			// variable part of the shift is zero
			// For the source, find the offset of source[0] within reg_wire
			int src_base = -1;
			for (int i = 0; i < GetSize(source); i++) {
				SigBit b = source[i];
				if (b.wire == reg_wire) {
					src_base = b.offset - i;
					break;
				}
			}
			if (src_base < 0) continue;

			// Count constant lower shift bits
			int shift_align = 0;
			int const_lower = 0;
			for (int i = 0; i < GetSize(shift); i++) {
				SigBit b = sigmap(shift[i]);
				if (b == State::S0)
					shift_align++;
				else if (b == State::S1)
					{ const_lower |= (1 << i); shift_align++; }
				else
					break;
			}

			SigSpec shift_var = shift.extract(shift_align,
				GetSize(shift) - shift_align);

			// reg_offset: register position of output bit 0 when
			// all dynamic inputs are zero.  Evaluated by
			// constant-propagating the full shift signal.
			int shift_at_zero = eval_at_zero(shift);
			int reg_offset = src_base + shift_at_zero;

			shr_infos.push_back({shr, reg_wire, reg_offset,
				out_w, shift_var, const_lower, shift_align});
		}

		if (shr_infos.empty())
			return;

		// Group by (register wire, input root bits of shift
		// variable, alignment).  Using trace_input_roots lets
		// reads with different carry patterns but the same
		// underlying dynamic variable group together.
		struct MergeKey {
			Wire *wire;
			SigSpec roots;
			int align;
			bool operator<(const MergeKey &o) const {
				if (wire != o.wire) return wire < o.wire;
				if (align != o.align) return align < o.align;
				return roots < o.roots;
			}
		};

		std::map<MergeKey, std::vector<int>> groups;
		for (int i = 0; i < GetSize(shr_infos); i++) {
			auto &info = shr_infos[i];
			SigSpec roots = trace_input_roots(info.shift_variable);
			groups[{info.reg_wire, roots, info.shift_align}].push_back(i);
		}

		for (auto &[key, indices] : groups) {
			if (GetSize(indices) < 2)
				continue;

			Wire *reg = key.wire;
			int reg_width = reg->width;
			int align = key.align;

			// Find the reference read (lowest reg_offset)
			int ref_idx = indices[0];
			for (int idx : indices)
				if (shr_infos[idx].reg_offset < shr_infos[ref_idx].reg_offset)
					ref_idx = idx;
			auto &ref_info = shr_infos[ref_idx];
			int ref_offset = ref_info.reg_offset;

			// Use the reference read's full shift signal
			// for the shared barrel shifter
			SigSpec ref_shift = ref_info.shr->getPort(ID::B);
			SigSpec reg_source(reg);

			Wire *shared_y = module->addWire(
				NEW_ID_SUFFIX("vps_shared_y"), reg_width);
			Cell *shared_shr = module->addShr(
				NEW_ID_SUFFIX("vps_shared_shr"),
				reg_source, ref_shift, SigSpec(shared_y));
			shared_shr->add_strpool_attribute(ID::src,
				ref_info.shr->get_strpool_attribute(ID::src));

			log("  VPS shared barrel shifter: %s (reg=%s, width=%d, "
			    "align=%d, serves %d reads, ref_offset=%d)\n",
			    log_id(shared_shr->name), log_id(reg->name),
			    reg_width, 1 << align, GetSize(indices), ref_offset);

			for (int idx : indices) {
				auto &info = shr_infos[idx];
				SigSpec orig_y = info.shr->getPort(ID::Y);
				int off = info.reg_offset - ref_offset;
				if (off < 0) off = 0;

				SigSpec slice;
				for (int j = 0; j < info.output_width; j++) {
					int pos = off + j;
					if (pos >= 0 && pos < reg_width)
						slice.append(SigBit(shared_y, pos));
					else
						slice.append(State::S0);
				}
				module->connect(orig_y, slice);

				log("    read %s: WIDTH=%d, reg_offset=%d, "
				    "slice_offset=%d -> shared[%d:%d]\n",
				    log_id(info.shr->name), info.output_width,
				    info.reg_offset, off,
				    off, off + info.output_width - 1);

				module->remove(info.shr);
			}

			groups_optimized++;
		}
	}

	void process_vps_reads(Cell *decoder)
	{
		SigSpec decoder_y = decoder->getPort(ID::Y);
		SigSpec binary_index = decoder->getPort(ID::B);

		struct ReadCandidate {
			Cell *cell;
			std::vector<int> dec_positions;
			std::vector<int> s_indices;
			int valid_n;
			bool strided;
		};
		std::vector<ReadCandidate> read_candidates;

		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($pmux))
				continue;
			int W = cell->getParam(ID::WIDTH).as_int();
			if (W <= 1)
				continue;

			SigSpec sig_a = cell->getPort(ID::A);
			if (!sig_a.is_fully_zero())
				continue;

			SigSpec sig_s = cell->getPort(ID::S);
			SigSpec sig_b = cell->getPort(ID::B);
			int N = GetSize(sig_s);

			// Trace S bits to decoder positions, skipping constant-zero
			// padding bits (Verific may insert zeros between one-hot bits
			// and append overflow bits at the MSB).
			std::vector<int> dec_positions;
			std::vector<int> s_indices;
			for (int i = 0; i < N; i++) {
				SigBit sb = sigmap(sig_s[i]);
				if (sb == State::S0)
					continue;
				int pos = trace_to_decoder_pos(sig_s[i], decoder_y);
				if (pos < 0)
					break;
				dec_positions.push_back(pos);
				s_indices.push_back(i);
			}
			if (GetSize(dec_positions) < 2)
				continue;

			// Check that decoder positions are contiguous
			bool contiguous = true;
			for (int i = 1; i < GetSize(dec_positions); i++) {
				if (dec_positions[i] != dec_positions[0] + i) {
					contiguous = false;
					break;
				}
			}
			if (!contiguous)
				continue;

			// Check for sliding window (stride-1) pattern in B
			int sliding_n = 1;
			for (int k = 0; k < GetSize(s_indices) - 1; k++) {
				int si_cur = s_indices[k];
				int si_nxt = s_indices[k + 1];
				bool ok = true;
				for (int j = 1; j < W && ok; j++)
					if (sigmap(sig_b[si_cur * W + j]) != sigmap(sig_b[si_nxt * W + (j - 1)]))
						ok = false;
				if (!ok)
					break;
				sliding_n = k + 2;
			}

			if (sliding_n >= 2) {
				read_candidates.push_back({cell, dec_positions, s_indices, sliding_n, false});
				continue;
			}

			// No stride-1 overlap; fall back to general window
			// packing (stride=W) which works for any W that is a
			// power of 2.  The packed source is built by
			// concatenating B-port windows for each valid select
			// line; the $shr indexes it with binary_index << log2(W).
			bool strided_ok = (W & (W - 1)) == 0 && GetSize(s_indices) >= 2;
			if (strided_ok)
				read_candidates.push_back({cell, dec_positions, s_indices, GetSize(s_indices), true});
		}

		for (auto &rc : read_candidates) {
			Cell *cell = rc.cell;
			int W = cell->getParam(ID::WIDTH).as_int();
			SigSpec sig_b = cell->getPort(ID::B);
			SigSpec sig_y = cell->getPort(ID::Y);
			int full_s = GetSize(cell->getPort(ID::S));
			int valid_n = rc.valid_n;
			int base = rc.dec_positions[0];

		// Detect if binary_index has constant lower bits.
		// Verific encodes VPS reads as `source[(idx + W-1) -: W]`
		// where idx = stride * k.  The decoder's B port is then
		// `stride * k + offset`, driven by a chain of
		//   $mul(stride, k) → $add(., offset)
		// When stride is a power of 2, the lower log2(stride)
		// bits of (stride*k + offset) are the constant value
		// (offset & (stride-1)).  Making those bits structural
		// constants lets techmap's constmap skip the
		// corresponding barrel-shifter stages.
		int log2_align = 0;
		int fixed_lower = 0;
		{
			auto count_const_lower_bits = [&](SigSpec sig) -> std::pair<int, int> {
				int count = 0, value = 0;
				for (int i = 0; i < GetSize(sig); i++) {
					SigBit b = sigmap(sig[i]);
					if (b == State::S0)
						count++;
					else if (b == State::S1) {
						value |= (1 << i);
						count++;
					} else
						break;
				}
				return {count, value};
			};

			auto find_sole_driver = [&](SigSpec sig) -> Cell * {
				Cell *drv = nullptr;
				for (int i = 0; i < GetSize(sig); i++) {
					Cell *d = bit_drivers.at(sigmap(sig[i]), nullptr);
					if (!d) return nullptr;
					if (!drv) drv = d;
					else if (drv != d) return nullptr;
				}
				return drv;
			};

			auto [n0, v0] = count_const_lower_bits(binary_index);
			if (n0 > 0) {
				log2_align = n0;
				fixed_lower = v0;
			}

			if (log2_align == 0) {
				Cell *drv = find_sole_driver(binary_index);
				if (drv && (drv->type == ID($add) || drv->type == ID($sub))) {
					SigSpec aa = drv->getPort(ID::A);
					SigSpec ab = drv->getPort(ID::B);
					SigSpec non_const;
					int offset = 0;
					bool is_sub = (drv->type == ID($sub));
					if (aa.is_fully_const()) {
						offset = aa.as_int();
						non_const = ab;
					} else if (ab.is_fully_const()) {
						offset = ab.as_int();
						non_const = aa;
					}
					if (GetSize(non_const) > 0) {
						auto [nc, nv] = count_const_lower_bits(non_const);
						if (nc > 0) {
							log2_align = nc;
							int mask = (1 << nc) - 1;
							if (is_sub) {
								if (non_const == ab)
									fixed_lower = ((offset & mask) - nv) & mask;
								else
									fixed_lower = (nv - (offset & mask)) & mask;
							} else {
								fixed_lower = (nv + (offset & mask)) & mask;
							}
						}
					}
				}
			}
		}

		int src_bits = 0;
		if (!rc.strided) {
			// Stride-1: reconstruct source from overlapping windows
			int source_width = valid_n + W - 1;
			SigSpec source;
			for (int k = 0; k < source_width; k++) {
				int idx = std::min(k, valid_n - 1);
				int si = rc.s_indices[idx];
				int j = k - idx;
				source.append(sigmap(sig_b[si * W + j]));
			}

			// Identify the register wire from the source bits
			// and truncate to the actual register range
			Wire *reg_wire = nullptr;
			int reg_lo = INT_MAX, reg_hi = INT_MIN;
			for (int i = 0; i < GetSize(source); i++) {
				SigBit b = source[i];
				if (b.wire) {
					if (!reg_wire) reg_wire = b.wire;
					if (b.wire == reg_wire) {
						reg_lo = std::min(reg_lo, b.offset);
						reg_hi = std::max(reg_hi, b.offset);
					}
				}
			}
			if (reg_wire) {
				int first_reg = -1, last_reg = -1;
				for (int i = 0; i < GetSize(source); i++) {
					SigBit b = source[i];
					if (b.wire == reg_wire) {
						if (first_reg < 0) first_reg = i;
						last_reg = i;
					}
				}
				if (first_reg > 0 || last_reg < GetSize(source) - 1) {
					int new_len = last_reg - first_reg + 1;
					source = source.extract(first_reg, new_len);
					base += first_reg;
				}
			}

			SigSpec shift_amount;
			SigSpec raw_idx = binary_index;
			if (base > 0) {
				Wire *sub_w = module->addWire(NEW_ID_SUFFIX("vps_rd_idx"), GetSize(binary_index));
				module->addSub(NEW_ID_SUFFIX("vps_rd_sub"),
					       binary_index, Const(base, GetSize(binary_index)), sub_w);
				raw_idx = SigSpec(sub_w);
			}
			if (log2_align > 0) {
				int adj_lower = (fixed_lower - (base & ((1 << log2_align) - 1)))
						& ((1 << log2_align) - 1);
				for (int i = 0; i < log2_align; i++)
					shift_amount.append((adj_lower >> i) & 1 ? State::S1 : State::S0);
				shift_amount.append(raw_idx.extract(
					log2_align, GetSize(binary_index) - log2_align));
			} else {
				shift_amount = raw_idx;
			}

			src_bits = GetSize(source);
			Cell *shr = module->addShr(NEW_ID_SUFFIX("vps_rd_shr"),
						   source, shift_amount, sig_y);
			shr->add_strpool_attribute(ID::src, cell->get_strpool_attribute(ID::src));
			vps_shr_cells.insert(shr);
		} else {
			// Stride=W: pack windows sequentially, shift by W*binary_index
			SigSpec packed;
			for (int k = 0; k < valid_n; k++) {
				int si = rc.s_indices[k];
				for (int j = 0; j < W; j++)
					packed.append(sigmap(sig_b[si * W + j]));
			}

			// Identify the register wire from packed source bits
			// and trim trailing windows that have no register data
			Wire *reg_wire = nullptr;
			for (int i = 0; i < GetSize(packed); i++) {
				SigBit b = packed[i];
				if (b.wire) { reg_wire = b.wire; break; }
			}
			if (reg_wire) {
				int last_valid_window = -1;
				for (int k = 0; k < valid_n; k++) {
					for (int j = 0; j < W; j++) {
						if (packed[k * W + j].wire == reg_wire)
							{ last_valid_window = k; break; }
					}
				}
				if (last_valid_window >= 0 &&
				    last_valid_window < valid_n - 1) {
					packed = packed.extract(0,
						(last_valid_window + 1) * W);
				}
			}

			int log2w = 0;
			for (int v = W; v > 1; v >>= 1)
				log2w++;

			SigSpec shifted_idx;
			shifted_idx.append(Const(0, log2w));
			if (log2_align > 0) {
				for (int i = 0; i < log2_align; i++)
					shifted_idx.append((fixed_lower >> i) & 1 ?
							   State::S1 : State::S0);
				shifted_idx.append(binary_index.extract(
					log2_align, GetSize(binary_index) - log2_align));
			} else {
				shifted_idx.append(binary_index);
			}

			src_bits = GetSize(packed);
			Cell *shr = module->addShr(NEW_ID_SUFFIX("vps_rd_shr"),
						   packed, shifted_idx, sig_y);
			shr->add_strpool_attribute(ID::src, cell->get_strpool_attribute(ID::src));
			vps_shr_cells.insert(shr);
		}

			log("  VPS read: pmux %s (WIDTH=%d, S_WIDTH=%d/%d, base=%d, src=%d%s%s) -> $shr\n",
			    log_id(cell->name), W, valid_n, full_s, base, src_bits,
			    rc.strided ? ", strided" : "",
			    log2_align > 0 ?
			      stringf(", align=%d", 1 << log2_align).c_str() : "");

			module->remove(cell);
			pmux_replaced++;
			vps_reads_replaced++;
		}

		if (!read_candidates.empty())
			groups_optimized++;
	}

	void process_decoder(Cell *decoder)
	{
		SigSpec decoder_y = decoder->getPort(ID::Y);

		std::vector<PmuxInfo> candidates;

		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($pmux))
				continue;
			if (cell->getParam(ID::WIDTH).as_int() != 1)
				continue;
			SigSpec sig_a = cell->getPort(ID::A);
			if (!sig_a.is_fully_zero())
				continue;

			SigSpec sig_s = cell->getPort(ID::S);
			int s_width = GetSize(sig_s);
			if (s_width < min_stride)
				continue;

			std::vector<int> positions;
			bool valid = true;

			for (int i = 0; i < s_width; i++) {
				int pos = trace_to_decoder_pos(sig_s[i], decoder_y);
				if (pos < 0) { valid = false; break; }
				positions.push_back(pos);
			}
			if (!valid)
				continue;

			bool contiguous = true;
			for (int i = 1; i < s_width; i++) {
				if (positions[i] != positions[i - 1] + 1) {
					contiguous = false;
					break;
				}
			}
			if (!contiguous)
				continue;

			candidates.push_back({cell, positions[0]});
		}

		// Detect VPS read patterns (WIDTH > 1) from this decoder
		process_vps_reads(decoder);

		if (candidates.empty())
			return;

		std::sort(candidates.begin(), candidates.end(),
			  [](const PmuxInfo &a, const PmuxInfo &b) {
				  return a.window_start < b.window_start;
			  });

		// Partition candidates by S_WIDTH, then separate multiplexed
		// VPS groups that share the same decoder positions.
		dict<int, std::vector<PmuxInfo>> by_swidth;
		for (auto &c : candidates)
			by_swidth[GetSize(c.cell->getPort(ID::S))].push_back(c);

		for (auto &[W, cells] : by_swidth) {
			// Sort by window_start
			std::sort(cells.begin(), cells.end(),
				  [](const PmuxInfo &a, const PmuxInfo &b) {
					  return a.window_start < b.window_start;
				  });

			// Build position buckets: window_start -> list of cells
			dict<int, std::vector<PmuxInfo>> by_pos;
			for (auto &c : cells)
				by_pos[c.window_start].push_back(c);

			// Find longest contiguous run of positions
			std::vector<int> positions;
			for (auto &[pos, _] : by_pos)
				positions.push_back(pos);
			std::sort(positions.begin(), positions.end());

			// Extract contiguous runs
			int run_start = 0;
			while (run_start < (int)positions.size()) {
				int run_end = run_start + 1;
				while (run_end < (int)positions.size() &&
				       positions[run_end] == positions[run_end - 1] + 1)
					run_end++;

				int N = run_end - run_start;
				if (N >= W) {
					int base = positions[run_start];
					int multiplicity = GetSize(by_pos[base]);
					for (int pos_idx = run_start; pos_idx < run_end; pos_idx++)
						multiplicity = std::min(multiplicity,
							GetSize(by_pos[positions[pos_idx]]));

					for (int g = 0; g < multiplicity; g++) {
						std::vector<PmuxInfo> group;
						for (int pos_idx = run_start; pos_idx < run_end; pos_idx++)
							group.push_back(by_pos[positions[pos_idx]][g]);

						// Store group in candidates array for optimize_group
						int gstart = candidates.size();
						for (auto &c : group)
							candidates.push_back(c);
						optimize_group(decoder, candidates, gstart,
							       N, W);
					}
				}

				run_start = run_end;
			}
		}
	}

	void optimize_group(Cell *decoder, std::vector<PmuxInfo> &candidates,
			    int group_start, int N, int W)
	{
		int base = candidates[group_start].window_start;
		int lane_count = (N + W - 1) / W;

		log("  VPS group: decoder %s, base=%d, %d bits, stride=%d, %d lanes\n",
		    log_id(decoder->name), base, N, W, lane_count);

		SigSpec decoder_y = decoder->getPort(ID::Y);

		// Collect gated decoder bits and overflow conditions
		dict<int, SigBit> gated_bits;
		dict<int, SigBit> overflow_bits;

		for (int i = 0; i < N; i++) {
			Cell *pmux_cell = candidates[group_start + i].cell;
			SigSpec sig_s = pmux_cell->getPort(ID::S);
			int ws = candidates[group_start + i].window_start;
			for (int k = 0; k < W; k++) {
				int pos = ws + k;
				SigBit sb = sigmap(sig_s[k]);
				if (gated_bits.count(pos)) {
					if (gated_bits[pos] != sb) {
						log("    WARNING: inconsistent gated bit at decoder pos %d\n", pos);
						return;
					}
				} else {
					gated_bits[pos] = sb;
					SigBit ov_cond;
					trace_to_decoder_pos(sb, decoder_y, &ov_cond);
					overflow_bits[pos] = ov_cond;
				}
			}
		}

		// Try binary-index lane enables: instead of OR-reducing W one-hot
		// decoder bits per lane, compare the binary index directly.
		// Requirements: W is a power of 2, base is W-aligned.
		bool use_binary = (W & (W - 1)) == 0 && (base % W) == 0;

		SigSpec binary_index;
		int log2_w = 0;

		if (use_binary) {
			binary_index = decoder->getPort(ID::B);
			for (int tmp = W; tmp > 1; tmp >>= 1)
				log2_w++;

			int decoder_y_width = GetSize(decoder->getPort(ID::Y));
			if (base + lane_count * W > decoder_y_width)
				use_binary = false;
		}

		std::vector<SigBit> lane_en(lane_count);

		if (use_binary) {
			int upper_width = GetSize(binary_index) - log2_w;
			SigSpec upper_bits;
			if (upper_width > 0)
				upper_bits = binary_index.extract(log2_w, upper_width);

			for (int L = 0; L < lane_count; L++) {
				SigBit range_bit;

				if (upper_width > 0) {
					int lane_idx = base / W + L;
					Wire *eq_w = module->addWire(NEW_ID_SUFFIX("vps_lane_eq"), 1);
					module->addEq(NEW_ID_SUFFIX("vps_lane_cmp"),
						      upper_bits, Const(lane_idx, upper_width), eq_w);
					range_bit = SigBit(eq_w);
				} else {
					range_bit = State::S1;
				}

				lane_en[L] = range_bit;
			}

			log("    using binary-index lane enables (%d upper bits)\n",
			    upper_width > 0 ? upper_width : 0);
		} else {
			for (int L = 0; L < lane_count; L++) {
				SigSpec lane_bits;
				for (int k = 0; k < W; k++) {
					int pos = base + L * W + k;
					if (gated_bits.count(pos))
						lane_bits.append(gated_bits.at(pos));
				}

				if (GetSize(lane_bits) == 0) {
					lane_en[L] = State::S0;
				} else if (GetSize(lane_bits) == 1) {
					lane_en[L] = lane_bits[0];
				} else {
					Wire *w = module->addWire(NEW_ID_SUFFIX("vps_lane_en"), 1);
					module->addReduceOr(NEW_ID_SUFFIX("vps_lane_or"), lane_bits, w);
					lane_en[L] = SigBit(w);
				}
			}
		}

		// Probe for the full feedback collapse pattern:
		//   $pmux.Y -> $mux(Q[i], pmux_Y, gated_en).Y -> top_$mux(Q, {results}, wr_en)
		// When detected, replace the entire chain with per-lane wide muxes.
		bool full_collapse = use_binary && (N % W == 0);
		Cell *top_wr_mux = nullptr;
		SigBit wr_en_sig;
		std::vector<FeedbackInfo> fb_info(N);

		if (full_collapse) {
			for (int i = 0; i < N; i++) {
				Cell *pmux_cell = candidates[group_start + i].cell;
				SigBit pmux_y = sigmap(pmux_cell->getPort(ID::Y)[0]);

				Cell *fb_mux = find_sole_consumer(pmux_y);
				if (!fb_mux || fb_mux->type != ID($mux) ||
				    fb_mux->getParam(ID::WIDTH).as_int() != 1 ||
				    sigmap(fb_mux->getPort(ID::B)[0]) != pmux_y) {
					full_collapse = false;
					break;
				}

				SigBit q_bit = sigmap(fb_mux->getPort(ID::A)[0]);
				SigBit gated_en = sigmap(fb_mux->getPort(ID::S)[0]);

				Cell *and_gate = bit_drivers.at(gated_en, nullptr);
				if (and_gate &&
				    and_gate->type != ID($and) &&
				    and_gate->type != ID($_AND_))
					and_gate = nullptr;

				SigBit fb_y = sigmap(fb_mux->getPort(ID::Y)[0]);
				Cell *wr_mux = find_sole_consumer(fb_y);
				if (!wr_mux || wr_mux->type != ID($mux) ||
				    wr_mux->getParam(ID::WIDTH).as_int() <= 1) {
					full_collapse = false;
					break;
				}

				SigSpec wr_b = wr_mux->getPort(ID::B);
				bool in_b = false;
				for (int j = 0; j < GetSize(wr_b); j++)
					if (sigmap(wr_b[j]) == fb_y) { in_b = true; break; }
				if (!in_b) {
					full_collapse = false;
					break;
				}

				SigBit this_wr_en = sigmap(wr_mux->getPort(ID::S)[0]);
				if (top_wr_mux == nullptr) {
					top_wr_mux = wr_mux;
					wr_en_sig = this_wr_en;
				} else if (top_wr_mux != wr_mux) {
					full_collapse = false;
					break;
				}

				fb_info[i] = {fb_mux, and_gate, q_bit};
			}
		}

		// Build lookup: S SigSpec (through sigmap) -> $reduce_or cell
		dict<SigSpec, Cell *> reduce_or_map;
		for (auto cell : module->cells()) {
			if (cell->type != ID($reduce_or))
				continue;
			SigSpec a = sigmap(cell->getPort(ID::A));
			reduce_or_map[a] = cell;
		}

		if (full_collapse) {
			log("    full feedback collapse: %d lanes, wr_en mux %s\n",
			    lane_count, log_id(top_wr_mux->name));

			pool<Cell *> cells_to_remove;

			for (int L = 0; L < lane_count; L++) {
				SigSpec data_lane, q_lane, fb_y_lane;

				for (int b = 0; b < W; b++) {
					int i = L * W + b;
					Cell *pmux_cell = candidates[group_start + i].cell;
					SigSpec cell_b = pmux_cell->getPort(ID::B);
					data_lane.append(cell_b[W - 1 - b]);
					q_lane.append(fb_info[i].q_bit);
					fb_y_lane.append(fb_info[i].feedback_mux->getPort(ID::Y));

					cells_to_remove.insert(pmux_cell);
					cells_to_remove.insert(fb_info[i].feedback_mux);
					if (fb_info[i].and_gate) {
						SigBit and_y = sigmap(fb_info[i].and_gate->getPort(ID::Y)[0]);
						auto ac = bit_consumers.find(and_y);
						if (ac != bit_consumers.end() && ac->second.size() == 1)
							cells_to_remove.insert(fb_info[i].and_gate);
					}

					SigSpec pmux_s = sigmap(pmux_cell->getPort(ID::S));
					auto it = reduce_or_map.find(pmux_s);
					if (it != reduce_or_map.end()) {
						cells_to_remove.insert(it->second);
						reduce_or_map.erase(it);
						reduce_or_replaced++;
					}
					pmux_replaced++;
				}

				Wire *gated_w = module->addWire(NEW_ID_SUFFIX("vps_wr_lane_en"), 1);
				module->addAnd(NEW_ID_SUFFIX("vps_wr_lane_and"),
					       SigSpec(wr_en_sig), SigSpec(lane_en[L]),
					       SigSpec(gated_w));

				Cell *lane_mux = module->addMux(
					NEW_ID_SUFFIX("vps_lane_mux"),
					q_lane, data_lane, SigBit(gated_w), fb_y_lane);
				lane_mux->add_strpool_attribute(ID::src,
					candidates[group_start + L * W].cell->get_strpool_attribute(ID::src));
			}

			for (auto c : cells_to_remove)
				module->remove(c);

			// Remove redundant top-level wr_en mux if all its B-port
			// bits are now driven by the per-lane muxes.
			if (N == top_wr_mux->getParam(ID::WIDTH).as_int()) {
				SigSpec wr_y = top_wr_mux->getPort(ID::Y);
				SigSpec wr_b = top_wr_mux->getPort(ID::B);
				module->connect(wr_y, wr_b);
				module->remove(top_wr_mux);
				log("    removed redundant top-level wr_en mux %s\n",
				    log_id(top_wr_mux->name));
			}

			feedback_collapsed += N;
		} else {
			// Fallback: per-bit $mux replacement
			for (int i = 0; i < N; i++) {
				Cell *pmux_cell = candidates[group_start + i].cell;
				int L = i / W;
				int b = i % W;

				SigSpec cell_b = pmux_cell->getPort(ID::B);
				SigBit data_bit = cell_b[W - 1 - b];
				SigSpec sig_y = pmux_cell->getPort(ID::Y);

				Cell *mux = module->addMux(NEW_ID_SUFFIX("vps_mux"),
							   State::S0, data_bit, lane_en[L], sig_y);
				mux->add_strpool_attribute(ID::src,
							   pmux_cell->get_strpool_attribute(ID::src));

				SigSpec pmux_s = sigmap(pmux_cell->getPort(ID::S));
				auto it = reduce_or_map.find(pmux_s);
				if (it != reduce_or_map.end()) {
					Cell *ror = it->second;
					module->connect(ror->getPort(ID::Y), lane_en[L]);
					module->remove(ror);
					reduce_or_map.erase(it);
					reduce_or_replaced++;
				}

				module->remove(pmux_cell);
				pmux_replaced++;
			}
		}

		groups_optimized++;
	}
};

struct OptVpsPass : public Pass {
	OptVpsPass() : Pass("opt_vps", "optimize Verific variable-part-select patterns") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_vps [options] [selection]\n");
		log("\n");
		log("Detect variable-part-select (VPS) patterns generated by Verific and\n");
		log("replace them with efficient equivalents.\n");
		log("\n");
		log("VPS WRITES: Verific lowers `reg[idx -: W] <= data` into a\n");
		log("bit-granularity decoder ($shl with A=1) followed by overflow-gated\n");
		log("AND gates and N sliding-window one-hot $pmux cells (one per output\n");
		log("bit, each with S_WIDTH=W). This pass recovers the lane structure\n");
		log("and replaces each W-entry $pmux with a single 2:1 $mux gated by a\n");
		log("shared per-lane enable, reducing gates from O(N*W) to O(N + N/W).\n");
		log("\n");
		log("VPS READS: Verific lowers `out = reg[idx +: W]` into a one-hot\n");
		log("decoder plus a wide $pmux (WIDTH=W, S_WIDTH=N) that selects among\n");
		log("all N sliding windows. This pass detects the sliding-window pattern\n");
		log("and replaces the $pmux with a $shr barrel shifter, reducing gates\n");
		log("from O(N*W) to O(log(N)*W).\n");
		log("\n");
		log("    -min_stride <n>\n");
		log("        Minimum stride (S_WIDTH of the VPS write $pmux cells) to\n");
		log("        consider. Default: 4.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int min_stride = 4;

		log_header(design, "Executing OPT_VPS pass (optimize Verific VPS patterns).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-min_stride" && argidx + 1 < args.size()) {
				min_stride = std::stoi(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_groups = 0, total_pmux = 0, total_ror = 0, total_fb = 0, total_rd = 0;

		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;

			OptVpsWorker worker(module, min_stride);
			worker.run();

			if (worker.groups_optimized > 0)
				log("  Module %s: %d VPS group(s), %d $pmux replaced, "
				    "%d $reduce_or replaced, %d feedback collapsed, "
				    "%d VPS reads -> $shr.\n",
				    log_id(module->name), worker.groups_optimized,
				    worker.pmux_replaced, worker.reduce_or_replaced,
				    worker.feedback_collapsed, worker.vps_reads_replaced);

			total_groups += worker.groups_optimized;
			total_pmux += worker.pmux_replaced;
			total_ror += worker.reduce_or_replaced;
			total_fb += worker.feedback_collapsed;
			total_rd += worker.vps_reads_replaced;
		}

		log("Optimized %d VPS group(s), %d $pmux replaced, "
		    "%d $reduce_or replaced, %d feedback collapsed, "
		    "%d VPS reads -> $shr.\n",
		    total_groups, total_pmux, total_ror, total_fb, total_rd);
	}
} OptVpsPass;

PRIVATE_NAMESPACE_END
