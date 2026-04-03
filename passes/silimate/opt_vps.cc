/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2025  Silimate Inc.     <akash@silimate.com>
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
	int min_stride;

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

	void run()
	{
		std::vector<Cell *> decoders;
		for (auto cell : module->selected_cells())
			if (is_decoder_shl(cell))
				decoders.push_back(cell);

		for (auto decoder : decoders)
			process_decoder(decoder);
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

			// Build position buckets: window_start → list of cells
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
		log("Detect variable-part-select (VPS) write patterns generated by Verific\n");
		log("and replace the per-bit sliding-window $pmux cells with per-lane\n");
		log("enable logic and direct data wiring.\n");
		log("\n");
		log("Verific lowers VPS writes like `reg[idx -: W] <= data` into a\n");
		log("bit-granularity decoder ($shl with A=1) followed by overflow-gated\n");
		log("AND gates and N sliding-window one-hot $pmux cells (one per output\n");
		log("bit, each with S_WIDTH=W). This structure has O(N*W) gates after\n");
		log("pmuxtree expansion.\n");
		log("\n");
		log("This pass recovers the lane structure and replaces each W-entry\n");
		log("$pmux with a single 2:1 $mux gated by a shared per-lane enable,\n");
		log("reducing the gate count to O(N + N/W).\n");
		log("\n");
		log("The pass also replaces per-bit $reduce_or enable cells with the\n");
		log("shared lane enable signal.\n");
		log("\n");
		log("    -min_stride <n>\n");
		log("        Minimum stride (S_WIDTH of the $pmux cells) to consider.\n");
		log("        Default: 4.\n");
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

		int total_groups = 0, total_pmux = 0, total_ror = 0, total_fb = 0;

		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;

			OptVpsWorker worker(module, min_stride);
			worker.run();

			if (worker.groups_optimized > 0)
				log("  Module %s: %d VPS group(s), %d $pmux replaced, "
				    "%d $reduce_or replaced, %d feedback collapsed.\n",
				    log_id(module->name), worker.groups_optimized,
				    worker.pmux_replaced, worker.reduce_or_replaced,
				    worker.feedback_collapsed);

			total_groups += worker.groups_optimized;
			total_pmux += worker.pmux_replaced;
			total_ror += worker.reduce_or_replaced;
			total_fb += worker.feedback_collapsed;
		}

		log("Optimized %d VPS group(s), %d $pmux replaced, "
		    "%d $reduce_or replaced, %d feedback collapsed.\n",
		    total_groups, total_pmux, total_ror, total_fb);
	}
} OptVpsPass;

PRIVATE_NAMESPACE_END
