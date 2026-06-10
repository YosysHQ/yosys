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

struct OptPriorityOnehotWorker {
	// One detected priority-onehot region ready to be rewritten.
	struct Candidate {
		Wire *out_wire = nullptr;   // one-hot output O (width W = 2^idx_w)
		Wire *valid_wire = nullptr; // request / valid bus V (width N)
		SigSpec valid_sig;          // N bits
		SigSpec field_sig;          // N * idx_w bits: concatenated per-lane index fields
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

	Module *module;
	SigMap sigmap;
	dict<SigBit, Cell *> bit_to_driver;
	pool<SigBit> input_port_bits;
	Cell *cell = nullptr;

	int min_width = 4;
	int max_width = 64;
	int regions_rewritten = 0;
	int cells_added = 0;

	OptPriorityOnehotWorker(Module *module) : module(module), sigmap(module)
	{
		build_indexes();
	}

	bool is_sequential(Cell *c)
	{
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

	void build_indexes()
	{
		for (auto c : module->cells()) {
			if (is_sequential(c))
				continue;
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire)
						continue;
					auto it = bit_to_driver.find(bit);
					if (it == bit_to_driver.end())
						bit_to_driver[bit] = c;
					else if (it->second != c)
						it->second = nullptr;
				}
			}
		}

		for (auto w : module->wires()) {
			if (!w->port_input)
				continue;
			for (auto bit : sigmap(SigSpec(w)))
				if (bit.wire)
					input_port_bits.insert(bit);
		}
	}

	// Combinational fanin cone of `from`. Leaves are port-input bits or bits
	// driven by sequential cells / undriven. Returns false if size limits are
	// exceeded.
	bool get_cone(SigSpec from, pool<Cell *> &cone_cells, pool<SigBit> &leaf_bits,
	              int max_cone_cells, int max_leaf_bits)
	{
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		for (auto bit : sigmap(from)) {
			if (!bit.wire)
				continue;
			if (visited.insert(bit).second)
				worklist.push(bit);
		}

		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();

			if (input_port_bits.count(bit)) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits)
					return false;
				continue;
			}

			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits)
					return false;
				continue;
			}

			if (!cone_cells.insert(drv).second)
				continue;
			if (GetSize(cone_cells) > max_cone_cells)
				return false;

			for (auto &conn : drv->connections()) {
				if (!drv->input(conn.first))
					continue;
				for (auto in_bit : sigmap(conn.second)) {
					if (!in_bit.wire)
						continue;
					if (visited.insert(in_bit).second)
						worklist.push(in_bit);
				}
			}
		}

		return true;
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

	bool leaves_are_candidate_inputs(const pool<SigBit> &leaf_bits, const SigSpec &valid_sig,
	                                 const SigSpec &field_sig)
	{
		pool<SigBit> allowed;
		for (auto bit : sigmap(valid_sig))
			if (bit.wire)
				allowed.insert(bit);
		for (auto bit : sigmap(field_sig))
			if (bit.wire)
				allowed.insert(bit);
		for (auto bit : leaf_bits)
			if (!allowed.count(bit))
				return false;
		return true;
	}

	struct InputBus {
		SigSpec sig;
		std::string name;
		int entries = 0;
		int elem_width = 0;
	};

	// Parse a split-port name of the form "base[index]" (Verific lowers packed
	// multi-dimensional ports into per-lane wires named this way).
	bool parse_indexed_port_name(Wire *wire, std::string &base, int &index)
	{
		std::string name = wire->name.str();
		size_t rbrack = name.size();
		if (rbrack == 0 || name[rbrack - 1] != ']')
			return false;
		size_t lbrack = name.rfind('[');
		if (lbrack == std::string::npos || lbrack + 1 >= rbrack - 1)
			return false;
		for (size_t i = lbrack + 1; i < rbrack - 1; i++)
			if (!isdigit(name[i]))
				return false;
		base = name.substr(0, lbrack);
		index = atoi(name.substr(lbrack + 1, rbrack - lbrack - 2).c_str());
		return true;
	}

	// Group per-lane split-port wires into contiguous, equal-width buses. The
	// run may start at any base index (Verific lowers both [N-1:0] -> id[0..N-1]
	// and [N:1] -> id[1..N]); we only require consecutive indices and matching
	// widths. The resulting sig is the ascending-index concatenation, so lane k
	// is sig[k*elem_width ...] = the (base+k)-th port.
	vector<InputBus> collect_split_input_buses(const vector<Wire *> &inputs)
	{
		std::map<std::string, vector<std::pair<int, Wire *>>> groups;
		for (auto w : inputs) {
			std::string base;
			int index = -1;
			if (parse_indexed_port_name(w, base, index))
				groups[base].push_back({index, w});
		}

		vector<InputBus> buses;
		for (auto &it : groups) {
			auto entries = it.second;
			std::sort(entries.begin(), entries.end(),
			          [](const std::pair<int, Wire *> &a, const std::pair<int, Wire *> &b) {
			              return a.first < b.first;
			          });
			if (entries.empty())
				continue;
			bool contiguous = true;
			int base_index = entries.front().first;
			int elem_width = GetSize(entries.front().second);
			for (int i = 0; i < GetSize(entries); i++) {
				if (entries[i].first != base_index + i ||
				    GetSize(entries[i].second) != elem_width) {
					contiguous = false;
					break;
				}
			}
			if (!contiguous)
				continue;

			SigSpec sig;
			for (auto &entry : entries)
				sig.append(SigSpec(entry.second));
			buses.push_back({sig, it.first, GetSize(entries), elem_width});
		}

		return buses;
	}

	bool find_anchor_driver(Wire *out_wire, Cell *&anchor)
	{
		for (auto bit : sigmap(SigSpec(out_wire))) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr) {
				anchor = drv;
				return true;
			}
		}
		return false;
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
		ConstEval ce(module);
		SigSpec out_sig = sigmap(SigSpec(cand.out_wire));
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

	bool check_candidate(Candidate &cand, const pool<SigBit> &leaf_bits)
	{
		if (cand.n < min_width || cand.n > max_width)
			return false;
		if (!is_power_of_two(cand.w) || (1 << cand.idx_w) != cand.w)
			return false;
		if (!leaves_are_candidate_inputs(leaf_bits, cand.valid_sig, cand.field_sig)) {
			log_debug("  reject %s (valid=%s index=%s): cone leaves outside valid+field\n",
			          log_id(cand.out_wire), log_id(cand.valid_wire), cand.index_name.c_str());
			return false;
		}
		if (!find_anchor_driver(cand.out_wire, cand.anchor))
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
		          log_id(cand.out_wire), log_id(cand.valid_wire), cand.index_name.c_str());
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
		SigBit lhs_invalid = module->Not(NEW_ID2_SUFFIX("prionehot_ninv"), SigSpec(lhs.valid))[0];
		cells_added++;
		SigBit take_rhs = module->And(NEW_ID2_SUFFIX("prionehot_take"),
		                              SigSpec(lhs_invalid), SigSpec(rhs.valid))[0];
		cells_added++;

		Record out;
		out.valid = module->Or(NEW_ID2_SUFFIX("prionehot_orv"),
		                       SigSpec(lhs.valid), SigSpec(rhs.valid))[0];
		cells_added++;
		out.index = module->Mux(NEW_ID2_SUFFIX("prionehot_mux"), lhs.index, rhs.index,
		                        SigSpec(take_rhs));
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
			SigBit idx_bit_n = module->Not(NEW_ID2_SUFFIX("prionehot_ndec"), idx_bit)[0];
			cells_added++;
			int group = GetSize(cur);
			vector<SigBit> nxt(group * 2);
			for (int g = 0; g < group; g++) {
				nxt[g] = module->And(NEW_ID2_SUFFIX("prionehot_dec0"),
				                     SigSpec(cur[g]), SigSpec(idx_bit_n))[0];
				cells_added++;
				nxt[g + group] = module->And(NEW_ID2_SUFFIX("prionehot_dec1"),
				                             SigSpec(cur[g]), idx_bit)[0];
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

	void disconnect_old_output(const Candidate &cand)
	{
		pool<SigBit> target_bits;
		for (auto bit : sigmap(SigSpec(cand.out_wire)))
			if (bit.wire)
				target_bits.insert(bit);

		pool<Cell *> seen_cells;
		for (auto target : target_bits) {
			Cell *drv = bit_to_driver.at(target, nullptr);
			if (drv == nullptr || seen_cells.count(drv))
				continue;
			seen_cells.insert(drv);

			for (auto &conn : drv->connections()) {
				if (!drv->output(conn.first))
					continue;
				SigSpec orig = conn.second;
				SigSpec replacement = orig;
				bool changed = false;
				Cell *cell = drv;
				Wire *dangling = module->addWire(NEW_ID2_SUFFIX("prionehot_dangling"),
				                                 GetSize(orig));
				for (int i = 0; i < GetSize(orig); i++) {
					if (target_bits.count(sigmap(orig[i]))) {
						replacement[i] = SigBit(dangling, i);
						changed = true;
					}
				}
				if (changed)
					drv->setPort(conn.first, replacement);
			}
		}
	}

	void run()
	{
		if (module->has_processes_warn())
			return;

		vector<Wire *> inputs;
		vector<Wire *> outputs;
		for (auto w : module->wires()) {
			if (w->port_input)
				inputs.push_back(w);
			if (w->port_output && !w->port_input)
				outputs.push_back(w);
		}

		// Per-lane split-port buses ("id[0]".."id[N-1]") are grouped once.
		vector<InputBus> split_buses = collect_split_input_buses(inputs);

		vector<Candidate> rewrites;
		pool<Wire *> claimed_outputs;
		for (auto out : outputs) {
			if (claimed_outputs.count(out))
				continue;
			int w = GetSize(out);
			if (w < 2 || !is_power_of_two(w))
				continue;
			int idx_w = clog2_int(w);

			pool<Cell *> cone_cells;
			pool<SigBit> leaf_bits;
			int max_cone_cells = std::max(256, max_width * 96);
			int max_leaf_bits = max_width * max_width + max_width * w + max_width;
			if (!get_cone(SigSpec(out), cone_cells, leaf_bits, max_cone_cells, max_leaf_bits)) {
				log_debug("output %s (w=%d): cone exceeds size limits\n", log_id(out), w);
				continue;
			}
			if (cone_cells.empty())
				continue;
			log_debug("output %s (w=%d, idx_w=%d): cone %d cells, %d leaf bits\n",
			          log_id(out), w, idx_w, GetSize(cone_cells), GetSize(leaf_bits));

			bool done = false;
			for (auto valid : inputs) {
				if (done)
					break;
				int n = GetSize(valid);
				if (n < min_width || n > max_width)
					continue;

				// Candidate index sources: a flat input bus split into n lanes,
				// or a per-lane split-port bus with n entries.
				vector<std::pair<SigSpec, std::string>> sources;
				for (auto d : inputs) {
					if (d == valid)
						continue;
					if (GetSize(d) % n == 0)
						sources.push_back({SigSpec(d), d->name.str()});
				}
				for (auto &bus : split_buses)
					if (bus.entries == n)
						sources.push_back({bus.sig, bus.name});

				for (auto &src : sources) {
					int total = GetSize(src.first);
					if (total % n != 0)
						continue;
					int s = total / n;
					if (s < idx_w)
						continue;

					SigSpec field_sig;
					if (!infer_field(src.first, n, idx_w, s, leaf_bits, field_sig)) {
						log_debug("  valid=%s index=%s (n=%d, s=%d): field layout inference failed\n",
						          log_id(valid), src.second.c_str(), n, s);
						continue;
					}

					Candidate cand;
					cand.out_wire = out;
					cand.valid_wire = valid;
					cand.valid_sig = SigSpec(valid);
					cand.field_sig = field_sig;
					cand.index_name = src.second;
					cand.n = n;
					cand.w = w;
					cand.idx_w = idx_w;
					if (!check_candidate(cand, leaf_bits))
						continue;

					rewrites.push_back(cand);
					claimed_outputs.insert(out);
					log("  %s: %s <- priority_onehot(valid=%s, index=%s) "
					    "[N=%d, W=%d, IDX_W=%d, %s]\n",
					    log_id(module), log_id(out), log_id(valid), src.second.c_str(),
					    cand.n, cand.w, cand.idx_w,
					    cand.msb_first ? "MSB-first" : "LSB-first");
					done = true;
					break;
				}
			}
		}

		for (auto &cand : rewrites) {
			cell = cand.anchor;
			SigSpec new_out = emit_priority_onehot(cand);
			disconnect_old_output(cand);
			module->connect(SigSpec(cand.out_wire), new_out);
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
		log("After rewriting, the original cone cells become unused and are removed\n");
		log("by the trailing 'clean -purge'.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_PRIORITY_ONEHOT pass (priority select + one-hot scatter).\n");

		int max_width = 64;
		int min_width = 4;
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
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0;
		int total_cells_added = 0;
		for (auto module : design->selected_modules()) {
			OptPriorityOnehotWorker worker(module);
			worker.max_width = max_width;
			worker.min_width = min_width;
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
