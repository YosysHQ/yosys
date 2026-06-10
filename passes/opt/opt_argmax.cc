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
#include <cctype>
#include <map>
#include <queue>

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

static Const packed_table_const(const vector<uint64_t> &values, int elem_width)
{
	vector<State> bits(values.size() * elem_width, State::S0);
	for (int i = 0; i < GetSize(values); i++)
		for (int b = 0; b < elem_width && b < 64; b++)
			if ((values[i] >> b) & 1ULL)
				bits[i * elem_width + b] = State::S1;
	return Const(bits);
}

static Const packed_valid_const(const vector<int> &valid)
{
	vector<State> bits(valid.size(), State::S0);
	for (int i = 0; i < GetSize(valid); i++)
		if (valid[i])
			bits[i] = State::S1;
	return Const(bits);
}

struct OptArgmaxWorker
{
	struct TestVector {
		vector<int> valid;
		vector<uint64_t> index;
		vector<uint64_t> values;
	};

	struct Candidate {
		Wire *out_wire = nullptr;
		Wire *valid_wire = nullptr;
		SigSpec valid_sig;
		SigSpec index_sig;
		SigSpec values_sig;
		std::string index_name;
		std::string values_name;
		bool identity_index = false;
		int width = 0;
		int index_width = 0;
		int value_width = 0;
		Cell *anchor = nullptr;
		IdString anchor_port;
	};

	struct OutputCone {
		pool<Cell *> cells;
		pool<SigBit> leaves;
		bool saw_bmux = false;
		bool saw_lt = false;
	};

	struct InputBus {
		SigSpec sig;
		std::string name;
		int entries = 0;
		int elem_width = 0;
	};

	struct Record {
		SigBit valid;
		SigSpec value;
		SigSpec index;
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

	OptArgmaxWorker(Module *module) : module(module), sigmap(module)
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

	OutputCone summarize_output_cone(const pool<Cell *> &cone_cells, pool<SigBit> leaf_bits)
	{
		OutputCone cone;
		cone.cells = cone_cells;
		cone.leaves = std::move(leaf_bits);
		for (auto c : cone_cells) {
			cone.saw_bmux = cone.saw_bmux || c->type == ID($bmux);
			cone.saw_lt = cone.saw_lt || c->type == ID($lt);
		}
		return cone;
	}

	bool cone_has_required_shape(const OutputCone &cone, int value_width)
	{
		return cone.saw_bmux && (cone.saw_lt || value_width == 1);
	}

	bool leaves_are_candidate_inputs(const pool<SigBit> &leaf_bits, const Candidate &cand)
	{
		pool<SigBit> allowed;
		for (auto bit : sigmap(cand.valid_sig))
			if (bit.wire)
				allowed.insert(bit);
		if (!cand.identity_index)
			for (auto bit : sigmap(cand.index_sig))
				if (bit.wire)
					allowed.insert(bit);
		for (auto bit : sigmap(cand.values_sig))
			if (bit.wire)
				allowed.insert(bit);

		for (auto bit : leaf_bits)
			if (!allowed.count(bit))
				return false;
		return true;
	}

	bool find_anchor_driver(Wire *out_wire, Cell *&anchor, IdString &anchor_port)
	{
		for (auto bit : sigmap(SigSpec(out_wire))) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr)
				continue;
			for (auto &conn : drv->connections()) {
				if (!drv->output(conn.first))
					continue;
				for (auto out_bit : sigmap(conn.second)) {
					if (out_bit == bit) {
						anchor = drv;
						anchor_port = conn.first;
						return true;
					}
				}
			}
		}
		return false;
	}

	uint64_t value_mask(int width)
	{
		if (width >= 64)
			return ~0ULL;
		return (1ULL << width) - 1;
	}

	void add_vector(vector<TestVector> &vectors, const vector<int> &valid,
	                const vector<uint64_t> &index, const vector<uint64_t> &values)
	{
		vectors.push_back({valid, index, values});
	}

	vector<TestVector> make_test_vectors(int width, int value_width)
	{
		vector<TestVector> vectors;
		vector<uint64_t> identity(width), reverse(width), inc(width), dec(width), equal(width, 7);
		uint64_t mask = value_mask(value_width);
		for (int i = 0; i < width; i++) {
			identity[i] = i;
			reverse[i] = width - 1 - i;
			inc[i] = uint64_t(i + 1) & mask;
			dec[i] = uint64_t(width - i) & mask;
		}

		vector<int> valid(width, 0);
		add_vector(vectors, valid, identity, inc);

		for (int i = 0; i < width; i++) {
			valid.assign(width, 0);
			valid[i] = 1;
			add_vector(vectors, valid, identity, inc);
		}

		valid.assign(width, 1);
		add_vector(vectors, valid, identity, inc);
		add_vector(vectors, valid, identity, dec);
		add_vector(vectors, valid, identity, equal);
		add_vector(vectors, valid, reverse, inc);
		add_vector(vectors, valid, reverse, dec);

		for (int i = 0; i + 1 < width; i++) {
			vector<uint64_t> vals(width, 3);
			valid.assign(width, 0);
			valid[i] = 1;
			valid[i + 1] = 1;
			vals[i] = 1;
			vals[i + 1] = 9;
			add_vector(vectors, valid, identity, vals);
			vals[i] = 5;
			vals[i + 1] = 5;
			add_vector(vectors, valid, identity, vals);
		}

		if (width > 2) {
			vector<uint64_t> vals(width, 0);
			valid.assign(width, 0);
			valid[0] = 1;
			valid[width - 1] = 1;
			vals[0] = 2;
			vals[width - 1] = 11;
			add_vector(vectors, valid, identity, vals);
			vals[0] = 13;
			vals[width - 1] = 13;
			add_vector(vectors, valid, identity, vals);
		}

		return vectors;
	}

	int expected_argmax(const TestVector &tv, int width, int value_width, bool identity_index)
	{
		uint64_t mask = value_mask(value_width);
		int best_idx = 0;
		bool best_valid = tv.valid[0] != 0;
		uint64_t best_value = tv.values[identity_index ? 0 : tv.index[0]] & mask;

		for (int k = 1; k < width; k++) {
			bool cand_valid = tv.valid[k] != 0;
			uint64_t cand_value = tv.values[identity_index ? k : tv.index[k]] & mask;
			if (!best_valid && cand_valid) {
				best_idx = k;
				best_valid = true;
				best_value = cand_value;
			} else if (best_valid && cand_valid && best_value < cand_value) {
				best_idx = k;
				best_value = cand_value;
			}
		}

		return best_idx;
	}

	bool fingerprint(const Candidate &cand)
	{
		ConstEval ce(module);
		SigSpec out_sig = sigmap(SigSpec(cand.out_wire));
		SigSpec valid_sig = sigmap(cand.valid_sig);
		SigSpec index_sig = cand.identity_index ? SigSpec() : sigmap(cand.index_sig);
		SigSpec values_sig = sigmap(cand.values_sig);

		vector<TestVector> vectors = make_test_vectors(cand.width, cand.value_width);
		for (auto &tv : vectors) {
			ce.push();
			ce.set(valid_sig, packed_valid_const(tv.valid));
			if (!cand.identity_index)
				ce.set(index_sig, packed_table_const(tv.index, cand.index_width));
			ce.set(values_sig, packed_table_const(tv.values, cand.value_width));

			SigSpec out = out_sig;
			SigSpec undef;
			bool ok = ce.eval(out, undef);
			ce.pop();
			if (!ok || !out.is_fully_const())
				return false;

			int actual = out.as_const().as_int();
			int expected = expected_argmax(tv, cand.width, cand.value_width, cand.identity_index);
			if (actual != expected)
				return false;
		}

		return true;
	}

	SigSpec zext(SigSpec sig, int width)
	{
		sig = sigmap(sig);
		if (GetSize(sig) > width)
			return sig.extract(0, width);
		while (GetSize(sig) < width)
			sig.append(State::S0);
		return sig;
	}

	SigSpec emit_not(Cell *anchor, SigSpec a)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Not(NEW_ID2_SUFFIX("argmax_not"), a);
	}

	SigSpec emit_and(Cell *anchor, SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->And(NEW_ID2_SUFFIX("argmax_and"), a, b);
	}

	SigSpec emit_or(Cell *anchor, SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Or(NEW_ID2_SUFFIX("argmax_or"), a, b);
	}

	SigSpec emit_lt(Cell *anchor, SigSpec a, SigSpec b)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Lt(NEW_ID2_SUFFIX("argmax_lt"), a, b);
	}

	SigSpec emit_mux(Cell *anchor, SigSpec a, SigSpec b, SigSpec s)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Mux(NEW_ID2_SUFFIX("argmax_mux"), a, b, s);
	}

	SigSpec emit_bmux(Cell *anchor, SigSpec a, SigSpec s)
	{
		Cell *cell = anchor;
		cells_added++;
		return module->Bmux(NEW_ID2_SUFFIX("argmax_val"), a, s);
	}

	Record combine(Cell *anchor, const Record &lhs, const Record &rhs)
	{
		SigSpec lhs_invalid = emit_not(anchor, SigSpec(lhs.valid));
		SigSpec value_lt = emit_lt(anchor, lhs.value, rhs.value);
		SigSpec valid_and_lt = emit_and(anchor, SigSpec(lhs.valid), value_lt);
		SigSpec take_reason = emit_or(anchor, lhs_invalid, valid_and_lt);
		SigSpec take_rhs = emit_and(anchor, SigSpec(rhs.valid), take_reason);

		Record out;
		out.valid = emit_or(anchor, SigSpec(lhs.valid), SigSpec(rhs.valid))[0];
		out.value = emit_mux(anchor, lhs.value, rhs.value, take_rhs);
		out.index = emit_mux(anchor, lhs.index, rhs.index, take_rhs);
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

	SigSpec emit_argmax(const Candidate &cand)
	{
		vector<Record> leaves;
		SigSpec valid = sigmap(cand.valid_sig);
		SigSpec index_map = cand.identity_index ? SigSpec() : sigmap(cand.index_sig);
		SigSpec values = sigmap(cand.values_sig);

		for (int k = 0; k < cand.width; k++) {
			SigSpec value;
			if (cand.identity_index)
				value = values.extract(k * cand.value_width, cand.value_width);
			else {
				SigSpec index = index_map.extract(k * cand.index_width, cand.index_width);
				value = emit_bmux(cand.anchor, values, index);
			}
			leaves.push_back({valid[k], value, SigSpec(Const(k, cand.index_width))});
		}

		Record root = emit_tree_rec(cand.anchor, leaves, 0, GetSize(leaves));
		return zext(root.index, cand.index_width);
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
				Wire *dangling = module->addWire(NEW_ID2_SUFFIX("argmax_dangling"), GetSize(orig));
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

	bool check_candidate(Candidate &cand, const OutputCone &cone)
	{
		if (cand.width < min_width || cand.width > max_width)
			return false;
		if (!is_power_of_two(cand.width))
			return false;
		if (cand.index_width != clog2_int(cand.width))
			return false;
		if (cand.value_width <= 0 || cand.value_width > 62)
			return false;

		if (!cone_has_required_shape(cone, cand.value_width))
			return false;
		if (!leaves_are_candidate_inputs(cone.leaves, cand))
			return false;
		if (!find_anchor_driver(cand.out_wire, cand.anchor, cand.anchor_port))
			return false;

		return fingerprint(cand);
	}

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
			if (entries.empty() || entries.front().first != 0)
				continue;
			bool contiguous = true;
			int elem_width = GetSize(entries.front().second);
			for (int i = 0; i < GetSize(entries); i++) {
				if (entries[i].first != i || GetSize(entries[i].second) != elem_width) {
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

		vector<Candidate> rewrites;
		pool<Wire *> claimed_outputs;
		for (auto out : outputs) {
			if (claimed_outputs.count(out))
				continue;
			int out_width = GetSize(out);
			if (out_width < 2)
				continue;

			pool<Cell *> cone_cells;
			pool<SigBit> leaf_bits;
			int max_cone_cells = std::max(256, max_width * 96);
			int max_leaf_bits = max_width * (out_width + max_width) + max_width;
			if (!get_cone(SigSpec(out), cone_cells, leaf_bits,
			              max_cone_cells, max_leaf_bits))
				continue;
			OutputCone cone = summarize_output_cone(cone_cells, std::move(leaf_bits));
			if (!cone.saw_bmux)
				continue;

			for (auto valid : inputs) {
				int width = GetSize(valid);
				if (width < min_width || width > max_width)
					continue;
				if (clog2_int(width) != out_width)
					continue;

				vector<InputBus> index_buses;
				vector<InputBus> values_buses;
				for (auto input : inputs) {
					if (input == valid)
						continue;
					if (GetSize(input) == width * out_width)
						index_buses.push_back({SigSpec(input), input->name.str(), width, out_width});
					if (GetSize(input) % width == 0)
						values_buses.push_back({SigSpec(input), input->name.str(), width, GetSize(input) / width});
				}

				vector<InputBus> split_buses = collect_split_input_buses(inputs);
				for (auto bus : split_buses) {
					if (bus.entries == width && bus.elem_width == out_width)
						index_buses.push_back(bus);
					if (bus.entries == width)
						values_buses.push_back(bus);
				}

				for (auto &values : values_buses) {
					Candidate cand;
					cand.out_wire = out;
					cand.valid_wire = valid;
					cand.valid_sig = SigSpec(valid);
					cand.values_sig = values.sig;
					cand.index_name = "<identity>";
					cand.values_name = values.name;
					cand.identity_index = true;
					cand.width = width;
					cand.index_width = out_width;
					cand.value_width = values.elem_width;
					if (!check_candidate(cand, cone))
						continue;

					rewrites.push_back(cand);
					claimed_outputs.insert(out);
					log("  %s: %s <- argmax(valid=%s, index=<identity>, values=%s) [N=%d, IW=%d, VW=%d]\n",
					    log_id(module), log_id(out), log_id(valid), values.name.c_str(),
					    cand.width, cand.index_width, cand.value_width);
					goto next_output;
				}

				for (auto &index : index_buses) {
					for (auto &values : values_buses) {
						if (index.sig == values.sig)
							continue;
						Candidate cand;
						cand.out_wire = out;
						cand.valid_wire = valid;
						cand.valid_sig = SigSpec(valid);
						cand.index_sig = index.sig;
						cand.values_sig = values.sig;
						cand.index_name = index.name;
						cand.values_name = values.name;
						cand.identity_index = false;
						cand.width = width;
						cand.index_width = out_width;
						cand.value_width = values.elem_width;
						if (!check_candidate(cand, cone))
							continue;

						rewrites.push_back(cand);
						claimed_outputs.insert(out);
						log("  %s: %s <- argmax(valid=%s, index=%s, values=%s) [N=%d, IW=%d, VW=%d]\n",
						    log_id(module), log_id(out), log_id(valid), index.name.c_str(),
						    values.name.c_str(), cand.width, cand.index_width, cand.value_width);
						goto next_output;
					}
				}
			}
next_output:
			;
		}

		for (auto &cand : rewrites) {
			cell = cand.anchor;
			SigSpec new_out = emit_argmax(cand);
			disconnect_old_output(cand);
			module->connect(SigSpec(cand.out_wire), new_out);
			regions_rewritten++;
		}
	}
};

struct OptArgmaxPass : public Pass
{
	OptArgmaxPass() : Pass("opt_argmax",
		"detect and rewrite masked argmax loops into balanced compare trees") {}

	void help() override
	{
		log("\n");
		log("    opt_argmax [options] [selection]\n");
		log("\n");
		log("Detect combinational masked argmax loops of the form used by\n");
		log("read-after dependency logic and replace the serial loop-carried\n");
		log("index/update cone with a balanced tree of {valid,value,index}\n");
		log("comparators. Ties preserve the lower candidate index, matching a\n");
		log("strict '<' update condition; all-invalid inputs return index zero.\n");
		log("\n");
		log("    -max-width N, -max_width N\n");
		log("        maximum candidate count to consider (default 64).\n");
		log("\n");
		log("    -min-width N, -min_width N\n");
		log("        minimum candidate count to consider (default 4).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_ARGMAX pass (masked argmax rewrite).\n");

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
			OptArgmaxWorker worker(module);
			worker.max_width = max_width;
			worker.min_width = min_width;
			worker.run();
			total_regions += worker.regions_rewritten;
			total_cells_added += worker.cells_added;
		}

		log("Rewrote %d argmax region(s); emitted %d new cell(s).\n",
		    total_regions, total_cells_added);

		if (total_regions)
			Yosys::run_pass("clean -purge");
	}
} OptArgmaxPass;

PRIVATE_NAMESPACE_END
