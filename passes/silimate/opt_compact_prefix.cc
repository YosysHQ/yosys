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

struct OptCompactPrefixWorker
{
	Module *module;
	SigMap sigmap;
	int max_width;
	dict<SigBit, Cell *> bit_drivers;
	Cell *ref_cell = nullptr;

	int forward_rewrites = 0;
	int reverse_rewrites = 0;
	int modulo_rewrites = 0;
	int old_cells_removed = 0;
	int new_cells_emitted = 0;

	OptCompactPrefixWorker(Module *module, int max_width)
		: module(module), sigmap(module), max_width(max_width)
	{
		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (!cell->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second))
					bit_drivers[bit] = cell;
			}
		}
	}

	vector<Wire *> input_ports()
	{
		vector<Wire *> ports;
		for (auto wire : module->wires())
			if (wire->port_input)
				ports.push_back(wire);
		return ports;
	}

	vector<Wire *> output_ports()
	{
		vector<Wire *> ports;
		for (auto wire : module->wires())
			if (wire->port_output)
				ports.push_back(wire);
		return ports;
	}

	int count_cells(IdString type)
	{
		int n = 0;
		for (auto cell : module->cells())
			if (cell->type == type)
				n++;
		return n;
	}

	bool sig_is_const_value(SigSpec sig, int64_t value)
	{
		sig = sigmap(sig);
		if (!sig.is_fully_const())
			return false;
		uint64_t uvalue = (uint64_t)value;
		for (int i = 0; i < GetSize(sig); i++) {
			bool want = (i < 64) ? ((uvalue >> i) & 1) : (value < 0);
			if (sig[i] != (want ? State::S1 : State::S0))
				return false;
		}
		return true;
	}

	int count_binop_const(IdString type, int64_t value)
	{
		int n = 0;
		for (auto cell : module->cells()) {
			if (cell->type != type)
				continue;
			if (sig_is_const_value(cell->getPort(ID::A), value) ||
			    sig_is_const_value(cell->getPort(ID::B), value))
				n++;
		}
		return n;
	}

	bool has_binop_const_other_than(IdString type, int64_t value)
	{
		for (auto cell : module->cells()) {
			if (cell->type != type)
				continue;
			bool a_const = sigmap(cell->getPort(ID::A)).is_fully_const();
			bool b_const = sigmap(cell->getPort(ID::B)).is_fully_const();
			if (a_const && !sig_is_const_value(cell->getPort(ID::A), value))
				return true;
			if (b_const && !sig_is_const_value(cell->getPort(ID::B), value))
				return true;
		}
		return false;
	}

	int eval_bit_at_zero(SigBit bit, dict<SigBit, int> &cache, int depth)
	{
		bit = sigmap(bit);
		if (bit == State::S0) return 0;
		if (bit == State::S1) return 1;
		if (!bit.wire) return 0;

		auto it = cache.find(bit);
		if (it != cache.end())
			return it->second;
		if (depth > 64)
			return 0;

		cache[bit] = 0;
		Cell *drv = bit_drivers.at(bit, nullptr);
		if (!drv || !drv->hasPort(ID::Y) || !drv->hasPort(ID::A))
			return 0;

		int bit_pos = -1;
		SigSpec y = sigmap(drv->getPort(ID::Y));
		for (int i = 0; i < GetSize(y); i++) {
			if (y[i] == bit) {
				bit_pos = i;
				break;
			}
		}
		if (bit_pos < 0)
			return 0;

		auto eval_sig = [&](SigSpec sig) -> int64_t {
			int64_t result = 0;
			for (int i = 0; i < GetSize(sig) && i < 62; i++)
				result |= ((int64_t)eval_bit_at_zero(sig[i], cache, depth + 1) << i);
			return result;
		};

		int64_t av = eval_sig(drv->getPort(ID::A));
		int64_t bv = drv->hasPort(ID::B) ? eval_sig(drv->getPort(ID::B)) : 0;
		int64_t rv = 0;
		if (drv->type == ID($add)) rv = av + bv;
		else if (drv->type == ID($sub)) rv = av - bv;
		else if (drv->type == ID($and) || drv->type == ID($_AND_)) rv = av & bv;
		else if (drv->type == ID($or) || drv->type == ID($_OR_)) rv = av | bv;
		else if (drv->type == ID($xor) || drv->type == ID($_XOR_)) rv = av ^ bv;
		else if (drv->type == ID($not) || drv->type == ID($_NOT_)) rv = ~av;
		else if (drv->type == ID($logic_not)) rv = !av;
		else if (drv->type == ID($reduce_or)) rv = av != 0;
		else if (drv->type == ID($gt)) rv = av > bv;
		else if (drv->type == ID($eq)) rv = av == bv;
		else if (drv->type == ID($shl) || drv->type == ID($sshl)) rv = av << bv;
		else if (drv->type == ID($shr) || drv->type == ID($sshr)) rv = av >> bv;
		else if (drv->type == ID($mux)) {
			int sv = eval_bit_at_zero(drv->getPort(ID::S)[0], cache, depth + 1);
			rv = sv ? bv : av;
		}

		int val = (rv >> bit_pos) & 1;
		cache[bit] = val;
		return val;
	}

	bool eval_sig_is_zero(SigSpec sig)
	{
		dict<SigBit, int> cache;
		for (auto bit : sigmap(sig))
			if (eval_bit_at_zero(bit, cache, 0) != 0)
				return false;
		return true;
	}

	int64_t eval_sig_at_zero(SigSpec sig)
	{
		dict<SigBit, int> cache;
		int64_t result = 0;
		for (int i = 0; i < GetSize(sig) && i < 62; i++)
			result |= ((int64_t)eval_bit_at_zero(sig[i], cache, 0) << i);
		return result;
	}

	int output_bits_controlled_by(Wire *control, Wire *output)
	{
		pool<int> bits;
		for (auto cell : module->cells()) {
			if (cell->type != ID($mux))
				continue;
			SigSpec sel = sigmap(cell->getPort(ID::S));
			if (GetSize(sel) != 1 || sel[0].wire != control)
				continue;
			for (auto bit : sigmap(cell->getPort(ID::Y)))
				if (bit.wire == output)
					bits.insert(bit.offset);
		}
		return GetSize(bits);
	}

	bool indexed_reads_stay_in_range(Wire *data, int loop_width)
	{
		bool saw_data_read = false;
		for (auto cell : module->cells()) {
			if (!cell->type.in(ID($bmux), ID($shiftx)))
				continue;
			if (sigmap(cell->getPort(ID::A)) != sigmap(SigSpec(data)))
				continue;
			saw_data_read = true;
			IdString select_port = cell->type == ID($bmux) ? ID::S : ID::B;
			if (eval_sig_at_zero(cell->getPort(select_port)) >= loop_width)
				return false;
		}
		return saw_data_read;
	}

	SigSpec zext(SigSpec sig, int width)
	{
		sig = sigmap(sig);
		if (GetSize(sig) > width)
			return sig.extract(0, width);
		if (GetSize(sig) < width)
			sig.append(SigSpec(State::S0, width - GetSize(sig)));
		return sig;
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

	static Const const_u64(uint64_t value, int width)
	{
		vector<State> bits(width, State::S0);
		for (int i = 0; i < width && i < 64; i++)
			if ((value >> i) & 1ULL)
				bits[i] = State::S1;
		return Const(bits);
	}

	void remove_old_cells(const vector<Cell *> &old_cells)
	{
		for (auto cell : old_cells) {
			if (module->cell(cell->name) == nullptr)
				continue;
			module->remove(cell);
			old_cells_removed++;
		}
	}

	bool rewrite_forward_dense_pack()
	{
		vector<Wire *> inputs = input_ports();
		vector<Wire *> outputs = output_ports();
		if (GetSize(inputs) != 1 || GetSize(outputs) != 1)
			return false;
		Wire *sig = inputs[0];
		Wire *sig2 = outputs[0];
		if (GetSize(sig) != GetSize(sig2))
			return false;
		if (GetSize(sig) < 4 || GetSize(sig) > max_width)
			return false;
		if (GetSize(module->ports) != 2)
			return false;
		if (count_binop_const(ID($add), 1) < GetSize(sig) - 2)
			return false;
		if (count_cells(ID($mux)) < GetSize(sig))
			return false;
		if (!eval_sig_is_zero(SigSpec(sig2)))
			return false;

		vector<Cell *> old_cells(module->cells().begin(), module->cells().end());
		ref_cell = old_cells.front();

		int width = GetSize(sig);
		int count_width = ceil_log2_int(width + 1);
		vector<SigSpec> bits;
		for (int i = 0; i < width; i++)
			bits.push_back(SigSpec(sigmap(SigBit(sig, i))));

		SigSpec count = balanced_sum(bits, count_width);
		SigSpec packed;
		for (int i = 0; i < width; i++)
			packed.append(emit_gt(count, i, count_width));

		module->connect(SigSpec(sig2), packed);
		remove_old_cells(old_cells);

		log("  Forward dense pack: %s -> %s, width=%d, count_width=%d.\n",
		    log_id(sig->name), log_id(sig2->name), width, count_width);
		forward_rewrites++;
		return true;
	}

	bool rewrite_reverse_suffix_read()
	{
		vector<Wire *> inputs = input_ports();
		vector<Wire *> outputs = output_ports();
		if (GetSize(inputs) != 2 || GetSize(outputs) != 1)
			return false;
		Wire *mask = outputs[0];
		if (GetSize(inputs[0]) != GetSize(inputs[1]) || GetSize(mask) != GetSize(inputs[0]))
			return false;

		int dec_count = std::max(count_binop_const(ID($sub), 1),
		                         count_binop_const(ID($add), -1));
		int loop_width = dec_count + 1;
		if (count_cells(ID($mux)) < loop_width)
			return false;
		if (has_binop_const_other_than(ID($sub), 1) ||
		    has_binop_const_other_than(ID($add), -1))
			return false;

		Wire *disable = nullptr;
		int controlled_width = 0;
		for (auto input : inputs) {
			int n = output_bits_controlled_by(input, mask);
			if (n == 0)
				continue;
			if (disable != nullptr)
				return false;
			disable = input;
			controlled_width = n;
		}
		if (disable == nullptr)
			return false;
		if (controlled_width > 0)
			loop_width = controlled_width;
		if (loop_width < 4 || loop_width > max_width || loop_width > GetSize(mask))
			return false;
		if (dec_count < loop_width - 1)
			return false;
		Wire *data = (inputs[0] == disable) ? inputs[1] : inputs[0];

		if (!indexed_reads_stay_in_range(data, loop_width))
			return false;
		if (!eval_sig_is_zero(SigSpec(mask)))
			return false;

		vector<Cell *> old_cells(module->cells().begin(), module->cells().end());
		ref_cell = old_cells.front();

		int count_width = ceil_log2_int(loop_width + 1);
		vector<SigBit> valid(loop_width);
		for (int i = 0; i < loop_width; i++)
			valid[i] = emit_not(sigmap(SigBit(disable, i)));

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
				SigBit gated_data = emit_and(sigmap(SigBit(data, k)), is_source);
				candidates.append(gated_data);
			}

			SigBit selected = emit_reduce_or(candidates);
			out_bits.append(emit_and(valid[j], selected));
		}

		if (GetSize(mask) > loop_width)
			out_bits.append(SigSpec(State::S0, GetSize(mask) - loop_width));

		module->connect(SigSpec(mask), out_bits);
		remove_old_cells(old_cells);

		log("  Reverse suffix read: %s/%s -> %s, loop_width=%d, count_width=%d.\n",
		    log_id(disable->name), log_id(data->name), log_id(mask->name),
		    loop_width, count_width);
		reverse_rewrites++;
		return true;
	}

	// Reference function for the modulo-n decimation loop: scanning the enable
	// vector from one end, mark every n-th enabled bit. Equivalent closed form:
	//   mask[I] = en[I] && n>0 && (inclusive_popcount(I) % n == 0)
	// where the popcount runs from the scan's leading end down to (incl.) I.
	uint64_t expected_modulo_mask(uint64_t en, uint64_t n, int width, bool msb_first)
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
			if (v % n == 0)
				mask |= (1ULL << i);
		}
		return mask;
	}

	// Confirm the combinational function from (en, n) to mask matches the modulo
	// decimation reference for the given scan direction, using ConstEval over a
	// structured + pseudo-random vector set (cf. opt_argmax's fingerprint).
	bool fingerprint_modulo(Wire *en, Wire *n, Wire *mask, int width, bool msb_first)
	{
		if (width <= 0 || width > 62)
			return false;
		ConstEval ce(module);
		SigSpec en_sig = sigmap(SigSpec(en));
		SigSpec n_sig = sigmap(SigSpec(n));
		SigSpec mask_sig = sigmap(SigSpec(mask));
		int nw = GetSize(n);

		vector<uint64_t> nvals;
		uint64_t nmax = (nw >= 64) ? ~0ULL : ((1ULL << nw) - 1);
		for (uint64_t v = 0; v <= (uint64_t)width + 1 && v <= nmax; v++)
			nvals.push_back(v);
		if (nmax > (uint64_t)width + 1)
			nvals.push_back(nmax);

		uint64_t full = (width >= 64) ? ~0ULL : ((1ULL << width) - 1);
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
				ce.push();
				ce.set(en_sig, const_u64(ev, width));
				ce.set(n_sig, const_u64(nv, nw));
				SigSpec out = mask_sig;
				SigSpec undef;
				bool ok = ce.eval(out, undef);
				ce.pop();
				if (!ok || !out.is_fully_const())
					return false;
				Const cv = out.as_const();
				uint64_t actual = 0;
				for (int i = 0; i < width && i < 64; i++)
					if (cv[i] == State::S1)
						actual |= (1ULL << i);
				if (actual != expected_modulo_mask(ev, nv, width, msb_first))
					return false;
			}
		return true;
	}

	bool rewrite_modulo_decimation()
	{
		vector<Wire *> inputs = input_ports();
		vector<Wire *> outputs = output_ports();
		if (GetSize(inputs) != 2 || GetSize(outputs) != 1)
			return false;
		if (GetSize(module->ports) != 3)
			return false;

		Wire *mask = outputs[0];
		int width = GetSize(mask);
		if (width < 4 || width > max_width)
			return false;

		// en matches the mask width; n (the modulus) is a distinct, narrower bus.
		// Requiring different widths also disambiguates from the reverse suffix
		// read form, whose two inputs share the mask width.
		Wire *en = nullptr, *n = nullptr;
		for (auto in : inputs) {
			if (GetSize(in) == width && en == nullptr)
				en = in;
			else
				n = in;
		}
		if (en == nullptr || n == nullptr || en == n || GetSize(n) == width)
			return false;

		bool msb_first;
		if (fingerprint_modulo(en, n, mask, width, true))
			msb_first = true;
		else if (fingerprint_modulo(en, n, mask, width, false))
			msb_first = false;
		else
			return false;

		vector<Cell *> old_cells(module->cells().begin(), module->cells().end());
		if (old_cells.empty())
			return false;
		ref_cell = old_cells.front();

		int cnt_width = ceil_log2_int(width + 1);
		int table_size = 1 << cnt_width;
		int cmp_width = std::max(GetSize(n), cnt_width);

		auto en_bit = [&](int i) { return sigmap(SigBit(en, i)); };

		// 1) Inclusive prefix popcount as a naive linear $add cascade. Each
		//    running sum is consumed below, so the downstream opt_parallel_prefix
		//    pass rebuilds the cascade into a shared log-depth prefix network.
		vector<SigSpec> popcount(width);
		Cell *cell = ref_cell;
		int start = msb_first ? width - 1 : 0;
		int step = msb_first ? -1 : 1;
		int last = msb_first ? 0 : width - 1;
		SigSpec acc = SigSpec(en_bit(start));
		popcount[start] = zext(acc, cnt_width);
		for (int i = start + step; i != last + step; i += step) {
			Wire *sum = module->addWire(NEW_ID2_SUFFIX("compact_pop"), cnt_width);
			module->addAdd(NEW_ID2_SUFFIX("compact_pop_add"), acc, SigSpec(en_bit(i)), sum);
			new_cells_emitted++;
			acc = SigSpec(sum);
			popcount[i] = SigSpec(sum);
		}

		// 2) Decode the modulus once: eq_d = (n == d) for d in [1..width].
		vector<SigBit> eqd(width + 1, State::S0);
		for (int d = 1; d <= width; d++)
			eqd[d] = emit_eq(SigSpec(n), d, cmp_width);

		// 3) Divisibility per popcount value: div_k = OR_{d | k} eq_d. n>0 and
		//    n>width fall out for free (no divisor in range matches).
		vector<SigBit> divisible(table_size, State::S0);
		divisible[0] = State::S1; // gated away by en[]; defined to size the table
		for (int k = 1; k <= width; k++) {
			SigSpec terms;
			for (int d = 1; d <= k; d++)
				if (k % d == 0)
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
			out_bits.append(emit_and(en_bit(i), sel_divisible));
		}

		module->connect(SigSpec(mask), out_bits);
		remove_old_cells(old_cells);

		log("  Modulo decimation: en=%s, n=%s -> %s, width=%d, %s scan.\n",
		    log_id(en->name), log_id(n->name), log_id(mask->name), width,
		    msb_first ? "MSB-first" : "LSB-first");
		modulo_rewrites++;
		return true;
	}

	void run()
	{
		if (module->has_processes_warn())
			return;
		if (rewrite_forward_dense_pack())
			return;
		if (rewrite_reverse_suffix_read())
			return;
		rewrite_modulo_decimation();
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
		log("The modulo decimation form (mark every n-th enabled bit while scanning\n");
		log("the enable vector) is lowered to a prefix-popcount plus divisor-decode\n");
		log("divisibility check. The popcount is emitted as a plain linear $add\n");
		log("cascade so a subsequent opt_parallel_prefix pass can rebuild it into a\n");
		log("shared log-depth network.\n");
		log("\n");
		log("    -max_width <n>\n");
		log("        Maximum compaction width to rewrite. Default: 64.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_COMPACT_PREFIX pass (monotonic compaction rewrites).\n");

		int max_width = 64;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_width" && argidx + 1 < args.size()) {
				max_width = atoi(args[++argidx].c_str());
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
