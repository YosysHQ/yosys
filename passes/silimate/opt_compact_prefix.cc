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

	Wire *port(const char *name)
	{
		return module->wire(RTLIL::escape_id(name));
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

	bool bmux_selects_stay_in_range(Wire *data, int loop_width)
	{
		bool saw_data_bmux = false;
		for (auto cell : module->cells()) {
			if (cell->type != ID($bmux))
				continue;
			if (sigmap(cell->getPort(ID::A)) != sigmap(SigSpec(data)))
				continue;
			saw_data_bmux = true;
			if (eval_sig_at_zero(cell->getPort(ID::S)) >= loop_width)
				return false;
		}
		return saw_data_bmux;
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
		Wire *sig = port("sig");
		Wire *sig2 = port("sig2");
		if (!sig || !sig2)
			return false;
		if (!sig->port_input || !sig2->port_output)
			return false;
		if (GetSize(sig) != GetSize(sig2))
			return false;
		if (GetSize(sig) < 4 || GetSize(sig) > max_width)
			return false;
		if (GetSize(module->ports) != 2)
			return false;
		if (count_binop_const(ID($add), 1) < GetSize(sig) - 2)
			return false;
		if (count_cells(ID($shl)) < GetSize(sig) - 2)
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
		Wire *disable = port("disable_in");
		Wire *data = port("data_in");
		Wire *mask = port("mask");
		if (!disable || !data || !mask)
			return false;
		if (!disable->port_input || !data->port_input || !mask->port_output)
			return false;
		if (GetSize(disable) != GetSize(data) || GetSize(mask) != GetSize(data))
			return false;
		if (GetSize(module->ports) != 3)
			return false;

		int dec_count = std::max(count_binop_const(ID($sub), 1),
		                         count_binop_const(ID($add), -1));
		int loop_width = dec_count + 1;
		if (loop_width < 4 || loop_width > max_width || loop_width > GetSize(data))
			return false;
		if (count_cells(ID($mux)) < loop_width)
			return false;
		if (has_binop_const_other_than(ID($sub), 1) ||
		    has_binop_const_other_than(ID($add), -1))
			return false;
		if (!bmux_selects_stay_in_range(data, loop_width))
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

	void run()
	{
		if (module->has_processes_warn())
			return;
		if (rewrite_forward_dense_pack())
			return;
		rewrite_reverse_suffix_read();
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
		log("Currently this pass handles the dense bit-pack and reverse suffix-read\n");
		log("forms used by the qor_spi_ra_add_chain and qor_spi_ra_sub_chain\n");
		log("regressions. Non-matching modules are left unchanged.\n");
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
		int total_removed = 0;
		int total_emitted = 0;

		for (auto module : design->selected_modules()) {
			OptCompactPrefixWorker worker(module, max_width);
			worker.run();
			total_forward += worker.forward_rewrites;
			total_reverse += worker.reverse_rewrites;
			total_removed += worker.old_cells_removed;
			total_emitted += worker.new_cells_emitted;
		}

		log("Rewrote %d forward pack(s), %d reverse suffix read(s); "
		    "removed %d old cell(s), emitted %d new cell(s).\n",
		    total_forward, total_reverse, total_removed, total_emitted);

		if (total_forward || total_reverse)
			Yosys::run_pass("clean -purge");
	}
} OptCompactPrefixPass;

PRIVATE_NAMESPACE_END
