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
#include "kernel/ff.h"
#include "kernel/ffinit.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Value ranges are tracked in 128-bit signed arithmetic. Anything that would overflow
// that, or that the analysis cannot interpret, becomes "top" (the declared width).
typedef __int128 wideint_t;

// No endpoint is ever allowed past this width, so -x is always representable and the
// rules may negate an endpoint without checking. cell_range enforces it.
static const int max_range_width = 126;

struct Range {
	bool top;
	wideint_t lo, hi;

	Range() : top(true), lo(0), hi(0) { }
	Range(wideint_t lo, wideint_t hi) : top(false), lo(lo), hi(hi) { }

	static Range unknown() { return Range(); }
};

// Smallest signed bit width whose two's-complement range covers [lo, hi]
static int signed_width(wideint_t lo, wideint_t hi)
{
	for (int n = 1; n < 128; n++) {
		wideint_t limit = (wideint_t)1 << (n - 1);
		if (-limit <= lo && hi <= limit - 1)
			return n;
	}
	return 128;
}

// Smallest unsigned bit width covering [0, hi]
static int unsigned_width(wideint_t hi)
{
	for (int n = 0; n < 128; n++)
		if (hi < ((wideint_t)1 << n))
			return n;
	return 128;
}

// Widest range an opaque word of the given width can hold
static Range declared_range(int width, bool is_signed)
{
	if (width <= 0)
		return Range(0, 0);
	if (width > max_range_width)
		return Range::unknown();
	if (is_signed)
		return Range(-((wideint_t)1 << (width - 1)), ((wideint_t)1 << (width - 1)) - 1);
	return Range(0, ((wideint_t)1 << width) - 1);
}

// Overflow-checked helpers: any overflow collapses the result to top
static bool add_ovf(wideint_t a, wideint_t b, wideint_t &out)
{
	return __builtin_add_overflow(a, b, &out);
}

static bool mul_ovf(wideint_t a, wideint_t b, wideint_t &out)
{
	return __builtin_mul_overflow(a, b, &out);
}

struct SignifWorker
{
	Module *module;
	SigMap sigmap;
	FfInitVals initvals;   // init attributes, for bounding a flop's reset/power-up value

	// Sigmapped output bit -> the cell driving it and which output bit it is
	dict<SigBit, std::pair<Cell *, int>> bit_driver;

	dict<Cell *, Range> memo;
	pool<Cell *> active;   // cells on the current recursion stack, for cycle breaking
	int steps = 0;         // evaluation budget guard
	int max_steps;
	int max_depth;         // recursion depth guard, since active.size() is the C++ depth

	pool<IdString> narrow_types;
	bool cross_flops;      // carry ranges across registers (assumes reset before use)

	// One cell's narrowing decision. Flipping an unsigned cell to signed is a property
	// of the whole cell, so ports cannot be decided independently.
	struct Plan {
		Cell *cell = nullptr;
		bool make_signed = false;
		bool change[2] = {false, false};   // index 0 is port A, 1 is port B
		SigSpec sig[2];
		// Full-width word each port is sliced from. try_swap_cmp narrows a rebuilt word
		// rather than the port itself, so re-slicing later cannot just read the port.
		SigSpec base[2];
		int from[2] = {0, 0};
		int to[2] = {0, 0};

		int bits_saved() const
		{
			int n = 0;
			for (int i = 0; i < 2; i++)
				if (change[i])
					n += from[i] - to[i];
			return n;
		}
	};
	vector<Plan> plans;

	SignifWorker(Module *module, int max_steps, int max_depth,
			const pool<IdString> &narrow_types, bool cross_flops) :
			module(module), sigmap(module), initvals(&sigmap, module),
			max_steps(max_steps), max_depth(max_depth), narrow_types(narrow_types),
			cross_flops(cross_flops)
	{
		// Index every cell output bit. Cells whose semantics we do not model still get
		// indexed; their range rule falls through to the declared width.
		for (auto cell : module->cells()) {
			IdString out = out_port(cell);
			if (out == IdString())
				continue;
			SigSpec y = sigmap(cell->getPort(out));
			for (int i = 0; i < GetSize(y); i++)
				if (y[i].is_wire())
					bit_driver[y[i]] = std::make_pair(cell, i);
		}
	}

	// A flop's Q word is a value like any other: it only ever holds something its D
	// input held, so the analysis can carry a range across it instead of stopping.
	static bool is_ff(Cell *cell)
	{
		return RTLIL::builtin_ff_cell_types().count(cell->type) && cell->hasPort(ID::Q);
	}

	// The output word this cell drives, if the analysis can name one
	IdString out_port(Cell *cell)
	{
		if (cell->hasPort(ID::Y))
			return ID::Y;
		return cross_flops && is_ff(cell) ? ID::Q : IdString();
	}

	// The width parameter that governs a cell's output word
	static IdString out_width_param(Cell *cell)
	{
		return cell->hasParam(ID::Y_WIDTH) ? ID::Y_WIDTH : ID::WIDTH;
	}

	static int out_width(Cell *cell)
	{
		IdString param = out_width_param(cell);
		return cell->hasParam(param) ? cell->getParam(param).as_int() : 0;
	}

	// If bits are exactly cell->Y[0 +: n] in order, return that cell, else nullptr
	Cell *whole_output_of(const std::vector<SigBit> &bits)
	{
		if (bits.empty() || !bits[0].is_wire())
			return nullptr;
		auto it = bit_driver.find(bits[0]);
		if (it == bit_driver.end() || it->second.second != 0)
			return nullptr;
		Cell *cell = it->second.first;
		for (int i = 1; i < GetSize(bits); i++) {
			if (!bits[i].is_wire())
				return nullptr;
			auto jt = bit_driver.find(bits[i]);
			if (jt == bit_driver.end() || jt->second.first != cell || jt->second.second != i)
				return nullptr;
		}
		return cell;
	}

	// Two's-complement add/sub/mul/neg produce the same bits for signed and unsigned
	// operands when nothing is extended and the result is truncated to that same width.
	// In that modular case an operand may be read as signed even where the port says
	// unsigned, which is how elaborated signed arithmetic over pre-extended operands
	// reaches us. Without this the analysis loses the range at every such cell.
	bool modular_signed_ok(Cell *cell)
	{
		if (!cell->type.in(ID($add), ID($sub), ID($mul), ID($neg), ID($pos)))
			return false;
		int width = op_width(cell);
		if (!cell->hasParam(ID::Y_WIDTH) || cell->getParam(ID::Y_WIDTH).as_int() != width)
			return false;
		for (IdString param : {ID::A_WIDTH, ID::B_WIDTH})
			if (cell->hasParam(param) && cell->getParam(param).as_int() != width)
				return false;
		return true;
	}

	// Range of an input port, read with that port's own signedness
	Range port_range(Cell *cell, char port)
	{
		int idx = port == 'A' ? 0 : 1;
		bool is_signed = port_is_signed(cell, idx) || modular_signed_ok(cell);
		return sig_range(cell->getPort(port_id(idx)), is_signed);
	}

	// Range of an arbitrary SigSpec interpreted as a signed or unsigned integer
	Range sig_range(const SigSpec &sig_in, bool is_signed)
	{
		SigSpec sig = sigmap(sig_in);
		std::vector<SigBit> bits = sig.to_sigbit_vector();
		if (bits.empty())
			return Range(0, 0);

		// Fully constant: exact value. Undefined bits are not values, so bail.
		bool all_const = true;
		for (auto &bit : bits)
			if (bit.is_wire()) {
				all_const = false;
				break;
			}
		if (all_const) {
			if (GetSize(bits) > max_range_width)
				return Range::unknown();
			wideint_t val = 0;
			for (int i = 0; i < GetSize(bits); i++) {
				if (bits[i].data != State::S0 && bits[i].data != State::S1)
					return Range::unknown();
				if (bits[i].data == State::S1)
					val |= (wideint_t)1 << i;
			}
			if (is_signed && bits[GetSize(bits) - 1].data == State::S1)
				val -= (wideint_t)1 << GetSize(bits);
			return Range(val, val);
		}

		// Constant-zero high bits mean the value is a narrower *unsigned* quantity,
		// whatever signedness the reader asked for.
		int k = GetSize(bits);
		while (k > 1 && !bits[k - 1].is_wire() && bits[k - 1].data == State::S0)
			k--;
		if (k < GetSize(bits))
			return sig_range(sig.extract(0, k), false);

		// A whole cell output word (or a low slice of one that provably fits)
		Cell *cell = whole_output_of(bits);
		if (cell != nullptr) {
			Range r = cell_range(cell);
			if (r.top)
				return declared_range(GetSize(bits), is_signed);
			// Reading fewer bits than the cell drives is a truncation, which only
			// preserves the value when the range already fits in the slice.
			int need = is_signed ? signed_width(r.lo, r.hi) : (r.lo < 0 ? 128 : unsigned_width(r.hi));
			if (GetSize(bits) >= need)
				return r;
			return declared_range(GetSize(bits), is_signed);
		}

		// A word can also be driven bit by bit by a blasted register, which is the shape
		// a pipeline register actually reaches this pass in: the flow splits every flop
		// into one-bit cells for reporting, so the whole-output test above never matches
		// one. Rebuilding the word its data inputs form recovers the range.
		Range ff = ff_word_range(bits, is_signed);
		if (!ff.top)
			return ff;

		return declared_range(GetSize(bits), is_signed);
	}

	// True when two flops capture on the same event, so a word split across them always
	// holds one consistent snapshot of their data inputs. Without this a sign-extended
	// range would be unsound: skewed bits could pair a negative high bit with a
	// positive low word, which no single reachable value of the data word allows.
	bool same_ff_control(const FfData &a, const FfData &b)
	{
		if (a.has_clk != b.has_clk || a.has_ce != b.has_ce || a.has_aload != b.has_aload ||
				a.has_arst != b.has_arst || a.has_srst != b.has_srst ||
				a.has_sr != b.has_sr || a.has_gclk != b.has_gclk)
			return false;
		if (a.has_clk && (sigmap(a.sig_clk) != sigmap(b.sig_clk) ||
				a.pol_clk != b.pol_clk))
			return false;
		if (a.has_ce && (sigmap(a.sig_ce) != sigmap(b.sig_ce) || a.pol_ce != b.pol_ce))
			return false;
		if (a.has_arst && (sigmap(a.sig_arst) != sigmap(b.sig_arst) ||
				a.pol_arst != b.pol_arst))
			return false;
		if (a.has_srst && (sigmap(a.sig_srst) != sigmap(b.sig_srst) ||
				a.pol_srst != b.pol_srst || a.ce_over_srst != b.ce_over_srst))
			return false;
		if (a.has_aload && (sigmap(a.sig_aload) != sigmap(b.sig_aload) ||
				a.pol_aload != b.pol_aload))
			return false;
		return true;
	}

	// Range of a word whose bits are driven by flops that all capture together. The word
	// only ever holds a snapshot of the word its data inputs form, plus whatever the
	// resets and init force, so the union of those bounds it.
	Range ff_word_range(const std::vector<SigBit> &bits, bool is_signed)
	{
		if (!cross_flops || ++steps > max_steps)
			return Range::unknown();

		pool<Cell *> cells;
		SigSpec sig_d, sig_ad;
		std::vector<State> arst, srst, init;
		FfData *ctrl = nullptr;
		std::vector<std::unique_ptr<FfData>> ffs;

		for (auto &bit : bits) {
			auto it = bit.is_wire() ? bit_driver.find(bit) : bit_driver.end();
			if (it == bit_driver.end() || !is_ff(it->second.first))
				return Range::unknown();
			Cell *cell = it->second.first;
			// A flop already on the recursion stack means feedback: a genuine
			// accumulator, which must keep its declared width.
			if (active.count(cell) || GetSize(active) + GetSize(cells) >= max_depth)
				return Range::unknown();
			ffs.push_back(std::make_unique<FfData>(&initvals, cell));
			FfData &ff = *ffs.back();
			if (ff.has_sr || ff.is_fine || !ff.has_clk)
				return Range::unknown();
			if (ctrl == nullptr)
				ctrl = &ff;
			else if (!same_ff_control(*ctrl, ff))
				return Range::unknown();
			cells.insert(cell);

			int off = it->second.second;
			sig_d.append(ff.sig_d[off]);
			if (ff.has_aload)
				sig_ad.append(ff.sig_ad[off]);
			if (ff.has_arst)
				arst.push_back(ff.val_arst[off]);
			if (ff.has_srst)
				srst.push_back(ff.val_srst[off]);
			init.push_back(GetSize(ff.val_init) > off ? ff.val_init[off] : State::Sx);
		}

		// Guard the whole run at once, so a cycle through any of its flops is caught.
		for (auto cell : cells)
			active.insert(cell);
		Range out = sig_range(sig_d, is_signed);
		if (!out.top && GetSize(sig_ad)) {
			Range ad = sig_range(sig_ad, is_signed);
			if (ad.top)
				out = Range::unknown();
			else {
				out.lo = std::min(out.lo, ad.lo);
				out.hi = std::max(out.hi, ad.hi);
			}
		}
		for (auto cell : cells)
			active.erase(cell);
		if (out.top)
			return Range::unknown();

		// An all-undefined init word just means no flop in the run carried one.
		if (std::all_of(init.begin(), init.end(), [](State s) { return s == State::Sx; }))
			init.clear();

		int width = GetSize(bits);
		for (auto *val : {&arst, &srst, &init}) {
			if (val->empty())
				continue;
			// A partially forced word says nothing about the bits it leaves alone.
			if (GetSize(*val) != width)
				return Range::unknown();
			Range c = const_range(Const(*val), width, is_signed);
			if (c.top)
				return Range::unknown();
			out.lo = std::min(out.lo, c.lo);
			out.hi = std::max(out.hi, c.hi);
		}

		// Keep the range inside the word the bits actually hold, and inside the
		// interval arithmetic: a 128-bit accumulator holding an 8-bit value is the
		// case most worth handling, but every endpoint still has to be negatable.
		// Unsigned uses the same need the reader will: a negative lo means the forced
		// bits were not a value in that encoding, not a signed wrap to keep.
		int need = is_signed ? signed_width(out.lo, out.hi)
				: (out.lo < 0 ? 128 : unsigned_width(out.hi));
		if (need > std::min(width, max_range_width))
			return Range::unknown();
		return out;
	}

	// Range of a cell's Y word, memoized; feedback and unknown cells yield top
	Range cell_range(Cell *cell)
	{
		auto it = memo.find(cell);
		if (it != memo.end())
			return it->second;

		// Bail out to the declared width on a feedback loop, on budget exhaustion, or on
		// a chain deeper than max_depth. The depth guard is not redundant with the step
		// budget: a long chain of dependent adds recurses once per link, so a budget in
		// the tens of thousands would let the native C++ stack overflow before it trips.
		int ywidth = out_width(cell);
		if (active.count(cell) || ++steps > max_steps || GetSize(active) >= max_depth)
			return declared_range(ywidth, true);
		active.insert(cell);

		Range out = eval_cell(cell, ywidth);

		// The output word only holds the low ywidth bits. If the exact range needs more
		// bits than that, the result wraps and the range says nothing. Compare widths
		// rather than clamping: clamping would silently drop the wrapped value, and a
		// word wider than the interval arithmetic can represent still bounds a narrow
		// result perfectly well.
		//
		// Cap at max_range_width as well, which is what keeps every endpoint's
		// negation representable. Without it a 128-bit word could carry an endpoint at
		// the 128-bit minimum -- reachable as a checked product, e.g. -2^63 * (2^64-1)
		// -- and the next $neg or $sub would negate it, which is undefined.
		if (out.top || signed_width(out.lo, out.hi) > std::min(ywidth, max_range_width))
			out = declared_range(ywidth, true);

		active.erase(cell);
		memo[cell] = out;
		return out;
	}

	Range eval_cell(Cell *cell, int ywidth)
	{
		// Comparisons and reductions produce a single boolean bit
		if (cell->type.in(ID($eq), ID($ne), ID($eqx), ID($nex), ID($lt), ID($le),
				ID($gt), ID($ge), ID($logic_and), ID($logic_or), ID($logic_not),
				ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor),
				ID($reduce_bool)))
			return Range(0, 1);

		if (cell->type == ID($pos))
			return port_range(cell, 'A');

		if (cell->type == ID($neg)) {
			Range a = port_range(cell, 'A');
			if (a.top)
				return Range::unknown();
			return Range(-a.hi, -a.lo);
		}

		if (cell->type.in(ID($add), ID($sub))) {
			Range a = port_range(cell, 'A'), b = port_range(cell, 'B');
			if (a.top || b.top)
				return Range::unknown();
			wideint_t lo, hi;
			if (cell->type == ID($add)) {
				if (add_ovf(a.lo, b.lo, lo) || add_ovf(a.hi, b.hi, hi))
					return Range::unknown();
			} else {
				if (add_ovf(a.lo, -b.hi, lo) || add_ovf(a.hi, -b.lo, hi))
					return Range::unknown();
			}
			return Range(lo, hi);
		}

		if (cell->type == ID($mul)) {
			Range a = port_range(cell, 'A'), b = port_range(cell, 'B');
			if (a.top || b.top)
				return Range::unknown();
			wideint_t corners[4];
			if (mul_ovf(a.lo, b.lo, corners[0]) || mul_ovf(a.lo, b.hi, corners[1]) ||
					mul_ovf(a.hi, b.lo, corners[2]) || mul_ovf(a.hi, b.hi, corners[3]))
				return Range::unknown();
			wideint_t lo = corners[0], hi = corners[0];
			for (int i = 1; i < 4; i++) {
				lo = std::min(lo, corners[i]);
				hi = std::max(hi, corners[i]);
			}
			return Range(lo, hi);
		}

		// Bitwise ops on non-negative operands stay within the operand magnitudes
		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
			Range a = port_range(cell, 'A'), b = port_range(cell, 'B');
			if (a.top || b.top || a.lo < 0 || b.lo < 0)
				return Range::unknown();
			if (cell->type == ID($and))
				return Range(0, std::min(a.hi, b.hi));
			int n = std::max(unsigned_width(a.hi), unsigned_width(b.hi));
			return declared_range(n, false);
		}

		// Left shift by a bounded, non-negative amount: scale by each shift extreme
		if (cell->type.in(ID($shl), ID($sshl))) {
			Range a = port_range(cell, 'A'), b = port_range(cell, 'B');
			if (a.top || b.top || b.lo < 0 || b.hi > max_range_width)
				return Range::unknown();
			wideint_t lo_scale = (wideint_t)1 << (int)b.lo;
			wideint_t hi_scale = (wideint_t)1 << (int)b.hi;
			wideint_t corners[4];
			if (mul_ovf(a.lo, lo_scale, corners[0]) || mul_ovf(a.lo, hi_scale, corners[1]) ||
					mul_ovf(a.hi, lo_scale, corners[2]) || mul_ovf(a.hi, hi_scale, corners[3]))
				return Range::unknown();
			wideint_t lo = corners[0], hi = corners[0];
			for (int i = 1; i < 4; i++) {
				lo = std::min(lo, corners[i]);
				hi = std::max(hi, corners[i]);
			}
			return Range(lo, hi);
		}

		// Right shift moves toward zero, so the operand range still bounds the result
		if (cell->type == ID($sshr)) {
			Range a = port_range(cell, 'A');
			Range b = port_range(cell, 'B');
			if (a.top || b.top || b.lo < 0)
				return Range::unknown();
			return Range(std::min<wideint_t>(a.lo, 0), std::max<wideint_t>(a.hi, 0));
		}
		if (cell->type == ID($shr)) {
			Range a = port_range(cell, 'A');
			Range b = port_range(cell, 'B');
			if (a.top || b.top || a.lo < 0 || b.lo < 0)
				return Range::unknown();
			return Range(0, a.hi);
		}

		// A flop holds a value its data input held, or one of the constants it can be
		// forced to, so the union of those bounds Q. Feedback is already broken by the
		// `active` guard, which is what keeps a genuine accumulator at declared width.
		if (is_ff(cell))
			return ff_range(cell, ywidth);

		// Multiplexers: the union over the arms
		if (cell->type.in(ID($mux), ID($pmux))) {
			Range out = sig_range(cell->getPort(ID::A), true);
			if (out.top)
				return Range::unknown();
			SigSpec b = cell->getPort(ID::B);
			int width = ywidth > 0 ? ywidth : GetSize(b);
			for (int off = 0; width > 0 && off + width <= GetSize(b); off += width) {
				Range arm = sig_range(b.extract(off, width), true);
				if (arm.top)
					return Range::unknown();
				out.lo = std::min(out.lo, arm.lo);
				out.hi = std::max(out.hi, arm.hi);
			}
			return out;
		}

		return Range::unknown();
	}

	// Range of a constant that may carry undefined bits. setundef runs later in the
	// flow, so an x could still become either value: treat it as the whole word.
	static Range const_range(const Const &val, int width, bool is_signed)
	{
		if (GetSize(val) > max_range_width)
			return declared_range(width, is_signed);
		for (int i = 0; i < GetSize(val); i++)
			if (val[i] != State::S0 && val[i] != State::S1)
				return declared_range(width, is_signed);
		wideint_t v = 0;
		for (int i = 0; i < GetSize(val); i++)
			if (val[i] == State::S1)
				v |= (wideint_t)1 << i;
		// A flop's constant is a bit pattern of its own width; read it the same way the
		// Q word is read, so a set-to-all-ones register is -1 when signed and 2^w-1
		// when unsigned.
		if (is_signed && GetSize(val) > 0 && val[GetSize(val) - 1] == State::S1)
			v -= (wideint_t)1 << GetSize(val);
		return Range(v, v);
	}

	// Q of a flip-flop: the union of everything it can latch and everything it can be
	// forced to. Bit-level set/reset can produce arbitrary patterns, so those bail.
	Range ff_range(Cell *cell, int ywidth)
	{
		FfData ff(&initvals, cell);
		if (ff.has_sr || ff.is_fine)
			return Range::unknown();

		Range out = sig_range(ff.sig_d, true);
		if (out.top)
			return Range::unknown();

		// An asynchronous load is a second data path into the same word.
		if (ff.has_aload) {
			Range ad = sig_range(ff.sig_ad, true);
			if (ad.top)
				return Range::unknown();
			out.lo = std::min(out.lo, ad.lo);
			out.hi = std::max(out.hi, ad.hi);
		}

		// An all-undefined init is the absence of one, not a value: this is where the
		// reset-before-use assumption lives. A partly defined init says nothing about
		// the bits it leaves alone, so const_range rejects it below.
		for (int i = 0; i < 3; i++) {
			bool present = i == 0 ? ff.has_arst : i == 1 ? ff.has_srst
					: GetSize(ff.val_init) > 0 && !ff.val_init.is_fully_undef();
			if (!present)
				continue;
			Range c = const_range(i == 0 ? ff.val_arst : i == 1 ? ff.val_srst : ff.val_init,
					ywidth, true);
			if (c.top)
				return Range::unknown();
			out.lo = std::min(out.lo, c.lo);
			out.hi = std::max(out.hi, c.hi);
		}
		return out;
	}

	static IdString port_id(int idx) { return idx == 0 ? ID::A : ID::B; }
	static IdString width_id(int idx) { return idx == 0 ? ID::A_WIDTH : ID::B_WIDTH; }
	static IdString signed_id(int idx) { return idx == 0 ? ID::A_SIGNED : ID::B_SIGNED; }

	bool has_port(Cell *cell, int idx)
	{
		return cell->hasPort(port_id(idx)) && cell->hasParam(width_id(idx));
	}

	bool port_is_signed(Cell *cell, int idx)
	{
		return cell->hasParam(signed_id(idx)) && cell->getParam(signed_id(idx)).as_bool();
	}

	// The operation width every operand is extended to before the operator is applied
	static int op_width(Cell *cell)
	{
		int w = 0;
		for (IdString param : {ID::A_WIDTH, ID::B_WIDTH, ID::Y_WIDTH})
			if (cell->hasParam(param))
				w = std::max(w, cell->getParam(param).as_int());
		return w;
	}

	static bool is_compare(Cell *cell)
	{
		return cell->type.in(ID($lt), ID($le), ID($gt), ID($ge), ID($eq), ID($ne));
	}

	// A comparison's two operands are only meaningful against each other, and the rest of
	// the flow relies on that: wreduce trims a compare's operands together, and
	// opt_maxcmp compares one operand's lanes against the other operand directly, so it
	// aborts outright if the two widths disagree. Narrow both to the wider of the two
	// requirements, and leave a compare whose operands already disagree alone entirely.
	Plan equalize_compare(Plan plan, Cell *cell)
	{
		if (plan.cell == nullptr || !is_compare(cell))
			return plan;

		int w0 = GetSize(cell->getPort(ID::A));
		if (GetSize(cell->getPort(ID::B)) != w0)
			return Plan();

		// A port left unchanged still needs its declared width, so it sets the floor
		int want = 0;
		for (int i = 0; i < 2; i++)
			want = std::max(want, plan.change[i] ? plan.to[i] : w0);
		if (want >= w0)
			return Plan();

		for (int i = 0; i < 2; i++) {
			SigSpec src = plan.base[i].empty() ? cell->getPort(port_id(i)) : plan.base[i];
			plan.change[i] = true;
			plan.sig[i] = src.extract(0, want);
			plan.from[i] = w0;
			plan.to[i] = want;
		}
		return plan;
	}

	// Narrow each port under the signedness the cell already declares
	Plan try_direct(Cell *cell)
	{
		Plan plan;
		plan.cell = cell;
		for (int i = 0; i < 2; i++) {
			if (!has_port(cell, i))
				continue;
			// The B port of a shift is a distance, not a value in the result's domain
			if (i == 1 && cell->type.in(ID($shl), ID($shr), ID($sshl), ID($sshr)))
				continue;

			SigSpec sig = cell->getPort(port_id(i));
			int cur = GetSize(sig);
			if (cur < 2)
				continue;

			bool is_signed = port_is_signed(cell, i);
			Range r = sig_range(sig, is_signed);
			if (r.top)
				continue;

			int need;
			if (is_signed) {
				need = signed_width(r.lo, r.hi);
			} else {
				if (r.lo < 0)
					continue;
				need = std::max(1, unsigned_width(r.hi));
			}
			if (need >= cur)
				continue;

			plan.change[i] = true;
			plan.sig[i] = sig.extract(0, need);
			plan.base[i] = sig;
			plan.from[i] = cur;
			plan.to[i] = need;
		}
		return equalize_compare(plan, cell);
	}

	// Elaborators commonly emit unsigned $add/$sub/$mul whose operands were already
	// sign-extended to the operation width. Read those operands as signed instead, which
	// exposes the narrowing -- but only when flipping the cell to signed reproduces the
	// same extended operand value. Today each operand is zero-extended from its width to
	// the operation width; afterwards it is sign-extended from the narrowed width. Those
	// agree exactly when no extension happens (width == op_width) or the value is >= 0.
	Plan try_flip(Cell *cell)
	{
		if (!cell->type.in(ID($add), ID($sub), ID($mul)))
			return Plan();
		for (int i = 0; i < 2; i++) {
			if (!has_port(cell, i))
				return Plan();
			if (port_is_signed(cell, i))
				return Plan();   // already signed: try_direct owns that case
		}

		int width = op_width(cell);
		Plan plan;
		plan.cell = cell;
		plan.make_signed = true;

		for (int i = 0; i < 2; i++) {
			SigSpec sig = cell->getPort(port_id(i));
			int cur = GetSize(sig);
			Range r = sig_range(sig, true);

			if (cur != width && (r.top || r.lo < 0))
				return Plan();   // the extension would change value

			if (r.top || cur < 2)
				continue;
			int need = signed_width(r.lo, r.hi);
			if (need >= cur)
				continue;

			plan.change[i] = true;
			plan.sig[i] = sig.extract(0, need);
			plan.base[i] = sig;
			plan.from[i] = cur;
			plan.to[i] = need;
		}

		return plan.bits_saved() > 0 ? plan : Plan();
	}

	// A signed compare is commonly lowered to an unsigned compare of the two operands
	// with their sign bits exchanged, since unsigned_lt({Ymsb, Xlow}, {Xmsb, Ylow}) is
	// exactly signed_lt(X, Y) -- equal sign bits leave an unsigned compare of the low
	// bits, and unequal ones decide it. Swapping the top bits back recovers the operands
	// the compare really means, which the analysis can then narrow. A genuinely unsigned
	// compare self-rejects: the swap produces a mixed word that no cell drives, so its
	// range degrades to the declared width and nothing narrows.
	Plan try_swap_cmp(Cell *cell)
	{
		if (!cell->type.in(ID($lt), ID($le), ID($gt), ID($ge)))
			return Plan();
		for (int i = 0; i < 2; i++)
			if (!has_port(cell, i) || port_is_signed(cell, i))
				return Plan();

		SigSpec a = cell->getPort(ID::A), b = cell->getPort(ID::B);
		int width = GetSize(a);
		if (width < 2 || GetSize(b) != width)
			return Plan();

		SigSpec x = a.extract(0, width - 1);
		x.append(b[width - 1]);
		SigSpec y = b.extract(0, width - 1);
		y.append(a[width - 1]);

		Range rx = sig_range(x, true), ry = sig_range(y, true);
		if (rx.top || ry.top)
			return Plan();
		int need_x = signed_width(rx.lo, rx.hi), need_y = signed_width(ry.lo, ry.hi);
		if (need_x >= width || need_y >= width)
			return Plan();

		Plan plan;
		plan.cell = cell;
		plan.make_signed = true;
		plan.change[0] = true;
		plan.sig[0] = x.extract(0, need_x);
		plan.base[0] = x;
		plan.from[0] = width;
		plan.to[0] = need_x;
		plan.change[1] = true;
		plan.sig[1] = y.extract(0, need_y);
		plan.base[1] = y;
		plan.from[1] = width;
		plan.to[1] = need_y;
		return equalize_compare(plan, cell);
	}

	// Choose, per cell, whichever rewrite removes the most operand bits
	void collect()
	{
		for (auto cell : module->selected_cells()) {
			if (!narrow_types.count(cell->type))
				continue;

			Plan direct = try_direct(cell);
			Plan flip = try_flip(cell);
			Plan swap = try_swap_cmp(cell);
			Plan *best = nullptr;
			if (direct.bits_saved() > 0)
				best = &direct;
			if (flip.bits_saved() > (best != nullptr ? best->bits_saved() : 0))
				best = &flip;
			if (swap.bits_saved() > (best != nullptr ? best->bits_saved() : 0))
				best = &swap;
			if (best == nullptr)
				continue;

			for (int i = 0; i < 2; i++)
				if (best->change[i])
					log_debug("Narrowing %s port %s of %s.%s from %d to %d bits%s.\n",
							log_id(cell->type), log_id(port_id(i)), log_id(module),
							log_id(cell), best->from[i], best->to[i],
							best->make_signed ? " (unsigned -> signed)" : "");
			plans.push_back(*best);
		}
	}

	int run()
	{
		collect();
		int ports = 0;
		for (auto &plan : plans) {
			if (plan.make_signed) {
				plan.cell->setParam(ID::A_SIGNED, 1);
				plan.cell->setParam(ID::B_SIGNED, 1);
			}
			for (int i = 0; i < 2; i++) {
				if (!plan.change[i])
					continue;
				plan.cell->setPort(port_id(i), plan.sig[i]);
				plan.cell->setParam(width_id(i), plan.to[i]);
				ports++;
			}
		}
		return ports;
	}

	int cells_touched() const { return GetSize(plans); }
	int steps_used() const { return steps; }
};

// Arithmetic operators, whose per-port widths are independent parameters so a port can be
// narrowed on its own, and whose cost grows with operand width -- which is the point of
// the pass. Mux-like cells share one WIDTH across A, B and Y and so are never narrowed.
//
// $neg earns its place for the same reason the binary operators do: a sign mux over a
// magnitude lowers to a negate at the full declared width, so datapath code pays that
// width once per lane even when the products themselves are written narrowly.
//
// Comparisons are deliberately not in the default set even though the analysis handles
// them. A compare's width is also read by the pattern matchers that run later: opt_maxcmp
// fingerprints a compare cone by packing the threshold operand at the *value lane* width
// and asserts if the two disagree, and the argmax / prefix matchers fingerprint compare
// widths directly. Narrowing compares upstream of those costs more in lost rewrites than
// the operand bits are worth, so it has to be asked for explicitly with -types.
static pool<IdString> default_narrow_types()
{
	return { ID($add), ID($sub), ID($mul), ID($neg) };
}

struct OptSignifPass : public Pass {
	OptSignifPass() : Pass("opt_signif", "narrow operands to their significant width") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_signif [options] [selection]\n");
		log("\n");
		log("This pass narrows arithmetic operand ports whose upper bits are provably\n");
		log("sign (or zero) extension, using a forward value-range analysis over the\n");
		log("word-level operator graph.\n");
		log("\n");
		log("'wreduce' already strips a sign-extension prefix, but it decides how many\n");
		log("bits to strip by comparing the top two bits of a port for *net identity*\n");
		log("after sigmap. That only fires when the redundant bits are literally the\n");
		log("same net. It cannot see the common datapath idiom\n");
		log("\n");
		log("    wire signed [127:0] wa = s ? -$signed({1'b0, m}) : $signed({1'b0, m});\n");
		log("\n");
		log("where m is 4 bits wide. Here bits 5..127 of wa are all functionally the\n");
		log("sign bit, but each is a distinct $mux output bit fed by a distinct $neg\n");
		log("output bit, so no two of them are the same net and the following $mul keeps\n");
		log("128x128 operands instead of 5x5.\n");
		log("\n");
		log("The information needed is a *value range*, which is a word-level property:\n");
		log("a $neg of a 4-bit unsigned input can only produce values in [-15, 0], so\n");
		log("six signed bits suffice no matter how wide its Y word is declared. This\n");
		log("pass propagates such ranges forward and then rewrites each operand port to\n");
		log("its low 'need' bits, leaving the cell's own sign-extension semantics to\n");
		log("reproduce the discarded bits. Run 'wreduce' afterwards to shrink the Y\n");
		log("widths that the narrowed consumers no longer read.\n");
		log("\n");
		log("Range rules, by cell class:\n");
		log("\n");
		log("    constants                exact value\n");
		log("    constant-zero high bits  re-read as a narrower unsigned word\n");
		log("    $pos / $neg              [lo, hi] / [-hi, -lo]\n");
		log("    $add / $sub              [la+lb, ha+hb] / [la-hb, ha-lb]\n");
		log("    $mul                     min/max over the four corner products\n");
		log("    $and                     [0, min(ha, hb)]      (non-negative operands)\n");
		log("    $or / $xor / $xnor        magnitude of the wider operand\n");
		log("    $shl / $sshl             scaled by the largest possible shift\n");
		log("    $shr / $sshr             bounded by the operand range\n");
		log("    compares / reductions    [0, 1]\n");
		log("    $mux / $pmux             union over the arms\n");
		log("    flip-flops               with -cross-flops only: union of D, async\n");
		log("                             load, reset and init values\n");
		log("    anything else            the declared width (no narrowing)\n");
		log("\n");
		log("Everything the analysis cannot interpret -- module inputs, flip-flop outputs\n");
		log("without -cross-flops, bit-level logic, undefined bits, per-bit set/reset, and\n");
		log("any range that overflows the 128-bit interval arithmetic -- degrades to the\n");
		log("declared width, so the pass can only ever narrow a port and never widens one.\n");
		log("Feedback loops (an accumulator that genuinely grows) are broken by returning\n");
		log("the declared width for the cell being revisited, which is why a\n");
		log("self-accumulating register is left alone.\n");
		log("\n");
		log("    -cross-flops\n");
		log("        carry ranges across registers, including registers that have been\n");
		log("        blasted to one-bit cells, whose data inputs are reassembled into a\n");
		log("        word. Only bits captured on the same event are combined: skewed bits\n");
		log("        could pair a negative high bit with a positive low word, which no\n");
		log("        single reachable value of the data word allows.\n");
		log("\n");
		log("        This matters because a pipelined datapath puts a register in front of\n");
		log("        every accumulate tree, and stopping there leaves each adder priced at\n");
		log("        the declared accumulator width -- which real synthesis charges\n");
		log("        nothing for, since those upper bits are all copies of the sign.\n");
		log("\n");
		log("        A reset or init value is a value the register can hold, so it is\n");
		log("        unioned in; an all-undefined init is the absence of one and is\n");
		log("        ignored, which is where the assumption below lives.\n");
		log("\n");
		log("        NOT equivalence-preserving from an arbitrary power-up state: a\n");
		log("        register that has never been written can hold a value outside the\n");
		log("        range its data input can produce, and the narrowed operand reads only\n");
		log("        the low bits of it. The rule assumes every register is reset or\n");
		log("        loaded before its value is used, so keep it off where the power-up\n");
		log("        state is observable.\n");
		log("\n");
		log("    -types <type1>,<type2>,...\n");
		log("        Only narrow ports of these cell types. Defaults to\n");
		log("        $add,$sub,$mul,$neg: operators whose per-port widths are independent\n");
		log("        parameters and whose cost grows with operand width. $mux and $pmux\n");
		log("        share a single WIDTH across A, B and Y and so are never narrowed,\n");
		log("        though the analysis still traverses them.\n");
		log("\n");
		log("        $lt/$le/$gt/$ge/$eq/$ne are supported but off by default, because a\n");
		log("        compare's operand width is also read by the pattern matchers that\n");
		log("        run later (opt_maxcmp packs the threshold at the value-lane width\n");
		log("        and asserts if they disagree; the argmax and prefix matchers\n");
		log("        fingerprint compare widths). When narrowing is asked for on those\n");
		log("        types, both operands are always taken to the same width.\n");
		log("\n");
		log("    -max_steps <n>\n");
		log("        Budget on range evaluations per module (default 100000). Reaching\n");
		log("        it degrades the remaining cells to their declared widths.\n");
		log("\n");
		log("    -max_depth <n>\n");
		log("        Cap on driver-chain recursion depth (default 1000). A chain longer\n");
		log("        than this degrades to declared widths rather than risking a native\n");
		log("        stack overflow. Real datapaths are far shallower; only unbalanced\n");
		log("        reduction chains get close.\n");
		log("\n");
		log("    -max_iters <n>\n");
		log("        Cap on fixed-point iterations per module (default 4). Narrowing a\n");
		log("        cell tightens what its consumers see, so chains need more than one\n");
		log("        sweep. Iteration stops as soon as a sweep changes nothing, so a\n");
		log("        design with no candidates costs exactly one analysis pass.\n");
		log("\n");
		log("Runtime is linear in the total port width of the module: the driver index\n");
		log("is built once, each cell's range is memoized on first use, and no candidate\n");
		log("rescans the cell list.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_SIGNIF pass (narrow operands to significant width).\n");

		int max_steps = 100000;
		int max_iters = 4;
		int max_depth = 1000;
		bool cross_flops = false;
		pool<IdString> narrow_types = default_narrow_types();

		size_t argidx = 1;
		for (; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max_steps" && argidx + 1 < args.size()) {
				max_steps = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max_depth" && argidx + 1 < args.size()) {
				max_depth = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max_iters" && argidx + 1 < args.size()) {
				max_iters = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-types" && argidx + 1 < args.size()) {
				narrow_types.clear();
				for (auto &name : split_tokens(args[++argidx], ","))
					narrow_types.insert(RTLIL::escape_id(name));
				continue;
			}
			if (args[argidx] == "-cross-flops") {
				cross_flops = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_ports = 0, total_cells = 0, total_steps = 0;
		for (auto module : design->selected_modules()) {
			// Narrowing one cell tightens the ranges its consumers see, and flipping a
			// cell to signed only becomes visible to the analysis once applied, so
			// iterate. Widths only ever shrink, so this terminates; an iteration that
			// changes nothing is the fixed point and costs one analysis pass.
			int ports = 0, cells = 0;
			for (int iter = 0; iter < max_iters; iter++) {
				SignifWorker worker(module, max_steps, max_depth, narrow_types,
						cross_flops);
				int found = worker.run();
				total_steps += worker.steps_used();
				if (found == 0)
					break;
				ports += found;
				cells += worker.cells_touched();
			}
			total_ports += ports;
			total_cells += cells;
			if (ports)
				log("Narrowed %d operand port%s on %d cell%s in module %s.\n",
					ports, ports == 1 ? "" : "s", cells, cells == 1 ? "" : "s",
					log_id(module));
		}

		if (total_ports)
			design->scratchpad_set_bool("opt.did_something", true);
		// Range evaluations are a machine-independent stand-in for the pass's cost, which
		// wall-clock on a shared machine is not.
		design->scratchpad_set_int("opt_signif.steps", total_steps);
		log("Narrowed %d operand port%s on %d cell%s total.\n",
			total_ports, total_ports == 1 ? "" : "s",
			total_cells, total_cells == 1 ? "" : "s");
	}
} OptSignifPass;

PRIVATE_NAMESPACE_END
