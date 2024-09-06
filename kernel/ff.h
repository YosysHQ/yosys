/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Marcelina Kościelnicka <mwk@0x04.net>
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

#ifndef FF_H
#define FF_H

#include "kernel/yosys.h"
#include "kernel/ffinit.h"

YOSYS_NAMESPACE_BEGIN

// Describes a flip-flop or a latch.
//
// If has_gclk, this is a formal verification FF with implicit global clock:
// Q is simply previous cycle's D. Additionally if is_anyinit is true, this is
// an $anyinit cell which always has an undefined initialization value. Note
// that $anyinit is not considered to be among the FF celltypes, so a pass has
// to explicitly opt-in to process $anyinit cells with FfData.
//
// Otherwise, the FF/latch can have any number of features selected by has_*
// attributes that determine Q's value (in order of decreasing priority):
//
// - on start, register is initialized to val_init
// - if has_sr is present:
//   - sig_clr is per-bit async clear, and sets the corresponding bit to 0
//     if active
//   - sig_set is per-bit async set, and sets the corresponding bit to 1
//     if active
// - if has_arst is present:
//   - sig_arst is whole-reg async reset, and sets the whole register to val_arst
// - if has_aload is present:
//   - sig_aload is whole-reg async load (aka latch gate enable), and sets the whole
//     register to sig_ad
// - if has_clk is present, and we're currently on a clock edge:
//   - if has_ce is present and ce_over_srst is true:
//     - ignore clock edge (don't change value) unless sig_ce is active
//   - if has_srst is present:
//     - sig_srst is whole-reg sync reset and sets the register to val_srst
//   - if has_ce is present and ce_over_srst is false:
//     - ignore clock edge (don't change value) unless sig_ce is active
//   - set whole reg to sig_d
// - if nothing of the above applies, the reg value remains unchanged
//
// Since the yosys FF cell library isn't fully generic, not all combinations
// of the features above can be supported:
//
// - only one of has_srst, has_arst, has_sr can be used
// - if has_clk is used together with has_aload, then has_srst, has_arst,
//   has_sr cannot be used
//
// The valid feature combinations are thus:
//
// - has_clk + optional has_ce [dff/dffe]
// - has_clk + optional has_ce + has_arst [adff/adffe]
// - has_clk + optional has_ce + has_aload [aldff/aldffe]
// - has_clk + optional has_ce + has_sr [dffsr/dffsre]
// - has_clk + optional has_ce + has_srst [sdff/sdffe/sdffce]
// - has_aload [dlatch]
// - has_aload + has_arst [adlatch]
// - has_aload + has_sr [dlatchsr]
// - has_sr [sr]
// - has_arst [does not correspond to a native cell, represented as dlatch with const D input]
// - empty set [not a cell — will be emitted as a simple direct connection]

struct FfData {
	Module *module;
	FfInitVals *initvals;
	Cell *cell;
	IdString name;
	// The FF output.
	SigSpec sig_q;
	// The sync data input, present if has_clk or has_gclk.
	SigSpec sig_d;
	// The async data input, present if has_aload.
	SigSpec sig_ad;
	// The sync clock, present if has_clk.
	SigSpec sig_clk;
	// The clock enable, present if has_ce.
	SigSpec sig_ce;
	// The async load enable, present if has_aload.
	SigSpec sig_aload;
	// The async reset, preset if has_arst.
	SigSpec sig_arst;
	// The sync reset, preset if has_srst.
	SigSpec sig_srst;
	// The async clear (per-lane), present if has_sr.
	SigSpec sig_clr;
	// The async set (per-lane), present if has_sr.
	SigSpec sig_set;
	// True if this is a clocked (edge-sensitive) flip-flop.
	bool has_clk;
	// True if this is a $ff, exclusive with every other has_*.
	bool has_gclk;
	// True if this FF has a clock enable.  Depends on has_clk.
	bool has_ce;
	// True if this FF has async load function — this includes D latches.
	// If this and has_clk are both set, has_arst and has_sr cannot be set.
	bool has_aload;
	// True if this FF has sync set/reset.  Depends on has_clk, exclusive
	// with has_arst, has_sr, has_aload.
	bool has_srst;
	// True if this FF has async set/reset.  Exclusive with has_srst,
	// has_sr.  If this and has_clk are both set, has_aload cannot be set.
	bool has_arst;
	// True if this FF has per-bit async set + clear.  Exclusive with
	// has_srst, has_arst.  If this and has_clk are both set, has_aload
	// cannot be set.
	bool has_sr;
	// If has_ce and has_srst are both set, determines their relative
	// priorities: if true, inactive ce disables srst; if false, srst
	// operates independent of ce.
	bool ce_over_srst;
	// True if this FF is a fine cell, false if it is a coarse cell.
	// If true, width must be 1.
	bool is_fine;
	// True if this FF is an $anyinit cell.  Depends on has_gclk.
	bool is_anyinit;
	// Polarities, corresponding to sig_*.
	// True means rising edge, false means falling edge.
	bool pol_clk;
	// True means active-high, false
	// means active-low.
	bool pol_ce;
	bool pol_aload;
	bool pol_arst;
	bool pol_srst;
	bool pol_clr;
	bool pol_set;
	// The value loaded by sig_arst.
	Const val_arst;
	// The value loaded by sig_srst.
	Const val_srst;
	// The initial value at power-up.
	Const val_init;
	// The FF data width in bits.
	int width;
	dict<IdString, Const> attributes;

	FfData(Module *module = nullptr, FfInitVals *initvals = nullptr, IdString name = IdString()) : module(module), initvals(initvals), cell(nullptr), name(name) {
		width = 0;
		has_clk = false;
		has_gclk = false;
		has_ce = false;
		has_aload = false;
		has_srst = false;
		has_arst = false;
		has_sr = false;
		ce_over_srst = false;
		is_fine = false;
		is_anyinit = false;
		pol_clk = false;
		pol_aload = false;
		pol_ce = false;
		pol_arst = false;
		pol_srst = false;
		pol_clr = false;
		pol_set = false;
	}

	FfData(FfInitVals *initvals, Cell *cell_);

	// Returns a FF identical to this one, but only keeping bit indices from the argument.
	FfData slice(const std::vector<int> &bits);

	void add_dummy_ce();
	void add_dummy_srst();
	void add_dummy_arst();
	void add_dummy_aload();
	void add_dummy_sr();
	void add_dummy_clk();

	void arst_to_aload();
	void arst_to_sr();

	void aload_to_sr();

	// Given a FF with both has_ce and has_srst, sets ce_over_srst to the given value and
	// fixes up control signals appropriately to preserve semantics.
	void convert_ce_over_srst(bool val);

	void unmap_ce();
	void unmap_srst();

	void unmap_ce_srst() {
		unmap_ce();
		unmap_srst();
	}

	Cell *emit();

	// Removes init attribute from the Q output, but keeps val_init unchanged.
	// It will be automatically reattached on emit.  Use this before changing sig_q.
	void remove_init() {
		if (initvals)
			initvals->remove_init(sig_q);
	}

	void remove();

	// Flip the sense of the given bit slices of the FF: insert inverters on data
	// inputs and output, flip the corresponding init/reset bits, swap clr/set
	// inputs with proper priority fix.
	void flip_bits(const pool<int> &bits);

	void flip_rst_bits(const pool<int> &bits);
};

YOSYS_NAMESPACE_END

#endif
