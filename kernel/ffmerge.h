/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Marcelina Kościelnicka <mwk@0x04.net>
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

#ifndef FFMERGE_H
#define FFMERGE_H

#include "kernel/ffinit.h"
#include "kernel/ff.h"

YOSYS_NAMESPACE_BEGIN

// A helper class for passes that want to merge FFs on the input or output
// of a cell into the cell itself.
//
// The procedure is:
//
// 1. Construct this class (at beginning of processing for a given module).
// 2. For every considered cell:
//
//    a. Call find_output_ff for every considered output.
//    b. Call find_input_ff for every considered input.
//    c. Look at the FF description returned (if any) from each call, reject
//       results that cannot be merged into given cell for any reason.
//       If both inputs and outputs are being merged, take care of FF bits that
//       are returned in both input and output results (a FF bit cannot be
//       merged to both).  Decide on the final set of FF bits to merge.
//    d. Call remove_output_ff for every find_output_ff result that will be used
//       for merging.  This removes the actual FF bits from design and from index.
//    e. Call mark_input_ff for every find_input_ff result that will be used
//       for merging.  This updates the index disallowing further usage of these
//       FF bits for output FF merging, if they were eligible before.  The actual
//       FF bits are still left in the design and can be merged into other inputs.
//       If the FF bits are not otherwise used, they will be removed by later
//       opt passes.
//    f. Merge the FFs into the cell.
//
// Note that, if both inputs and outputs are being considered for merging in
// a single pass, the result may be nondeterministic (depending on cell iteration
// order) because a given FF bit could be eligible for both input and output merge,
// perhaps in different cells.  For this reason, it may be a good idea to separate
// input and output merging.

struct FfMergeHelper
{
	const SigMap *sigmap;
	RTLIL::Module *module;
	FfInitVals *initvals;

	dict<SigBit, std::pair<Cell*, int>> dff_driver;
	dict<SigBit, pool<std::pair<Cell*, int>>> dff_sink;
	dict<SigBit, int> sigbit_users_count;

	// Returns true if all bits in sig are completely unused.
	bool is_output_unused(RTLIL::SigSpec sig);

	// Finds the FF to merge into a given cell output.  Takes sig, which
	// is the current cell output — it will be the sig_d of the found FF.
	// If found, returns true, and fills the two output arguments.
	//
	// For every bit of sig, this function finds a FF bit that has
	// the same sig_d, and fills the output FfData according to the FF
	// bits found.  This function will only consider FF bits that are
	// the only user of the given sig bits — if any bit in sig is used
	// by anything other than a single FF, this function will return false.
	//
	// The returned FfData structure does not correspond to any actual FF
	// cell in the design — it is the amalgamation of extracted FF bits,
	// possibly coming from several FF cells.
	//
	// If some of the bits in sig have no users at all, this function
	// will accept them as well (and fill returned FfData with dummy values
	// for the given bit, effectively synthesizing an unused FF bit of the
	// appropriate type).  However, if all bits in sig are completely
	// unused, this function will fail and return false (having no idea
	// what kind of FF to produce) — use the above helper if that case
	// is important to handle.
	//
	// Note that this function does not remove the FF bits returned from
	// the design — this is so that the caller can decide whether to accept
	// this FF for merging or not.  If the result is accepted,
	// remove_output_ff should be called on the second output argument.
	bool find_output_ff(RTLIL::SigSpec sig, FfData &ff, pool<std::pair<Cell *, int>> &bits);

	// Like above, but returns a FF to merge into a given cell input.  Takes
	// sig_q, which is the current cell input — it will search for FFs with
	// matching sig_q.
	//
	// As opposed to find_output_ff, this function doesn't care about usage
	// counts, and may return FF bits that also have other fanout.  This
	// should not be a problem for input FF merging.
	//
	// As a special case, if some of the bits in sig_q are constant, this
	// function will accept them as well, by synthesizing in-place
	// a constant-input FF bit (with matching initial value and reset value).
	// However, this will not work if the input is all-constant — if the caller
	// cares about this case, it needs to check for it explicitely.
	bool find_input_ff(RTLIL::SigSpec sig, FfData &ff, pool<std::pair<Cell *, int>> &bits);

	// To be called on find_output_ff result that will be merged.  This
	// marks the given FF bits as used up (and not to be considered for
	// further merging as inputs), and reconnects their Q ports to a dummy
	// wire (since the wire previously connected there will now be driven
	// by the merged-to cell instead).
	void remove_output_ff(const pool<std::pair<Cell *, int>> &bits);

	// To be called on find_input_ff result that will be merged.  This
	// marks the given FF bits as used, and disallows merging them as
	// outputs.  They can, however, still be merged as inputs again
	// (perhaps for another cell).
	void mark_input_ff(const pool<std::pair<Cell *, int>> &bits);

	void set(FfInitVals *initvals_, RTLIL::Module *module_);

	void clear();

	FfMergeHelper(FfInitVals *initvals, RTLIL::Module *module) {
		set(initvals, module);
	}

	FfMergeHelper() {}
};

YOSYS_NAMESPACE_END

#endif
