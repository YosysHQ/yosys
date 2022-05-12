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

#ifndef MEM_H
#define MEM_H

#include "kernel/yosys.h"
#include "kernel/ffinit.h"

YOSYS_NAMESPACE_BEGIN

struct MemRd : RTLIL::AttrObject {
	bool removed;
	Cell *cell;
	int wide_log2;
	bool clk_enable, clk_polarity, ce_over_srst;
	Const arst_value, srst_value, init_value;
	// One bit for every write port, true iff simultanous read on this
	// port and write on the other port will bypass the written data
	// to this port's output (default behavior is to read old value).
	// Can only be set for write ports that have the same clock domain.
	std::vector<bool> transparency_mask;
	// One bit for every write port, true iff simultanous read on this
	// port and write on the other port will return an all-X (don't care)
	// value.  Mutually exclusive with transparency_mask.
	// Can only be set for write ports that have the same clock domain.
	// For optimization purposes, this will also be set if we can
	// determine that the two ports can never be active simultanously
	// (making the above vacuously true).
	std::vector<bool> collision_x_mask;
	SigSpec clk, en, arst, srst, addr, data;

	MemRd() : removed(false), cell(nullptr), wide_log2(0), clk_enable(false), clk_polarity(true), ce_over_srst(false), clk(State::Sx), en(State::S1), arst(State::S0), srst(State::S0) {}

	// Returns the address of given subword index accessed by this port.
	SigSpec sub_addr(int sub) {
		SigSpec res = addr;
		for (int i = 0; i < wide_log2; i++)
			res[i] = State(sub >> i & 1);
		return res;
	}
};

struct MemWr : RTLIL::AttrObject {
	bool removed;
	Cell *cell;
	int wide_log2;
	bool clk_enable, clk_polarity;
	std::vector<bool> priority_mask;
	SigSpec clk, en, addr, data;

	MemWr() : removed(false), cell(nullptr) {}

	// Returns the address of given subword index accessed by this port.
	SigSpec sub_addr(int sub) {
		SigSpec res = addr;
		for (int i = 0; i < wide_log2; i++)
			res[i] = State(sub >> i & 1);
		return res;
	}

	std::pair<SigSpec, std::vector<int>> compress_en();
	SigSpec decompress_en(const std::vector<int> &swizzle, SigSpec sig);
};

struct MemInit : RTLIL::AttrObject {
	bool removed;
	Cell *cell;
	Const addr;
	Const data;
	Const en;
	MemInit() : removed(false), cell(nullptr) {}
};

struct Mem : RTLIL::AttrObject {
	Module *module;
	IdString memid;
	bool packed;
	RTLIL::Memory *mem;
	Cell *cell;
	int width, start_offset, size;
	std::vector<MemInit> inits;
	std::vector<MemRd> rd_ports;
	std::vector<MemWr> wr_ports;

	// Removes this memory from the module.  The data in helper structures
	// is unaffected except for the cell/mem fields.
	void remove();

	// Commits all changes in helper structures into the module — ports and
	// inits marked as removed are actually removed, new ports/inits create
	// new cells, modified port/inits are commited into their existing
	// cells.  Note that this reindexes the ports and inits array (actually
	// removing the ports/inits marked as removed).
	void emit();

	// Marks all inits as removed.
	void clear_inits();

	// Coalesces inits: whenever two inits have overlapping or touching
	// address ranges, they are combined into one, with the higher-priority
	// one's data overwriting the other.  Running this results in
	// an inits list equivalent to the original, in which all entries
	// cover disjoint (and non-touching) address ranges, and all enable
	// masks are all-1.
	void coalesce_inits();

	// Checks consistency of this memory and all its ports/inits, using
	// log_assert.
	void check();

	// Gathers all initialization data into a single big const covering
	// the whole memory.  For all non-initialized bits, Sx will be returned.
	Const get_init_data() const;

	// Constructs and returns the helper structures for all memories
	// in a module.
	static std::vector<Mem> get_all_memories(Module *module);

	// Constructs and returns the helper structures for all selected
	// memories in a module.
	static std::vector<Mem> get_selected_memories(Module *module);

	// Converts a synchronous read port into an asynchronous one by
	// extracting the data (or, in some rare cases, address) register
	// into a separate cell, together with any soft-transparency
	// logic necessary to preserve its semantics.  Returns the created
	// register cell, if any.  Note that in some rare cases this function
	// may succeed and perform a conversion without creating a new
	// register — a nullptr result doesn't imply nothing was done.
	Cell *extract_rdff(int idx, FfInitVals *initvals);

	// Splits all wide ports in this memory into equivalent narrow ones.
	// This function performs no modifications at all to the actual
	// netlist unless and until emit() is called.
	void narrow();

	// If write port idx2 currently has priority over write port idx1,
	// inserts extra logic on idx1's enable signal to disable writes
	// when idx2 is writing to the same address, then removes the priority
	// from the priority mask.  If there is a memory port that is
	// transparent with idx1, but not with idx2, that port is converted
	// to use soft transparency logic.
	void emulate_priority(int idx1, int idx2, FfInitVals *initvals);

	// Creates soft-transparency logic on read port ridx, bypassing the
	// data from write port widx.  Should only be called when ridx is
	// transparent wrt widx in the first place.  Once we're done, the
	// transparency_mask bit will be cleared, and the collision_x_mask
	// bit will be set instead (since whatever value is read will be
	// replaced by the soft transparency logic).
	void emulate_transparency(int widx, int ridx, FfInitVals *initvals);

	// Prepares for merging write port idx2 into idx1 (where idx1 < idx2).
	// Specifically, takes care of priority masks: any priority relations
	// that idx2 had are replicated onto idx1, unless they conflict with
	// priorities already present on idx1, in which case emulate_priority
	// is called.  Likewise, ensures transparency and undefined collision
	// masks of all read ports have the same values for both ports,
	// calling emulate_transparency if necessary.
	void prepare_wr_merge(int idx1, int idx2, FfInitVals *initvals);

	// Prepares for merging read port idx2 into idx1.
	// Specifically, makes sure the transparency and undefined collision
	// masks of both ports are equal, by changing undefined behavior
	// of one port to the other's defined behavior, or by calling
	// emulate_transparency if necessary.
	void prepare_rd_merge(int idx1, int idx2, FfInitVals *initvals);

	// Prepares the memory for widening a port to a given width.  This
	// involves ensuring that start_offset and size are aligned to the
	// target width.
	void widen_prep(int wide_log2);

	// Widens a write port up to a given width.  The newly port is
	// equivalent to the original, made by replicating enable/data bits
	// and masking enable bits with decoders on the low part of the
	// original address.
	void widen_wr_port(int idx, int wide_log2);

	// Emulates a sync read port's enable functionality in soft logic,
	// changing the actual read port's enable to be always-on.
	void emulate_rden(int idx, FfInitVals *initvals);

	// Emulates a sync read port's initial/reset value functionality in
	// soft logic, removing it from the actual read port.
	void emulate_reset(int idx, bool emu_init, bool emu_arst, bool emu_srst, FfInitVals *initvals);

	// Given a read port with ce_over_srst set, converts it to a port
	// with ce_over_srst unset without changing its behavior by adding
	// emulation logic.
	void emulate_rd_ce_over_srst(int idx);

	// Given a read port with ce_over_srst unset, converts it to a port
	// with ce_over_srst set without changing its behavior by adding
	// emulation logic.
	void emulate_rd_srst_over_ce(int idx);

	// Returns true iff emulate_read_first makes sense to call.
	bool emulate_read_first_ok();

	// Emulates all read-first read-write port relationships in terms of
	// all-transparent ports, by delaying all write ports by one cycle.
	// This can only be used when all read ports and all write ports are
	// in the same clock domain.
	void emulate_read_first(FfInitVals *initvals);

	Mem(Module *module, IdString memid, int width, int start_offset, int size) : module(module), memid(memid), packed(false), mem(nullptr), cell(nullptr), width(width), start_offset(start_offset), size(size) {}
};

YOSYS_NAMESPACE_END

#endif
