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

struct MemRd {
	bool removed;
	dict<IdString, Const> attributes;
	Cell *cell;
	int wide_log2;
	bool clk_enable, clk_polarity, ce_over_srst;
	Const arst_value, srst_value, init_value;
	bool transparent;
	SigSpec clk, en, arst, srst, addr, data;
	MemRd() : removed(false), cell(nullptr) {}
};

struct MemWr {
	bool removed;
	dict<IdString, Const> attributes;
	Cell *cell;
	int wide_log2;
	bool clk_enable, clk_polarity;
	std::vector<bool> priority_mask;
	SigSpec clk, en, addr, data;
	MemWr() : removed(false), cell(nullptr) {}
};

struct MemInit {
	dict<IdString, Const> attributes;
	Cell *cell;
	Const addr;
	Const data;
	MemInit() : cell(nullptr) {}
};

struct Mem {
	Module *module;
	IdString memid;
	dict<IdString, Const> attributes;
	bool packed;
	RTLIL::Memory *mem;
	Cell *cell;
	int width, start_offset, size;
	std::vector<MemInit> inits;
	std::vector<MemRd> rd_ports;
	std::vector<MemWr> wr_ports;

	void remove();
	void emit();
	void clear_inits();
	void check();
	Const get_init_data() const;
	static std::vector<Mem> get_all_memories(Module *module);
	static std::vector<Mem> get_selected_memories(Module *module);
	Cell *extract_rdff(int idx, FfInitVals *initvals);
	void narrow();

	// If write port idx2 currently has priority over write port idx1,
	// inserts extra logic on idx1's enable signal to disable writes
	// when idx2 is writing to the same address, then removes the priority
	// from the priority mask.
	void emulate_priority(int idx1, int idx2);

	// Prepares for merging write port idx2 into idx1 (where idx1 < idx2).
	// Specifically, takes care of priority masks: any priority relations
	// that idx2 had are replicated onto idx1, unless they conflict with
	// priorities already present on idx1, in which case emulate_priority
	// is called.
	void prepare_wr_merge(int idx1, int idx2);

	// Prepares the memory for widening a port to a given width.  This
	// involves ensuring that start_offset and size are aligned to the
	// target width.
	void widen_prep(int wide_log2);

	// Widens a write port up to a given width.  The newly port is
	// equivalent to the original, made by replicating enable/data bits
	// and masking enable bits with decoders on the low part of the
	// original address.
	void widen_wr_port(int idx, int wide_log2);

	Mem(Module *module, IdString memid, int width, int start_offset, int size) : module(module), memid(memid), packed(false), mem(nullptr), cell(nullptr), width(width), start_offset(start_offset), size(size) {}
};

YOSYS_NAMESPACE_END

#endif
