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

YOSYS_NAMESPACE_BEGIN

struct MemRd {
	dict<IdString, Const> attributes;
	Cell *cell;
	bool clk_enable, clk_polarity;
	bool transparent;
	SigSpec clk, en, addr, data;
	MemRd() : cell(nullptr) {}
};

struct MemWr {
	dict<IdString, Const> attributes;
	Cell *cell;
	bool clk_enable, clk_polarity;
	SigSpec clk, en, addr, data;
	MemWr() : cell(nullptr) {}
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
	void remove_wr_port(int idx);
	void remove_rd_port(int idx);
	void clear_inits();
	Const get_init_data() const;
	static std::vector<Mem> get_all_memories(Module *module);
	static std::vector<Mem> get_selected_memories(Module *module);
	Cell *extract_rdff(int idx);
	Mem(Module *module, IdString memid, int width, int start_offset, int size) : module(module), memid(memid), packed(false), mem(nullptr), cell(nullptr), width(width), start_offset(start_offset), size(size) {}
};

YOSYS_NAMESPACE_END

#endif
