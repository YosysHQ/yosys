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

#ifndef MEMLIB_H
#define MEMLIB_H

#include <string>
#include <vector>

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace MemLibrary {

enum class RamKind {
	Auto,
	Logic,
	NotLogic,
	Distributed,
	Block,
	Huge,
};

enum class WidthMode {
	Single,
	Global,
	PerPort,
};

enum class MemoryInitKind {
	None,
	Zero,
	Any,
	NoUndef,
};

enum class PortKind {
	Sr,
	Ar,
	Sw,
	Srsw,
	Arsw,
};

enum class ClkPolKind {
	Anyedge,
	Posedge,
	Negedge,
};

enum class RdWrKind {
	Undefined,
	NoChange,
	New,
	Old,
	NewOnly,
};

enum class ResetValKind {
	None,
	Zero,
	Any,
	NoUndef,
	Init,
};

enum class SrstKind {
	None,
	Ungated,
	GatedClkEn,
	GatedRdEn,
};

enum class WrTransTargetKind {
	All,
	Group,
};

enum class WrTransKind {
	New,
	Old,
};

struct WrTransDef {
	WrTransTargetKind target_kind;
	int target_group;
	WrTransKind kind;
};

struct PortVariant {
	dict<std::string, Const> options;
	PortKind kind;
	int clk_shared;
	ClkPolKind clk_pol;
	bool clk_en;
	bool width_tied;
	int min_wr_wide_log2;
	int max_wr_wide_log2;
	int min_rd_wide_log2;
	int max_rd_wide_log2;
	bool rd_en;
	RdWrKind rdwr;
	ResetValKind rdinitval;
	ResetValKind rdarstval;
	ResetValKind rdsrstval;
	SrstKind rdsrstmode;
	bool rdsrst_block_wr;
	bool wrbe_separate;
	std::vector<int> wrprio;
	std::vector<WrTransDef> wrtrans;
};

struct PortGroup {
	bool optional;
	bool optional_rw;
	std::vector<std::string> names;
	std::vector<PortVariant> variants;
};

struct RamClock {
	std::string name;
	bool anyedge;
};

struct Ram {
	IdString id;
	RamKind kind;
	dict<std::string, Const> options;
	std::vector<PortGroup> port_groups;
	bool prune_rom;
	int abits;
	std::vector<int> dbits;
	WidthMode width_mode;
	std::string resource_name;
	int resource_count;
	double cost;
	double widthscale;
	int byte;
	MemoryInitKind init;
	std::vector<std::string> style;
	std::vector<RamClock> shared_clocks;
};

struct Library {
	std::vector<Ram> rams;
};

Library parse_library(const std::vector<std::string> &filenames, const pool<std::string> &defines);

}

YOSYS_NAMESPACE_END

#endif
