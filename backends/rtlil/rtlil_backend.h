/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
 *  ---
 *
 *  A very simple and straightforward backend for the RTLIL text
 *  representation.
 *
 */

#ifndef RTLIL_BACKEND_H
#define RTLIL_BACKEND_H

#include "kernel/yosys.h"
#include <stdio.h>

YOSYS_NAMESPACE_BEGIN

namespace RTLIL_BACKEND {
	// How names are rendered in the RTLIL text representation:
	//   Replayable - twine handles ($pub@N) + a `twines` pool section +
	//                `# name` comments. The default; perfectly replayable.
	//   Readable   - real escaped names inline, no pool section, no comments.
	//                Matches the historic RTLIL look. Lossy: breaks replay.
	//   Small      - like Replayable but omits the `# name` comments.
	enum class DumpMode { Replayable, Readable, Small };

	void dump_attributes(std::ostream &f, std::string indent, const RTLIL::AttrObject *obj, const RTLIL::Design *design = nullptr, DumpMode mode = DumpMode::Replayable);

	void dump_twines(std::ostream &f, const RTLIL::Design *design);
	void dump_const(std::ostream &f, const RTLIL::Const &data, int width = -1, int offset = 0, bool autoint = true);
	void dump_sigchunk(std::ostream &f, const RTLIL::SigChunk &chunk, bool autoint = true, DumpMode mode = DumpMode::Replayable);
	void dump_sigspec(std::ostream &f, const RTLIL::SigSpec &sig, bool autoint = true, DumpMode mode = DumpMode::Replayable);
	void dump_wire(std::ostream &f, std::string indent, const RTLIL::Wire *wire, const RTLIL::Design *design = nullptr, DumpMode mode = DumpMode::Replayable);
	void dump_memory(std::ostream &f, std::string indent, const RTLIL::Memory *memory, const RTLIL::Design *design = nullptr, DumpMode mode = DumpMode::Replayable);
	void dump_cell(std::ostream &f, std::string indent, const RTLIL::Cell *cell, const RTLIL::Design *design = nullptr, DumpMode mode = DumpMode::Replayable);
	void dump_proc_case_body(std::ostream &f, std::string indent, const RTLIL::CaseRule *cs, const RTLIL::Design *design = nullptr, DumpMode mode = DumpMode::Replayable);
	void dump_proc_switch(std::ostream &f, std::string indent, const RTLIL::SwitchRule *sw, const RTLIL::Design *design = nullptr, DumpMode mode = DumpMode::Replayable);
	void dump_proc_sync(std::ostream &f, std::string indent, const RTLIL::SyncRule *sy, const RTLIL::Design *design = nullptr, DumpMode mode = DumpMode::Replayable);
	void dump_proc(std::ostream &f, std::string indent, const RTLIL::Process *proc, const RTLIL::Design *design = nullptr, DumpMode mode = DumpMode::Replayable);
	void dump_conn(std::ostream &f, std::string indent, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right, DumpMode mode = DumpMode::Replayable);
	void dump_module(std::ostream &f, std::string indent, RTLIL::Module *module, RTLIL::Design *design, bool only_selected, bool flag_m = true, bool flag_n = false, DumpMode mode = DumpMode::Replayable);
	void dump_design(std::ostream &f, RTLIL::Design *design, bool only_selected, bool flag_m = true, bool flag_n = false, DumpMode mode = DumpMode::Replayable);
}

YOSYS_NAMESPACE_END

#endif
