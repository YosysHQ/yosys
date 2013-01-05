/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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
 *  representation (as understood by the 'ilang' frontend).
 *
 */

#ifndef ILANG_BACKEND_H
#define ILANG_BACKEND_H

#include "kernel/rtlil.h"
#include <stdio.h>

namespace ILANG_BACKEND {
	void dump_const(FILE *f, const RTLIL::Const &data, int width = -1, int offset = 0, bool autoint = true);
	void dump_sigchunk(FILE *f, const RTLIL::SigChunk &chunk, bool autoint = true);
	void dump_sigspec(FILE *f, const RTLIL::SigSpec &sig, bool autoint = true);
	void dump_wire(FILE *f, std::string indent, const RTLIL::Wire *wire);
	void dump_memory(FILE *f, std::string indent, const RTLIL::Memory *memory);
	void dump_cell(FILE *f, std::string indent, const RTLIL::Cell *cell);
	void dump_proc_case_body(FILE *f, std::string indent, const RTLIL::CaseRule *cs);
	void dump_proc_switch(FILE *f, std::string indent, const RTLIL::SwitchRule *sw);
	void dump_proc_sync(FILE *f, std::string indent, const RTLIL::SyncRule *sy);
	void dump_proc(FILE *f, std::string indent, const RTLIL::Process *proc);
	void dump_conn(FILE *f, std::string indent, const RTLIL::SigSpec &left, const RTLIL::SigSpec &right);
	void dump_module(FILE *f, std::string indent, const RTLIL::Module *module);
	void dump_design(FILE *f, const RTLIL::Design *design);
}

#endif
