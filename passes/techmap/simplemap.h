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
 */

#ifndef SIMPLEMAP_H
#define SIMPLEMAP_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

extern void simplemap_not(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_pos(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_bitop(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_reduce(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_lognot(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_logbin(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_mux(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_lut(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_slice(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_concat(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_sr(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_dff(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_dffe(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_dffsr(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_adff(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap_dlatch(RTLIL::Module *module, RTLIL::Cell *cell);
extern void simplemap(RTLIL::Module *module, RTLIL::Cell *cell);

extern void simplemap_get_mappers(std::map<RTLIL::IdString, void(*)(RTLIL::Module*, RTLIL::Cell*)> &mappers);

YOSYS_NAMESPACE_END

#endif
