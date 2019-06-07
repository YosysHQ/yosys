/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                      Eddie Hung <eddie@fpgeh.com>
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

#ifndef ABC_AIGERPARSE
#define ABC_AIGERPARSE

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct AigerReader
{
    RTLIL::Design *design;
    std::istream &f;
    RTLIL::IdString clk_name;
    RTLIL::Module *module;

    unsigned M, I, L, O, A;
    unsigned B, C, J, F; // Optional in AIGER 1.9
    unsigned line_count;

    std::vector<RTLIL::Wire*> inputs;
    std::vector<RTLIL::Wire*> latches;
    std::vector<RTLIL::Wire*> outputs;
    std::vector<RTLIL::Wire*> bad_properties;

    AigerReader(RTLIL::Design *design, std::istream &f, RTLIL::IdString module_name, RTLIL::IdString clk_name);
    void parse_aiger();
    void parse_aiger_ascii();
    void parse_aiger_binary();
};

YOSYS_NAMESPACE_END

#endif
