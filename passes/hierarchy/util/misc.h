/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2018  Ruben Undheim <ruben.undheim@gmail.com>
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

#ifndef HIERARCHY_MISC_H
#define HIERARCHY_MISC_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace Hierarchy {
    struct ArrayType {
        std::string name;
        int pos_idx;
        int pos_num;
        int pos_type;
    };
    std::optional<ArrayType> try_make_array(const std::string celltype);

    // Try to read an IdString as a numbered connection name ("$123" or similar),
    // writing the result to dst. If the string isn't of the right format, ignore
    // dst and return false.
    bool read_id_num(RTLIL::IdString str, int *dst);

    void set_keeps(Design* design, bool keep_prints, bool keep_asserts);
    bool set_keep_print(std::map<RTLIL::Module*, bool> &cache, RTLIL::Module *mod);
    bool set_keep_assert(std::map<RTLIL::Module*, bool> &cache, RTLIL::Module *mod);
};

YOSYS_NAMESPACE_END

#endif /* HIERARCHY_MISC_H */
