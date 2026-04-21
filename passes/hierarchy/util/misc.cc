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

#include "kernel/yosys_common.h"
#include "passes/hierarchy/util/misc.h"

YOSYS_NAMESPACE_BEGIN

namespace Hierarchy {

std::optional<ArrayType> try_make_array(const std::string celltype) {
	if (celltype.compare(0, strlen("$array:"), "$array:") == 0) {
		int pos_idx = celltype.find_first_of(':');
		int pos_num = celltype.find_first_of(':', pos_idx + 1);
		int pos_type = celltype.find_first_of(':', pos_num + 1);
		return ArrayType {
			celltype.substr(pos_type + 1),
			pos_idx,
			pos_num,
			pos_type,
		};
	}
	return std::nullopt;
}

bool read_id_num(RTLIL::IdString str, int *dst) {
	log_assert(dst);

	const char *c_str = str.c_str();
	if (c_str[0] != '$' || !('0' <= c_str[1] && c_str[1] <= '9'))
		return false;

	*dst = atoi(c_str + 1);
	return true;
}

void set_keeps(Design* design, bool keep_prints, bool keep_asserts) {
	if (keep_prints) {
		std::map<RTLIL::Module*, bool> cache;
		for (auto mod : design->modules())
			if (set_keep_print(cache, mod)) {
				log("Module %s directly or indirectly displays text -> setting \"keep\" attribute.\n", log_id(mod));
				mod->set_bool_attribute(ID::keep);
			}
	}

	if (keep_asserts) {
		std::map<RTLIL::Module*, bool> cache;
		for (auto mod : design->modules())
			if (set_keep_assert(cache, mod)) {
				log("Module %s directly or indirectly contains formal properties -> setting \"keep\" attribute.\n", log_id(mod));
				mod->set_bool_attribute(ID::keep);
			}
	}
}

bool set_keep_print(std::map<RTLIL::Module*, bool> &cache, RTLIL::Module *mod) {
	if (cache.count(mod) == 0)
		for (auto c : mod->cells()) {
			RTLIL::Module *m = mod->design->module(c->type);
			if ((m != nullptr && set_keep_print(cache, m)) || c->type == ID($print))
				return cache[mod] = true;
		}
	return cache[mod];
}

bool set_keep_assert(std::map<RTLIL::Module*, bool> &cache, RTLIL::Module *mod) {
	if (cache.count(mod) == 0)
		for (auto c : mod->cells()) {
			RTLIL::Module *m = mod->design->module(c->type);
			if ((m != nullptr && set_keep_assert(cache, m)) || c->type.in(ID($check), ID($assert), ID($assume), ID($live), ID($fair), ID($cover)))
				return cache[mod] = true;
		}
	return cache[mod];
}

};
YOSYS_NAMESPACE_END
