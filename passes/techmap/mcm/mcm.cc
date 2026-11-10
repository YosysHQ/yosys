/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Nick Allison <nick@yosyshq.com>
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

#include "mcm.h"

#include <algorithm>
#include <tuple>
#include <utility>



namespace Yosys::Mcm {

UnsignedContainer::UnsignedContainer(const BigUnsigned &integer) : value(uint64_t(0))
{
	if (integer.bitLength() <= 64) {
		value = integer.toUnsignedLong();
	} else {
		value = integer;
	}
}

BigUnsigned UnsignedContainer::to_big_unsigned() const
{
	if (auto small_value = get_uint64_t())
		// static cast needed for MacOS
		return BigUnsigned(static_cast<unsigned long>(*small_value));
	return get<BigUnsigned>();
}

int max_bit_width(const IntSet &int_set) {
	int max_width = 0;
	for (const auto &n : int_set)
		max_width = std::max(max_width, bit_width(n));
	return max_width;
}

AdderGraph::AdderGraph() {
	ops.insert(std::pair<UnsignedContainer, AOp>(1, ONE));
}

} // namespace Yosys::Mcm
