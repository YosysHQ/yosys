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
 */

#ifndef CELLAIGS_H
#define CELLAIGS_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct AigNode
{
	IdString portname;
	int portbit;
	bool inverter;
	int left_parent, right_parent;
	vector<pair<IdString, int>> outports;

	AigNode();
	bool operator==(const AigNode &other) const;
	[[nodiscard]] Hasher hash_into(Hasher h) const;
};

struct Aig
{
	string name;
	vector<AigNode> nodes;
	Aig(Cell *cell);

	bool operator==(const Aig &other) const;
	[[nodiscard]] Hasher hash_into(Hasher h) const;
};

YOSYS_NAMESPACE_END

#endif
