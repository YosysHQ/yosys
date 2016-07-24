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

#include "kernel/celledges.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void add_bitwise_unary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	IdString A = "\\A", Y = "\\Y";

	bool is_signed = cell->getParam("\\A_SIGNED").as_bool();
	int a_width = GetSize(cell->getPort(A));
	int y_width = GetSize(cell->getPort(Y));

	for (int i = 0; i < y_width; i++)
	{
		if (i < a_width)
			db->add_edge(cell, A, i, Y, i);
		else if (is_signed && a_width > 0)
			db->add_edge(cell, A, a_width-1, Y, i);
	}
}

void add_bitwise_binary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	IdString A = "\\A", B = "\\B", Y = "\\Y";

	bool is_signed = cell->getParam("\\A_SIGNED").as_bool();
	int a_width = GetSize(cell->getPort(A));
	int b_width = GetSize(cell->getPort(B));
	int y_width = GetSize(cell->getPort(Y));

	if (cell->type == "$and" && !is_signed) {
		if (a_width > b_width)
			a_width = b_width;
		else
			b_width = a_width;
	}

	for (int i = 0; i < y_width; i++)
	{
		if (i < a_width)
			db->add_edge(cell, A, i, Y, i);
		else if (is_signed && a_width > 0)
			db->add_edge(cell, A, a_width-1, Y, i);

		if (i < b_width)
			db->add_edge(cell, B, i, Y, i);
		else if (is_signed && b_width > 0)
			db->add_edge(cell, B, b_width-1, Y, i);
	}
}

PRIVATE_NAMESPACE_END

bool YOSYS_NAMESPACE_PREFIX AbstractCellEdgesDatabase::add_cell(RTLIL::Cell *cell)
{
	if (cell->type.in("$not", "$pos")) {
		add_bitwise_unary_op(this, cell);
		return true;
	}

	if (cell->type.in("$and", "$or", "$xor", "$xnor")) {
		add_bitwise_binary_op(this, cell);
		return true;
	}

	return false;
}

