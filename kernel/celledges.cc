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

void bitwise_unary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	IdString A = "\\A", Y = "\\Y";

	bool is_signed = cell->getParam("\\A_SIGNED").as_bool();
	int a_width = GetSize(cell->getPort(A));
	int y_width = GetSize(cell->getPort(Y));

	for (int i = 0; i < y_width; i++)
	{
		if (i < a_width)
			db->add_edge(cell, A, i, Y, i, -1);
		else if (is_signed && a_width > 0)
			db->add_edge(cell, A, a_width-1, Y, i, -1);
	}
}

void bitwise_binary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
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
			db->add_edge(cell, A, i, Y, i, -1);
		else if (is_signed && a_width > 0)
			db->add_edge(cell, A, a_width-1, Y, i, -1);

		if (i < b_width)
			db->add_edge(cell, B, i, Y, i, -1);
		else if (is_signed && b_width > 0)
			db->add_edge(cell, B, b_width-1, Y, i, -1);
	}
}

void arith_neg_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	IdString A = "\\A", Y = "\\Y";

	bool is_signed = cell->getParam("\\A_SIGNED").as_bool();
	int a_width = GetSize(cell->getPort(A));
	int y_width = GetSize(cell->getPort(Y));

	if (is_signed && a_width == 1)
		y_width = std::min(y_width, 1);

	for (int i = 0; i < y_width; i++)
	for (int k = 0; k <= i && k < a_width; k++)
		db->add_edge(cell, A, k, Y, i, -1);
}

void arith_binary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	IdString A = "\\A", B = "\\B", Y = "\\Y";

	bool is_signed = cell->getParam("\\A_SIGNED").as_bool();
	int a_width = GetSize(cell->getPort(A));
	int b_width = GetSize(cell->getPort(B));
	int y_width = GetSize(cell->getPort(Y));

	if (!is_signed && cell->type != "$sub") {
		int ab_width = std::max(a_width, b_width);
		y_width = std::min(y_width, ab_width+1);
	}

	for (int i = 0; i < y_width; i++)
	{
		for (int k = 0; k <= i; k++)
		{
			if (k < a_width)
				db->add_edge(cell, A, k, Y, i, -1);

			if (k < b_width)
				db->add_edge(cell, B, k, Y, i, -1);
		}
	}
}

void reduce_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	IdString A = "\\A", Y = "\\Y";

	int a_width = GetSize(cell->getPort(A));

	for (int i = 0; i < a_width; i++)
		db->add_edge(cell, A, i, Y, 0, -1);
}

void compare_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	IdString A = "\\A", B = "\\B", Y = "\\Y";

	int a_width = GetSize(cell->getPort(A));
	int b_width = GetSize(cell->getPort(B));

	for (int i = 0; i < a_width; i++)
		db->add_edge(cell, A, i, Y, 0, -1);

	for (int i = 0; i < b_width; i++)
		db->add_edge(cell, B, i, Y, 0, -1);
}

void mux_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	IdString A = "\\A", B = "\\B", S = "\\S", Y = "\\Y";

	int a_width = GetSize(cell->getPort(A));
	int b_width = GetSize(cell->getPort(B));
	int s_width = GetSize(cell->getPort(S));

	for (int i = 0; i < a_width; i++)
	{
		db->add_edge(cell, A, i, Y, i, -1);

		for (int k = i; k < b_width; k += a_width)
			db->add_edge(cell, B, k, Y, i, -1);

		for (int k = 0; k < s_width; k++)
			db->add_edge(cell, S, k, Y, i, -1);
	}
}

PRIVATE_NAMESPACE_END

bool YOSYS_NAMESPACE_PREFIX AbstractCellEdgesDatabase::add_edges_from_cell(RTLIL::Cell *cell)
{
	if (cell->type.in("$not", "$pos")) {
		bitwise_unary_op(this, cell);
		return true;
	}

	if (cell->type.in("$and", "$or", "$xor", "$xnor")) {
		bitwise_binary_op(this, cell);
		return true;
	}

	if (cell->type == "$neg") {
		arith_neg_op(this, cell);
		return true;
	}

	if (cell->type.in("$add", "$sub")) {
		arith_binary_op(this, cell);
		return true;
	}

	if (cell->type.in("$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor", "$reduce_bool", "$logic_not")) {
		reduce_op(this, cell);
		return true;
	}

	// FIXME:
	// if (cell->type.in("$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx")) {
	// 	shift_op(this, cell);
	// 	return true;
	// }

	if (cell->type.in("$lt", "$le", "$eq", "$ne", "$eqx", "$nex", "$ge", "$gt")) {
		compare_op(this, cell);
		return true;
	}

	if (cell->type.in("$mux", "$pmux")) {
		mux_op(this, cell);
		return true;
	}

	// FIXME: $mul $div $mod $slice $concat
	// FIXME: $lut $sop $alu $lcu $macc $fa

	return false;
}

