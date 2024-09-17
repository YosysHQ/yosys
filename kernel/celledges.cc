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

#include "kernel/celledges.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void bitwise_unary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	bool is_signed = (cell->type != ID($buf)) && cell->getParam(ID::A_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(ID::A));
	int y_width = GetSize(cell->getPort(ID::Y));

	for (int i = 0; i < y_width; i++)
	{
		if (i < a_width)
			db->add_edge(cell, ID::A, i, ID::Y, i, -1);
		else if (is_signed && a_width > 0)
			db->add_edge(cell, ID::A, a_width-1, ID::Y, i, -1);
	}
}

void bitwise_binary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(ID::A));
	int b_width = GetSize(cell->getPort(ID::B));
	int y_width = GetSize(cell->getPort(ID::Y));

	if (cell->type == ID($and) && !is_signed) {
		if (a_width > b_width)
			a_width = b_width;
		else
			b_width = a_width;
	}

	for (int i = 0; i < y_width; i++)
	{
		if (i < a_width)
			db->add_edge(cell, ID::A, i, ID::Y, i, -1);
		else if (is_signed && a_width > 0)
			db->add_edge(cell, ID::A, a_width-1, ID::Y, i, -1);

		if (i < b_width)
			db->add_edge(cell, ID::B, i, ID::Y, i, -1);
		else if (is_signed && b_width > 0)
			db->add_edge(cell, ID::B, b_width-1, ID::Y, i, -1);
	}
}

void arith_neg_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(ID::A));
	int y_width = GetSize(cell->getPort(ID::Y));

	if (is_signed && a_width == 1)
		y_width = std::min(y_width, 1);

	for (int i = 0; i < y_width; i++)
	for (int k = 0; k <= i && k < a_width; k++)
		db->add_edge(cell, ID::A, k, ID::Y, i, -1);
}

void arith_binary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(ID::A));
	int b_width = GetSize(cell->getPort(ID::B));
	int y_width = GetSize(cell->getPort(ID::Y));

	if (!is_signed && cell->type != ID($sub)) {
		int ab_width = std::max(a_width, b_width);
		y_width = std::min(y_width, ab_width+1);
	}

	for (int i = 0; i < y_width; i++)
	{
		for (int k = 0; k <= i; k++)
		{
			if (k < a_width)
				db->add_edge(cell, ID::A, k, ID::Y, i, -1);

			if (k < b_width)
				db->add_edge(cell, ID::B, k, ID::Y, i, -1);
		}
	}
}

void reduce_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int a_width = GetSize(cell->getPort(ID::A));

	for (int i = 0; i < a_width; i++)
		db->add_edge(cell, ID::A, i, ID::Y, 0, -1);
}

void compare_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int a_width = GetSize(cell->getPort(ID::A));
	int b_width = GetSize(cell->getPort(ID::B));

	for (int i = 0; i < a_width; i++)
		db->add_edge(cell, ID::A, i, ID::Y, 0, -1);

	for (int i = 0; i < b_width; i++)
		db->add_edge(cell, ID::B, i, ID::Y, 0, -1);
}

void mux_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int a_width = GetSize(cell->getPort(ID::A));
	int b_width = GetSize(cell->getPort(ID::B));
	int s_width = GetSize(cell->getPort(ID::S));

	for (int i = 0; i < a_width; i++)
	{
		db->add_edge(cell, ID::A, i, ID::Y, i, -1);

		for (int k = i; k < b_width; k += a_width)
			db->add_edge(cell, ID::B, k, ID::Y, i, -1);

		for (int k = 0; k < s_width; k++)
			db->add_edge(cell, ID::S, k, ID::Y, i, -1);
	}
}

void bmux_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int width = GetSize(cell->getPort(ID::Y));
	int a_width = GetSize(cell->getPort(ID::A));
	int s_width = GetSize(cell->getPort(ID::S));

	for (int i = 0; i < width; i++)
	{
		for (int k = i; k < a_width; k += width)
			db->add_edge(cell, ID::A, k, ID::Y, i, -1);

		for (int k = 0; k < s_width; k++)
			db->add_edge(cell, ID::S, k, ID::Y, i, -1);
	}
}

void demux_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int width = GetSize(cell->getPort(ID::Y));
	int a_width = GetSize(cell->getPort(ID::A));
	int s_width = GetSize(cell->getPort(ID::S));

	for (int i = 0; i < width; i++)
	{
		db->add_edge(cell, ID::A, i % a_width, ID::Y, i, -1);
		for (int k = 0; k < s_width; k++)
			db->add_edge(cell, ID::S, k, ID::Y, i, -1);
	}
}

void shift_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
	bool is_b_signed = cell->getParam(ID::B_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(ID::A));
	int b_width = GetSize(cell->getPort(ID::B));
	int y_width = GetSize(cell->getPort(ID::Y));

	// Behavior of the different shift cells:
	//
	//  $shl, $sshl -- shifts left by the amount on B port, B always unsigned
	//  $shr, $sshr -- ditto right
	//  $shift, $shiftx -- shifts right by the amount on B port, B optionally signed
	//
	// Sign extension (if A signed):
	//
	//  $shl, $shr, $shift -- only sign-extends up to size of Y, then shifts in zeroes
	//  $sshl, $sshr -- fully sign-extends
	//  $shiftx -- no sign extension
	//
	// Because $shl, $sshl only shift left, and $shl sign-extens up to size of Y, they
	// are effectively the same.

	// the cap below makes sure we don't overflow in the arithmetic further down, though
	// it makes the edge data invalid once a_width approaches the order of 2**30
	// (that ever happening is considered improbable)
	int b_width_capped = min(b_width, 30);

	int b_high, b_low;
	if (!is_b_signed) {
		b_high = (1 << b_width_capped) - 1;
		b_low = 0;
	} else {
		b_high = (1 << (b_width_capped - 1)) - 1;
		b_low = -(1 << (b_width_capped - 1));
	}

	for (int i = 0; i < y_width; i++){
		// highest position of Y that can change with the value of B
		int b_range_upper = 0;
		// 1 + highest position of A that can be moved to Y[i]
		int a_range_upper;
		// lowest position of A that can be moved to Y[i]
		int a_range_lower;

		if (cell->type.in(ID($shl), ID($sshl))) {
			b_range_upper = a_width + b_high;
			if (is_signed) b_range_upper -= 1;
			a_range_lower = max(0, i - b_high);
			a_range_upper = min(i+1, a_width);
		} else if (cell->type.in(ID($shr), ID($sshr)) || (cell->type.in(ID($shift), ID($shiftx)) && !is_b_signed)) {
			b_range_upper = a_width;
			a_range_lower = min(i, a_width - 1);
			a_range_upper = min(i+1 + b_high, a_width);
		} else if (cell->type.in(ID($shift), ID($shiftx)) && is_b_signed) {
			// can go both ways depending on sign of B
			// 2's complement range is different depending on direction
			b_range_upper = a_width - b_low;
			a_range_lower = max(0, i + b_low);
			if (is_signed)
				a_range_lower = min(a_range_lower, a_width - 1);
			a_range_upper = min(i+1 + b_high, a_width);
		} else {
			log_assert(false && "unreachable");
		}

		if (i < b_range_upper) {
			for (int k = a_range_lower; k < a_range_upper; k++)
				db->add_edge(cell, ID::A, k, ID::Y, i, -1);
		} else {
			// only influence is through sign extension
			if (is_signed)
				db->add_edge(cell, ID::A, a_width - 1, ID::Y, i, -1);
		}

		for (int k = 0; k < b_width; k++) {
			// left shifts
			if (cell->type.in(ID($shl), ID($sshl))) {
				if (a_width == 1 && is_signed) {
					int skip = 1 << (k + 1);
					int base = skip -1;
					if (i % skip != base && i - a_width + 2 < 1 << b_width)
						db->add_edge(cell, ID::B, k, ID::Y, i, -1);	
				} else if (is_signed) {
					if (i - a_width + 2 < 1 << b_width)
						db->add_edge(cell, ID::B, k, ID::Y, i, -1);
				} else {
					if (i - a_width + 1 < 1 << b_width)
						db->add_edge(cell, ID::B, k, ID::Y, i, -1);
				}
			// right shifts
			} else if (cell->type.in(ID($shr), ID($sshr)) || (cell->type.in(ID($shift), ID($shiftx)) && !is_b_signed)) {
				if (is_signed) {
					bool shift_in_bulk = i < a_width - 1;
					// can we jump into the zero-padding by toggling B[k]?
					bool zpad_jump = (((y_width - i) & ((1 << (k + 1)) - 1)) != 0 \
									&& (((y_width - i) & ~(1 << k)) < (1 << b_width)));

					if (shift_in_bulk || (cell->type.in(ID($shr), ID($shift), ID($shiftx)) && zpad_jump))
						db->add_edge(cell, ID::B, k, ID::Y, i, -1);
				} else {
					if (i < a_width)
						db->add_edge(cell, ID::B, k, ID::Y, i, -1);
				}
			// bidirectional shifts (positive B shifts right, negative left)
			} else if (cell->type.in(ID($shift), ID($shiftx)) && is_b_signed) {
				if (is_signed) {
					if (k != b_width - 1) {
						bool r_shift_in_bulk = i < a_width - 1;
						// assuming B is positive, can we jump into the upper zero-padding by toggling B[k]?
						bool r_zpad_jump = (((y_width - i) & ((1 << (k + 1)) - 1)) != 0 \
											&& (((y_width - i) & ~(1 << k)) <= b_high));
						// assuming B is negative, can we influence Y[i] by toggling B[k]?
						bool l = a_width - 2 - i >= b_low;
						if (a_width == 1) {
							// in case of a_width==1 we go into more detailed reasoning
							l = l && (~(i - a_width) & ((1 << (k + 1)) - 1)) != 0;
						}
						if (r_shift_in_bulk || r_zpad_jump || l)
							db->add_edge(cell, ID::B, k, ID::Y, i, -1);
					} else {
						if (y_width - i <= b_high || a_width - 2 - i >= b_low)
							db->add_edge(cell, ID::B, k, ID::Y, i, -1);
					}
				} else {
					if (a_width - 1 - i >= b_low)
						db->add_edge(cell, ID::B, k, ID::Y, i, -1);
				}
			} else {
				log_assert(false && "unreachable");
			}
		}
	}
}

void packed_mem_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	log_assert(cell->type == ID($mem_v2));
	Const rd_clk_enable = cell->getParam(ID::RD_CLK_ENABLE);
	int n_rd_ports = cell->getParam(ID::RD_PORTS).as_int();
	int abits = cell->getParam(ID::ABITS).as_int();
	int width = cell->getParam(ID::WIDTH).as_int();

	for (int i = 0; i < n_rd_ports; i++) {
		if (rd_clk_enable[i] != State::S0) {
			for (int k = 0; k < width; k++)
				db->add_edge(cell, ID::RD_ARST, i, ID::RD_DATA, i * width + k, -1);
			continue;
		}

		for (int j = 0; j < abits; j++)
			for (int k = 0; k < width; k++)
				db->add_edge(cell, ID::RD_ADDR, i * abits + j,
								   ID::RD_DATA, i * width + k, -1);
	}
}

void memrd_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	log_assert(cell->type.in(ID($memrd), ID($memrd_v2)));
	int abits = cell->getParam(ID::ABITS).as_int();
	int width = cell->getParam(ID::WIDTH).as_int();

	if (cell->getParam(ID::CLK_ENABLE).as_bool()) {
		if (cell->type == ID($memrd_v2)) {
			for (int k = 0; k < width; k++)
				db->add_edge(cell, ID::ARST, 0, ID::DATA, k, -1);
		}
		return;
	}

	for (int j = 0; j < abits; j++)
		for (int k = 0; k < width; k++)
			db->add_edge(cell, ID::ADDR, j, ID::DATA, k, -1);
}

void mem_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	if (cell->type == ID($mem_v2))
		packed_mem_op(db, cell);
	else if (cell->type.in(ID($memrd), ID($memrd_v2)))
		memrd_op(db, cell);
	else if (cell->type.in(ID($memwr), ID($memwr_v2), ID($meminit)))
		return; /* no edges here */
	else
		log_abort();
}

void ff_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int width = cell->getPort(ID::Q).size();

	if (cell->type.in(ID($dlatch), ID($adlatch), ID($dlatchsr))) {
		for (int k = 0; k < width; k++) {
			db->add_edge(cell, ID::D, k, ID::Q, k, -1);
			db->add_edge(cell, ID::EN, 0, ID::Q, k, -1);
		}
	}

	if (cell->hasPort(ID::CLR))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, ID::CLR, 0, ID::Q, k, -1);
	if (cell->hasPort(ID::SET))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, ID::SET, 0, ID::Q, k, -1);
	if (cell->hasPort(ID::ALOAD))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, ID::ALOAD, 0, ID::Q, k, -1);
	if (cell->hasPort(ID::AD))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, ID::AD, k, ID::Q, k, -1);
	if (cell->hasPort(ID::ARST))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, ID::ARST, 0, ID::Q, k, -1);
}

PRIVATE_NAMESPACE_END

bool YOSYS_NAMESPACE_PREFIX AbstractCellEdgesDatabase::add_edges_from_cell(RTLIL::Cell *cell)
{
	if (cell->type.in(ID($not), ID($pos), ID($buf))) {
		bitwise_unary_op(this, cell);
		return true;
	}

	if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
		bitwise_binary_op(this, cell);
		return true;
	}

	if (cell->type == ID($neg)) {
		arith_neg_op(this, cell);
		return true;
	}

	if (cell->type.in(ID($add), ID($sub))) {
		arith_binary_op(this, cell);
		return true;
	}

	if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool), ID($logic_not))) {
		reduce_op(this, cell);
		return true;
	}

	if (cell->type.in(ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx))) {
		shift_op(this, cell);
		return true;
	}

	if (cell->type.in(ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt))) {
		compare_op(this, cell);
		return true;
	}

	if (cell->type.in(ID($mux), ID($pmux))) {
		mux_op(this, cell);
		return true;
	}

	if (cell->type == ID($bmux)) {
		bmux_op(this, cell);
		return true;
	}

	if (cell->type == ID($demux)) {
		demux_op(this, cell);
		return true;
	}

	if (cell->type.in(ID($mem_v2), ID($memrd), ID($memrd_v2), ID($memwr), ID($memwr_v2), ID($meminit))) {
		mem_op(this, cell);
		return true;
	}

	if (RTLIL::builtin_ff_cell_types().count(cell->type)) {
		ff_op(this, cell);
		return true;
	}

	// FIXME: $mul $div $mod $divfloor $modfloor $slice $concat
	// FIXME: $lut $sop $alu $lcu $macc $fa
	// FIXME: $mul $div $mod $divfloor $modfloor $pow $slice $concat $bweqx
	// FIXME: $lut $sop $alu $lcu $macc $fa $logic_and $logic_or $bwmux

	// FIXME: $_BUF_ $_NOT_ $_AND_ $_NAND_ $_OR_ $_NOR_ $_XOR_ $_XNOR_ $_ANDNOT_ $_ORNOT_
	// FIXME: $_MUX_ $_NMUX_ $_MUX4_ $_MUX8_ $_MUX16_ $_AOI3_ $_OAI3_ $_AOI4_ $_OAI4_

	// FIXME: $specify2 $specify3 $specrule ???
	// FIXME: $equiv $set_tag $get_tag $overwrite_tag $original_tag

	if (cell->type.in(ID($assert), ID($assume), ID($live), ID($fair), ID($cover), ID($initstate), ID($anyconst), ID($anyseq), ID($allconst), ID($allseq)))
		return true; // no-op: these have either no inputs or no outputs

	return false;
}

