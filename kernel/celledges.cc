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
	bool is_signed = (cell->type != TW($buf)) && cell->getParam(ID::A_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(TW::A));
	int y_width = GetSize(cell->getPort(TW::Y));

	for (int i = 0; i < y_width; i++)
	{
		if (i < a_width)
			db->add_edge(cell, TW::A, i, TW::Y, i, -1);
		else if (is_signed && a_width > 0)
			db->add_edge(cell, TW::A, a_width-1, TW::Y, i, -1);
	}
}

void bitwise_binary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(TW::A));
	int b_width = GetSize(cell->getPort(TW::B));
	int y_width = GetSize(cell->getPort(TW::Y));

	if (cell->type == TW($and) && !is_signed) {
		if (a_width > b_width)
			a_width = b_width;
		else
			b_width = a_width;
	}

	for (int i = 0; i < y_width; i++)
	{
		if (i < a_width)
			db->add_edge(cell, TW::A, i, TW::Y, i, -1);
		else if (is_signed && a_width > 0)
			db->add_edge(cell, TW::A, a_width-1, TW::Y, i, -1);

		if (i < b_width)
			db->add_edge(cell, TW::B, i, TW::Y, i, -1);
		else if (is_signed && b_width > 0)
			db->add_edge(cell, TW::B, b_width-1, TW::Y, i, -1);
	}
}

void arith_neg_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(TW::A));
	int y_width = GetSize(cell->getPort(TW::Y));

	if (is_signed && a_width == 1)
		y_width = std::min(y_width, 1);

	for (int i = 0; i < y_width; i++)
	for (int k = 0; k <= i && k < a_width; k++)
		db->add_edge(cell, TW::A, k, TW::Y, i, -1);
}

void arith_binary_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(TW::A));
	int b_width = GetSize(cell->getPort(TW::B));
	int y_width = GetSize(cell->getPort(TW::Y));

	if (!is_signed && cell->type != TW($sub)) {
		int ab_width = std::max(a_width, b_width);
		y_width = std::min(y_width, ab_width+1);
	}

	for (int i = 0; i < y_width; i++)
	{
		for (int k = 0; k <= i; k++)
		{
			if (k < a_width)
				db->add_edge(cell, TW::A, k, TW::Y, i, -1);

			if (k < b_width)
				db->add_edge(cell, TW::B, k, TW::Y, i, -1);
		}
	}
}

void reduce_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int a_width = GetSize(cell->getPort(TW::A));

	for (int i = 0; i < a_width; i++)
		db->add_edge(cell, TW::A, i, TW::Y, 0, -1);
}

void logic_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int a_width = GetSize(cell->getPort(TW::A));
	int b_width = GetSize(cell->getPort(TW::B));

	for (int i = 0; i < a_width; i++)
		db->add_edge(cell, TW::A, i, TW::Y, 0, -1);
	for (int i = 0; i < b_width; i++)
		db->add_edge(cell, TW::B, i, TW::Y, 0, -1);
}

void concat_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int a_width = GetSize(cell->getPort(TW::A));
	int b_width = GetSize(cell->getPort(TW::B));

	for (int i = 0; i < a_width; i++)
		db->add_edge(cell, TW::A, i, TW::Y, i, -1);
	for (int i = 0; i < b_width; i++)
		db->add_edge(cell, TW::B, i, TW::Y, a_width + i, -1);
}

void slice_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int offset = cell->getParam(ID::OFFSET).as_int();
	int a_width = GetSize(cell->getPort(TW::A));
	int y_width = GetSize(cell->getPort(TW::Y));

	for (int i = 0; i < y_width; i++) {
		int a_bit = offset + i;
		if (a_bit >= 0 && a_bit < a_width)
			db->add_edge(cell, TW::A, a_bit, TW::Y, i, -1);
	}
}

void compare_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int a_width = GetSize(cell->getPort(TW::A));
	int b_width = GetSize(cell->getPort(TW::B));

	for (int i = 0; i < a_width; i++)
		db->add_edge(cell, TW::A, i, TW::Y, 0, -1);

	for (int i = 0; i < b_width; i++)
		db->add_edge(cell, TW::B, i, TW::Y, 0, -1);
}

void mux_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int a_width = GetSize(cell->getPort(TW::A));
	int b_width = GetSize(cell->getPort(TW::B));
	int s_width = GetSize(cell->getPort(TW::S));

	for (int i = 0; i < a_width; i++)
	{
		db->add_edge(cell, TW::A, i, TW::Y, i, -1);

		for (int k = i; k < b_width; k += a_width)
			db->add_edge(cell, TW::B, k, TW::Y, i, -1);

		for (int k = 0; k < s_width; k++)
			db->add_edge(cell, TW::S, k, TW::Y, i, -1);
	}
}

void bmux_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int width = GetSize(cell->getPort(TW::Y));
	int a_width = GetSize(cell->getPort(TW::A));
	int s_width = GetSize(cell->getPort(TW::S));

	for (int i = 0; i < width; i++)
	{
		for (int k = i; k < a_width; k += width)
			db->add_edge(cell, TW::A, k, TW::Y, i, -1);

		for (int k = 0; k < s_width; k++)
			db->add_edge(cell, TW::S, k, TW::Y, i, -1);
	}
}

void demux_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int width = GetSize(cell->getPort(TW::Y));
	int a_width = GetSize(cell->getPort(TW::A));
	int s_width = GetSize(cell->getPort(TW::S));

	for (int i = 0; i < width; i++)
	{
		db->add_edge(cell, TW::A, i % a_width, TW::Y, i, -1);
		for (int k = 0; k < s_width; k++)
			db->add_edge(cell, TW::S, k, TW::Y, i, -1);
	}
}

void shift_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	bool is_signed = cell->getParam(ID::A_SIGNED).as_bool();
	bool is_b_signed = cell->getParam(ID::B_SIGNED).as_bool();
	int a_width = GetSize(cell->getPort(TW::A));
	int b_width = GetSize(cell->getPort(TW::B));
	int y_width = GetSize(cell->getPort(TW::Y));

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

		if (cell->type.in(TW($shl), TW($sshl))) {
			b_range_upper = a_width + b_high;
			if (is_signed) b_range_upper -= 1;
			a_range_lower = max(0, i - b_high);
			a_range_upper = min(i+1, a_width);
		} else if (cell->type.in(TW($shr), TW($sshr)) || (cell->type.in(TW($shift), TW($shiftx)) && !is_b_signed)) {
			b_range_upper = a_width;
			a_range_lower = min(i, a_width - 1);
			a_range_upper = min(i+1 + b_high, a_width);
		} else if (cell->type.in(TW($shift), TW($shiftx)) && is_b_signed) {
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
				db->add_edge(cell, TW::A, k, TW::Y, i, -1);
		} else {
			// only influence is through sign extension
			if (is_signed)
				db->add_edge(cell, TW::A, a_width - 1, TW::Y, i, -1);
		}

		for (int k = 0; k < b_width_capped; k++) {
			// left shifts
			if (cell->type.in(TW($shl), TW($sshl))) {
				if (a_width == 1 && is_signed) {
					int skip = 1 << (k + 1);
					int base = skip -1;
					if (i % skip != base && i - a_width + 2 < 1 << b_width_capped)
						db->add_edge(cell, TW::B, k, TW::Y, i, -1);
				} else if (is_signed) {
					if (i - a_width + 2 < 1 << b_width_capped)
						db->add_edge(cell, TW::B, k, TW::Y, i, -1);
				} else {
					if (i - a_width + 1 < 1 << b_width_capped)
						db->add_edge(cell, TW::B, k, TW::Y, i, -1);
				}
			// right shifts
			} else if (cell->type.in(TW($shr), TW($sshr)) || (cell->type.in(TW($shift), TW($shiftx)) && !is_b_signed)) {
				if (is_signed) {
					bool shift_in_bulk = i < a_width - 1;
					// can we jump into the zero-padding by toggling B[k]?
					bool zpad_jump = (((y_width - i) & ((1 << (k + 1)) - 1)) != 0 \
									&& (((y_width - i) & ~(1 << k)) < (1 << b_width_capped)));

					if (shift_in_bulk || (cell->type.in(TW($shr), TW($shift), TW($shiftx)) && zpad_jump))
						db->add_edge(cell, TW::B, k, TW::Y, i, -1);
				} else {
					if (i < a_width)
						db->add_edge(cell, TW::B, k, TW::Y, i, -1);
				}
			// bidirectional shifts (positive B shifts right, negative left)
			} else if (cell->type.in(TW($shift), TW($shiftx)) && is_b_signed) {
				if (is_signed) {
					if (k != b_width_capped - 1) {
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
							db->add_edge(cell, TW::B, k, TW::Y, i, -1);
					} else {
						if (y_width - i <= b_high || a_width - 2 - i >= b_low)
							db->add_edge(cell, TW::B, k, TW::Y, i, -1);
					}
				} else {
					if (a_width - 1 - i >= b_low)
						db->add_edge(cell, TW::B, k, TW::Y, i, -1);
				}
			} else {
				log_assert(false && "unreachable");
			}
		}
	}
}

void packed_mem_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	log_assert(cell->type == TW($mem_v2));
	Const rd_clk_enable = cell->getParam(ID::RD_CLK_ENABLE);
	int n_rd_ports = cell->getParam(ID::RD_PORTS).as_int();
	int abits = cell->getParam(ID::ABITS).as_int();
	int width = cell->getParam(ID::WIDTH).as_int();

	for (int i = 0; i < n_rd_ports; i++) {
		if (rd_clk_enable[i] != State::S0) {
			for (int k = 0; k < width; k++)
				db->add_edge(cell, TW::RD_ARST, i, TW::RD_DATA, i * width + k, -1);
			continue;
		}

		for (int j = 0; j < abits; j++)
			for (int k = 0; k < width; k++)
				db->add_edge(cell, TW::RD_ADDR, i * abits + j,
								   TW::RD_DATA, i * width + k, -1);
	}
}

void memrd_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	log_assert(cell->type.in(TW($memrd), TW($memrd_v2)));
	int abits = cell->getParam(ID::ABITS).as_int();
	int width = cell->getParam(ID::WIDTH).as_int();

	if (cell->getParam(ID::CLK_ENABLE).as_bool()) {
		if (cell->type == TW($memrd_v2)) {
			for (int k = 0; k < width; k++)
				db->add_edge(cell, TW::ARST, 0, TW::DATA, k, -1);
		}
		return;
	}

	for (int j = 0; j < abits; j++)
		for (int k = 0; k < width; k++)
			db->add_edge(cell, TW::ADDR, j, TW::DATA, k, -1);
}

void mem_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	if (cell->type == TW($mem_v2))
		packed_mem_op(db, cell);
	else if (cell->type.in(TW($memrd), TW($memrd_v2)))
		memrd_op(db, cell);
	else if (cell->type.in(TW($memwr), TW($memwr_v2), TW($meminit)))
		return; /* no edges here */
	else
		log_abort();
}

void ff_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int width = cell->getPort(TW::Q).size();

	if (cell->type.in(TW($dlatch), TW($adlatch), TW($dlatchsr))) {
		for (int k = 0; k < width; k++) {
			db->add_edge(cell, TW::D, k, TW::Q, k, -1);
			db->add_edge(cell, TW::EN, 0, TW::Q, k, -1);
		}
	}

	if (cell->hasPort(TW::CLR))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, TW::CLR, 0, TW::Q, k, -1);
	if (cell->hasPort(TW::SET))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, TW::SET, 0, TW::Q, k, -1);
	if (cell->hasPort(TW::ALOAD))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, TW::ALOAD, 0, TW::Q, k, -1);
	if (cell->hasPort(TW::AD))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, TW::AD, k, TW::Q, k, -1);
	if (cell->hasPort(TW::ARST))
		for (int k = 0; k < width; k++)
			db->add_edge(cell, TW::ARST, 0, TW::Q, k, -1);
}

void full_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	std::vector<TwineRef> input_ports;
	std::vector<TwineRef> output_ports;

	for (auto &conn : cell->connections())
	{
		TwineRef port = conn.first;
		RTLIL::PortDir dir = cell->port_dir(port);
		if (cell->input(port) || dir == RTLIL::PortDir::PD_INOUT)
			input_ports.push_back(port);
		if (cell->output(port) || dir == RTLIL::PortDir::PD_INOUT)
			output_ports.push_back(port);
	}

	for (auto out_port : output_ports)
	{
		int out_width = GetSize(cell->getPort(out_port));
		for (int out_bit = 0; out_bit < out_width; out_bit++)
		{
			for (auto in_port : input_ports)
			{
				int in_width = GetSize(cell->getPort(in_port));
				for (int in_bit = 0; in_bit < in_width; in_bit++)
					db->add_edge(cell, in_port, in_bit, out_port, out_bit, -1);
			}
		}
	}
}

void bweqx_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int width = GetSize(cell->getPort(TW::Y));
	int a_width = GetSize(cell->getPort(TW::A));
	int b_width = GetSize(cell->getPort(TW::B));
	int max_width = std::min(width, std::min(a_width, b_width));

	for (int i = 0; i < max_width; i++) {
		db->add_edge(cell, TW::A, i, TW::Y, i, -1);
		db->add_edge(cell, TW::B, i, TW::Y, i, -1);
	}
}

void bwmux_op(AbstractCellEdgesDatabase *db, RTLIL::Cell *cell)
{
	int width = GetSize(cell->getPort(TW::Y));
	int a_width = GetSize(cell->getPort(TW::A));
	int b_width = GetSize(cell->getPort(TW::B));
	int s_width = GetSize(cell->getPort(TW::S));
	int max_width = std::min(width, std::min(a_width, std::min(b_width, s_width)));

	for (int i = 0; i < max_width; i++) {
		db->add_edge(cell, TW::A, i, TW::Y, i, -1);
		db->add_edge(cell, TW::B, i, TW::Y, i, -1);
		db->add_edge(cell, TW::S, i, TW::Y, i, -1);
	}
}

PRIVATE_NAMESPACE_END

bool YOSYS_NAMESPACE_PREFIX AbstractCellEdgesDatabase::add_edges_from_cell(RTLIL::Cell *cell)
{
	if (cell->type.in(TW($not), TW($pos), TW($buf))) {
		bitwise_unary_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($and), TW($or), TW($xor), TW($xnor))) {
		bitwise_binary_op(this, cell);
		return true;
	}

	if (cell->type == TW($neg)) {
		arith_neg_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($add), TW($sub))) {
		arith_binary_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($reduce_and), TW($reduce_or), TW($reduce_xor), TW($reduce_xnor), TW($reduce_bool), TW($logic_not))) {
		reduce_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($logic_and), TW($logic_or))) {
		logic_op(this, cell);
		return true;
	}

	if (cell->type == TW($slice)) {
		slice_op(this, cell);
		return true;
	}

	if (cell->type == TW($concat)) {
		concat_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($shl), TW($shr), TW($sshl), TW($sshr), TW($shift), TW($shiftx))) {
		shift_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($lt), TW($le), TW($eq), TW($ne), TW($eqx), TW($nex), TW($ge), TW($gt))) {
		compare_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($mux), TW($pmux))) {
		mux_op(this, cell);
		return true;
	}

	if (cell->type == TW($bmux)) {
		bmux_op(this, cell);
		return true;
	}

	if (cell->type == TW($demux)) {
		demux_op(this, cell);
		return true;
	}

	if (cell->type == TW($bweqx)) {
		bweqx_op(this, cell);
		return true;
	}

	if (cell->type == TW($bwmux)) {
		bwmux_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($mem_v2), TW($memrd), TW($memrd_v2), TW($memwr), TW($memwr_v2), TW($meminit))) {
		mem_op(this, cell);
		return true;
	}

	if (cell->is_builtin_ff()) {
		ff_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($mul), TW($div), TW($mod), TW($divfloor), TW($modfloor), TW($pow))) {
		full_op(this, cell);
		return true;
	}

	if (cell->type.in(TW($lut), TW($sop), TW($alu), TW($lcu), TW($macc), TW($macc_v2))) {
		full_op(this, cell);
		return true;
	}

	if (cell->type.in(
			TW($_BUF_), TW($_NOT_), TW($_AND_), TW($_NAND_), TW($_OR_), TW($_NOR_),
			TW($_XOR_), TW($_XNOR_), TW($_ANDNOT_), TW($_ORNOT_), TW($_MUX_), TW($_NMUX_),
			TW($_MUX4_), TW($_MUX8_), TW($_MUX16_), TW($_AOI3_), TW($_OAI3_), TW($_AOI4_),
			TW($_OAI4_), TW($_TBUF_))) {
		full_op(this, cell);
		return true;
	}

	// FIXME: $specify2 $specify3 $specrule ???
	// FIXME: $equiv $set_tag $get_tag $overwrite_tag $original_tag

	if (cell->type.in(TW($assert), TW($assume), TW($live), TW($fair), TW($cover), TW($initstate), TW($anyconst), TW($anyseq), TW($allconst), TW($allseq)))
		return true; // no-op: these have either no inputs or no outputs

	return false;
}
