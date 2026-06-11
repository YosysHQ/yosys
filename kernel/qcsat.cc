/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Marcelina Kościelnicka <mwk@0x04.net>
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

#include "kernel/qcsat.h"

USING_YOSYS_NAMESPACE

std::vector<int> QuickConeSat::importSig(SigSpec sig)
{
	sig = modwalker.sigmap(sig);
	for (auto bit : sig)
		bits_queue.insert(bit);
	return satgen.importSigSpec(sig);
}

int QuickConeSat::importSigBit(SigBit bit)
{
	bit = modwalker.sigmap(bit);
	bits_queue.insert(bit);
	return satgen.importSigBit(bit);
}

void QuickConeSat::prepare()
{
	while (!bits_queue.empty())
	{
		pool<ModWalker::PortBit> portbits;
		modwalker.get_drivers(portbits, bits_queue);

		for (auto bit : bits_queue)
			if (bit.wire && bit.wire->get_bool_attribute(ID::onehot) && !imported_onehot.count(bit.wire))
			{
				std::vector<int> bits = satgen.importSigSpec(bit.wire);
				for (int i : bits)
				for (int j : bits)
					if (i != j)
						ez->assume(ez->NOT(i), j);
				imported_onehot.insert(bit.wire);
			}

		bits_queue.clear();

		for (auto &pbit : portbits)
		{
			if (imported_cells.count(pbit.cell))
				continue;
			if (cell_complexity(pbit.cell) > max_cell_complexity)
				continue;
			if (max_cell_outs && GetSize(modwalker.cell_outputs[pbit.cell]) > max_cell_outs)
				continue;
			auto &inputs = modwalker.cell_inputs[pbit.cell];
			bits_queue.insert(inputs.begin(), inputs.end());
			satgen.importCell(pbit.cell);
			imported_cells.insert(pbit.cell);
		}

		if (max_cell_count && GetSize(imported_cells) > max_cell_count)
			break;
	}
}

int QuickConeSat::cell_complexity(RTLIL::Cell *cell)
{
	if (cell->type.in(TW($concat), TW($slice), TW($pos), TW($buf), TW($_BUF_)))
		return 0;
	if (cell->type.in(TW($not), TW($and), TW($or), TW($xor), TW($xnor),
			TW($reduce_and), TW($reduce_or), TW($reduce_xor),
			TW($reduce_xnor), TW($reduce_bool),
			TW($logic_not), TW($logic_and), TW($logic_or),
			TW($eq), TW($ne), TW($eqx), TW($nex), TW($fa),
			TW($mux), TW($pmux), TW($bmux), TW($demux), TW($lut), TW($sop),
			TW($_NOT_), TW($_AND_), TW($_NAND_), TW($_OR_), TW($_NOR_),
			TW($_XOR_), TW($_XNOR_), TW($_ANDNOT_), TW($_ORNOT_),
			TW($_MUX_), TW($_NMUX_), TW($_MUX4_), TW($_MUX8_), TW($_MUX16_),
			TW($_AOI3_), TW($_OAI3_), TW($_AOI4_), TW($_OAI4_)))
		return 1;
	if (cell->type.in(TW($neg), TW($add), TW($sub), TW($alu), TW($lcu),
			TW($lt), TW($le), TW($gt), TW($ge)))
		return 2;
	if (cell->type.in(TW($shl), TW($shr), TW($sshl), TW($sshr), TW($shift), TW($shiftx)))
		return 3;
	if (cell->type.in(TW($mul), TW($macc), TW($div), TW($mod), TW($divfloor), TW($modfloor), TW($pow)))
		return 4;
	// Unknown cell.
	return 5;
}
