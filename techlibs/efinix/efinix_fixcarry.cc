/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2019  Miodrag Milanovic <miodrag@symbioticeda.com>
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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static SigBit get_bit_or_zero(const SigSpec &sig)
{
	if (GetSize(sig) == 0)
		return State::S0;
	return sig[0];
}

static void fix_carry_chain(Module *module)
{
	SigMap sigmap(module);

	pool<SigBit> ci_bits;
	dict<SigBit, SigBit> mapping_bits;

	for (auto cell : module->cells())
	{
		if (cell->type == "\\EFX_ADD") {
			SigBit bit_i0 = get_bit_or_zero(cell->getPort("\\I0"));
			SigBit bit_i1 = get_bit_or_zero(cell->getPort("\\I1"));
			if (bit_i0 == State::S0 && bit_i1== State::S0) {
				SigBit bit_ci = get_bit_or_zero(cell->getPort("\\CI"));
				SigBit bit_o = sigmap(cell->getPort("\\O"));
				ci_bits.insert(bit_ci);				
				mapping_bits[bit_ci] = bit_o;
			}
		}
	}
	
	vector<Cell*> adders_to_fix_cells;
	for (auto cell : module->cells())
	{
		if (cell->type == "\\EFX_ADD") {
			SigBit bit_ci = get_bit_or_zero(cell->getPort("\\CI"));
			SigBit bit_i0 = get_bit_or_zero(cell->getPort("\\I0"));
			SigBit bit_i1 = get_bit_or_zero(cell->getPort("\\I1"));			
			SigBit canonical_bit = sigmap(bit_ci);
			if (!ci_bits.count(canonical_bit))
				continue;			
			if (bit_i0 == State::S0 && bit_i1== State::S0) 
				continue;

			adders_to_fix_cells.push_back(cell);
			log("Found %s cell named %s with invalid CI signal.\n", log_id(cell->type), log_id(cell));
		}
	}

	for (auto cell : adders_to_fix_cells)
	{
		SigBit bit_ci = get_bit_or_zero(cell->getPort("\\CI"));
		SigBit canonical_bit = sigmap(bit_ci);
		auto bit = mapping_bits.at(canonical_bit);
		log("Fixing %s cell named %s breaking carry chain.\n", log_id(cell->type), log_id(cell));
		Cell *c = module->addCell(NEW_ID, "\\EFX_ADD");
		SigBit new_bit = module->addWire(NEW_ID);
		c->setParam("\\I0_POLARITY", State::S1);
		c->setParam("\\I1_POLARITY", State::S1);
		c->setPort("\\I0", bit);
		c->setPort("\\I1", State::S1);
		c->setPort("\\CI", State::S0);
		c->setPort("\\CO", new_bit);
		
		cell->setPort("\\CI", new_bit);
	}
}

struct EfinixCarryFixPass : public Pass {
	EfinixCarryFixPass() : Pass("efinix_fixcarry", "Efinix: fix carry chain") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    efinix_fixcarry [options] [selection]\n");
		log("\n");
		log("Add Efinix adders to fix carry chain if needed.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing efinix_fixcarry pass (fix invalid carry chain).\n");
		
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);

		Module *module = design->top_module();

		if (module == nullptr)
			log_cmd_error("No top module found.\n");

		fix_carry_chain(module);		
	}
} EfinixCarryFixPass;

PRIVATE_NAMESPACE_END
