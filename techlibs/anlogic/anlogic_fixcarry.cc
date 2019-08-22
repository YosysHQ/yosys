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
		if (cell->type == "\\AL_MAP_ADDER") {
			if (cell->getParam("\\ALUTYPE") != Const("ADD")) continue;
			SigBit bit_i0 = get_bit_or_zero(cell->getPort("\\a"));
			SigBit bit_i1 = get_bit_or_zero(cell->getPort("\\b"));
			if (bit_i0 == State::S0 && bit_i1== State::S0) {
				SigBit bit_ci = get_bit_or_zero(cell->getPort("\\c"));
				SigSpec o = cell->getPort("\\o");
				if (GetSize(o) == 2) {
					SigBit bit_o = o[0];
					ci_bits.insert(bit_ci);				
					mapping_bits[bit_ci] = bit_o;				
				}
			}
		}
	}
	vector<Cell*> adders_to_fix_cells;
	for (auto cell : module->cells())
	{
		if (cell->type == "\\AL_MAP_ADDER") {
			if (cell->getParam("\\ALUTYPE") != Const("ADD")) continue;
			SigBit bit_ci = get_bit_or_zero(cell->getPort("\\c"));
			SigBit bit_i0 = get_bit_or_zero(cell->getPort("\\a"));
			SigBit bit_i1 = get_bit_or_zero(cell->getPort("\\b"));			
			SigBit canonical_bit = sigmap(bit_ci);
			if (!ci_bits.count(canonical_bit))
				continue;			
			if (bit_i0 == State::S0 && bit_i1== State::S0) 
				continue;

			adders_to_fix_cells.push_back(cell);
			log("Found %s cell named %s with invalid 'c' signal.\n", log_id(cell->type), log_id(cell));
		}
	}

	for (auto cell : adders_to_fix_cells)
	{
		SigBit bit_ci = get_bit_or_zero(cell->getPort("\\c"));
		SigBit canonical_bit = sigmap(bit_ci);
		auto bit = mapping_bits.at(canonical_bit);
		log("Fixing %s cell named %s breaking carry chain.\n", log_id(cell->type), log_id(cell));
		Cell *c = module->addCell(NEW_ID, "\\AL_MAP_ADDER");
		SigBit new_bit = module->addWire(NEW_ID);
		SigBit dummy_bit = module->addWire(NEW_ID);
		SigSpec bits;
		bits.append(dummy_bit);
		bits.append(new_bit);
		c->setParam("\\ALUTYPE", Const("ADD_CARRY"));
		c->setPort("\\a", bit);
		c->setPort("\\b", State::S0);
		c->setPort("\\c", State::S0);
		c->setPort("\\o", bits);
		
		cell->setPort("\\c", new_bit);
	}
	
}

struct AnlogicCarryFixPass : public Pass {
	AnlogicCarryFixPass() : Pass("anlogic_fixcarry", "Anlogic: fix carry chain") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    anlogic_fixcarry [options] [selection]\n");
		log("\n");
		log("Add Anlogic adders to fix carry chain if needed.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing anlogic_fixcarry pass (fix invalid carry chain).\n");
		
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
} AnlogicCarryFixPass;

PRIVATE_NAMESPACE_END
