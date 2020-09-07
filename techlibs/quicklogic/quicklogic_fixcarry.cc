#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static void fix_carry_chain(Module *module)
{
	SigMap sigmap(module);

	pool<SigBit> ci_bits;
	dict<SigBit, SigBit> mapping_bits;

	for (auto cell : module->cells())
	{
		if (cell->type == ID(full_adder)) {
			SigBit bit_ci = cell->getPort(ID::CI);
			SigBit bit_s = sigmap(cell->getPort(ID::S));
			ci_bits.insert(bit_ci);				
			mapping_bits[bit_ci] = bit_s;
		}
	}
	
	vector<Cell*> adders_to_fix_cells;
	for (auto cell : module->cells())
	{
		if (cell->type == ID(full_adder)) {
			SigBit bit_ci = cell->getPort(ID::CI);
			SigBit canonical_bit = sigmap(bit_ci);
			if (!ci_bits.count(canonical_bit))
				continue;			

			adders_to_fix_cells.push_back(cell);
			log("Found %s cell named %s with invalid CI signal.\n", log_id(cell->type), log_id(cell));
		}
	}

	for (auto cell : adders_to_fix_cells)
	{
		SigBit bit_ci = cell->getPort(ID::CI);
		SigBit canonical_bit = sigmap(bit_ci);
		auto bit = mapping_bits.at(canonical_bit);
		log("Fixing %s cell named %s breaking carry chain.\n", log_id(cell->type), log_id(cell));
		Cell *c = module->addCell(NEW_ID, ID(full_adder));
		SigBit new_bit = module->addWire(NEW_ID);
		c->setPort(ID(A), bit);
		c->setPort(ID(B), State::S1);
		c->setPort(ID::CI, State::S0);
		c->setPort(ID::CO, new_bit);
		
		cell->setPort(ID::CI, new_bit);
	}
}

struct QuicklogicCarryFixPass : public Pass {
	QuicklogicCarryFixPass() : Pass("quicklogic_fixcarry", "Quicklogic: fix carry chain") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    quicklogic_fixcarry [options] [selection]\n");
		log("\n");
		log("Add Quicklogic adders to fix carry chain if needed.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing QUICKLOGIC_FIXCARRY pass (fix invalid carry chain).\n");
		
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
} QuicklogicCarryFixPass;

PRIVATE_NAMESPACE_END
