#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// $add and $sub are signed only if both operands are
bool nexus_add_signed(Cell *add) { return add->getParam(ID::A_SIGNED).as_bool() && add->getParam(ID::B_SIGNED).as_bool(); }

// Bits [0, width) of the exact product of mul, or empty if its Y cuts them off
SigSpec nexus_product_bits(Cell *mul, const SigSpec &mul_y, int width)
{
	int full_width = GetSize(mul->getPort(ID::A)) + GetSize(mul->getPort(ID::B));
	if (GetSize(mul_y) < width && GetSize(mul_y) < full_width)
		return SigSpec();

	SigSpec bits = mul_y;
	bits.extend_u0(width, mul->getParam(ID::A_SIGNED).as_bool());
	return bits;
}

// Bits [0, width) of a partial sum, or empty if it is narrower
SigSpec nexus_sum_bits(const SigSpec &sum_y, int width)
{
	if (GetSize(sum_y) < width)
		return SigSpec();
	return sum_y.extract(0, width);
}

// True if an adder operand, extended as the adder does, is value
bool nexus_operand_is(SigSpec operand, bool add_signed, const SigSpec &value)
{
	if (value.empty())
		return false;
	operand.extend_u0(GetSize(value), add_signed);
	return operand == value;
}

#include "techlibs/lattice/lattice_dsp_nexus_pm.h"

struct LatticeDspNexusPass : public Pass {
	LatticeDspNexusPass() : Pass("lattice_dsp_nexus", "Lattice Nexus DSP inference") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    lattice_dsp_nexus [options] [selection]\n");
		log("\n");
		log("Infer Lattice Nexus sysDSP macrocells (MULTADDSUB18X18, MULTADDSUB36X36,\n");
		log("MULTPREADD18X18, MULTADDSUB9X9WIDE) from MAC and dot-product patterns, and\n");
		log("absorb the pipeline flip-flops around bare MULT18X18 / MULT36X36 multipliers\n");
		log("into the hardened DSP input and output registers.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing LATTICE_DSP_NEXUS pass.\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules()) {
			lattice_dsp_nexus_pm pm(module, module->cells());

			pm.run_nexus_mac9_4lane();
			pm.run_nexus_mac();
			pm.run_nexus_preadd18();
			pm.run_nexus_mul_reg();
		}
	}
} LatticeDspNexusPass;

PRIVATE_NAMESPACE_END
