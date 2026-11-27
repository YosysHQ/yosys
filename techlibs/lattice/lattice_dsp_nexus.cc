#include "kernel/yosys.h"
#include "techlibs/lattice/lattice_dsp_nexus.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

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
			MatchContext ctx(module);
			vector<Cell*> cells = module->cells();
			NexusMac9_4Lane mac9_4lane(ctx, cells);
			NexusMac mac(ctx, cells);
			NexusPreadd18 preadd18(ctx, cells);
			NexusMulReg mul_reg(ctx, cells);

			mac9_4lane.run();
			mac.run();
			preadd18.run();
			mul_reg.run();
		}
	}
} LatticeDspNexusPass;

PRIVATE_NAMESPACE_END
