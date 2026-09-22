#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "techlibs/lattice/lattice_dsp_nexus_pm.h"

struct LatticeDspNexusPass : public Pass {
	LatticeDspNexusPass() : Pass("lattice_dsp_nexus", "Lattice Nexus DSP inference") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    lattice_dsp_nexus [options] [selection]\n");
		log("\n");
		log("Infer Lattice Nexus sysDSP macrocells (MULTADDSUB18X18,\n");
		log("MULTADDSUB36X36, MULTPREADD18X18, MULTADDSUB9X9WIDE) from MAC\n");
		log("and dot-product patterns, including a 36x36 multiply-add and a\n");
		log("4-lane 9x9 dot product with an accumulate, and absorb the\n");
		log("pipeline flip-flops around bare MULT18X18 / MULT36X36 multipliers\n");
		log("into the hardened DSP input and output registers.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing LATTICE_DSP_NEXUS pass.\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules()) {
			lattice_dsp_nexus_pm pm(module, module->cells());

			// Consume dot4+C before the bare dot4, and the wide MAC after the
			// 18-bit MAC, so the narrower mapping still wins.
			pm.run_nexus_mac9_4lane_c();
			pm.run_nexus_mac9_4lane_c_pre();
			pm.run_nexus_mac9_4lane();
			pm.run_nexus_mac18();
			pm.run_nexus_mac36();
			pm.run_nexus_preadd18();
			pm.run_nexus_mul_reg();
		}
	}
} LatticeDspNexusPass;

PRIVATE_NAMESPACE_END
