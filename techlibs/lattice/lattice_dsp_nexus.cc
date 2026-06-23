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
		log("Infer Lattice Nexus sysDSP macrocells (MULTADDSUB18X18, MULTPREADD18X18,\n");
		log("MULTADDSUB9X9WIDE) from MAC and dot-product patterns.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing LATTICE_DSP_NEXUS pass.\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules()) {
			lattice_dsp_nexus_pm pm(module, module->cells());

			pm.run_nexus_mac9_4lane();
			pm.run_nexus_mac18();
			pm.run_nexus_preadd18();
		}
	}
} LatticeDspNexusPass;

PRIVATE_NAMESPACE_END
