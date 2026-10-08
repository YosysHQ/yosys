#ifndef EQUIV_H
#define EQUIV_H

#include "kernel/log.h"
#include "kernel/yosys_common.h"
#include "kernel/sigtools.h"
#include "kernel/satgen.h"
#include "kernel/newcelltypes.h"

YOSYS_NAMESPACE_BEGIN

struct EquivBasicConfig {
	bool model_undef = false;
	int max_seq = 1;
	bool set_assumes = false;
	bool ignore_unknown_cells = false;

	bool parse(const std::vector<std::string>& args, size_t& idx) {
		if (args[idx] == "-undef") {
			model_undef = true;
			return true;
		}
		if (args[idx] == "-seq" && idx+1 < args.size()) {
			max_seq = atoi(args[++idx].c_str());
			return true;
		}
		if (args[idx] == "-set-assumes") {
			set_assumes = true;
			return true;
		}
		if (args[idx] == "-ignore-unknown-cells") {
			ignore_unknown_cells = true;
			return true;
		}
		return false;
	}
	static void help(const char* default_seq) {
		log("    -undef\n");
		log("        enable modelling of undef states\n");
		log("\n");
		log("    -seq <N>\n");
		log("        the max. number of time steps to be considered (default = %s)\n", default_seq);
		log("\n");
		log("    -set-assumes\n");
		log("        set all assumptions provided via $assume cells\n");
		log("\n");
		log("    -ignore-unknown-cells\n");
		log("        ignore all cells that can not be matched to a SAT model\n");
	}
};

template<typename Config = EquivBasicConfig>
struct EquivWorker {
	RTLIL::Module *module;

	ezSatPtr ez;
	SatGen satgen;
	Config cfg;

	EquivWorker(RTLIL::Module *module, const SigMap *sigmap, Config cfg) : module(module), satgen(ez.get(), sigmap), cfg(cfg) {
		satgen.model_undef = cfg.model_undef;
		satgen.model_barriers = true;
	}
};

YOSYS_NAMESPACE_END
#endif // EQUIV_H
