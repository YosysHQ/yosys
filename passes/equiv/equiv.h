#ifndef EQUIV_H
#define EQUIV_H

#include "kernel/log.h"
#include "kernel/yosys_common.h"
#include "kernel/sigtools.h"
#include "kernel/satgen.h"

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
	static std::string help(const char* default_seq) {
		return stringf(
		"    -undef\n"
		"        enable modelling of undef states\n"
		"\n"
		"    -seq <N>\n"
		"        the max. number of time steps to be considered (default = %s)\n"
		"\n"
		"    -set-assumes\n"
		"        set all assumptions provided via $assume cells\n"
		"\n"
		"    -ignore-unknown-cells\n"
		"        ignore all cells that can not be matched to a SAT model\n"
		, default_seq);
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
	}
};

YOSYS_NAMESPACE_END
#endif // EQUIV_H
