#ifndef EQUIV_H
#define EQUIV_H

#include "kernel/log.h"
#include "kernel/yosys_common.h"
#include "kernel/sigtools.h"
#include "kernel/satgen.h"

YOSYS_NAMESPACE_BEGIN

static void report_missing_model(bool warn_only, RTLIL::Cell* cell)
{
	std::string s;
	if (cell->is_builtin_ff())
		s = stringf("No SAT model available for async FF cell %s (%s).  Consider running `async2sync` or `clk2fflogic` first.\n", log_id(cell), log_id(cell->type));
	else
		s = stringf("No SAT model available for cell %s (%s).\n", log_id(cell), log_id(cell->type));

	if (warn_only) {
		log_formatted_warning_noprefix(s);
	} else {
		log_formatted_error(s);
	}
}

struct EquivWorker {
	RTLIL::Module *module;

    ezSatPtr ez;
	SatGen satgen;

    struct Config {
		bool model_undef = false;
		int max_seq = 1;
		bool set_assumes = false;

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
			, default_seq);
		}
    };
    Config cfg;

	EquivWorker(RTLIL::Module *module, const SigMap *sigmap, Config cfg) : module(module), satgen(ez.get(), sigmap), cfg(cfg) {
		satgen.model_undef = cfg.model_undef;
	}
};

YOSYS_NAMESPACE_END
#endif // EQUIV_H
