#ifndef PROC_DLATCH_H
#define PROC_DLATCH_H

#include "kernel/yosys_common.h"
#include "kernel/log.h"

YOSYS_NAMESPACE_BEGIN

enum class LatchPolicy {
	Info,
	Warn,
	Error
};

inline bool latch_policy_from_string(const std::string &str, LatchPolicy &policy)
{
	if (str == "info")
		policy = LatchPolicy::Info;
	else if (str == "warn")
		policy = LatchPolicy::Warn;
	else if (str == "error")
		policy = LatchPolicy::Error;
	else
		return false;
	return true;
}

inline const char *latch_policy_str(LatchPolicy policy)
{
	switch (policy) {
	case LatchPolicy::Info: return "info";
	case LatchPolicy::Warn: return "warn";
	default: return "error";
	}
}

// shared -latches option handling for synth_* passes
struct SynthLatchesConfig {
	LatchPolicy policy = LatchPolicy::Error;

	bool parse(const std::vector<std::string> &args, size_t &idx)
	{
		if (args[idx] == "-latches" && idx+1 < args.size()) {
			if (!latch_policy_from_string(args[++idx], policy))
				log_cmd_error("Invalid value '%s' for -latches (expected info|warn|error).\n", args[idx].c_str());
			return true;
		}
		return false;
	}

	const char *str() const { return latch_policy_str(policy); }

	static const char *help()
	{
		return
		"    -latches <info|warn|error>\n"
		"        select the behaviour for latches that cannot be mapped to a\n"
		"        dedicated hardware primitive and are implemented using LUTs\n"
		"        instead. 'error' (the default) aborts synthesis, 'warn' only\n"
		"        prints a warning, and 'info' permits them with an info-level message.\n"
		"        Latches explicitly requested with 'always_latch' are always permitted.\n";
	}
};

YOSYS_NAMESPACE_END

#endif
