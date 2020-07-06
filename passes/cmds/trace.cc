/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2014  Johann Glaser <Johann.Glaser@gmx.at>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TraceMonitor : public RTLIL::Monitor
{
	void notify_module_add(RTLIL::Module *module) YS_OVERRIDE
	{
		log("#TRACE# Module add: %s\n", log_id(module));
	}

	void notify_module_del(RTLIL::Module *module) YS_OVERRIDE
	{
		log("#TRACE# Module delete: %s\n", log_id(module));
	}

	void notify_connect(RTLIL::Cell *cell, const RTLIL::IdString &port, const RTLIL::SigSpec &old_sig, RTLIL::SigSpec &sig) YS_OVERRIDE
	{
		log("#TRACE# Cell connect: %s.%s.%s = %s (was: %s)\n", log_id(cell->module), log_id(cell), log_id(port), log_signal(sig), log_signal(old_sig));
	}

	void notify_connect(RTLIL::Module *module, const RTLIL::SigSig &sigsig) YS_OVERRIDE
	{
		log("#TRACE# Connection in module %s: %s = %s\n", log_id(module), log_signal(sigsig.first), log_signal(sigsig.second));
	}

	void notify_connect(RTLIL::Module *module, const std::vector<RTLIL::SigSig> &sigsig_vec) YS_OVERRIDE
	{
		log("#TRACE# New connections in module %s:\n", log_id(module));
		for (auto &sigsig : sigsig_vec)
			log("##    %s = %s\n", log_signal(sigsig.first), log_signal(sigsig.second));
	}

	void notify_blackout(RTLIL::Module *module) YS_OVERRIDE
	{
		log("#TRACE# Blackout in module %s:\n", log_id(module));
	}
};

struct TracePass : public Pass {
	TracePass() : Pass("trace", "redirect command output to file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    trace cmd\n");
		log("\n");
		log("Execute the specified command, logging all changes the command performs on\n");
		log("the design in real time.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// .. parse options ..
			break;
		}

		TraceMonitor monitor;
		design->monitors.insert(&monitor);

		try {
			std::vector<std::string> new_args(args.begin() + argidx, args.end());
			Pass::call(design, new_args);
		} catch (...) {
			design->monitors.erase(&monitor);
			throw;
		}

		design->monitors.erase(&monitor);
	}
} TracePass;

struct DebugPass : public Pass {
	DebugPass() : Pass("debug", "run command with debug log messages enabled") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    debug cmd\n");
		log("\n");
		log("Execute the specified command with debug log messages enabled\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// .. parse options ..
			break;
		}

		log_force_debug++;

		try {
			std::vector<std::string> new_args(args.begin() + argidx, args.end());
			Pass::call(design, new_args);
		} catch (...) {
			log_force_debug--;
			throw;
		}

		log_force_debug--;
	}
} DebugPass;

PRIVATE_NAMESPACE_END
