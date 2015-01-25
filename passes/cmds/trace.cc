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
	virtual void notify_module_add(RTLIL::Module *module) YS_OVERRIDE
	{
		log("#TRACE# Module add: %s\n", log_id(module));
	}

	virtual void notify_module_del(RTLIL::Module *module) YS_OVERRIDE
	{
		log("#TRACE# Module delete: %s\n", log_id(module));
	}

	virtual void notify_connect(RTLIL::Cell *cell, const RTLIL::IdString &port, const RTLIL::SigSpec &old_sig, RTLIL::SigSpec &sig) YS_OVERRIDE
	{
		log("#TRACE# Cell connect: %s.%s.%s = %s (was: %s)\n", log_id(cell->module), log_id(cell), log_id(port), log_signal(sig), log_signal(old_sig));
	}

	virtual void notify_connect(RTLIL::Module *module, const RTLIL::SigSig &sigsig) YS_OVERRIDE
	{
		log("#TRACE# Connection in module %s: %s = %s\n", log_id(module), log_signal(sigsig.first), log_signal(sigsig.second));
	}

	virtual void notify_connect(RTLIL::Module *module, const std::vector<RTLIL::SigSig> &sigsig_vec) YS_OVERRIDE
	{
		log("#TRACE# New connections in module %s:\n", log_id(module));
		for (auto &sigsig : sigsig_vec)
			log("##    %s = %s\n", log_signal(sigsig.first), log_signal(sigsig.second));
	}

	virtual void notify_blackout(RTLIL::Module *module) YS_OVERRIDE
	{
		log("#TRACE# Blackout in module %s:\n", log_id(module));
	}
};

struct TracePass : public Pass {
	TracePass() : Pass("trace", "redirect command output to file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    trace cmd\n");
		log("\n");
		log("Execute the specified command, logging all changes the command performs on\n");
		log("the design in real time.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
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

PRIVATE_NAMESPACE_END

