/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
#include "kernel/ffinit.h"
#include "kernel/threading.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>
#include "passes/opt/opt_clean/shared.h"
#include "passes/opt/opt_clean/keep_cache.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using RTLIL::id2cstr;

void rmunused_module(RTLIL::Module *module, ParallelDispatchThreadPool &thread_pool, bool purge_mode, bool verbose, bool rminit, CleanRunContext &clean_ctx, keep_cache_t &keep_cache)
{
	if (verbose)
		log("Finding unused cells or wires in module %s..\n", module->name);

	// Use no more than one worker per thousand cells, rounded down, so
	// we only start multithreading with at least 2000 cells.
	int num_worker_threads = ThreadPool::work_pool_size(0, module->cells_size(), 1000);
	ParallelDispatchThreadPool::Subpool subpool(thread_pool, num_worker_threads);
	remove_temporary_cells(module, subpool, verbose);
	rmunused_module_cells(module, subpool, verbose, clean_ctx, keep_cache);
	while (rmunused_module_signals(module, subpool, purge_mode, verbose, clean_ctx)) { }

	if (rminit && rmunused_module_init(module, subpool, verbose))
		while (rmunused_module_signals(module, subpool, purge_mode, verbose, clean_ctx)) { }
}
struct OptCleanPass : public Pass {
	OptCleanPass() : Pass("opt_clean", "remove unused cells and wires") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_clean [options] [selection]\n");
		log("\n");
		log("This pass identifies wires and cells that are unused and removes them. Other\n");
		log("passes often remove cells but leave the wires in the design or reconnect the\n");
		log("wires but leave the old cells in the design. This pass can be used to clean up\n");
		log("after the passes that do the actual work.\n");
		log("\n");
		log("This pass only operates on completely selected modules without processes.\n");
		log("\n");
		log("    -purge\n");
		log("        also remove internal nets if they have a public name\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool purge_mode = false;

		log_header(design, "Executing OPT_CLEAN pass (remove unused cells and wires).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge") {
				purge_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::vector<RTLIL::Module*> selected_modules;
		for (auto module : design->selected_whole_modules_warn())
			if (!module->has_processes_warn())
				selected_modules.push_back(module);
		int thread_pool_size = 0;
		for (RTLIL::Module *m : selected_modules)
			thread_pool_size = std::max(thread_pool_size, ThreadPool::work_pool_size(0, m->cells_size(), 1000));
		ParallelDispatchThreadPool thread_pool(thread_pool_size);
		keep_cache_t keep_cache(purge_mode, thread_pool, selected_modules);

		{
			CleanRunContext clean_ctx(design);
			for (auto module : selected_modules)
				rmunused_module(module, thread_pool, purge_mode, true, true, clean_ctx, keep_cache);
			clean_ctx.stats.log();

			design->optimize();
			design->check();
		}

		log_pop();

		request_garbage_collection();
	}
} OptCleanPass;

struct CleanPass : public Pass {
	CleanPass() : Pass("clean", "remove unused cells and wires") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    clean [options] [selection]\n");
		log("\n");
		log("This is identical to 'opt_clean', but less verbose.\n");
		log("\n");
		log("When commands are separated using the ';;' token, this command will be executed\n");
		log("between the commands.\n");
		log("\n");
		log("When commands are separated using the ';;;' token, this command will be executed\n");
		log("in -purge mode between the commands.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool purge_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge") {
				purge_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::vector<RTLIL::Module*> selected_modules;
		for (auto module : design->selected_unboxed_whole_modules())
			if (!module->has_processes())
				selected_modules.push_back(module);
		int thread_pool_size = 0;
		for (RTLIL::Module *m : selected_modules)
			thread_pool_size = std::max(thread_pool_size, ThreadPool::work_pool_size(0, m->cells_size(), 1000));
		ParallelDispatchThreadPool thread_pool(thread_pool_size);
		keep_cache_t keep_cache(purge_mode, thread_pool, selected_modules);

		{
			CleanRunContext clean_ctx(design);
			for (auto module : selected_modules)
				rmunused_module(module, thread_pool, purge_mode, ys_debug(), true, clean_ctx, keep_cache);

			log_suppressed();
			clean_ctx.stats.log();

			design->optimize();
			design->check();
		}

		request_garbage_collection();
	}
} CleanPass;

PRIVATE_NAMESPACE_END
