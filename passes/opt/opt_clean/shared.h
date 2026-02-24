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

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/threading.h"
#include "kernel/celltypes.h"
#include "kernel/yosys_common.h"
#include "passes/opt/opt_clean/keep_cache.h"

#ifndef OPT_CLEAN_SHARED_H
#define OPT_CLEAN_SHARED_H

YOSYS_NAMESPACE_BEGIN


struct AnalysisContext {
	SigMap assign_map;
	const RTLIL::Module *mod;
	ParallelDispatchThreadPool::Subpool &subpool;
	AnalysisContext(RTLIL::Module* m, ParallelDispatchThreadPool::Subpool &p) : assign_map(m), mod(m), subpool(p) {}
};

struct RmStats {
	int count_rm_cells = 0;
	int count_rm_wires = 0;

	void log()
	{
		if (count_rm_cells > 0 || count_rm_wires > 0)
			YOSYS_NAMESPACE_PREFIX log("Removed %d unused cells and %d unused wires.\n", count_rm_cells, count_rm_wires);
	}
};

struct Flags {
	bool purge = false;
	bool verbose = false;
};
struct CleanRunContext {
	CellTypes ct_reg;
	CellTypes ct_all;
	RmStats stats;
	ParallelDispatchThreadPool thread_pool;
	std::vector<RTLIL::Module*> selected_modules;
	keep_cache_t keep_cache;
	Flags flags;

private:
	// Helper to compute thread pool size
	static int compute_thread_pool_size(RTLIL::Design* design) {
		int thread_pool_size = 0;
		for (auto module : design->selected_unboxed_whole_modules())
			if (!module->has_processes())
				thread_pool_size = std::max(thread_pool_size,
					ThreadPool::work_pool_size(0, module->cells_size(), 1000));
		return thread_pool_size;
	}

	static std::vector<RTLIL::Module*> get_selected_modules(RTLIL::Design* design) {
		std::vector<RTLIL::Module*> modules;
		for (auto module : design->selected_unboxed_whole_modules())
			if (!module->has_processes())
				modules.push_back(module);
		return modules;
	}

public:
	CleanRunContext(RTLIL::Design* design, Flags f)
		: thread_pool(compute_thread_pool_size(design)),
		selected_modules(get_selected_modules(design)),
		keep_cache(f.purge, thread_pool, selected_modules),
		flags(f)
	{
		ct_reg.setup_internals_mem();
		ct_reg.setup_internals_anyinit();
		ct_reg.setup_stdcells_mem();
		ct_all.setup(design);
	}

	~CleanRunContext() {
		ct_reg.clear();
		ct_all.clear();
	}
};

void remove_temporary_cells(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose);
void rmunused_module_cells(Module *module, ParallelDispatchThreadPool::Subpool &subpool, CleanRunContext &clean_ctx);
bool rmunused_module_signals(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, CleanRunContext &clean_ctx);
bool rmunused_module_init(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose);

YOSYS_NAMESPACE_END

#endif /* OPT_CLEAN_SHARED_H */
