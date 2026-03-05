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
#include "kernel/threading.h"
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
	static constexpr auto ct_reg = StaticCellTypes::Categories::join(
		StaticCellTypes::Compat::mem_ff,
		StaticCellTypes::categories.is_anyinit);
	NewCellTypes ct_all;
	RmStats stats;
	ParallelDispatchThreadPool thread_pool;
	KeepCache keep_cache;
	Flags flags;

private:
	// Helper to compute thread pool size
	static int compute_thread_pool_size(const std::vector<RTLIL::Module*>& selected_modules) {
		int thread_pool_size = 0;
		for (auto module : selected_modules)
			thread_pool_size = std::max(thread_pool_size,
				ThreadPool::work_pool_size(0, module->cells_size(), 1000));
		return thread_pool_size;
	}

public:
	CleanRunContext(RTLIL::Design* design, const std::vector<RTLIL::Module*>& selected_modules, Flags f)
		: thread_pool(compute_thread_pool_size(selected_modules)),
		keep_cache(f.purge, thread_pool, selected_modules),
		flags(f)
	{
		ct_all.setup(design);
	}

	~CleanRunContext() {
		ct_all.clear();
	}
};

void remove_temporary_cells(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose);
void rmunused_module_cells(Module *module, ParallelDispatchThreadPool::Subpool &subpool, CleanRunContext &clean_ctx);
bool rmunused_module_signals(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, CleanRunContext &clean_ctx);
bool rmunused_module_init(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose);

YOSYS_NAMESPACE_END

#endif /* OPT_CLEAN_SHARED_H */
