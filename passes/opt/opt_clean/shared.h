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

struct CleanRunContext {
	CellTypes ct_reg;
	CellTypes ct_all;
	RmStats stats;
	CleanRunContext(RTLIL::Design* design) {
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

struct keep_cache_t;
void remove_temporary_cells(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose);
void rmunused_module_cells(Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose, CleanRunContext &clean_ctx, keep_cache_t &keep_cache);
bool rmunused_module_signals(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool purge_mode, bool verbose, CleanRunContext &clean_ctx);
bool rmunused_module_init(RTLIL::Module *module, ParallelDispatchThreadPool::Subpool &subpool, bool verbose);

YOSYS_NAMESPACE_END

#endif /* OPT_CLEAN_SHARED_H */
