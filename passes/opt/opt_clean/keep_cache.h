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

#ifndef OPT_CLEAN_KEEP_CACHE_H
#define OPT_CLEAN_KEEP_CACHE_H

YOSYS_NAMESPACE_BEGIN

struct keep_cache_t
{
	dict<Module*, bool> keep_modules;
	bool purge_mode;

	keep_cache_t(bool purge_mode, ParallelDispatchThreadPool &thread_pool, const std::vector<RTLIL::Module *> &selected_modules)
			: purge_mode(purge_mode) {

		std::vector<RTLIL::Module *> scan_modules_worklist;
		dict<RTLIL::Module *, std::vector<RTLIL::Module*>> dependents;
		std::vector<RTLIL::Module *> propagate_kept_modules_worklist;
		for (RTLIL::Module *module : selected_modules) {
			if (keep_modules.count(module))
				continue;
			bool keep = scan_module(module, thread_pool, dependents, ALL_CELLS, scan_modules_worklist);
			keep_modules[module] = keep;
			if (keep)
				propagate_kept_modules_worklist.push_back(module);
		}

		while (!scan_modules_worklist.empty()) {
			RTLIL::Module *module = scan_modules_worklist.back();
			scan_modules_worklist.pop_back();
			if (keep_modules.count(module))
				continue;
			bool keep = scan_module(module, thread_pool, dependents, MINIMUM_CELLS, scan_modules_worklist);
			keep_modules[module] = keep;
			if (keep)
				propagate_kept_modules_worklist.push_back(module);
		}

		while (!propagate_kept_modules_worklist.empty()) {
			RTLIL::Module *module = propagate_kept_modules_worklist.back();
			propagate_kept_modules_worklist.pop_back();
			for (RTLIL::Module *dependent : dependents[module]) {
				if (keep_modules[dependent])
					continue;
				keep_modules[dependent] = true;
				propagate_kept_modules_worklist.push_back(dependent);
			}
		}
	}

	bool query(Cell *cell) const
	{
		if (keep_cell(cell, purge_mode))
			return true;
		if (cell->type.in(ID($specify2), ID($specify3), ID($specrule)))
			return true;
		if (cell->module && cell->module->design) {
			RTLIL::Module *cell_module = cell->module->design->module(cell->type);
			return cell_module != nullptr && keep_modules.at(cell_module);
		}
		return false;
	}

private:
	enum ScanCells {
		// Scan every cell to see if it uses a module that is kept.
		ALL_CELLS,
		// Stop scanning cells if we determine early that this module is kept.
		MINIMUM_CELLS,
	};
	bool scan_module(Module *module, ParallelDispatchThreadPool &thread_pool, dict<RTLIL::Module *, std::vector<RTLIL::Module*>> &dependents,
			ScanCells scan_cells, std::vector<Module*> &worklist) const
	{
		MonotonicFlag keep_module;
		if (module->get_bool_attribute(ID::keep)) {
			if (scan_cells == MINIMUM_CELLS)
				return true;
			keep_module.set();
		}

		ParallelDispatchThreadPool::Subpool subpool(thread_pool, ThreadPool::work_pool_size(0, module->cells_size(), 1000));
		ShardedVector<Module*> deps(subpool);
		const RTLIL::Module *const_module = module;
		bool purge_mode = this->purge_mode;
		subpool.run([purge_mode, const_module, scan_cells, &deps, &keep_module](const ParallelDispatchThreadPool::RunCtx &ctx) {
			bool keep = false;
			for (int i : ctx.item_range(const_module->cells_size())) {
				Cell *cell = const_module->cell_at(i);
				if (keep_cell(cell, purge_mode)) {
					if (scan_cells == MINIMUM_CELLS) {
						keep_module.set();
						return;
					}
					keep = true;
				}
				if (const_module->design) {
					RTLIL::Module *cell_module = const_module->design->module(cell->type);
					if (cell_module != nullptr)
						deps.insert(ctx, cell_module);
				}
			}
			if (keep) {
				keep_module.set();
				return;
			}
			for (int i : ctx.item_range(const_module->wires_size())) {
				Wire *wire = const_module->wire_at(i);
				if (wire->get_bool_attribute(ID::keep)) {
					keep_module.set();
					return;
				}
			}
		});
		if (scan_cells == MINIMUM_CELLS && keep_module.load())
			return true;
		for (Module *dep : deps) {
			dependents[dep].push_back(module);
			worklist.push_back(dep);
		}
		return keep_module.load();
	}

	static bool keep_cell(Cell *cell, bool purge_mode)
	{
		if (cell->type.in(ID($assert), ID($assume), ID($live), ID($fair), ID($cover)))
			return true;

		if (cell->type.in(ID($overwrite_tag)))
			return true;

		if (cell->type == ID($print) || cell->type == ID($check))
			return true;

		if (cell->has_keep_attr())
			return true;

		if (!purge_mode && cell->type == ID($scopeinfo))
			return true;
		return false;
	}
};

YOSYS_NAMESPACE_END
#endif /* OPT_CLEAN_KEEP_CACHE_H */
