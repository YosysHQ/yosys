/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2023  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

#include "kernel/celltypes.h"
#include "kernel/ff.h"
#include "kernel/ffinit.h"
#include "kernel/modtools.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"
#include "kernel/yosys.h"
#include <deque>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct FutureOptions {
};

struct FutureWorker {
	Module *module;
	FutureOptions options;
	ModWalker modwalker;
	SigMap &sigmap;
	FfInitVals initvals;

	dict<SigBit, SigBit> future_ff_signals;

	FutureWorker(Module *module, FutureOptions options) :
		module(module), options(options), modwalker(module->design), sigmap(modwalker.sigmap)
	{
		modwalker.setup(module);
		initvals.set(&modwalker.sigmap, module);

		std::vector<Cell *> replaced_cells;
		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($future_ff))
				continue;

			module->connect(cell->getPort(ID::Y), future_ff(cell->getPort(ID::A)));
			replaced_cells.push_back(cell);
		}

		for (auto cell : replaced_cells) {
			module->remove(cell);
		}
	}

	SigSpec future_ff(SigSpec sig)
	{
		for (auto &bit : sig) {
			bit = future_ff(bit);
		}
		return sig;
	}

	SigBit future_ff(SigBit bit)
	{
		if (!bit.is_wire())
			return bit;

		auto found = future_ff_signals.find(bit);
		if (found != future_ff_signals.end())
			return found->second;

		auto found_driver = modwalker.signal_drivers.find(bit);
		if (found_driver == modwalker.signal_drivers.end() || found_driver->second.size() < 1)
			log_error("No driver for future_ff target signal %s found\n", log_signal(bit));
		if (found_driver->second.size() > 1)
			log_error("Found multiple drivers for future_ff target signal %s\n", log_signal(bit));
		auto driver = *found_driver->second.begin();
		if (!RTLIL::builtin_ff_cell_types().count(driver.cell->type) && driver.cell->type != ID($anyinit))
			log_error("Driver for future_ff target signal %s has non-FF cell type %s\n", log_signal(bit), log_id(driver.cell->type));

		FfData ff(&initvals, driver.cell);

		if (!ff.has_clk && !ff.has_gclk)
			log_error("Driver for future_ff target signal %s has cell type %s, which is not clocked\n", log_signal(bit),
				  log_id(driver.cell->type));

		ff.unmap_ce_srst();

		// We insert all bits into the mapping, because unmap_ce_srst might
		// have removed the cell which is still present in the modwalker data.
		// By inserting all bits driven by th FF we ensure that we'll never use
		// that stale modwalker data again.

		for (int i = 0; i < ff.width; ++i) {
			future_ff_signals.emplace(ff.sig_q[i], ff.sig_d[i]);
		}

		return future_ff_signals.at(bit);
	}
};

struct FuturePass : public Pass {
	FuturePass() : Pass("future", "resolve future sampled value functions") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    future [options] [selection]\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		FutureOptions options;

		log_header(design, "Executing FUTURE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {

			break;
		}

		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			FutureWorker worker(module, options);
		}
	}
} FuturePass;

PRIVATE_NAMESPACE_END
