/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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

struct BwmuxmapPass : public Pass {
	BwmuxmapPass() : Pass("bwmuxmap", "replace $bwmux cells with equivalent logic") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    bwmxumap [options] [selection]\n");
		log("\n");
		log("This pass replaces $bwmux cells with equivalent logic\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing BWMUXMAP pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-arg") {
			// 	continue;
			// }
			break;
		}

		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		for (auto cell : module->selected_cells())
		{
			if (cell->type != ID($bwmux))
				continue;
			auto &sig_y = cell->getPort(ID::Y);
			auto &sig_a = cell->getPort(ID::A);
			auto &sig_b = cell->getPort(ID::B);
			auto &sig_s = cell->getPort(ID::S);

			auto not_s = module->Not(NEW_ID, sig_s);
			auto masked_b = module->And(NEW_ID, sig_s, sig_b);
			auto masked_a = module->And(NEW_ID, not_s, sig_a);
			module->addOr(NEW_ID, masked_a, masked_b, sig_y);

			module->remove(cell);
		}
	}
} BwmuxmapPass;

PRIVATE_NAMESPACE_END
