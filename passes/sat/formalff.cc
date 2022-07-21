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
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct FormalFfPass : public Pass {
	FormalFfPass() : Pass("formalff", "prepare FFs for formal") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    formalff [options] [selection]\n");
		log("\n");
		log("This pass transforms clocked flip-flops to prepare a design for formal\n");
		log("verification. If a design contains latches and/or multiple different clocks run\n");
		log("the async2sync or clk2fflogic passes before using this pass.\n");
		log("\n");
		log("    -clk2ff\n");
		log("        Replace all clocked flip-flops with $ff cells that use the implicit\n");
		log("        global clock. This assumes, without checking, that the design uses a\n");
		log("        single global clock. If that is not the case, the clk2fflogic pass\n");
		log("        should be used instead.\n");
		log("\n");
		log("    -ff2anyinit\n");
		log("        Replace uninitialized bits of $ff cells with $anyinit cells. An\n");
		log("        $anyinit cell behaves exactly like an $ff cell with an undefined\n");
		log("        initialization value. The difference is that $anyinit inhibits\n");
		log("        don't-care optimizations and is used to track solver-provided values\n");
		log("        in witness traces.\n");
		log("\n");
		log("        If combined with -clk2ff this also affects newly created $ff cells.\n");
		log("\n");
		log("    -anyinit2ff\n");
		log("        Replaces $anyinit cells with uninitialized $ff cells. This performs the\n");
		log("        reverse of -ff2anyinit and can be used, before running a backend pass\n");
		log("        (or similar) that is not yet aware of $anyinit cells.\n");
		log("\n");
		log("        Note that after running -anyinit2ff, in general, performing don't-care\n");
		log("        optimizations is not sound in a formal verification setting.\n");
		log("\n");
		log("    -fine\n");
		log("        Emit fine-grained $_FF_ cells instead of coarse-grained $ff cells for\n");
		log("        -anyinit2ff. Cannot be combined with -clk2ff or -ff2anyinit.\n");
		log("\n");

		// TODO: An option to check whether all FFs use the same clock before changing it to the global clock
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool flag_clk2ff = false;
		bool flag_ff2anyinit = false;
		bool flag_anyinit2ff = false;
		bool flag_fine = false;

		log_header(design, "Executing FORMALFF pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-clk2ff") {
				flag_clk2ff = true;
				continue;
			}
			if (args[argidx] == "-ff2anyinit") {
				flag_ff2anyinit = true;
				continue;
			}
			if (args[argidx] == "-anyinit2ff") {
				flag_anyinit2ff = true;
				continue;
			}
			if (args[argidx] == "-fine") {
				flag_fine = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!(flag_clk2ff || flag_ff2anyinit || flag_anyinit2ff))
			log_cmd_error("One of the options -clk2ff, -ff2anyinit, or -anyinit2ff must be specified.\n");

		if (flag_ff2anyinit && flag_anyinit2ff)
			log_cmd_error("The options -ff2anyinit and -anyinit2ff are exclusive.\n");

		if (flag_fine && !flag_anyinit2ff)
			log_cmd_error("The option -fine requries the -anyinit2ff option.\n");

		if (flag_fine && flag_clk2ff)
			log_cmd_error("The options -fine and -clk2ff are exclusive.\n");

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			FfInitVals initvals(&sigmap, module);


			for (auto cell : module->selected_cells())
			{
				if (flag_anyinit2ff && cell->type == ID($anyinit))
				{
					FfData ff(&initvals, cell);
					ff.remove();
					ff.is_anyinit = false;
					ff.is_fine = flag_fine;
					if (flag_fine)
						for (int i = 0; i < ff.width; i++)
							ff.slice({i}).emit();
					else
						ff.emit();

					continue;
				}

				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				FfData ff(&initvals, cell);
				bool emit = false;

				if (flag_clk2ff && ff.has_clk) {
					if (ff.sig_clk.is_fully_const())
						log_error("Const CLK on %s (%s) from module %s, run async2sync first.\n",
								log_id(cell), log_id(cell->type), log_id(module));

					ff.unmap_ce_srst();
					ff.has_clk = false;
					ff.has_gclk = true;
					emit = true;
				}

				if (!ff.has_gclk) {
					continue;
				}

				if (flag_ff2anyinit && !ff.val_init.is_fully_def())
				{
					ff.remove();
					emit = false;

					int cursor = 0;
					while (cursor < ff.val_init.size())
					{
						bool is_anyinit = ff.val_init[cursor] == State::Sx;
						std::vector<int> bits;
						bits.push_back(cursor++);
						while (cursor < ff.val_init.size() && (ff.val_init[cursor] == State::Sx) == is_anyinit)
							bits.push_back(cursor++);

						if ((int)bits.size() == ff.val_init.size()) {
							// This check is only to make the private names more helpful for debugging
							ff.is_anyinit = true;
							emit = true;
							break;
						}

						auto slice = ff.slice(bits);
						slice.is_anyinit = is_anyinit;
						slice.emit();
					}
				}

				if (emit)
					ff.emit();
			}
		}
	}
} FormalFfPass;

PRIVATE_NAMESPACE_END
