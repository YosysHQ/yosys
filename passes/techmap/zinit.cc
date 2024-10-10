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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ZinitPass : public Pass {
	ZinitPass() : Pass("zinit", "add inverters so all FF are zero-initialized") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    zinit [options] [selection]\n");
		log("\n");
		log("Add inverters as needed to make all FFs zero-initialized.\n");
		log("\n");
		log("    -all\n");
		log("        also add zero initialization to uninitialized FFs\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool all_mode = false;

		log_header(design, "Executing ZINIT pass (make all FFs zero-initialized).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-all") {
				all_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			FfInitVals initvals(&sigmap, module);

			for (auto cell : module->selected_cells())
			{
				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				FfData ff(&initvals, cell);

				log("FF init value for cell %s (%s): %s = %s\n", log_id(cell), log_id(cell->type),
						log_signal(ff.sig_q), log_signal(ff.val_init));

				pool<int> bits;
				for (int i = 0; i < ff.width; i++) {
					if (ff.val_init[i] == State::S1)
						bits.insert(i);
					else if (ff.val_init[i] != State::S0 && all_mode)
						ff.val_init.bits()[i] = State::S0;
				}
				ff.flip_bits(bits);
				ff.emit();
			}
		}
	}
} ZinitPass;

PRIVATE_NAMESPACE_END
