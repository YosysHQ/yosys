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

State invert(State s) {
	switch (s) {
		case State::S0: return State::S1;
		case State::S1: return State::S0;
		default: return s;
	}
}

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
				if (!ff.width)
					continue;

				// Supporting those would require a new cell type where S has priority over R.
				if (ff.has_sr)
					continue;

				Wire *new_q = module->addWire(NEW_ID, ff.width);

				log("FF init value for cell %s (%s): %s = %s\n", log_id(cell), log_id(cell->type),
						log_signal(ff.sig_q), log_signal(ff.val_init));

				IdString name = cell->name;
				module->remove(cell);
				initvals.remove_init(ff.sig_q);

				for (int i = 0; i < ff.width; i++)
					if (ff.val_init[i] == State::S1)
					{
						if (ff.has_clk || ff.has_gclk)
							ff.sig_d[i] = module->NotGate(NEW_ID, ff.sig_d[i]);
						if (ff.has_aload)
							ff.sig_ad[i] = module->NotGate(NEW_ID, ff.sig_ad[i]);
						if (ff.has_arst)
							ff.val_arst[i] = invert(ff.val_arst[i]);
						if (ff.has_srst)
							ff.val_srst[i] = invert(ff.val_srst[i]);
						module->addNotGate(NEW_ID, SigSpec(new_q, i), ff.sig_q[i]);
						ff.val_init[i] = State::S0;
					}
					else
					{
						module->connect(ff.sig_q[i], SigSpec(new_q, i));
						if (all_mode)
							ff.val_init[i] = State::S0;
					}

				ff.sig_q = new_q;
				ff.emit(module, name);
			}
		}
	}
} ZinitPass;

PRIVATE_NAMESPACE_END
