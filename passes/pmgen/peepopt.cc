/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool did_something;
dict<SigBit, State> initbits;
pool<SigBit> rminitbits;

#include "passes/pmgen/peepopt_pm.h"
#include "generate.h"

struct PeepoptPass : public Pass {
	PeepoptPass() : Pass("peepopt", "collection of peephole optimizers") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    peepopt [options] [selection]\n");
		log("\n");
		log("This pass applies a collection of peephole optimizers to the current design.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string genmode;

		log_header(design, "Executing PEEPOPT pass (run peephole optimizers).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-generate" && argidx+1 < args.size()) {
				genmode = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!genmode.empty())
		{
			initbits.clear();
			rminitbits.clear();

			if (genmode == "shiftmul")
				GENERATE_PATTERN(peepopt_pm, shiftmul);
			else if (genmode == "muldiv")
				GENERATE_PATTERN(peepopt_pm, muldiv);
			else if (genmode == "dffmux")
				GENERATE_PATTERN(peepopt_pm, dffmux);
			else
				log_abort();
			return;
		}

		for (auto module : design->selected_modules())
		{
			did_something = true;

			while (did_something)
			{
				did_something = false;
				initbits.clear();
				rminitbits.clear();

				peepopt_pm pm(module);

				for (auto w : module->wires()) {
					auto it = w->attributes.find(ID(init));
					if (it != w->attributes.end()) {
						SigSpec sig = pm.sigmap(w);
						Const val = it->second;
						int len = std::min(GetSize(sig), GetSize(val));
						for (int i = 0; i < len; i++) {
							if (sig[i].wire == nullptr)
								continue;
							if (val[i] != State::S0 && val[i] != State::S1)
								continue;
							initbits[sig[i]] = val[i];
						}
					}
				}

				pm.setup(module->selected_cells());

				pm.run_shiftmul();
				pm.run_muldiv();
				pm.run_dffmux();

				for (auto w : module->wires()) {
					auto it = w->attributes.find(ID(init));
					if (it != w->attributes.end()) {
						SigSpec sig = pm.sigmap(w);
						Const &val = it->second;
						int len = std::min(GetSize(sig), GetSize(val));
						for (int i = 0; i < len; i++) {
							if (rminitbits.count(sig[i]))
								val[i] = State::Sx;
						}
					}
				}

				initbits.clear();
				rminitbits.clear();
			}
		}
	}
} PeepoptPass;

PRIVATE_NAMESPACE_END
