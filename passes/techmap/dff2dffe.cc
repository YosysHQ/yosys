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

struct Dff2dffeWorker
{
	RTLIL::Module *module;
	SigMap sigmap;

	Dff2dffeWorker(RTLIL::Module *module) : module(module), sigmap(module)
	{
	}

	void run()
	{
		log("Transforming $dff to $dffe cells in module %s:\n", log_id(module));
	}
};

struct Dff2dffePass : public Pass {
	Dff2dffePass() : Pass("dff2dffe", "transform $dff cells to $dffe cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dff2dffe [selection]\n");
		log("\n");
		log("This pass transforms $dff cells driven by a tree of multiplexers with one or\n");
		log("more feedback paths to a $dffe cells.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing DFF2DFFE pass (transform $dff to $dffe where applicable).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-foobar") {
			// 	foobar_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules())
			if (!mod->has_processes_warn()) {
				Dff2dffeWorker worker(mod);
				worker.run();
			}
	}
} Dff2dffePass;
 
PRIVATE_NAMESPACE_END
