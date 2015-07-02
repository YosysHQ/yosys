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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ScatterPass : public Pass {
	ScatterPass() : Pass("scatter", "add additional intermediate nets") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    scatter [selection]\n");
		log("\n");
		log("This command adds additional intermediate nets on all cell ports. This is used\n");
		log("for testing the correct use of the SigMap helper in passes. If you don't know\n");
		log("what this means: don't worry -- you only need this pass when testing your own\n");
		log("extensions to Yosys.\n");
		log("\n");
		log("Use the opt_clean command to get rid of the additional nets.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		CellTypes ct(design);
		extra_args(args, 1, design);

		for (auto &mod_it : design->modules_)
		{
			if (!design->selected(mod_it.second))
				continue;

			for (auto &c : mod_it.second->cells_)
			for (auto &p : c.second->connections_)
			{
				RTLIL::Wire *wire = mod_it.second->addWire(NEW_ID, p.second.size());

				if (ct.cell_output(c.second->type, p.first)) {
					RTLIL::SigSig sigsig(p.second, wire);
					mod_it.second->connect(sigsig);
				} else {
					RTLIL::SigSig sigsig(wire, p.second);
					mod_it.second->connect(sigsig);
				}

				p.second = wire;
			}
		}
	}
} ScatterPass;

PRIVATE_NAMESPACE_END
