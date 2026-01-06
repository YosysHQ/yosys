/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Marcelina Kościelnicka <mwk@0x04.net>
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
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryNarrowPass : public Pass {
	MemoryNarrowPass() : Pass("memory_narrow", "split up wide memory ports") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_narrow [options] [selection]\n");
		log("\n");
		log("This pass splits up wide memory ports into several narrow ports.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing MEMORY_NARROW pass (splitting up wide memory ports).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;

			for (auto &mem : Mem::get_selected_memories(module))
			{
				bool wide = false;
				for (auto &port : mem.rd_ports)
					if (port.wide_log2)
						wide = true;
				for (auto &port : mem.wr_ports)
					if (port.wide_log2)
						wide = true;
				if (wide) {
					mem.narrow();
					mem.emit();
				}
			}
		}
	}
} MemoryNarrowPass;

PRIVATE_NAMESPACE_END
