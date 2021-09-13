/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Marcelina Kościelnicka <mwk@0x04.net>
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
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptMemWidenPass : public Pass {
	OptMemWidenPass() : Pass("opt_mem_widen", "optimize memories where all ports are wide") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_mem_widen [options] [selection]\n");
		log("\n");
		log("This pass looks for memories where all ports are wide and adjusts the base\n");
		log("memory width up until that stops being the case.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MEM_WIDEN pass (optimize memories where all ports are wide).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-nomux") {
			// 	mode_nomux = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto module : design->selected_modules()) {
			for (auto &mem : Mem::get_selected_memories(module)) {
				// If the memory has no read ports, opt_clean will remove it
				// instead.
				if (mem.rd_ports.empty())
					continue;
				int factor_log2 = mem.rd_ports[0].wide_log2;
				for (auto &port : mem.rd_ports)
					if (port.wide_log2 < factor_log2)
						factor_log2 = port.wide_log2;
				for (auto &port : mem.wr_ports)
					if (port.wide_log2 < factor_log2)
						factor_log2 = port.wide_log2;
				if (factor_log2 == 0)
					continue;
				log("Widening base width of memory %s in module %s by factor %d.\n", log_id(mem.memid), log_id(module->name), 1 << factor_log2);
				total_count++;
				// The inits are too messy to expand one-by-one, for they may
				// collide with one another after expansion.  Just hit it with
				// a hammer.
				bool has_init = !mem.inits.empty();
				Const init_data;
				if (has_init) {
					init_data = mem.get_init_data();
					mem.clear_inits();
				}
				mem.width <<= factor_log2;
				mem.size >>= factor_log2;
				mem.start_offset >>= factor_log2;
				if (has_init) {
					MemInit new_init;
					new_init.addr = mem.start_offset;
					new_init.data = init_data;
					new_init.en = Const(State::S1, mem.width);
					mem.inits.push_back(new_init);
				}
				for (auto &port : mem.rd_ports) {
					port.wide_log2 -= factor_log2;
					port.addr = port.addr.extract_end(factor_log2);
				}
				for (auto &port : mem.wr_ports) {
					port.wide_log2 -= factor_log2;
					port.addr = port.addr.extract_end(factor_log2);
				}
				mem.emit();
			}
		}

		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Performed a total of %d transformations.\n", total_count);
	}
} OptMemWidenPass;

PRIVATE_NAMESPACE_END
