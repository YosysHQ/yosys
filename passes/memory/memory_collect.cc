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
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryCollectPass : public Pass {
	MemoryCollectPass() : Pass("memory_collect", "creating multi-port memory cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_collect [selection]\n");
		log("\n");
		log("This pass collects memories and memory ports and creates generic multiport\n");
		log("memory cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing MEMORY_COLLECT pass (generating $mem cells).\n");
		extra_args(args, 1, design);
		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;

			for (auto &mem : Mem::get_selected_memories(module)) {
				if (!mem.packed) {
					mem.packed = true;
					mem.emit();
				}
			}
		}
	}
} MemoryCollectPass;

PRIVATE_NAMESPACE_END
