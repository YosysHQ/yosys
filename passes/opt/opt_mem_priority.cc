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
#include "kernel/modtools.h"
#include "kernel/qcsat.h"
#include "kernel/mem.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptMemPriorityPass : public Pass {
	OptMemPriorityPass() : Pass("opt_mem_priority", "remove priority relations between write ports that can never collide") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_mem_priority [selection]\n");
		log("\n");
		log("This pass detects cases where one memory write port has priority over another\n");
		log("even though they can never collide with each other -- ie. there can never be\n");
		log("a situation where a given memory bit is written by both ports at the same\n");
		log("time, for example because of always-different addresses, or mutually exclusive\n");
		log("enable signals. In such cases, the priority relation is removed.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_MEM_PRIORITY pass (removing unnecessary memory write priority relations).\n");
		extra_args(args, 1, design);

		ModWalker modwalker(design);

		int total_count = 0;
		for (auto module : design->selected_modules()) {
			modwalker.setup(module);
			for (auto &mem : Mem::get_selected_memories(module)) {
				bool mem_changed = false;
				QuickConeSat qcsat(modwalker);
				for (int i = 0; i < GetSize(mem.wr_ports); i++) {
					auto &wport1 = mem.wr_ports[i];
					for (int j = 0; j < GetSize(mem.wr_ports); j++) {
						auto &wport2 = mem.wr_ports[j];
						if (!wport1.priority_mask[j])
							continue;
						// No mixed width support — we could do it, but
						// that would complicate code and wouldn't help
						// anything since we run this pass before
						// wide ports are created in normal flow.
						if (wport1.wide_log2 != wport2.wide_log2)
							continue;
						// Two ports with priority, let's go.
						pool<std::pair<SigBit, SigBit>> checked;
						SigSpec addr1 = wport1.addr;
						SigSpec addr2 = wport2.addr;
						int abits = std::max(GetSize(addr1), GetSize(addr2));
						addr1.extend_u0(abits);
						addr2.extend_u0(abits);
						int addr_eq = qcsat.ez->vec_eq(qcsat.importSig(addr1), qcsat.importSig(addr2));
						bool ok = true;
						for (int k = 0; k < GetSize(wport1.data); k++) {
							SigBit wen1 = wport1.en[k];
							SigBit wen2 = wport2.en[k];
							if (checked.count({wen1, wen2}))
								continue;
							int wen1_sat = qcsat.importSigBit(wen1);
							int wen2_sat = qcsat.importSigBit(wen2);
							qcsat.prepare();
							if (qcsat.ez->solve(wen1_sat, wen2_sat, addr_eq)) {
								ok = false;
								break;
							}
							checked.insert({wen1, wen2});
						}
						if (ok) {
							total_count++;
							mem_changed = true;
							wport1.priority_mask[j] = false;
						}
					}
				}
				if (mem_changed)
					mem.emit();
			}
		}

		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Performed a total of %d transformations.\n", total_count);
	}
} OptMemPriorityPass;

PRIVATE_NAMESPACE_END

