/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Marcelina Kościelnicka <mwk@0x04.net>
 *  Copyright (C) 2022  Matt Johnston <matt@codeconstruct.com.au>
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

struct OptMemMergePass : public Pass {
	OptMemMergePass() : Pass("opt_mem_merge", "merge memories to use write enable bits") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_mem_merge [options] [selection]\n");
		log("\n");
		log("This pass merges memories that share a common write port source.\n");
		log("They are combined to a single memory with write enable bits.\n");
		log("It is useful in situations such as GHDL input which may not infer write\n");
		log("enable bits.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MEM_MERGE pass (merge memories to use write enable bits).\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules()) {
			dict<SigSpec, std::vector<Mem*>> addr_mem;
			// collect wr ports with same address lines
			auto mems = Mem::get_selected_memories(module);
			for (auto &mem : mems) {

				// log("   trying mem %s\n", mem.memid.str().c_str());
				if (!(GetSize(mem.rd_ports) == 1
					&& GetSize(mem.wr_ports) == 1
					&& GetSize(mem.inits) <= 1)) {
					// log("   mem %s wrong param\n", mem.memid.str().c_str());
					// for now we work with just single read/write port for simplicity
					continue;
				}

				addr_mem[mem.wr_ports.at(0).addr].push_back(&mem);
			}

			// log("addr_mem %zu entries\n", addr_mem.size());
			for (auto &i : addr_mem) {
				size_t n_merg = i.second.size();
				for (auto &m : i.second) {
					// log("   mem %s\n", m->memid.str().c_str());
				}
				if (n_merg < 2) {
					// log("   only 1 addr, no merge\n");
					continue;
				}

				// TODO: check that parameters are all the same.
				auto & m0 = *i.second.front();
				auto & w0 = m0.wr_ports.at(0);
				auto & r0 = m0.rd_ports.at(0);
				for (auto &m : i.second) {
					auto &w = m->wr_ports.at(0);
					auto &r = m->rd_ports.at(0);
					// TODO: instead use a comparison method in MemWr and MemRd.
					// Should compare everything except data/(en for Wr)?
					// Need matching MemInit.addr
					if (!(
						w.clk == w0.clk
						&& m->width == m0.width
						&& w.data.size() == w0.data.size()
						&& r.data.size() == r0.data.size()
						)) {
						// log("   mem %s mismatch\n", m0.memid.str().c_str());
						goto donegroup;
					}
				}
				if (0) {
					donegroup:
					continue;
				}


				if (GetSize(m0.inits) > 0) {
					auto & i0 = m0.inits.at(0);
					Const new_init_data(0, i0.data.size() * n_merg);
					// interleave old-width chunks from separate inits
					int ostride = m0.width * n_merg;
					for (size_t j = 0; j < n_merg; j++) {
						int offs = j * m0.width;
						auto & ini = i.second.at(j)->inits.at(0);
						auto ib = ini.data.begin();
						for (int k = 0; k < ini.data.size() / m0.width; k++) {
							for (int b = 0; b < m0.width; b++) {
								new_init_data[offs + k*ostride + b] = *ib;
								++ib;
							}
						}
					}
					i0.data = new_init_data;
				}

				for (size_t j = 1; j < n_merg; j++) {
					auto &m = *i.second.at(j);
					auto & wp = m.wr_ports.at(0);
					auto & rp = m.rd_ports.at(0);
					w0.data.append(wp.data);
					w0.en.append(wp.en);

					r0.data.append(rp.data);
					std::copy(rp.arst_value.begin(), rp.arst_value.end(),
						std::back_inserter(r0.arst_value.bits));
					std::copy(rp.srst_value.begin(), rp.srst_value.end(),
						std::back_inserter(r0.srst_value.bits));
					std::copy(rp.init_value.begin(), rp.init_value.end(),
						std::back_inserter(r0.init_value.bits));

					log(" rd  mem %s append %d %d new width %d %d\n",
						m.memid.str().c_str(), GetSize(rp.data), rp.data.size(),
						GetSize(r0.data), r0.data.size());
				}
				m0.width *= n_merg;
				log("   mem %s new width %d\n", m0.memid.str().c_str(), m0.width);
				w0.wide_log2 = ceil_log2(GetSize(w0.data) / m0.width);
				r0.wide_log2 = ceil_log2(GetSize(r0.data) / m0.width);

				for (size_t j = 1; j < n_merg; j++) {
					auto &m = *i.second.at(j);
					m.remove();
				}
				m0.emit();
			}
		}

	}
} OptMemMergePass;

PRIVATE_NAMESPACE_END
