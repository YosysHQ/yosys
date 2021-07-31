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
#include "kernel/mem.h"
#include "kernel/ff.h"
#include "kernel/ffmerge.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryDffWorker
{
	Module *module;
	SigMap sigmap;
	FfInitVals initvals;
	FfMergeHelper merger;

	MemoryDffWorker(Module *module) : module(module), sigmap(module)
	{
		initvals.set(&sigmap, module);
		merger.set(&initvals, module);
	}

	void handle_rd_port(Mem &mem, int idx)
	{
		auto &port = mem.rd_ports[idx];
		log("Checking read port `%s'[%d] in module `%s': ", mem.memid.c_str(), idx, module->name.c_str());

		FfData ff;
		pool<std::pair<Cell *, int>> bits;
		if (!merger.find_output_ff(port.data, ff, bits)) {
			log("no output FF found.\n");
			return;
		}
		if (!ff.has_clk) {
			log("output latches are not supported.\n");
			return;
		}
		if (ff.has_sr) {
			// Latches and FFs with SR are not supported.
			log("output FF has both set and reset, not supported.\n");
			return;
		}
		if (ff.has_srst || ff.has_arst || !ff.val_init.is_fully_undef()) {
			// TODO: not supported yet
			log("output FF has reset and/or init value, not supported yet.\n");
			return;
		}
		merger.remove_output_ff(bits);
		if (ff.has_en && !ff.pol_en)
			ff.sig_en = module->LogicNot(NEW_ID, ff.sig_en);
		if (ff.has_arst && !ff.pol_arst)
			ff.sig_arst = module->LogicNot(NEW_ID, ff.sig_arst);
		if (ff.has_srst && !ff.pol_srst)
			ff.sig_srst = module->LogicNot(NEW_ID, ff.sig_srst);
		port.clk = ff.sig_clk;
		port.clk_enable = true;
		port.clk_polarity = ff.pol_clk;
		if (ff.has_en)
			port.en = ff.sig_en;
		else
			port.en = State::S1;
#if 0
		if (ff.has_arst) {
			port.arst = ff.sig_arst;
			port.arst_value = ff.val_arst;
		} else {
			port.arst = State::S0;
		}
		if (ff.has_srst) {
			port.srst = ff.sig_srst;
			port.srst_value = ff.val_srst;
			port.ce_over_srst = ff.ce_over_srst;
		} else {
			port.srst = State::S0;
		}
		port.init_value = ff.val_init;
#endif
		port.data = ff.sig_q;
		mem.emit();
		log("merged output FF to cell.\n");
	}

	void handle_rd_port_addr(Mem &mem, int idx)
	{
		auto &port = mem.rd_ports[idx];
		log("Checking read port address `%s'[%d] in module `%s': ", mem.memid.c_str(), idx, module->name.c_str());

		FfData ff;
		pool<std::pair<Cell *, int>> bits;
		if (!merger.find_input_ff(port.addr, ff, bits)) {
			log("no address FF found.\n");
			return;
		}
		if (!ff.has_clk) {
			log("address latches are not supported.\n");
			return;
		}
		if (ff.has_sr || ff.has_arst) {
			log("address FF has async set and/or reset, not supported.\n");
			return;
		}
		// Trick part: this transform is invalid if the initial
		// value of the FF is fully-defined.  However, we
		// cannot simply reject FFs with any defined init bit,
		// as this is often the result of merging a const bit.
		if (ff.val_init.is_fully_def()) {
			log("address FF has fully-defined init value, not supported.\n");
			return;
		}
		for (int i = 0; i < GetSize(mem.wr_ports); i++) {
			auto &wport = mem.wr_ports[i];
			if (!wport.clk_enable || wport.clk != ff.sig_clk || wport.clk_polarity != ff.pol_clk) {
				log("address FF clock is not compatible with write clock.\n");
				return;
			}
		}
		// Now we're commited to merge it.
		merger.mark_input_ff(bits);
		// If the address FF has enable and/or sync reset, unmap it.
		ff.unmap_ce_srst(module);
		port.clk = ff.sig_clk;
		port.en = State::S1;
		port.addr = ff.sig_d;
		port.clk_enable = true;
		port.clk_polarity = ff.pol_clk;
		for (int i = 0; i < GetSize(mem.wr_ports); i++)
			port.transparency_mask[i] = true;
		mem.emit();
		log("merged address FF to cell.\n");
	}

	void run()
	{
		std::vector<Mem> memories = Mem::get_selected_memories(module);
		for (auto &mem : memories) {
			for (int i = 0; i < GetSize(mem.rd_ports); i++) {
				if (!mem.rd_ports[i].clk_enable)
					handle_rd_port(mem, i);
			}
		}
		for (auto &mem : memories) {
			for (int i = 0; i < GetSize(mem.rd_ports); i++) {
				if (!mem.rd_ports[i].clk_enable)
					handle_rd_port_addr(mem, i);
			}
		}
	}
};

struct MemoryDffPass : public Pass {
	MemoryDffPass() : Pass("memory_dff", "merge input/output DFFs into memory read ports") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_dff [options] [selection]\n");
		log("\n");
		log("This pass detects DFFs at memory read ports and merges them into the memory port.\n");
		log("I.e. it consumes an asynchronous memory port and the flip-flops at its\n");
		log("interface and yields a synchronous memory port.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing MEMORY_DFF pass (merging $dff cells to $memrd).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			MemoryDffWorker worker(mod);
			worker.run();
		}
	}
} MemoryDffPass;

PRIVATE_NAMESPACE_END
