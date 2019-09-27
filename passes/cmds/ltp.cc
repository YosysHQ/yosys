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
#include "kernel/celltypes.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct LtpWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap;

	dict<SigBit, tuple<int, SigBit, Cell*>> bits;
	dict<SigBit, dict<SigBit, Cell*>> bit2bits;
	dict<SigBit, tuple<SigBit, Cell*>> bit2ff;

	int maxlvl;
	SigBit maxbit;
	pool<SigBit> busy;

	LtpWorker(RTLIL::Module *module, bool noff) : design(module->design), module(module), sigmap(module)
	{
		CellTypes ff_celltypes;

		if (noff) {
			ff_celltypes.setup_internals_mem();
			ff_celltypes.setup_stdcells_mem();
		}

		for (auto wire : module->selected_wires())
			for (auto bit : sigmap(wire))
				bits[bit] = tuple<int, SigBit, Cell*>(-1, State::Sx, nullptr);

		for (auto cell : module->selected_cells())
		{
			pool<SigBit> src_bits, dst_bits;

			for (auto &conn : cell->connections())
				for (auto bit : sigmap(conn.second)) {
					if (cell->input(conn.first))
						src_bits.insert(bit);
					if (cell->output(conn.first))
						dst_bits.insert(bit);
				}

			if (noff && ff_celltypes.cell_known(cell->type)) {
				for (auto s : src_bits)
					for (auto d : dst_bits) {
						bit2ff[s] = tuple<SigBit, Cell*>(d, cell);
						break;
					}
				continue;
			}

			for (auto s : src_bits)
				for (auto d : dst_bits)
					bit2bits[s][d] = cell;
		}

		maxlvl = -1;
		maxbit = State::Sx;
	}

	void runner(SigBit bit, int level, SigBit from, Cell *via)
	{
		auto &bitinfo = bits.at(bit);

		if (get<0>(bitinfo) >= level)
			return;

		if (busy.count(bit) > 0) {
			log_warning("Detected loop at %s in %s\n", log_signal(bit), log_id(module));
			return;
		}

		busy.insert(bit);
		get<0>(bitinfo) = level;
		get<1>(bitinfo) = from;
		get<2>(bitinfo) = via;

		if (level > maxlvl) {
			maxlvl = level;
			maxbit = bit;
		}

		if (bit2bits.count(bit)) {
			for (auto &it : bit2bits.at(bit))
				runner(it.first, level+1, bit, it.second);
		}

		busy.erase(bit);
	}

	void printpath(SigBit bit)
	{
		auto &bitinfo = bits.at(bit);
		if (get<2>(bitinfo)) {
			printpath(get<1>(bitinfo));
			log("%5d: %s (via %s)\n", get<0>(bitinfo), log_signal(bit), log_id(get<2>(bitinfo)));
		} else {
			log("%5d: %s\n", get<0>(bitinfo), log_signal(bit));
		}
	}

	void run()
	{
		for (auto &it : bits)
			if (get<0>(it.second) < 0)
				runner(it.first, 0, State::Sx, nullptr);

		log("\n");
		log("Longest topological path in %s (length=%d):\n", log_id(module), maxlvl);

		if (maxlvl >= 0)
			printpath(maxbit);

		if (bit2ff.count(maxbit))
			log("%5s: %s (via %s)\n", "ff", log_signal(get<0>(bit2ff.at(maxbit))), log_id(get<1>(bit2ff.at(maxbit))));
	}
};

struct LtpPass : public Pass {
	LtpPass() : Pass("ltp", "print longest topological path") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ltp [options] [selection]\n");
		log("\n");
		log("This command prints the longest topological path in the design. (Only considers\n");
		log("paths within a single module, so the design must be flattened.)\n");
		log("\n");
		log("    -noff\n");
		log("        automatically exclude FF cell types\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool noff = false;

		log_header(design, "Executing LTP pass (find longest path).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-noff") {
				noff = true;
				continue;
			}
			break;
		}

		extra_args(args, argidx, design);

		for (Module *module : design->selected_modules())
		{
			if (module->has_processes_warn())
				continue;

			LtpWorker worker(module, noff);
			worker.run();
		}
	}
} LtpPass;

PRIVATE_NAMESPACE_END
