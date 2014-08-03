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
#include "kernel/modtools.h"

#include <type_traits>

USING_YOSYS_NAMESPACE
using namespace RTLIL;

PRIVATE_NAMESPACE_BEGIN

struct WreduceConfig
{
	std::set<IdString> supported_cell_types;

	WreduceConfig()
	{
		supported_cell_types.insert("$not");
		supported_cell_types.insert("$pos");
		supported_cell_types.insert("$bu0");
		supported_cell_types.insert("$neg");

		supported_cell_types.insert("$and");
		supported_cell_types.insert("$or");
		supported_cell_types.insert("$xor");
		supported_cell_types.insert("$xnor");

		supported_cell_types.insert("$shl");
		supported_cell_types.insert("$shr");
		supported_cell_types.insert("$sshl");
		supported_cell_types.insert("$sshr");
		supported_cell_types.insert("$shift");
		supported_cell_types.insert("$shiftx");

		supported_cell_types.insert("$lt");
		supported_cell_types.insert("$le");
		supported_cell_types.insert("$eq");
		supported_cell_types.insert("$ne");
		supported_cell_types.insert("$eqx");
		supported_cell_types.insert("$nex");
		supported_cell_types.insert("$ge");
		supported_cell_types.insert("$gt");

		supported_cell_types.insert("$add");
		supported_cell_types.insert("$sub");
		// supported_cell_types.insert("$mul");
		// supported_cell_types.insert("$div");
		// supported_cell_types.insert("$mod");
		// supported_cell_types.insert("$pow");

		// supported_cell_types.insert("$mux");
		// supported_cell_types.insert("$pmux");
		// supported_cell_types.insert("$safe_pmux");
	}
};

struct WreduceWorker
{
	WreduceConfig *config;
	Module *module;
	ModIndex mi;

	std::set<Cell*, IdString::compare_ptr_by_name<Cell>> work_queue_cells;
	std::set<SigBit> work_queue_bits;
	SigMap constmap;

	WreduceWorker(WreduceConfig *config, Module *module) :
			config(config), module(module), mi(module) { }

	void run_reduce_inport(Cell *cell, char port)
	{
		bool is_signed = cell->getParam(stringf("\\%c_SIGNED", port)).as_bool();
		SigSpec sig = mi.sigmap(cell->getPort(stringf("\\%c", port)));

		int bits_removed = 0;
		if (is_signed) {
			while (SIZE(sig) > 1 && constmap(sig[SIZE(sig)-1]) == constmap(sig[SIZE(sig)-2]))
				work_queue_bits.insert(sig[SIZE(sig)-1]), sig.remove(SIZE(sig)-1), bits_removed++;
		} else {
			while (SIZE(sig) > 1 && constmap(sig[SIZE(sig)-1]) == S0)
				work_queue_bits.insert(sig[SIZE(sig)-1]), sig.remove(SIZE(sig)-1), bits_removed++;
		}

		if (bits_removed) {
			log("Removed top %d bits (of %d) from port %c of cell %s.%s (%s).\n",
					bits_removed, SIZE(sig) + bits_removed, port, log_id(module), log_id(cell), log_id(cell->type));
			cell->setPort(stringf("\\%c", port), sig);
		}
	}

	void run_cell(Cell *cell)
	{
		if (config->supported_cell_types.count(cell->type) == 0)
			return;

		if (cell->type == ID("$shl") || cell->type == ID("$shr") || cell->type == ID("$sshl") || cell->type == ID("$sshr"))
			cell->setParam("\\B_SIGNED", false);

		if (cell->hasParam("\\A_SIGNED"))
			run_reduce_inport(cell, 'A');

		if (cell->hasParam("\\B_SIGNED"))
			run_reduce_inport(cell, 'B');

		SigSpec sig = mi.sigmap(cell->getPort("\\Y"));

		int bits_removed = 0;
		while (SIZE(sig) > 0) {
			auto info = mi.query(sig[SIZE(sig)-1]);
			if (info->is_output || SIZE(info->ports) > 1)
				break;
			sig.remove(SIZE(sig)-1);
			bits_removed++;
		}

		if (cell->type == ID("$not") || cell->type == ID("$pos") || cell->type == ID("$bu0") || cell->type == ID("$neg") ||
				cell->type == ID("$and") || cell->type == ID("$or") || cell->type == ID("$xor") || cell->type == ID("$xnor") ||
				cell->type == ID("$add") || cell->type == ID("$sub") || cell->type == ID("$mul"))
		{
			bool is_signed = cell->getParam("\\A_SIGNED").as_bool();

			int a_size = 0, b_size = 0;
			if (cell->hasPort("\\A")) a_size = SIZE(cell->getPort("\\A"));
			if (cell->hasPort("\\B")) b_size = SIZE(cell->getPort("\\B"));

			while (SIZE(sig) > 1 && SIZE(sig) > std::max(a_size, b_size)) {
				module->connect(sig[SIZE(sig)-1], is_signed ? sig[SIZE(sig)-2] : S0);
				sig.remove(SIZE(sig)-1);
				bits_removed++;
			}
		}

		if (bits_removed) {
			log("Removed top %d bits (of %d) from port Y of cell %s.%s (%s).\n",
					bits_removed, SIZE(sig) + bits_removed, log_id(module), log_id(cell), log_id(cell->type));
			cell->setPort("\\Y", sig);
		}

		cell->fixup_parameters();
	}

	void run()
	{
		for (auto c : module->selected_cells())
			work_queue_cells.insert(c);

		while (!work_queue_cells.empty())
		{
			work_queue_bits.clear();
			for (auto c : work_queue_cells)
				run_cell(c);

			work_queue_cells.clear();
			for (auto bit : work_queue_bits)
			for (auto port : mi.query_ports(bit))
				work_queue_cells.insert(port.cell);
		}

		std::set<SigBit> removed_wire_bits;

		for (auto w : module->selected_wires())
		{
			int bits_removed = 0;
			while (w->width > 0) {
				SigBit bit(w, w->width-1);
				auto info = mi.query(bit);
				if (info == nullptr || (!info->is_output && !info->is_input && !SIZE(info->ports))) {
					removed_wire_bits.insert(bit);
					bits_removed++;
					w->width--;
					continue;
				}
				break;
			}
			if (bits_removed)
				log("Removed top %d bits (of %d) from wire %s.%s.\n",
						bits_removed, SIZE(w) + bits_removed, log_id(module), log_id(w));
		}

		if (!removed_wire_bits.empty()) {
			std::vector<RTLIL::SigSig> new_conn = module->connections();
			for (auto &ss : new_conn) {
				SigSig new_ss;
				for (int i = 0; i < SIZE(ss.first); i++)
					if (!removed_wire_bits.count(ss.first[i]) && !removed_wire_bits.count(ss.second[i])) {
						new_ss.first.append_bit(ss.first[i]);
						new_ss.second.append_bit(ss.second[i]);
					}
				ss = std::move(new_ss);
			}
			module->new_connections(new_conn);
		}
	}
};

struct WreducePass : public Pass {
	WreducePass() : Pass("wreduce", "reduce the word size of operations is possible") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    wreduce [options] [selection]\n");
		log("\n");
		log("This command reduces the word size of operations.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, Design *design)
	{
		WreduceConfig config;

		log_header("Executing WREDCUE pass (reducing word size of cells).\n");

		log_error("FIXME: This command is under construction.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			if (module->has_processes_warn())
				continue;

			WreduceWorker worker(&config, module);
			worker.run();
		}
	}
} WreducePass;

PRIVATE_NAMESPACE_END

