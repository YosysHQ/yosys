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

USING_YOSYS_NAMESPACE
using namespace RTLIL;

PRIVATE_NAMESPACE_BEGIN

struct WreduceConfig
{
	pool<IdString> supported_cell_types;

	WreduceConfig()
	{
		supported_cell_types = pool<IdString>({
			"$not", "$pos", "$neg",
			"$and", "$or", "$xor", "$xnor",
			"$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx",
			"$lt", "$le", "$eq", "$ne", "$eqx", "$nex", "$ge", "$gt",
			"$add", "$sub", "$mul", // "$div", "$mod", "$pow",
			"$mux", "$pmux"
		});
	}
};

struct WreduceWorker
{
	WreduceConfig *config;
	Module *module;
	ModIndex mi;

	std::set<Cell*, IdString::compare_ptr_by_name<Cell>> work_queue_cells;
	std::set<SigBit> work_queue_bits;
	pool<SigBit> keep_bits;

	WreduceWorker(WreduceConfig *config, Module *module) :
			config(config), module(module), mi(module) { }

	void run_cell_mux(Cell *cell)
	{
		// Reduce size of MUX if inputs agree on a value for a bit or a output bit is unused

		SigSpec sig_a = mi.sigmap(cell->getPort("\\A"));
		SigSpec sig_b = mi.sigmap(cell->getPort("\\B"));
		SigSpec sig_s = mi.sigmap(cell->getPort("\\S"));
		SigSpec sig_y = mi.sigmap(cell->getPort("\\Y"));
		std::vector<SigBit> bits_removed;

		if (sig_y.has_const())
			return;

		for (int i = GetSize(sig_y)-1; i >= 0; i--)
		{
			auto info = mi.query(sig_y[i]);
			if (!info->is_output && GetSize(info->ports) <= 1 && !keep_bits.count(mi.sigmap(sig_y[i]))) {
				bits_removed.push_back(Sx);
				continue;
			}

			SigBit ref = sig_a[i];
			for (int k = 0; k < GetSize(sig_s); k++) {
				if (ref != Sx && sig_b[k*GetSize(sig_a) + i] != Sx && ref != sig_b[k*GetSize(sig_a) + i])
					goto no_match_ab;
				if (sig_b[k*GetSize(sig_a) + i] != Sx)
					ref = sig_b[k*GetSize(sig_a) + i];
			}
			if (0)
		no_match_ab:
				break;
			bits_removed.push_back(ref);
		}

		if (bits_removed.empty())
			return;

		SigSpec sig_removed;
		for (int i = GetSize(bits_removed)-1; i >= 0; i--)
			sig_removed.append_bit(bits_removed[i]);

		if (GetSize(bits_removed) == GetSize(sig_y)) {
			log("Removed cell %s.%s (%s).\n", log_id(module), log_id(cell), log_id(cell->type));
			module->connect(sig_y, sig_removed);
			module->remove(cell);
			return;
		}

		log("Removed top %d bits (of %d) from mux cell %s.%s (%s).\n",
				GetSize(sig_removed), GetSize(sig_y), log_id(module), log_id(cell), log_id(cell->type));

		int n_removed = GetSize(sig_removed);
		int n_kept = GetSize(sig_y) - GetSize(sig_removed);

		SigSpec new_work_queue_bits;
		new_work_queue_bits.append(sig_a.extract(n_kept, n_removed));
		new_work_queue_bits.append(sig_y.extract(n_kept, n_removed));

		SigSpec new_sig_a = sig_a.extract(0, n_kept);
		SigSpec new_sig_y = sig_y.extract(0, n_kept);
		SigSpec new_sig_b;

		for (int k = 0; k < GetSize(sig_s); k++) {
			new_sig_b.append(sig_b.extract(k*GetSize(sig_a), n_kept));
			new_work_queue_bits.append(sig_b.extract(k*GetSize(sig_a) + n_kept, n_removed));
		}

		for (auto bit : new_work_queue_bits)
			work_queue_bits.insert(bit);

		cell->setPort("\\A", new_sig_a);
		cell->setPort("\\B", new_sig_b);
		cell->setPort("\\Y", new_sig_y);
		cell->fixup_parameters();

		module->connect(sig_y.extract(n_kept, n_removed), sig_removed);
	}

	void run_reduce_inport(Cell *cell, char port, int max_port_size, bool &port_signed, bool &did_something)
	{
		port_signed = cell->getParam(stringf("\\%c_SIGNED", port)).as_bool();
		SigSpec sig = mi.sigmap(cell->getPort(stringf("\\%c", port)));

		if (port == 'B' && cell->type.in("$shl", "$shr", "$sshl", "$sshr"))
			port_signed = false;

		int bits_removed = 0;
		if (GetSize(sig) > max_port_size) {
			bits_removed = GetSize(sig) - max_port_size;
			for (auto bit : sig.extract(max_port_size, bits_removed))
				work_queue_bits.insert(bit);
			sig = sig.extract(0, max_port_size);
		}

		if (port_signed) {
			while (GetSize(sig) > 1 && sig[GetSize(sig)-1] == sig[GetSize(sig)-2])
				work_queue_bits.insert(sig[GetSize(sig)-1]), sig.remove(GetSize(sig)-1), bits_removed++;
		} else {
			while (GetSize(sig) > 1 && sig[GetSize(sig)-1] == S0)
				work_queue_bits.insert(sig[GetSize(sig)-1]), sig.remove(GetSize(sig)-1), bits_removed++;
		}

		if (bits_removed) {
			log("Removed top %d bits (of %d) from port %c of cell %s.%s (%s).\n",
					bits_removed, GetSize(sig) + bits_removed, port, log_id(module), log_id(cell), log_id(cell->type));
			cell->setPort(stringf("\\%c", port), sig);
			did_something = true;
		}
	}

	void run_cell(Cell *cell)
	{
		bool did_something = false;

		if (!cell->type.in(config->supported_cell_types))
			return;

		if (cell->type.in("$mux", "$pmux"))
			return run_cell_mux(cell);

		SigSpec sig = mi.sigmap(cell->getPort("\\Y"));

		if (sig.has_const())
			return;


		// Reduce size of ports A and B based on constant input bits and size of output port

		int max_port_a_size = cell->hasPort("\\A") ? GetSize(cell->getPort("\\A")) : -1;
		int max_port_b_size = cell->hasPort("\\B") ? GetSize(cell->getPort("\\B")) : -1;

		if (cell->type.in("$not", "$pos", "$neg", "$and", "$or", "$xor", "$add", "$sub")) {
			max_port_a_size = min(max_port_a_size, GetSize(sig));
			max_port_b_size = min(max_port_b_size, GetSize(sig));
		}

		bool port_a_signed = false;
		bool port_b_signed = false;

		if (max_port_a_size >= 0 && cell->type != "$shiftx")
			run_reduce_inport(cell, 'A', max_port_a_size, port_a_signed, did_something);

		if (max_port_b_size >= 0)
			run_reduce_inport(cell, 'B', max_port_b_size, port_b_signed, did_something);

		if (cell->hasPort("\\A") && cell->hasPort("\\B") && port_a_signed && port_b_signed) {
			SigSpec sig_a = mi.sigmap(cell->getPort("\\A")), sig_b = mi.sigmap(cell->getPort("\\B"));
			if (GetSize(sig_a) > 0 && sig_a[GetSize(sig_a)-1] == State::S0 &&
					GetSize(sig_b) > 0 && sig_b[GetSize(sig_b)-1] == State::S0) {
				log("Converting cell %s.%s (%s) from signed to unsigned.\n",
						log_id(module), log_id(cell), log_id(cell->type));
				cell->setParam("\\A_SIGNED", 0);
				cell->setParam("\\B_SIGNED", 0);
				port_a_signed = false;
				port_b_signed = false;
				did_something = true;
			}
		}

		if (cell->hasPort("\\A") && !cell->hasPort("\\B") && port_a_signed) {
			SigSpec sig_a = mi.sigmap(cell->getPort("\\A"));
			if (GetSize(sig_a) > 0 && sig_a[GetSize(sig_a)-1] == State::S0) {
				log("Converting cell %s.%s (%s) from signed to unsigned.\n",
						log_id(module), log_id(cell), log_id(cell->type));
				cell->setParam("\\A_SIGNED", 0);
				port_a_signed = false;
				did_something = true;
			}
		}


		// Reduce size of port Y based on sizes for A and B and unused bits in Y

		int bits_removed = 0;
		if (port_a_signed && cell->type == "$shr") {
			// do not reduce size of output on $shr cells with signed A inputs
		} else {
			while (GetSize(sig) > 0)
			{
				auto info = mi.query(sig[GetSize(sig)-1]);

				if (info->is_output || GetSize(info->ports) > 1)
					break;

				sig.remove(GetSize(sig)-1);
				bits_removed++;
			}
		}

		if (cell->type.in("$pos", "$add", "$mul", "$and", "$or", "$xor"))
		{
			bool is_signed = cell->getParam("\\A_SIGNED").as_bool();

			int a_size = 0, b_size = 0;
			if (cell->hasPort("\\A")) a_size = GetSize(cell->getPort("\\A"));
			if (cell->hasPort("\\B")) b_size = GetSize(cell->getPort("\\B"));

			int max_y_size = max(a_size, b_size);

			if (cell->type == "$add")
				max_y_size++;

			if (cell->type == "$mul")
				max_y_size = a_size + b_size;

			while (GetSize(sig) > 1 && GetSize(sig) > max_y_size) {
				module->connect(sig[GetSize(sig)-1], is_signed ? sig[GetSize(sig)-2] : S0);
				sig.remove(GetSize(sig)-1);
				bits_removed++;
			}
		}

		if (GetSize(sig) == 0) {
			log("Removed cell %s.%s (%s).\n", log_id(module), log_id(cell), log_id(cell->type));
			module->remove(cell);
			return;
		}

		if (bits_removed) {
			log("Removed top %d bits (of %d) from port Y of cell %s.%s (%s).\n",
					bits_removed, GetSize(sig) + bits_removed, log_id(module), log_id(cell), log_id(cell->type));
			cell->setPort("\\Y", sig);
			did_something = true;
		}

		if (did_something) {
			cell->fixup_parameters();
			run_cell(cell);
		}
	}

	static int count_nontrivial_wire_attrs(RTLIL::Wire *w)
	{
		int count = w->attributes.size();
		count -= w->attributes.count("\\src");
		count -= w->attributes.count("\\unused_bits");
		return count;
	}

	void run()
	{
		for (auto w : module->wires())
			if (w->get_bool_attribute("\\keep"))
				for (auto bit : mi.sigmap(w))
					keep_bits.insert(bit);

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
				if (module->selected(port.cell))
					work_queue_cells.insert(port.cell);
		}

		pool<SigSpec> complete_wires;
		for (auto w : module->wires())
			complete_wires.insert(mi.sigmap(w));

		for (auto w : module->selected_wires())
		{
			int unused_top_bits = 0;

			if (w->port_id > 0 || count_nontrivial_wire_attrs(w) > 0)
				continue;

			for (int i = GetSize(w)-1; i >= 0; i--) {
				SigBit bit(w, i);
				auto info = mi.query(bit);
				if (info && (info->is_input || info->is_output || GetSize(info->ports) > 0))
					break;
				unused_top_bits++;
			}

			if (unused_top_bits == 0 || unused_top_bits == GetSize(w))
				continue;

			if (complete_wires[mi.sigmap(w).extract(0, GetSize(w) - unused_top_bits)])
				continue;

			log("Removed top %d bits (of %d) from wire %s.%s.\n", unused_top_bits, GetSize(w), log_id(module), log_id(w));
			Wire *nw = module->addWire(NEW_ID, GetSize(w) - unused_top_bits);
			module->connect(nw, SigSpec(w).extract(0, GetSize(nw)));
			module->swap_names(w, nw);
		}
	}
};

struct WreducePass : public Pass {
	WreducePass() : Pass("wreduce", "reduce the word size of operations if possible") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    wreduce [options] [selection]\n");
		log("\n");
		log("This command reduces the word size of operations. For example it will replace\n");
		log("the 32 bit adders in the following code with adders of more appropriate widths:\n");
		log("\n");
		log("    module test(input [3:0] a, b, c, output [7:0] y);\n");
		log("        assign y = a + b + c + 1;\n");
		log("    endmodule\n");
		log("\n");
		log("Options:\n");
		log("\n");
		log("    -memx\n");
		log("        Do not change the width of memory address ports. Use this options in\n");
		log("        flows that use the 'memory_memx' pass.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, Design *design)
	{
		WreduceConfig config;
		bool opt_memx = false;

		log_header(design, "Executing WREDUCE pass (reducing word size of cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-memx") {
				opt_memx = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			if (module->has_processes_warn())
				continue;

			for (auto c : module->selected_cells())
			{
				if (c->type.in("$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor", "$reduce_bool",
						"$lt", "$le", "$eq", "$ne", "$eqx", "$nex", "$ge", "$gt",
						"$logic_not", "$logic_and", "$logic_or") && GetSize(c->getPort("\\Y")) > 1) {
					SigSpec sig = c->getPort("\\Y");
					if (!sig.has_const()) {
						c->setPort("\\Y", sig[0]);
						c->setParam("\\Y_WIDTH", 1);
						sig.remove(0);
						module->connect(sig, Const(0, GetSize(sig)));
					}
				}
				if (!opt_memx && c->type.in("$memrd", "$memwr", "$meminit")) {
					IdString memid = c->getParam("\\MEMID").decode_string();
					RTLIL::Memory *mem = module->memories.at(memid);
					if (mem->start_offset >= 0) {
						int cur_addrbits = c->getParam("\\ABITS").as_int();
						int max_addrbits = ceil_log2(mem->start_offset + mem->size);
						if (cur_addrbits > max_addrbits) {
							log("Removed top %d address bits (of %d) from memory %s port %s.%s (%s).\n",
									cur_addrbits-max_addrbits, cur_addrbits,
									c->type == "$memrd" ? "read" : c->type == "$memwr" ? "write" : "init",
									log_id(module), log_id(c), log_id(memid));
							c->setParam("\\ABITS", max_addrbits);
							c->setPort("\\ADDR", c->getPort("\\ADDR").extract(0, max_addrbits));
						}
					}
				}
			}

			WreduceWorker worker(&config, module);
			worker.run();
		}
	}
} WreducePass;

PRIVATE_NAMESPACE_END

