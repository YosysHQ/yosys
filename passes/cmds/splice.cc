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
#include "kernel/sigtools.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
#include <tuple>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SpliceWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;

	bool sel_by_cell;
	bool sel_by_wire;
	bool sel_any_bit;
	bool no_outputs;
	bool do_wires;

	std::set<RTLIL::IdString> ports;
	std::set<RTLIL::IdString> no_ports;

	CellTypes ct;
	SigMap sigmap;

	std::vector<RTLIL::SigBit> driven_bits;
	std::map<RTLIL::SigBit, int> driven_bits_map;

	std::set<RTLIL::SigSpec> driven_chunks;
	std::map<RTLIL::SigSpec, RTLIL::SigSpec> spliced_signals_cache;
	std::map<RTLIL::SigSpec, RTLIL::SigSpec> sliced_signals_cache;

	SpliceWorker(RTLIL::Design *design, RTLIL::Module *module) : design(design), module(module), ct(design), sigmap(module)
	{
	}

	RTLIL::SigSpec get_sliced_signal(RTLIL::SigSpec sig)
	{
		if (sig.size() == 0 || sig.is_fully_const())
			return sig;

		if (sliced_signals_cache.count(sig))
			return sliced_signals_cache.at(sig);

		int offset = 0;
		int p = driven_bits_map.at(sig.extract(0, 1).as_bit()) - 1;
		while (driven_bits.at(p) != RTLIL::State::Sm)
			p--, offset++;

		RTLIL::SigSpec sig_a;
		for (p++; driven_bits.at(p) != RTLIL::State::Sm; p++)
			sig_a.append(driven_bits.at(p));

		RTLIL::SigSpec new_sig = sig;

		if (sig_a.size() != sig.size()) {
			RTLIL::Cell *cell = module->addCell(NEW_ID, "$slice");
			cell->parameters["\\OFFSET"] = offset;
			cell->parameters["\\A_WIDTH"] = sig_a.size();
			cell->parameters["\\Y_WIDTH"] = sig.size();
			cell->setPort("\\A", sig_a);
			cell->setPort("\\Y", module->addWire(NEW_ID, sig.size()));
			new_sig = cell->getPort("\\Y");
		}

		sliced_signals_cache[sig] = new_sig;

		return new_sig;
	}

	RTLIL::SigSpec get_spliced_signal(RTLIL::SigSpec sig)
	{
		if (sig.size() == 0 || sig.is_fully_const())
			return sig;

		if (spliced_signals_cache.count(sig))
			return spliced_signals_cache.at(sig);

		int last_bit = -1;
		std::vector<RTLIL::SigSpec> chunks;

		for (auto &bit : sig.to_sigbit_vector())
		{
			if (bit.wire == NULL)
			{
				if (last_bit == 0)
					chunks.back().append(bit);
				else
					chunks.push_back(bit);
				last_bit = 0;
				continue;
			}

			if (driven_bits_map.count(bit))
			{
				int this_bit = driven_bits_map.at(bit);
				if (last_bit+1 == this_bit)
					chunks.back().append(bit);
				else
					chunks.push_back(bit);
				last_bit = this_bit;
				continue;
			}

			log("  Failed to generate spliced signal %s.\n", log_signal(sig));
			spliced_signals_cache[sig] = sig;
			return sig;
		}


		RTLIL::SigSpec new_sig = get_sliced_signal(chunks.front());
		for (size_t i = 1; i < chunks.size(); i++) {
			RTLIL::SigSpec sig2 = get_sliced_signal(chunks[i]);
			RTLIL::Cell *cell = module->addCell(NEW_ID, "$concat");
			cell->parameters["\\A_WIDTH"] = new_sig.size();
			cell->parameters["\\B_WIDTH"] = sig2.size();
			cell->setPort("\\A", new_sig);
			cell->setPort("\\B", sig2);
			cell->setPort("\\Y", module->addWire(NEW_ID, new_sig.size() + sig2.size()));
			new_sig = cell->getPort("\\Y");
		}

		spliced_signals_cache[sig] = new_sig;

		log("  Created spliced signal: %s -> %s\n", log_signal(sig), log_signal(new_sig));
		return new_sig;
	}

	void run()
	{
		log("Splicing signals in module %s:\n", RTLIL::id2cstr(module->name));

		driven_bits.push_back(RTLIL::State::Sm);
		driven_bits.push_back(RTLIL::State::Sm);

		for (auto &it : module->wires_)
			if (it.second->port_input) {
				RTLIL::SigSpec sig = sigmap(it.second);
				driven_chunks.insert(sig);
				for (auto &bit : sig.to_sigbit_vector())
					driven_bits.push_back(bit);
				driven_bits.push_back(RTLIL::State::Sm);
			}

		for (auto &it : module->cells_)
		for (auto &conn : it.second->connections())
			if (!ct.cell_known(it.second->type) || ct.cell_output(it.second->type, conn.first)) {
				RTLIL::SigSpec sig = sigmap(conn.second);
				driven_chunks.insert(sig);
				for (auto &bit : sig.to_sigbit_vector())
					driven_bits.push_back(bit);
				driven_bits.push_back(RTLIL::State::Sm);
			}

		driven_bits.push_back(RTLIL::State::Sm);

		for (size_t i = 0; i < driven_bits.size(); i++)
			driven_bits_map[driven_bits[i]] = i;

		SigPool selected_bits;
		if (!sel_by_cell)
			for (auto &it : module->wires_)
				if (design->selected(module, it.second))
					selected_bits.add(sigmap(it.second));

		std::vector<Cell*> mod_cells = module->cells();

		for (auto cell : mod_cells) {
			if (!sel_by_wire && !design->selected(module, cell))
				continue;
			for (auto &conn : cell->connections_)
				if (ct.cell_input(cell->type, conn.first)) {
					if (ports.size() > 0 && !ports.count(conn.first))
						continue;
					if (no_ports.size() > 0 && no_ports.count(conn.first))
						continue;
					RTLIL::SigSpec sig = sigmap(conn.second);
					if (!sel_by_cell) {
						if (!sel_any_bit && !selected_bits.check_all(sig))
							continue;
						if (sel_any_bit && !selected_bits.check_any(sig))
							continue;
					}
					if (driven_chunks.count(sig) > 0)
						continue;
					conn.second = get_spliced_signal(sig);
				}
		}

		std::vector<std::pair<RTLIL::Wire*, RTLIL::SigSpec>> rework_wires;
		std::vector<Wire*> mod_wires = module->wires();

		for (auto wire : mod_wires)
			if ((!no_outputs && wire->port_output) || (do_wires && wire->name[0] == '\\')) {
				if (!design->selected(module, wire))
					continue;
				RTLIL::SigSpec sig = sigmap(wire);
				if (driven_chunks.count(sig) > 0)
					continue;
				RTLIL::SigSpec new_sig = get_spliced_signal(sig);
				if (new_sig != sig)
					rework_wires.push_back(std::pair<RTLIL::Wire*, RTLIL::SigSpec>(wire, new_sig));
			} else
			if (!wire->port_input) {
				RTLIL::SigSpec sig = sigmap(wire);
				if (spliced_signals_cache.count(sig) && spliced_signals_cache.at(sig) != sig)
					rework_wires.push_back(std::pair<RTLIL::Wire*, RTLIL::SigSpec>(wire, spliced_signals_cache.at(sig)));
				else if (sliced_signals_cache.count(sig) && sliced_signals_cache.at(sig) != sig)
					rework_wires.push_back(std::pair<RTLIL::Wire*, RTLIL::SigSpec>(wire, sliced_signals_cache.at(sig)));
			}

		for (auto &it : rework_wires)
		{
			RTLIL::IdString orig_name = it.first->name;
			module->rename(it.first, NEW_ID);

			RTLIL::Wire *new_port = module->addWire(orig_name, it.first);
			it.first->port_id = 0;
			it.first->port_input = false;
			it.first->port_output = false;

			module->connect(RTLIL::SigSig(new_port, it.second));
		}
	}
};

struct SplicePass : public Pass {
	SplicePass() : Pass("splice", "create explicit splicing cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    splice [options] [selection]\n");
		log("\n");
		log("This command adds $slice and $concat cells to the design to make the splicing\n");
		log("of multi-bit signals explicit. This for example is useful for coarse grain\n");
		log("synthesis, where dedicated hardware is needed to splice signals.\n");
		log("\n");
		log("    -sel_by_cell\n");
		log("        only select the cell ports to rewire by the cell. if the selection\n");
		log("        contains a cell, than all cell inputs are rewired, if necessary.\n");
		log("\n");
		log("    -sel_by_wire\n");
		log("        only select the cell ports to rewire by the wire. if the selection\n");
		log("        contains a wire, than all cell ports driven by this wire are wired,\n");
		log("        if necessary.\n");
		log("\n");
		log("    -sel_any_bit\n");
		log("        it is sufficient if the driver of any bit of a cell port is selected.\n");
		log("        by default all bits must be selected.\n");
		log("\n");
		log("    -wires\n");
		log("        also add $slice and $concat cells to drive otherwise unused wires.\n");
		log("\n");
		log("    -no_outputs\n");
		log("        do not rewire selected module outputs.\n");
		log("\n");
		log("    -port <name>\n");
		log("        only rewire cell ports with the specified name. can be used multiple\n");
		log("        times. implies -no_output.\n");
		log("\n");
		log("    -no_port <name>\n");
		log("        do not rewire cell ports with the specified name. can be used multiple\n");
		log("        times. can not be combined with -port <name>.\n");
		log("\n");
		log("By default selected output wires and all cell ports of selected cells driven\n");
		log("by selected wires are rewired.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool sel_by_cell = false;
		bool sel_by_wire = false;
		bool sel_any_bit = false;
		bool no_outputs = false;
		bool do_wires = false;
		std::set<RTLIL::IdString> ports, no_ports;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-sel_by_cell") {
				sel_by_cell = true;
				continue;
			}
			if (args[argidx] == "-sel_by_wire") {
				sel_by_wire = true;
				continue;
			}
			if (args[argidx] == "-sel_any_bit") {
				sel_any_bit = true;
				continue;
			}
			if (args[argidx] == "-wires") {
				do_wires = true;
				continue;
			}
			if (args[argidx] == "-no_outputs") {
				no_outputs = true;
				continue;
			}
			if (args[argidx] == "-port" && argidx+1 < args.size()) {
				ports.insert(RTLIL::escape_id(args[++argidx]));
				no_outputs = true;
				continue;
			}
			if (args[argidx] == "-no_port" && argidx+1 < args.size()) {
				no_ports.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (sel_by_cell && sel_by_wire)
			log_cmd_error("The options -sel_by_cell and -sel_by_wire are exclusive!\n");

		if (sel_by_cell && sel_any_bit)
			log_cmd_error("The options -sel_by_cell and -sel_any_bit are exclusive!\n");

		if (!ports.empty() && !no_ports.empty())
			log_cmd_error("The options -port and -no_port are exclusive!\n");

		log_header(design, "Executing SPLICE pass (creating cells for signal splicing).\n");

		for (auto &mod_it : design->modules_)
		{
			if (!design->selected(mod_it.second))
				continue;

			if (mod_it.second->processes.size()) {
				log("Skipping module %s as it contains processes.\n", mod_it.second->name.c_str());
				continue;
			}

			SpliceWorker worker(design, mod_it.second);
			worker.sel_by_cell = sel_by_cell;
			worker.sel_by_wire = sel_by_wire;
			worker.sel_any_bit = sel_any_bit;
			worker.no_outputs = no_outputs;
			worker.do_wires = do_wires;
			worker.ports = ports;
			worker.no_ports = no_ports;
			worker.run();
		}
	}
} SplicePass;

PRIVATE_NAMESPACE_END
