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

struct SpliceWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;

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
		if (sig.width == 0 || sig.is_fully_const())
			return sig;

		if (sliced_signals_cache.count(sig))
			return sliced_signals_cache.at(sig);

		int offset = 0;
		int p = driven_bits_map.at(sig.extract(0, 1).to_single_sigbit()) - 1;
		while (driven_bits.at(p) != RTLIL::State::Sm)
			p--, offset++;

		RTLIL::SigSpec sig_a;
		for (p++; driven_bits.at(p) != RTLIL::State::Sm; p++)
			sig_a.append(driven_bits.at(p));

		RTLIL::SigSpec new_sig = sig;

		if (sig_a.width != sig.width) {
			RTLIL::Cell *cell = new RTLIL::Cell;
			cell->name = NEW_ID;
			cell->type = "$slice";
			cell->parameters["\\OFFSET"] = offset;
			cell->parameters["\\A_WIDTH"] = sig_a.width;
			cell->parameters["\\Y_WIDTH"] = sig.width;
			cell->connections["\\A"] = sig_a;
			cell->connections["\\Y"] = module->new_wire(sig.width, NEW_ID);
			new_sig = cell->connections["\\Y"];
			module->add(cell);
		}

		new_sig.optimize();
		sliced_signals_cache[sig] = new_sig;

		return new_sig;
	}

	RTLIL::SigSpec get_spliced_signal(RTLIL::SigSpec sig)
	{
		if (sig.width == 0)
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
			RTLIL::Cell *cell = new RTLIL::Cell;
			cell->name = NEW_ID;
			cell->type = "$concat";
			cell->parameters["\\A_WIDTH"] = new_sig.width;
			cell->parameters["\\B_WIDTH"] = sig2.width;
			cell->connections["\\A"] = new_sig;
			cell->connections["\\B"] = sig2;
			cell->connections["\\Y"] = module->new_wire(new_sig.width + sig2.width, NEW_ID);
			new_sig = cell->connections["\\Y"];
			module->add(cell);
		}

		new_sig.optimize();
		spliced_signals_cache[sig] = new_sig;

		log("  Created spliced signal: %s -> %s\n", log_signal(sig), log_signal(new_sig));
		return new_sig;
	}

	void run()
	{
		log("Splicing signals in module %s:\n", RTLIL::id2cstr(module->name));

		driven_bits.push_back(RTLIL::State::Sm);
		driven_bits.push_back(RTLIL::State::Sm);

		for (auto &it : module->wires)
			if (it.second->port_input) {
				RTLIL::SigSpec sig = sigmap(it.second);
				driven_chunks.insert(sig);
				for (auto &bit : sig.to_sigbit_vector())
					driven_bits.push_back(bit);
				driven_bits.push_back(RTLIL::State::Sm);
			}

		for (auto &it : module->cells)
		for (auto &conn : it.second->connections)
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

		for (auto &it : module->cells) {
			if (!design->selected(module, it.second))
				continue;
			for (auto &conn : it.second->connections)
				if (ct.cell_input(it.second->type, conn.first)) {
					RTLIL::SigSpec sig = sigmap(conn.second);
					if (driven_chunks.count(sig) > 0)
						continue;
					conn.second = get_spliced_signal(sig);
				}
		}

		std::vector<std::pair<RTLIL::Wire*, RTLIL::SigSpec>> rework_outputs;

		for (auto &it : module->wires)
			if (it.second->port_output) {
				if (!design->selected(module, it.second))
					continue;
				RTLIL::SigSpec sig = sigmap(it.second);
				if (driven_chunks.count(sig) > 0)
					continue;
				RTLIL::SigSpec new_sig = get_spliced_signal(sig);
				if (new_sig != sig)
					rework_outputs.push_back(std::pair<RTLIL::Wire*, RTLIL::SigSpec>(it.second, new_sig));
			}

		for (auto &it : rework_outputs)
		{
			module->wires.erase(it.first->name);
			RTLIL::Wire *new_port = new RTLIL::Wire(*it.first);
			it.first->name = NEW_ID;
			it.first->port_id = 0;
			it.first->port_input = false;
			it.first->port_output = false;
			module->add(it.first);
			module->add(new_port);
			module->connections.push_back(RTLIL::SigSig(new_port, it.second));
		}
	}
};

struct SplicePass : public Pass {
	SplicePass() : Pass("splice", "create explicit splicing cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    splice [selection]\n");
		log("\n");
		log("This command adds $slice and $concat cells to the design to make the splicing\n");
		log("of multi-bit signals explicit. This for example is useful for coarse grain\n");
		log("synthesis, where dedidacted hardware is needed to splice signals.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		extra_args(args, 1, design);

		log_header("Executing SPLICE pass (creating cells for signal splicing).\n");

		for (auto &mod_it : design->modules)
		{
			if (!design->selected(mod_it.second))
				continue;

			if (mod_it.second->processes.size()) {
				log("Skipping module %s as it contains processes.\n", mod_it.second->name.c_str());
				continue;
			}

			SpliceWorker worker(design, mod_it.second);
			worker.run();
		}
	}
} SplicePass;
 
