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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct EquivPurgeWorker
{
	Module *module;
	SigMap sigmap;
	int name_cnt;

	EquivPurgeWorker(Module *module) : module(module), sigmap(module), name_cnt(0) { }

	SigSpec make_output(SigSpec sig, IdString cellname)
	{
		if (sig.is_wire()) {
			Wire *wire = sig.as_wire();
			if (wire->name[0] == '\\') {
				if (!wire->port_output) {
					log("  Module output: %s (%s)\n", log_signal(wire), log_id(cellname));
					wire->port_output = true;
				}
				return wire;
			}
		}

		while (1)
		{
			IdString name = stringf("\\equiv_%d", name_cnt++);
			if (module->count_id(name))
				continue;

			Wire *wire = module->addWire(name, GetSize(sig));
			wire->port_output = true;
			module->connect(wire, sig);
			log("  Module output: %s (%s)\n", log_signal(wire), log_id(cellname));
			return wire;
		}
	}

	SigSpec make_input(SigSpec sig)
	{
		if (sig.is_wire()) {
			Wire *wire = sig.as_wire();
			if (wire->name[0] == '\\') {
				if (!wire->port_output) {
					log("  Module input: %s\n", log_signal(wire));
					wire->port_input = true;
				}
				return module->addWire(NEW_ID, GetSize(sig));
			}
		}

		while (1)
		{
			IdString name = stringf("\\equiv_%d", name_cnt++);
			if (module->count_id(name))
				continue;

			Wire *wire = module->addWire(name, GetSize(sig));
			wire->port_input = true;
			module->connect(sig, wire);
			log("  Module input: %s (%s)\n", log_signal(wire), log_signal(sig));
			return module->addWire(NEW_ID, GetSize(sig));
		}
	}

	void run()
	{
		log("Running equiv_purge on module %s:\n", log_id(module));

		for (auto wire : module->wires()) {
			wire->port_input = false;
			wire->port_output = false;
		}

		pool<SigBit> queue, visited;

		// cache for traversing signal flow graph
		dict<SigBit, pool<IdString>> up_bit2cells;
		dict<IdString, pool<SigBit>> up_cell2bits;

		for (auto cell : module->cells())
		{
			if (cell->type != "$equiv") {
				for (auto &port : cell->connections()) {
					if (cell->input(port.first))
						for (auto bit : sigmap(port.second))
							up_cell2bits[cell->name].insert(bit);
					if (cell->output(port.first))
						for (auto bit : sigmap(port.second))
							up_bit2cells[bit].insert(cell->name);
				}
				continue;
			}

			SigSpec sig_a = sigmap(cell->getPort("\\A"));
			SigSpec sig_b = sigmap(cell->getPort("\\B"));
			SigSpec sig_y = sigmap(cell->getPort("\\Y"));

			if (sig_a == sig_b)
				continue;

			for (auto bit : sig_a)
				queue.insert(bit);

			for (auto bit : sig_b)
				queue.insert(bit);

			for (auto bit : sig_y)
				visited.insert(bit);

			cell->setPort("\\Y", make_output(sig_y, cell->name));
		}

		SigSpec srcsig;
		SigMap rewrite_sigmap(module);

		while (!queue.empty())
		{
			pool<SigBit> next_queue;

			for (auto bit : queue)
				visited.insert(bit);

			for (auto bit : queue)
			{
				auto &cells = up_bit2cells[bit];

				if (cells.empty()) {
					srcsig.append(bit);
				} else {
					for (auto cell : cells)
					for (auto bit : up_cell2bits[cell])
						if (visited.count(bit) == 0)
							next_queue.insert(bit);
				}
			}

			next_queue.swap(queue);
		}

		srcsig.sort_and_unify();

		for (SigChunk chunk : srcsig.chunks())
			if (chunk.wire != nullptr)
				rewrite_sigmap.add(chunk, make_input(chunk));

		for (auto cell : module->cells())
			if (cell->type == "$equiv")
				cell->setPort("\\Y", rewrite_sigmap(sigmap(cell->getPort("\\Y"))));

		module->fixup_ports();
	}
};

struct EquivPurgePass : public Pass {
	EquivPurgePass() : Pass("equiv_purge", "purge equivalence checking module") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_purge [options] [selection]\n");
		log("\n");
		log("This command removes the proven part of an equivalence checking module, leaving\n");
		log("only the unproven segments in the design. This will also remove and add module\n");
		log("ports as needed.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing EQUIV_PURGE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-foobar") {
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_whole_modules_warn()) {
			EquivPurgeWorker worker(module);
			worker.run();
		}
	}
} EquivPurgePass;

PRIVATE_NAMESPACE_END
