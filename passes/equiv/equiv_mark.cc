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

struct EquivMarkWorker
{
	Module *module;
	SigMap sigmap;

	// cache for traversing signal flow graph
	dict<SigBit, pool<IdString>> up_bit2cells;
	dict<IdString, pool<SigBit>> up_cell2bits;
	pool<IdString> edge_cells, equiv_cells;

	// graph traversal state
	pool<SigBit> queue, visited;

	// assigned regions
	dict<IdString, int> cell_regions;
	dict<SigBit, int> bit_regions;
	int next_region;

	// merge-find
	mfp<int> region_mf;

	EquivMarkWorker(Module *module) : module(module), sigmap(module)
	{
		for (auto cell : module->cells())
		{
			if (cell->type == "$equiv")
				equiv_cells.insert(cell->name);

			for (auto &port : cell->connections())
			{
				if (cell->input(port.first))
					for (auto bit : sigmap(port.second))
						up_cell2bits[cell->name].insert(bit);

				if (cell->output(port.first))
					for (auto bit : sigmap(port.second))
						up_bit2cells[bit].insert(cell->name);
			}
		}

		next_region = 0;
	}

	void mark()
	{
		while (!queue.empty())
		{
			pool<IdString> cells;

			for (auto &bit : queue)
			{
				// log_assert(bit_regions.count(bit) == 0);
				bit_regions[bit] = next_region;
				visited.insert(bit);

				for (auto cell : up_bit2cells[bit])
					if (edge_cells.count(cell) == 0)
						cells.insert(cell);
			}

			queue.clear();

			for (auto cell : cells)
			{
				if (next_region == 0 && equiv_cells.count(cell))
					continue;

				if (cell_regions.count(cell)) {
					if (cell_regions.at(cell) != 0)
						region_mf.merge(cell_regions.at(cell), next_region);
					continue;
				}

				cell_regions[cell] = next_region;

				for (auto bit : up_cell2bits[cell])
					if (visited.count(bit) == 0)
						queue.insert(bit);
			}
		}

		next_region++;
	}

	void run()
	{
		log("Running equiv_mark on module %s:\n", log_id(module));

		// marking region 0

		for (auto wire : module->wires())
			if (wire->port_id > 0)
				for (auto bit : sigmap(wire))
					queue.insert(bit);

		for (auto cell_name : equiv_cells)
		{
			auto cell = module->cell(cell_name);

			SigSpec sig_a = sigmap(cell->getPort("\\A"));
			SigSpec sig_b = sigmap(cell->getPort("\\B"));

			if (sig_a == sig_b) {
				for (auto bit : sig_a)
					queue.insert(bit);
				edge_cells.insert(cell_name);
				cell_regions[cell_name] = 0;
			}
		}

		mark();

		// marking unsolved regions

		for (auto cell : module->cells())
		{
			if (cell_regions.count(cell->name) || cell->type != "$equiv")
				continue;

			SigSpec sig_a = sigmap(cell->getPort("\\A"));
			SigSpec sig_b = sigmap(cell->getPort("\\B"));

			log_assert(sig_a != sig_b);

			for (auto bit : sig_a)
				queue.insert(bit);

			for (auto bit : sig_b)
				queue.insert(bit);

			cell_regions[cell->name] = next_region;
			mark();
		}

		// setting attributes

		dict<int, int> final_region_map;
		int next_final_region = 0;

		dict<int, int> region_cell_count;
		dict<int, int> region_wire_count;

		for (int i = 0; i < next_region; i++) {
			int r = region_mf.find(i);
			if (final_region_map.count(r) == 0)
				final_region_map[r] = next_final_region++;
			final_region_map[i] = final_region_map[r];
		}

		for (auto cell : module->cells())
		{
			if (cell_regions.count(cell->name)) {
				int r = final_region_map.at(cell_regions.at(cell->name));
				cell->attributes["\\equiv_region"] = Const(r);
				region_cell_count[r]++;
			} else
				cell->attributes.erase("\\equiv_region");
		}

		for (auto wire : module->wires())
		{
			pool<int> regions;
			for (auto bit : sigmap(wire))
				if (bit_regions.count(bit))
					regions.insert(region_mf.find(bit_regions.at(bit)));

			if (GetSize(regions) == 1) {
				int r = final_region_map.at(*regions.begin());
				wire->attributes["\\equiv_region"] = Const(r);
				region_wire_count[r]++;
			} else
				wire->attributes.erase("\\equiv_region");
		}

		for (int i = 0; i < next_final_region; i++)
			log("  region %d: %d cells, %d wires\n", i, region_wire_count[i], region_cell_count[i]);
	}
};

struct EquivMarkPass : public Pass {
	EquivMarkPass() : Pass("equiv_mark", "mark equivalence checking regions") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_mark [options] [selection]\n");
		log("\n");
		log("This command marks the regions in an equivalence checking module. Region 0 is\n");
		log("the proven part of the circuit. Regions with higher numbers are connected\n");
		log("unproven subcricuits. The integer attribute 'equiv_region' is set on all\n");
		log("wires and cells.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, Design *design)
	{
		log_header(design, "Executing EQUIV_MARK pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-foobar") {
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_whole_modules_warn()) {
			EquivMarkWorker worker(module);
			worker.run();
		}
	}
} EquivMarkPass;

PRIVATE_NAMESPACE_END
