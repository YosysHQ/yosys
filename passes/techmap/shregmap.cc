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

struct ShregmapOptions
{
	std::string clkpol;
	int minlen, maxlen;
	int keep_before, keep_after;

	ShregmapOptions()
	{
		clkpol = "any";
		minlen = 2;
		maxlen = 0;
		keep_before = 0;
		keep_after = 0;
	}
};

struct ShregmapWorker
{
	Module *module;
	SigMap sigmap;

	const ShregmapOptions &opts;
	int dff_count, shreg_count;

	// next is set to NULL for sigbits that drive non-DFFs
	dict<SigBit, Cell*> sigbit_chain_next;
	dict<SigBit, Cell*> sigbit_chain_prev;
	pool<Cell*> chain_start_cells;

	void make_sigbit_chain_next_prev()
	{
		for (auto wire : module->wires()) {
			if (!wire->port_output)
				continue;
			for (auto bit : sigmap(wire))
				sigbit_chain_next[bit] = nullptr;
		}

		for (auto cell : module->cells())
		{
			if ((opts.clkpol != "pos" && cell->type == "$_DFF_N_") ||
					(opts.clkpol != "neg" && cell->type == "$_DFF_P_"))
			{
				SigBit d_bit = sigmap(cell->getPort("\\D").as_bit());
				if (sigbit_chain_next.count(d_bit))
					sigbit_chain_next[d_bit] = nullptr;
				else
					sigbit_chain_next[d_bit] = cell;

				SigBit q_bit = sigmap(cell->getPort("\\Q").as_bit());
				sigbit_chain_prev[q_bit] = cell;
				continue;
			}

			for (auto conn : cell->connections())
				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						sigbit_chain_next[bit] = nullptr;
		}
	}

	void find_chain_start_cells()
	{
		for (auto it : sigbit_chain_next)
		{
			if (it.second == nullptr)
				continue;

			if (sigbit_chain_prev.count(it.first) != 0)
			{
				Cell *c1 = sigbit_chain_prev.at(it.first);
				Cell *c2 = it.second;

				if (c1->type != c2->type)
					goto start_cell;

				if (sigmap(c1->getPort("\\C")) != c2->getPort("\\C"))
					goto start_cell;

				continue;
			}

		start_cell:
			chain_start_cells.insert(it.second);
		}
	}

	vector<Cell*> create_chain(Cell *start_cell)
	{
		vector<Cell*> chain;

		Cell *c = start_cell;
		while (c != nullptr)
		{
			chain.push_back(c);

			SigBit q_bit = sigmap(c->getPort("\\Q").as_bit());

			if (sigbit_chain_next.count(q_bit) == 0)
				break;

			c = sigbit_chain_next.at(q_bit);
			if (chain_start_cells.count(c) != 0)
				break;
		}

		return chain;
	}

	void process_chain(vector<Cell*> &chain)
	{
		if (GetSize(chain) < opts.keep_before + opts.minlen + opts.keep_after)
			return;

		int cursor = opts.keep_before;
		while (cursor < GetSize(chain) - opts.keep_after)
		{
			int depth = GetSize(chain) - opts.keep_after - cursor;

			if (opts.maxlen > 0)
				depth = std::min(opts.maxlen, depth);

			Cell *first_cell = chain[cursor], *last_cell = chain[cursor+depth-1];

			if (depth < 2)
				return;

			log("Converting %s.%s ... %s.%s to a shift register with depth %d.\n",
				log_id(module), log_id(first_cell), log_id(module), log_id(last_cell), depth);

			first_cell->type = "$__DFF_SHREG_" + first_cell->type.substr(6);
			first_cell->setPort("\\Q", last_cell->getPort("\\Q"));
			first_cell->setParam("\\DEPTH", depth);

			for (int i = 1; i < depth; i++)
				module->remove(chain[cursor+i]);
			cursor += depth;
		}
	}

	ShregmapWorker(Module *module, const ShregmapOptions &opts) :
			module(module), sigmap(module), opts(opts), dff_count(0), shreg_count(0)
	{
		make_sigbit_chain_next_prev();

		find_chain_start_cells();

		for (auto c : chain_start_cells) {
			vector<Cell*> chain = create_chain(c);
			process_chain(chain);
		}
	}
};

struct ShregmapPass : public Pass {
	ShregmapPass() : Pass("shregmap", "map shift registers") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    shregmap [options] [selection]\n");
		log("\n");
		log("This pass converts chains of $_DFF_[NP]_ gates to target specific shift register.\n");
		log("primitives. The generated shift register will be of type $__DFF_SHREG_[NP]_ and\n");
		log("will use the same interface as the original $_DFF_*_ cells. The cell parameter\n");
		log("'DEPTH' will contain the depth of the shift register. Use a target-specific\n");
		log("'techmap' map file to convert those cells to the actual target cells.\n");
		log("\n");
		log("    -minlen N\n");
		log("        minimum length of shift register (default = 2)\n");
		log("        (this is the length after -keep_before and -keep_after)\n");
		log("\n");
		log("    -maxlen N\n");
		log("        maximum length of shift register (default = no limit)\n");
		log("        larger chains will be mapped to multiple shift register instances\n");
		log("\n");
		log("    -keep_before N\n");
		log("        number of DFFs to keep before the shift register (default = 0)\n");
		log("\n");
		log("    -keep_after N\n");
		log("        number of DFFs to keep after the shift register (default = 0)\n");
		log("\n");
		log("    -clkpol pos|neg|any\n");
		log("        limit match to only positive or negative edge clocks. (default = any)\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		ShregmapOptions opts;

		log_header("Executing SHREGMAP pass (map shift registers).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-clkpol" && argidx+1 < args.size()) {
				opts.clkpol = args[++argidx];
				continue;
			}
			if (args[argidx] == "-minlen" && argidx+1 < args.size()) {
				opts.minlen = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-maxlen" && argidx+1 < args.size()) {
				opts.maxlen = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-keep_before" && argidx+1 < args.size()) {
				opts.keep_before = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-keep_after" && argidx+1 < args.size()) {
				opts.keep_after = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (opts.clkpol != "pos" && opts.clkpol != "neg" && opts.clkpol != "any")
			log_cmd_error("Invalid value for -clkpol: %s\n", opts.clkpol.c_str());

		int dff_count = 0;
		int shreg_count = 0;

		for (auto module : design->selected_modules()) {
			ShregmapWorker worker(module, opts);
			dff_count += worker.dff_count;
			shreg_count += worker.shreg_count;
		}

		log("Converted %d dff cells into %d shift registers.\n", dff_count, shreg_count);
	}
} ShregmapPass;

PRIVATE_NAMESPACE_END
