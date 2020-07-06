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

struct OptMemWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap;
	bool restart;

	dict<IdString, vector<IdString>> memrd, memwr, meminit;
	pool<IdString> remove_mem, remove_cells;

	OptMemWorker(RTLIL::Module *module) : design(module->design), module(module), sigmap(module), restart(false)
	{
		for (auto &it : module->memories)
		{
			memrd[it.first];
			memwr[it.first];
			meminit[it.first];
		}

		for (auto cell : module->cells())
		{
			if (cell->type == ID($memrd)) {
				IdString id = cell->getParam(ID(MEMID)).decode_string();
				memrd.at(id).push_back(cell->name);
			}

			if (cell->type == ID($memwr)) {
				IdString id = cell->getParam(ID(MEMID)).decode_string();
				memwr.at(id).push_back(cell->name);
			}

			if (cell->type == ID($meminit)) {
				IdString id = cell->getParam(ID(MEMID)).decode_string();
				meminit.at(id).push_back(cell->name);
			}
		}
	}

	~OptMemWorker()
	{
		for (auto it : remove_mem)
		{
			for (auto cell_name : memrd[it])
				module->remove(module->cell(cell_name));
			for (auto cell_name : memwr[it])
				module->remove(module->cell(cell_name));
			for (auto cell_name : meminit[it])
				module->remove(module->cell(cell_name));

			delete module->memories.at(it);
			module->memories.erase(it);
		}

		for (auto cell_name : remove_cells)
			module->remove(module->cell(cell_name));
	}

	int run(RTLIL::Memory *mem)
	{
		if (restart || remove_mem.count(mem->name))
			return 0;

		if (memwr.at(mem->name).empty() && meminit.at(mem->name).empty()) {
			log("Removing memory %s.%s with no write ports or init data.\n", log_id(module), log_id(mem));
			remove_mem.insert(mem->name);
			return 1;
		}

		return 0;
	}
};

struct OptMemPass : public Pass {
	OptMemPass() : Pass("opt_mem", "optimize memories") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_mem [options] [selection]\n");
		log("\n");
		log("This pass performs various optimizations on memories in the design.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing OPT_MEM pass (optimize memories).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-nomux") {
			// 	mode_nomux = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		int total_count = 0;
		for (auto module : design->selected_modules()) {
			while (1) {
				int cnt = 0;
				OptMemWorker worker(module);
				for (auto &it : module->memories)
					if (module->selected(it.second))
						cnt += worker.run(it.second);
				if (!cnt && !worker.restart)
					break;
				total_count += cnt;
			}
		}

		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Performed a total of %d transformations.\n", total_count);
	}
} OptMemPass;

PRIVATE_NAMESPACE_END
