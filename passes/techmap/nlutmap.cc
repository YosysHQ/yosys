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

struct NlutmapConfig
{
	vector<int> luts;
	bool assert_mode = false;
};

struct NlutmapWorker
{
	const NlutmapConfig &config;
	pool<Cell*> mapped_cells;
	Module *module;

	NlutmapWorker(const NlutmapConfig &config, Module *module) :
			config(config), module(module)
	{
	}

	RTLIL::Selection get_selection()
	{
		RTLIL::Selection sel(false);
		for (auto cell : module->cells())
			if (!mapped_cells.count(cell))
				sel.select(module, cell);
		return sel;
	}

	void run_abc(int lut_size)
	{
		Pass::call_on_selection(module->design, get_selection(), "lut2mux");

		if (lut_size > 0)
			Pass::call_on_selection(module->design, get_selection(), stringf("abc -lut 1:%d", lut_size));
		else
			Pass::call_on_selection(module->design, get_selection(), "abc");

		Pass::call_on_module(module->design, module, "opt_clean");
	}

	void run()
	{
		vector<int> available_luts = config.luts;

		while (GetSize(available_luts) > 1)
		{
			int n_luts = available_luts.back();
			int lut_size = GetSize(available_luts);
			available_luts.pop_back();

			if (n_luts == 0)
				continue;

			run_abc(lut_size);

			SigMap sigmap(module);
			dict<Cell*, int> candidate_ratings;
			dict<SigBit, int> bit_lut_count;

			for (auto cell : module->cells())
			{
				if (cell->type != "$lut" || mapped_cells.count(cell))
					continue;

				if (GetSize(cell->getPort("\\A")) == lut_size || lut_size == 2)
					candidate_ratings[cell] = 0;

				for (auto &conn : cell->connections())
					for (auto bit : sigmap(conn.second))
						bit_lut_count[bit]++;
			}
			
			for (auto &cand : candidate_ratings)
			{
				for (auto &conn : cand.first->connections())
					for (auto bit : sigmap(conn.second))
						cand.second -= bit_lut_count[bit];
			}

			vector<pair<int, IdString>> rated_candidates;

			for (auto &cand : candidate_ratings)
				rated_candidates.push_back(pair<int, IdString>(cand.second, cand.first->name));

			std::sort(rated_candidates.begin(), rated_candidates.end());

			while (n_luts > 0 && !rated_candidates.empty()) {
				mapped_cells.insert(module->cell(rated_candidates.back().second));
				rated_candidates.pop_back();
				n_luts--;
			}

			if (!available_luts.empty())
				available_luts.back() += n_luts;
		}

		if (config.assert_mode) {
			for (auto cell : module->cells())
				if (cell->type == "$lut" && !mapped_cells.count(cell))
					log_error("Insufficient number of LUTs to map all logic cells!\n");
		}

		run_abc(0);
	}
};

struct NlutmapPass : public Pass {
	NlutmapPass() : Pass("nlutmap", "map to LUTs of different sizes") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    nlutmap [options] [selection]\n");
		log("\n");
		log("This pass uses successive calls to 'abc' to map to an architecture. That\n");
		log("provides a small number of differently sized LUTs.\n");
		log("\n");
		log("    -luts N_1,N_2,N_3,...\n");
		log("        The number of LUTs with 1, 2, 3, ... inputs that are\n");
		log("        available in the target architecture.\n");
		log("\n");
		log("    -assert\n");
		log("        Create an error if not all logic can be mapped\n");
		log("\n");
		log("Excess logic that does not fit into the specified LUTs is mapped back\n");
		log("to generic logic gates ($_AND_, etc.).\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		NlutmapConfig config;

		log_header(design, "Executing NLUTMAP pass (mapping to constant drivers).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-luts" && argidx+1 < args.size()) {
				vector<string> tokens = split_tokens(args[++argidx], ",");
				config.luts.clear();
				for (auto &token : tokens)
					config.luts.push_back(atoi(token.c_str()));
				continue;
			}
			if (args[argidx] == "-assert") {
				config.assert_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_whole_modules_warn())
		{
			NlutmapWorker worker(config, module);
			worker.run();
		}

		log_pop();
	}
} NlutmapPass;

PRIVATE_NAMESPACE_END
