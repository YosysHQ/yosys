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

struct ShregmapTech
{
	virtual ~ShregmapTech() { }
	virtual bool analyze(vector<int> &taps) = 0;
	virtual bool fixup(Cell *cell, dict<int, SigBit> &taps) = 0;
};

struct ShregmapOptions
{
	int minlen, maxlen;
	int keep_before, keep_after;
	bool zinit, init, params, ffe;
	dict<IdString, pair<IdString, IdString>> ffcells;
	ShregmapTech *tech;

	ShregmapOptions()
	{
		minlen = 2;
		maxlen = 0;
		keep_before = 0;
		keep_after = 0;
		zinit = false;
		init = false;
		params = false;
		ffe = false;
		tech = nullptr;
	}
};

struct ShregmapTechGreenpak4 : ShregmapTech
{
	bool analyze(vector<int> &taps)
	{
		if (GetSize(taps) > 2 && taps[0] == 0 && taps[2] < 17) {
			taps.clear();
			return true;
		}

		if (GetSize(taps) > 2)
			return false;

		if (taps.back() > 16) return false;

		return true;
	}

	bool fixup(Cell *cell, dict<int, SigBit> &taps)
	{
		auto D = cell->getPort("\\D");
		auto C = cell->getPort("\\C");

		auto newcell = cell->module->addCell(NEW_ID, "\\GP_SHREG");
		newcell->setPort("\\nRST", State::S1);
		newcell->setPort("\\CLK", C);
		newcell->setPort("\\IN", D);

		int i = 0;
		for (auto tap : taps) {
			newcell->setPort(i ? "\\OUTB" : "\\OUTA", tap.second);
			newcell->setParam(i ? "\\OUTB_TAP" : "\\OUTA_TAP", tap.first + 1);
			i++;
		}

		cell->setParam("\\OUTA_INVERT", 0);
		return false;
	}
};

struct ShregmapWorker
{
	Module *module;
	SigMap sigmap;

	const ShregmapOptions &opts;
	int dff_count, shreg_count;

	pool<Cell*> remove_cells;
	pool<SigBit> remove_init;

	dict<SigBit, bool> sigbit_init;
	dict<SigBit, Cell*> sigbit_chain_next;
	dict<SigBit, Cell*> sigbit_chain_prev;
	pool<SigBit> sigbit_with_non_chain_users;
	pool<Cell*> chain_start_cells;

	void make_sigbit_chain_next_prev()
	{
		for (auto wire : module->wires())
		{
			if (wire->port_output || wire->get_bool_attribute("\\keep")) {
				for (auto bit : sigmap(wire))
					sigbit_with_non_chain_users.insert(bit);
			}

			if (wire->attributes.count("\\init")) {
				SigSpec initsig = sigmap(wire);
				Const initval = wire->attributes.at("\\init");
				for (int i = 0; i < GetSize(initsig) && i < GetSize(initval); i++)
					if (initval[i] == State::S0 && !opts.zinit)
						sigbit_init[initsig[i]] = false;
					else if (initval[i] == State::S1)
						sigbit_init[initsig[i]] = true;
			}
		}

		for (auto cell : module->cells())
		{
			if (opts.ffcells.count(cell->type) && !cell->get_bool_attribute("\\keep"))
			{
				IdString d_port = opts.ffcells.at(cell->type).first;
				IdString q_port = opts.ffcells.at(cell->type).second;

				SigBit d_bit = sigmap(cell->getPort(d_port).as_bit());
				SigBit q_bit = sigmap(cell->getPort(q_port).as_bit());

				if (opts.init || sigbit_init.count(q_bit) == 0)
				{
					if (sigbit_chain_next.count(d_bit)) {
						sigbit_with_non_chain_users.insert(d_bit);
					} else
						sigbit_chain_next[d_bit] = cell;

					sigbit_chain_prev[q_bit] = cell;
					continue;
				}
			}

			for (auto conn : cell->connections())
				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						sigbit_with_non_chain_users.insert(bit);
		}
	}

	void find_chain_start_cells()
	{
		for (auto it : sigbit_chain_next)
		{
			if (opts.tech == nullptr && sigbit_with_non_chain_users.count(it.first))
				goto start_cell;

			if (sigbit_chain_prev.count(it.first) != 0)
			{
				Cell *c1 = sigbit_chain_prev.at(it.first);
				Cell *c2 = it.second;

				if (c1->type != c2->type)
					goto start_cell;

				if (c1->parameters != c2->parameters)
					goto start_cell;

				IdString d_port = opts.ffcells.at(c1->type).first;
				IdString q_port = opts.ffcells.at(c1->type).second;

				auto c1_conn = c1->connections();
				auto c2_conn = c1->connections();

				c1_conn.erase(d_port);
				c1_conn.erase(q_port);

				c2_conn.erase(d_port);
				c2_conn.erase(q_port);

				if (c1_conn != c2_conn)
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

			IdString q_port = opts.ffcells.at(c->type).second;
			SigBit q_bit = sigmap(c->getPort(q_port).as_bit());

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

			Cell *first_cell = chain[cursor];
			IdString q_port = opts.ffcells.at(first_cell->type).second;
			dict<int, SigBit> taps_dict;

			if (opts.tech)
			{
				vector<SigBit> qbits;
				vector<int> taps;

				for (int i = 0; i < depth; i++)
				{
					Cell *cell = chain[cursor+i];
					auto qbit = sigmap(cell->getPort(q_port));
					qbits.push_back(qbit);

					if (sigbit_with_non_chain_users.count(qbit))
						taps.push_back(i);
				}

				while (depth > 0)
				{
					if (taps.empty() || taps.back() < depth-1)
						taps.push_back(depth-1);

					if (opts.tech->analyze(taps))
						break;

					taps.pop_back();
					depth--;
				}

				depth = 0;
				for (auto tap : taps) {
					taps_dict[tap] = qbits.at(tap);
					log_assert(depth < tap+1);
					depth = tap+1;
				}
			}

			if (depth < 2) {
				cursor++;
				continue;
			}

			Cell *last_cell = chain[cursor+depth-1];

			log("Converting %s.%s ... %s.%s to a shift register with depth %d.\n",
				log_id(module), log_id(first_cell), log_id(module), log_id(last_cell), depth);

			dff_count += depth;
			shreg_count += 1;

			string shreg_cell_type_str = "$__SHREG";
			if (opts.params) {
				shreg_cell_type_str += "_";
			} else {
				if (first_cell->type[1] != '_')
					shreg_cell_type_str += "_";
				shreg_cell_type_str += first_cell->type.substr(1);
			}

			if (opts.init) {
				vector<State> initval;
				for (int i = depth-1; i >= 0; i--) {
					SigBit bit = sigmap(chain[cursor+i]->getPort(q_port).as_bit());
					if (sigbit_init.count(bit) == 0)
						initval.push_back(State::Sx);
					else if (sigbit_init.at(bit))
						initval.push_back(State::S1);
					else
						initval.push_back(State::S0);
					remove_init.insert(bit);
				}
				first_cell->setParam("\\INIT", initval);
			}

			if (opts.zinit)
				for (int i = depth-1; i >= 0; i--) {
					SigBit bit = sigmap(chain[cursor+i]->getPort(q_port).as_bit());
					remove_init.insert(bit);
				}

			if (opts.params)
			{
				int param_clkpol = -1;
				int param_enpol = 2;

				if (first_cell->type == "$_DFF_N_") param_clkpol = 0;
				if (first_cell->type == "$_DFF_P_") param_clkpol = 1;

				if (first_cell->type == "$_DFFE_NN_") param_clkpol = 0, param_enpol = 0;
				if (first_cell->type == "$_DFFE_NP_") param_clkpol = 0, param_enpol = 1;
				if (first_cell->type == "$_DFFE_PN_") param_clkpol = 1, param_enpol = 0;
				if (first_cell->type == "$_DFFE_PP_") param_clkpol = 1, param_enpol = 1;

				log_assert(param_clkpol >= 0);
				first_cell->setParam("\\CLKPOL", param_clkpol);
				if (opts.ffe) first_cell->setParam("\\ENPOL", param_enpol);
			}

			first_cell->type = shreg_cell_type_str;
			first_cell->setPort(q_port, last_cell->getPort(q_port));
			first_cell->setParam("\\DEPTH", depth);

			if (opts.tech != nullptr && !opts.tech->fixup(first_cell, taps_dict))
				remove_cells.insert(first_cell);

			for (int i = 1; i < depth; i++)
				remove_cells.insert(chain[cursor+i]);
			cursor += depth;
		}
	}

	void cleanup()
	{
		for (auto cell : remove_cells)
			module->remove(cell);

		for (auto wire : module->wires())
		{
			if (wire->attributes.count("\\init") == 0)
				continue;

			SigSpec initsig = sigmap(wire);
			Const &initval = wire->attributes.at("\\init");

			for (int i = 0; i < GetSize(initsig) && i < GetSize(initval); i++)
				if (remove_init.count(initsig[i]))
					initval[i] = State::Sx;

			if (SigSpec(initval).is_fully_undef())
				wire->attributes.erase("\\init");
		}

		remove_cells.clear();
		sigbit_chain_next.clear();
		sigbit_chain_prev.clear();
		chain_start_cells.clear();
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

		cleanup();
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
		log("This pass converts chains of $_DFF_[NP]_ gates to target specific shift register\n");
		log("primitives. The generated shift register will be of type $__SHREG_DFF_[NP]_ and\n");
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
		log("    -enpol pos|neg|none|any_or_none|any\n");
		log("        limit match to FFs with the specified enable polarity. (default = none)\n");
		log("\n");
		log("    -match <cell_type>[:<d_port_name>:<q_port_name>]\n");
		log("        match the specified cells instead of $_DFF_N_ and $_DFF_P_. If\n");
		log("        ':<d_port_name>:<q_port_name>' is omitted then 'D' and 'Q' is used\n");
		log("        by default. E.g. the option '-clkpol pos' is just an alias for\n");
		log("        '-match $_DFF_P_', which is an alias for '-match $_DFF_P_:D:Q'.\n");
		log("\n");
		log("    -params\n");
		log("        instead of encoding the clock and enable polarity in the cell name by\n");
		log("        deriving from the original cell name, simply name all generated cells\n");
		log("        $__SHREG_ and use CLKPOL and ENPOL parameters. An ENPOL value of 2 is\n");
		log("        used to denote cells without enable input. The ENPOL parameter is\n");
		log("        omitted when '-enpol none' (or no -enpol option) is passed.\n");
		log("\n");
		log("    -zinit\n");
		log("        assume the shift register is automatically zero-initialized, so it\n");
		log("        becomes legal to merge zero initialized FFs into the shift register.\n");
		log("\n");
		log("    -init\n");
		log("        map initialized registers to the shift reg, add an INIT parameter to\n");
		log("        generated cells with the initialization value. (first bit to shift out\n");
		log("        in LSB position)\n");
		log("\n");
		log("    -tech greenpak4\n");
		log("        map to greenpak4 shift registers.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		ShregmapOptions opts;
		string clkpol, enpol;

		log_header(design, "Executing SHREGMAP pass (map shift registers).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-clkpol" && argidx+1 < args.size()) {
				clkpol = args[++argidx];
				continue;
			}
			if (args[argidx] == "-enpol" && argidx+1 < args.size()) {
				enpol = args[++argidx];
				continue;
			}
			if (args[argidx] == "-match" && argidx+1 < args.size()) {
				vector<string> match_args = split_tokens(args[++argidx], ":");
				if (GetSize(match_args) < 2)
					match_args.push_back("D");
				if (GetSize(match_args) < 3)
					match_args.push_back("Q");
				IdString id_cell_type(RTLIL::escape_id(match_args[0]));
				IdString id_d_port_name(RTLIL::escape_id(match_args[1]));
				IdString id_q_port_name(RTLIL::escape_id(match_args[2]));
				opts.ffcells[id_cell_type] = make_pair(id_d_port_name, id_q_port_name);
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
			if (args[argidx] == "-tech" && argidx+1 < args.size() && opts.tech == nullptr) {
				string tech = args[++argidx];
				if (tech == "greenpak4") {
					clkpol = "pos";
					opts.zinit = true;
					opts.tech = new ShregmapTechGreenpak4;
				} else {
					argidx--;
					break;
				}
				continue;
			}
			if (args[argidx] == "-zinit") {
				opts.zinit = true;
				continue;
			}
			if (args[argidx] == "-init") {
				opts.init = true;
				continue;
			}
			if (args[argidx] == "-params") {
				opts.params = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (opts.zinit && opts.init)
			log_cmd_error("Options -zinit and -init are exclusive!\n");

		if (opts.ffcells.empty())
		{
			bool clk_pos = clkpol == "" || clkpol == "pos" || clkpol == "any";
			bool clk_neg = clkpol == "" || clkpol == "neg" || clkpol == "any";

			bool en_none = enpol == "" || enpol == "none" || enpol == "any_or_none";
			bool en_pos = enpol == "pos" || enpol == "any" || enpol == "any_or_none";
			bool en_neg = enpol == "neg" || enpol == "any" || enpol == "any_or_none";

			if (clk_pos && en_none)
				opts.ffcells["$_DFF_P_"] = make_pair(IdString("\\D"), IdString("\\Q"));
			if (clk_neg && en_none)
				opts.ffcells["$_DFF_N_"] = make_pair(IdString("\\D"), IdString("\\Q"));

			if (clk_pos && en_pos)
				opts.ffcells["$_DFFE_PP_"] = make_pair(IdString("\\D"), IdString("\\Q"));
			if (clk_pos && en_neg)
				opts.ffcells["$_DFFE_PN_"] = make_pair(IdString("\\D"), IdString("\\Q"));

			if (clk_neg && en_pos)
				opts.ffcells["$_DFFE_NP_"] = make_pair(IdString("\\D"), IdString("\\Q"));
			if (clk_neg && en_neg)
				opts.ffcells["$_DFFE_NN_"] = make_pair(IdString("\\D"), IdString("\\Q"));

			if (en_pos || en_neg)
				opts.ffe = true;
		}
		else
		{
			if (!clkpol.empty())
				log_cmd_error("Options -clkpol and -match are exclusive!\n");
			if (!enpol.empty())
				log_cmd_error("Options -enpol and -match are exclusive!\n");
			if (opts.params)
				log_cmd_error("Options -params and -match are exclusive!\n");
		}

		int dff_count = 0;
		int shreg_count = 0;

		for (auto module : design->selected_modules()) {
			ShregmapWorker worker(module, opts);
			dff_count += worker.dff_count;
			shreg_count += worker.shreg_count;
		}

		log("Converted %d dff cells into %d shift registers.\n", dff_count, shreg_count);

		if (opts.tech != nullptr) {
			delete opts.tech;
			opts.tech = nullptr;
		}
	}
} ShregmapPass;

PRIVATE_NAMESPACE_END
