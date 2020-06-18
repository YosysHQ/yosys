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

struct ChformalPass : public Pass {
	ChformalPass() : Pass("chformal", "change formal constraints of the design") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    chformal [types] [mode] [options] [selection]\n");
		log("\n");
		log("Make changes to the formal constraints of the design. The [types] options\n");
		log("the type of constraint to operate on. If none of the following options are given,\n");
		log("the command will operate on all constraint types:\n");
		log("\n");
		log("    -assert       $assert cells, representing assert(...) constraints\n");
		log("    -assume       $assume cells, representing assume(...) constraints\n");
		log("    -live         $live cells, representing assert(s_eventually ...)\n");
		log("    -fair         $fair cells, representing assume(s_eventually ...)\n");
		log("    -cover        $cover cells, representing cover() statements\n");
		log("\n");
		log("Exactly one of the following modes must be specified:\n");
		log("\n");
		log("    -remove\n");
		log("        remove the cells and thus constraints from the design\n");
		log("\n");
		log("    -early\n");
		log("        bypass FFs that only delay the activation of a constraint\n");
		log("\n");
		log("    -delay <N>\n");
		log("        delay activation of the constraint by <N> clock cycles\n");
		log("\n");
		log("    -skip <N>\n");
		log("        ignore activation of the constraint in the first <N> clock cycles\n");
		log("\n");
		log("    -assert2assume\n");
		log("    -assume2assert\n");
		log("    -live2fair\n");
		log("    -fair2live\n");
		log("        change the roles of cells as indicated. these options can be combined\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool assert2assume = false;
		bool assume2assert = false;
		bool live2fair = false;
		bool fair2live = false;

		pool<IdString> constr_types;
		char mode = 0;
		int mode_arg = 0;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-assert") {
				constr_types.insert(ID($assert));
				continue;
			}
			if (args[argidx] == "-assume") {
				constr_types.insert(ID($assume));
				continue;
			}
			if (args[argidx] == "-live") {
				constr_types.insert(ID($live));
				continue;
			}
			if (args[argidx] == "-fair") {
				constr_types.insert(ID($fair));
				continue;
			}
			if (args[argidx] == "-cover") {
				constr_types.insert(ID($cover));
				continue;
			}
			if (mode == 0 && args[argidx] == "-remove") {
				mode = 'r';
				continue;
			}
			if (mode == 0 && args[argidx] == "-early") {
				mode = 'e';
				continue;
			}
			if (mode == 0 && args[argidx] == "-delay" && argidx+1 < args.size()) {
				mode = 'd';
				mode_arg = atoi(args[++argidx].c_str());
				continue;
			}
			if (mode == 0 && args[argidx] == "-skip" && argidx+1 < args.size()) {
				mode = 's';
				mode_arg = atoi(args[++argidx].c_str());
				continue;
			}
			if ((mode == 0 || mode == 'c') && args[argidx] == "-assert2assume") {
				assert2assume = true;
				mode = 'c';
				continue;
			}
			if ((mode == 0 || mode == 'c') && args[argidx] == "-assume2assert") {
				assume2assert = true;
				mode = 'c';
				continue;
			}
			if ((mode == 0 || mode == 'c') && args[argidx] == "-live2fair") {
				live2fair = true;
				mode = 'c';
				continue;
			}
			if ((mode == 0 || mode == 'c') && args[argidx] == "-fair2live") {
				fair2live = true;
				mode = 'c';
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (constr_types.empty()) {
			constr_types.insert(ID($assert));
			constr_types.insert(ID($assume));
			constr_types.insert(ID($live));
			constr_types.insert(ID($fair));
			constr_types.insert(ID($cover));
		}

		if (mode == 0)
			log_cmd_error("Mode option is missing.\n");

		for (auto module : design->selected_modules())
		{
			vector<Cell*> constr_cells;

			for (auto cell : module->selected_cells())
				if (constr_types.count(cell->type))
					constr_cells.push_back(cell);

			if (mode == 'r')
			{
				for (auto cell : constr_cells)
					module->remove(cell);
			}
			else
			if (mode == 'e')
			{
				SigMap sigmap(module);
				dict<SigBit, pair<SigBit, pair<SigBit, bool>>> ffmap;
				pool<SigBit> init_zero, init_one;

				for (auto wire : module->wires())
				{
					if (wire->attributes.count(ID::init) == 0)
						continue;

					SigSpec initsig = sigmap(wire);
					Const initval = wire->attributes.at(ID::init);

					for (int i = 0; i < GetSize(initsig) && i < GetSize(initval); i++) {
						if (initval[i] == State::S0)
							init_zero.insert(initsig[i]);
						if (initval[i] == State::S1)
							init_one.insert(initsig[i]);
					}
				}

				for (auto cell : module->selected_cells())
				{
					if (cell->type == ID($ff)) {
						SigSpec D = sigmap(cell->getPort(ID::D));
						SigSpec Q = sigmap(cell->getPort(ID::Q));
						for (int i = 0; i < GetSize(D); i++)
							ffmap[Q[i]] = make_pair(D[i], make_pair(State::Sm, false));
					}
					if (cell->type == ID($dff)) {
						SigSpec D = sigmap(cell->getPort(ID::D));
						SigSpec Q = sigmap(cell->getPort(ID::Q));
						SigSpec C = sigmap(cell->getPort(ID::CLK));
						bool clockpol = cell->getParam(ID::CLK_POLARITY).as_bool();
						for (int i = 0; i < GetSize(D); i++)
							ffmap[Q[i]] = make_pair(D[i], make_pair(C, clockpol));
					}
				}

				for (auto cell : constr_cells)
					while (true)
					{
						SigSpec A = sigmap(cell->getPort(ID::A));
						SigSpec EN = sigmap(cell->getPort(ID::EN));

						if (ffmap.count(A) == 0 || ffmap.count(EN) == 0)
							break;

						if (!init_zero.count(EN)) {
							if (cell->type == ID($cover)) break;
							if (cell->type.in(ID($assert), ID($assume)) && !init_one.count(A)) break;
						}

						const auto &A_map = ffmap.at(A);
						const auto &EN_map = ffmap.at(EN);

						if (A_map.second != EN_map.second)
							break;

						cell->setPort(ID::A, A_map.first);
						cell->setPort(ID::EN, EN_map.first);
					}
			}
			else
			if (mode == 'd')
			{
				for (auto cell : constr_cells)
				for (int i = 0; i < mode_arg; i++)
				{
					SigSpec orig_a = cell->getPort(ID::A);
					SigSpec orig_en = cell->getPort(ID::EN);

					Wire *new_a = module->addWire(NEW_ID);
					Wire *new_en = module->addWire(NEW_ID);
					new_en->attributes[ID::init] = State::S0;

					module->addFf(NEW_ID, orig_a, new_a);
					module->addFf(NEW_ID, orig_en, new_en);

					cell->setPort(ID::A, new_a);
					cell->setPort(ID::EN, new_en);
				}
			}
			else
			if (mode == 's')
			{
				SigSpec en = State::S1;

				for (int i = 0; i < mode_arg; i++) {
					Wire *w = module->addWire(NEW_ID);
					w->attributes[ID::init] = State::S0;
					module->addFf(NEW_ID, en, w);
					en = w;
				}

				for (auto cell : constr_cells)
					cell->setPort(ID::EN, module->LogicAnd(NEW_ID, en, cell->getPort(ID::EN)));
			}
			else
			if (mode == 'c')
			{
				for (auto cell : constr_cells)
					if (assert2assume && cell->type == ID($assert))
						cell->type = ID($assume);
					else if (assume2assert && cell->type == ID($assume))
						cell->type = ID($assert);
					else if (live2fair && cell->type == ID($live))
						cell->type = ID($fair);
					else if (fair2live && cell->type == ID($fair))
						cell->type = ID($live);
			}
		}
	}
} ChformalPass;

PRIVATE_NAMESPACE_END
