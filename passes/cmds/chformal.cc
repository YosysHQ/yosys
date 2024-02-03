/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

static RTLIL::IdString formal_flavor(RTLIL::Cell *cell)
{
	if (cell->type != ID($check))
		return cell->type;

	std::string flavor_param = cell->getParam(ID(FLAVOR)).decode_string();
	if (flavor_param == "assert")
		return ID($assert);
	else if (flavor_param == "assume")
		return ID($assume);
	else if (flavor_param == "cover")
		return ID($cover);
	else if (flavor_param == "live")
		return ID($live);
	else if (flavor_param == "fair")
		return ID($fair);
	else
		log_abort();
}

static void set_formal_flavor(RTLIL::Cell *cell, RTLIL::IdString flavor)
{
	if (cell->type != ID($check)) {
		cell->type = flavor;
		return;
	}

	if (flavor == ID($assert))
		cell->setParam(ID(FLAVOR), std::string("assert"));
	else if (flavor == ID($assume))
		cell->setParam(ID(FLAVOR), std::string("assume"));
	else if (flavor == ID($cover))
		cell->setParam(ID(FLAVOR), std::string("cover"));
	else if (flavor == ID($live))
		cell->setParam(ID(FLAVOR), std::string("live"));
	else if (flavor == ID($fair))
		cell->setParam(ID(FLAVOR), std::string("fair"));
	else
		log_abort();
}

static bool is_triggered_check_cell(RTLIL::Cell * cell)
{
	return cell->type == ID($check) && cell->getParam(ID(TRG_ENABLE)).as_bool();
}

struct ChformalPass : public Pass {
	ChformalPass() : Pass("chformal", "change formal constraints of the design") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    chformal [types] [mode] [options] [selection]\n");
		log("\n");
		log("Make changes to the formal constraints of the design. The [types] options\n");
		log("the type of constraint to operate on. If none of the following options are\n");
		log("given, the command will operate on all constraint types:\n");
		log("\n");
		log("    -assert       $assert cells, representing assert(...) constraints\n");
		log("    -assume       $assume cells, representing assume(...) constraints\n");
		log("    -live         $live cells, representing assert(s_eventually ...)\n");
		log("    -fair         $fair cells, representing assume(s_eventually ...)\n");
		log("    -cover        $cover cells, representing cover() statements\n");
		log("\n");
		log("    Additionally chformal will operate on $check cells corresponding to the\n");
		log("    selected constraint types.\n");
		log("\n");
		log("Exactly one of the following modes must be specified:\n");
		log("\n");
		log("    -remove\n");
		log("        remove the cells and thus constraints from the design\n");
		log("\n");
		log("    -early\n");
		log("        bypass FFs that only delay the activation of a constraint. When inputs\n");
		log("        of the bypassed FFs do not remain stable between clock edges, this may\n");
		log("        result in unexpected behavior.\n");
		log("\n");
		log("    -delay <N>\n");
		log("        delay activation of the constraint by <N> clock cycles\n");
		log("\n");
		log("    -skip <N>\n");
		log("        ignore activation of the constraint in the first <N> clock cycles\n");
		log("\n");
		log("    -coverenable\n");
		log("        add cover statements for the enable signals of the constraints\n");
		log("\n");
#ifdef YOSYS_ENABLE_VERIFIC
		log("        Note: For the Verific frontend it is currently not guaranteed that a\n");
		log("        reachable SVA statement corresponds to an active enable signal.\n");
		log("\n");
#endif
		log("    -assert2assume\n");
		log("    -assume2assert\n");
		log("    -live2fair\n");
		log("    -fair2live\n");
		log("        change the roles of cells as indicated. these options can be combined\n");
		log("\n");
		log("    -lower\n");
		log("        convert each $check cell into an $assert, $assume, $live, $fair or\n");
		log("        $cover cell. If the $check cell contains a message, also produce a\n");
		log("        $print cell.\n");
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
			if (mode == 0 && args[argidx] == "-coverenable") {
				mode = 'p';
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
			if (mode == 0 && args[argidx] == "-lower") {
				mode = 'l';
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
				if (constr_types.count(formal_flavor(cell)))
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
				{
					if (is_triggered_check_cell(cell)) {
						if (cell->getParam(ID::TRG_WIDTH).as_int() != 1)
							continue;
						cell->setPort(ID::TRG, SigSpec());
						cell->setParam(ID::TRG_ENABLE, false);
						cell->setParam(ID::TRG_WIDTH, 0);
						cell->setParam(ID::TRG_POLARITY, false);
					}

					IdString flavor = formal_flavor(cell);

					while (true)
					{
						SigSpec A = sigmap(cell->getPort(ID::A));
						SigSpec EN = sigmap(cell->getPort(ID::EN));

						if (ffmap.count(A) == 0 || ffmap.count(EN) == 0)
							break;

						if (!init_zero.count(EN)) {
							if (flavor == ID($cover)) break;
							if (flavor.in(ID($assert), ID($assume)) && !init_one.count(A)) break;
						}

						const auto &A_map = ffmap.at(A);
						const auto &EN_map = ffmap.at(EN);

						if (A_map.second != EN_map.second)
							break;

						cell->setPort(ID::A, A_map.first);
						cell->setPort(ID::EN, EN_map.first);
					}
				}
			}
			else
			if (mode == 'd')
			{
				for (auto cell : constr_cells)
				{
					if (is_triggered_check_cell(cell))
						log_error("Cannot delay edge triggered $check cell %s, run async2sync or clk2fflogic first.\n", log_id(cell));

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
			if (mode =='p')
			{
				for (auto cell : constr_cells)
				{
					if (cell->type == ID($check)) {
						Cell *cover = module->addCell(NEW_ID_SUFFIX("coverenable"), ID($check));
						cover->attributes = cell->attributes;
						cover->parameters = cell->parameters;
						cover->setParam(ID(FLAVOR), Const("cover"));

						for (auto const &conn : cell->connections())
							if (!conn.first.in(ID::A, ID::EN))
								cover->setPort(conn.first, conn.second);
						cover->setPort(ID::A, cell->getPort(ID::EN));
						cover->setPort(ID::EN, State::S1);
					} else {
						module->addCover(NEW_ID_SUFFIX("coverenable"),
							cell->getPort(ID::EN), State::S1, cell->get_src_attribute());
					}
				}
			}
			else
			if (mode == 'c')
			{
				for (auto cell : constr_cells) {
					IdString flavor = formal_flavor(cell);
					if (assert2assume && flavor == ID($assert))
						set_formal_flavor(cell, ID($assume));
					else if (assume2assert && flavor == ID($assume))
						set_formal_flavor(cell, ID($assert));
					else if (live2fair && flavor == ID($live))
						set_formal_flavor(cell, ID($fair));
					else if (fair2live && flavor == ID($fair))
						set_formal_flavor(cell, ID($live));
				}
			}
			else
			if (mode == 'l')
			{
				for (auto cell : constr_cells) {
					if (cell->type != ID($check))
						continue;

					if (is_triggered_check_cell(cell))
						log_error("Cannot lower edge triggered $check cell %s, run async2sync or clk2fflogic first.\n", log_id(cell));


					Cell *plain_cell = module->addCell(NEW_ID, formal_flavor(cell));

					plain_cell->attributes = cell->attributes;

					SigBit sig_a = cell->getPort(ID::A);
					SigBit sig_en = cell->getPort(ID::EN);

					plain_cell->setPort(ID::A, sig_a);
					plain_cell->setPort(ID::EN, sig_en);

					if (plain_cell->type.in(ID($assert), ID($assume)))
						sig_a = module->Not(NEW_ID, sig_a);

					SigBit combined_en = module->And(NEW_ID, sig_a, sig_en);

					module->swap_names(cell, plain_cell);

					if (cell->getPort(ID::ARGS).empty()) {
						module->remove(cell);
					} else {
						cell->type = ID($print);
						cell->setPort(ID::EN, combined_en);
						cell->unsetPort(ID::A);
						cell->unsetParam(ID(FLAVOR));
					}
				}
			}
		}
	}
} ChformalPass;

PRIVATE_NAMESPACE_END
