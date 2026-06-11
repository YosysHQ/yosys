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
#include "kernel/log_help.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static TwineRef formal_flavor(RTLIL::Cell *cell)
{
	if (cell->type != TW($check))
		return cell->type_impl;

	std::string flavor_param = cell->getParam(ID(FLAVOR)).decode_string();
	if (flavor_param == "assert")
		return TW($assert);
	else if (flavor_param == "assume")
		return TW($assume);
	else if (flavor_param == "cover")
		return TW($cover);
	else if (flavor_param == "live")
		return TW($live);
	else if (flavor_param == "fair")
		return TW($fair);
	else
		log_abort();
}

static void set_formal_flavor(RTLIL::Cell *cell, TwineRef flavor)
{
	if (cell->type != TW($check)) {
		cell->type_impl = flavor;
		return;
	}

	if (flavor == TW($assert))
		cell->setParam(ID(FLAVOR), std::string("assert"));
	else if (flavor == TW($assume))
		cell->setParam(ID(FLAVOR), std::string("assume"));
	else if (flavor == TW($cover))
		cell->setParam(ID(FLAVOR), std::string("cover"));
	else if (flavor == TW($live))
		cell->setParam(ID(FLAVOR), std::string("live"));
	else if (flavor == TW($fair))
		cell->setParam(ID(FLAVOR), std::string("fair"));
	else
		log_abort();
}

static bool is_triggered_check_cell(RTLIL::Cell * cell)
{
	return cell->type == TW($check) && cell->getParam(ID(TRG_ENABLE)).as_bool();
}

struct ChformalPass : public Pass {
	ChformalPass() : Pass("chformal", "change formal constraints of the design") {}

	bool formatted_help() override {
		auto *help = PrettyHelp::get_current();
		help->set_group("formal");

		auto content_root = help->get_root();

		content_root->usage("chformal [types] [mode] [options] [selection]");
		content_root->paragraph(
			"Make changes to the formal constraints of the design. The [types] options "
			"the type of constraint to operate on. If none of the following options are "
			"given, the command will operate on all constraint types:"
		);

		content_root->option("-assert", "`$assert` cells, representing ``assert(...)`` constraints");
		content_root->option("-assume", "`$assume` cells, representing ``assume(...)`` constraints");
		content_root->option("-live", "`$live` cells, representing ``assert(s_eventually ...)``");
		content_root->option("-fair", "`$fair` cells, representing ``assume(s_eventually ...)``");
		content_root->option("-cover", "`$cover` cells, representing ``cover()`` statements");
		content_root->paragraph(
			"Additionally chformal will operate on `$check` cells corresponding to the "
			"selected constraint types."
		);

		content_root->paragraph("Exactly one of the following modes must be specified:");

		content_root->option("-remove", "remove the cells and thus constraints from the design");
		content_root->option("-early",
			"bypass FFs that only delay the activation of a constraint. When inputs "
			"of the bypassed FFs do not remain stable between clock edges, this may "
			"result in unexpected behavior."
		);
		content_root->option("-delay <N>", "delay activation of the constraint by <N> clock cycles");
		content_root->option("-skip <N>", "ignore activation of the constraint in the first <N> clock cycles");
		auto cover_option = content_root->open_option("-coverenable");
		cover_option->paragraph(
			"add cover statements for the enable signals of the constraints"
		);
#ifdef YOSYS_ENABLE_VERIFIC
		cover_option->paragraph(
			"Note: For the Verific frontend it is currently not guaranteed that a "
			"reachable SVA statement corresponds to an active enable signal."
		);
#endif
		content_root->option("-assert2assume");
		content_root->option("-assert2cover");
		content_root->option("-assume2assert");
		content_root->option("-live2fair");
		content_root->option("-fair2live", "change the roles of cells as indicated. these options can be combined");
		content_root->option("-lower",
			"convert each $check cell into an $assert, $assume, $live, $fair or "
			"$cover cell. If the $check cell contains a message, also produce a "
			"$print cell."
		);
		return true;
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool assert2assume = false;
		bool assert2cover = false;
		bool assume2assert = false;
		bool live2fair = false;
		bool fair2live = false;

		pool<TwineRef> constr_types;
		char mode = 0;
		int mode_arg = 0;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-assert") {
				constr_types.insert(TW($assert));
				continue;
			}
			if (args[argidx] == "-assume") {
				constr_types.insert(TW($assume));
				continue;
			}
			if (args[argidx] == "-live") {
				constr_types.insert(TW($live));
				continue;
			}
			if (args[argidx] == "-fair") {
				constr_types.insert(TW($fair));
				continue;
			}
			if (args[argidx] == "-cover") {
				constr_types.insert(TW($cover));
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
			if ((mode == 0 || mode == 'c') && args[argidx] == "-assert2cover") {
				assert2cover = true;
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

		// TODO Disabled signorm because swap_names breaks fanout logic
		design->sigNormalize(false);

		if (constr_types.empty()) {
			constr_types.insert(TW($assert));
			constr_types.insert(TW($assume));
			constr_types.insert(TW($live));
			constr_types.insert(TW($fair));
			constr_types.insert(TW($cover));
		}

		if (assert2assume && assert2cover) {
			log_cmd_error("Cannot use both -assert2assume and -assert2cover.\n");
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
					if (cell->type == TW($ff)) {
						SigSpec D = sigmap(cell->getPort(TW::D));
						SigSpec Q = sigmap(cell->getPort(TW::Q));
						for (int i = 0; i < GetSize(D); i++)
							ffmap[Q[i]] = make_pair(D[i], make_pair(State::Sm, false));
					}
					if (cell->type == TW($dff)) {
						SigSpec D = sigmap(cell->getPort(TW::D));
						SigSpec Q = sigmap(cell->getPort(TW::Q));
						SigSpec C = sigmap(cell->getPort(TW::CLK));
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
						cell->setPort(TW::TRG, SigSpec());
						cell->setParam(ID::TRG_ENABLE, false);
						cell->setParam(ID::TRG_WIDTH, 0);
						cell->setParam(ID::TRG_POLARITY, false);
					}

					TwineRef flavor = formal_flavor(cell);

					while (true)
					{
						SigSpec A = sigmap(cell->getPort(TW::A));
						SigSpec EN = sigmap(cell->getPort(TW::EN));

						if (ffmap.count(A) == 0 || ffmap.count(EN) == 0)
							break;

						if (!init_zero.count(EN)) {
							if (flavor == TW($cover)) break;
							if (flavor.in(TW($assert), TW($assume)) && !init_one.count(A)) break;
						}

						const auto &A_map = ffmap.at(A);
						const auto &EN_map = ffmap.at(EN);

						if (A_map.second != EN_map.second)
							break;

						cell->setPort(TW::A, A_map.first);
						cell->setPort(TW::EN, EN_map.first);
					}
				}
			}
			else
			if (mode == 'd')
			{
				for (auto cell : constr_cells)
				{
					if (is_triggered_check_cell(cell))
						log_error("Cannot delay edge triggered $check cell %s, run async2sync or clk2fflogic first.\n", cell);

					for (int i = 0; i < mode_arg; i++)
					{
						SigSpec orig_a = cell->getPort(TW::A);
						SigSpec orig_en = cell->getPort(TW::EN);

						Wire *new_a = module->addWire(NEW_TWINE);
						Wire *new_en = module->addWire(NEW_TWINE);
						new_en->attributes[ID::init] = State::S0;

						module->addFf(NEW_TWINE, orig_a, new_a);
						module->addFf(NEW_TWINE, orig_en, new_en);

						cell->setPort(TW::A, new_a);
						cell->setPort(TW::EN, new_en);
					}
				}
			}
			else
			if (mode == 's')
			{
				SigSpec en = State::S1;

				for (int i = 0; i < mode_arg; i++) {
					Wire *w = module->addWire(NEW_TWINE);
					w->attributes[ID::init] = State::S0;
					module->addFf(NEW_TWINE, en, w);
					en = w;
				}

				for (auto cell : constr_cells)
					cell->setPort(TW::EN, module->LogicAnd(NEW_TWINE, en, cell->getPort(TW::EN)));
			}
			else
			if (mode =='p')
			{
				for (auto cell : constr_cells)
				{
					if (cell->type == TW($check)) {
						Cell *cover = module->addCell(NEW_TWINE_SUFFIX("coverenable"), TW::$check);
						cover->attributes = cell->attributes;
						if (cell->src_id() != Twine::Null && module->design)
							cover->set_src_id(cell->src_id());
						cover->parameters = cell->parameters;
						cover->setParam(ID(FLAVOR), Const("cover"));

						for (auto const &conn : cell->connections())
							if (conn.first != TW::A && conn.first != TW::EN)
								cover->setPort(conn.first, conn.second);
						cover->setPort(TW::A, cell->getPort(TW::EN));
						cover->setPort(TW::EN, State::S1);
					} else {
						module->addCover(NEW_TWINE_SUFFIX("coverenable"),
							cell->getPort(TW::EN), State::S1, module->design->twines.add(Twine{cell->get_src_attribute()}));
					}
				}
			}
			else
			if (mode == 'c')
			{
				for (auto cell : constr_cells) {
					TwineRef flavor = formal_flavor(cell);
					if (assert2assume && flavor == TW($assert))
						set_formal_flavor(cell, TW($assume));
					if (assert2cover && flavor == TW($assert))
						set_formal_flavor(cell, TW($cover));
					else if (assume2assert && flavor == TW($assume))
						set_formal_flavor(cell, TW($assert));
					else if (live2fair && flavor == TW($live))
						set_formal_flavor(cell, TW($fair));
					else if (fair2live && flavor == TW($fair))
						set_formal_flavor(cell, TW($live));
				}
			}
			else
			if (mode == 'l')
			{
				for (auto cell : constr_cells) {
					if (cell->type != TW($check))
						continue;

					if (is_triggered_check_cell(cell))
						log_error("Cannot lower edge triggered $check cell %s, run async2sync or clk2fflogic first.\n", cell);


					Cell *plain_cell = module->addCell(NEW_TWINE, formal_flavor(cell));

					plain_cell->attributes = cell->attributes;
					if (cell->src_id() != Twine::Null && module->design)
						plain_cell->set_src_id(cell->src_id());

					SigBit sig_a = cell->getPort(TW::A);
					SigBit sig_en = cell->getPort(TW::EN);

					plain_cell->setPort(TW::A, sig_a);
					plain_cell->setPort(TW::EN, sig_en);

					if (plain_cell->type.in(TW($assert), TW($assume)))
						sig_a = module->Not(NEW_TWINE, sig_a);

					SigBit combined_en = module->And(NEW_TWINE, sig_a, sig_en);

					module->swap_names(cell, plain_cell);

					if (cell->getPort(TW::ARGS).empty()) {
						module->remove(cell);
					} else {
						cell->type_impl = TW::$print;
						cell->setPort(TW::EN, combined_en);
						cell->unsetPort(TW::A);
						cell->unsetParam(ID(FLAVOR));
					}
				}
			}
		}
	}
} ChformalPass;

PRIVATE_NAMESPACE_END
