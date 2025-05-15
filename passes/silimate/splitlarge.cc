/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2025  Silimate Inc.     <akash@silimate.com>
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
 #include "kernel/utils.h"

 #include <queue>

 USING_YOSYS_NAMESPACE
 PRIVATE_NAMESPACE_BEGIN

 struct SplitlargeWorker
 {
	 Module *module;
	 int max_width;

	 SplitlargeWorker(Module *module, int max_width) : module(module), max_width(max_width)
	 {
	 }

	 void split_spec(int high_width, int low_width, SigSpec &high, SigSpec &low, const SigSpec &splittable, bool sign_extend)
	 {
		SigSpec splittable_ext = splittable;
		splittable_ext.extend_u0(high_width + low_width, sign_extend);

		high = splittable_ext.extract(low_width, high_width);
		low = splittable_ext.extract(0, low_width);
	 }

	 int width_addsub(Cell *cell)
	 {
		int a_width = cell->parameters[ID::A_WIDTH].as_int();
		int b_width = cell->parameters[ID::B_WIDTH].as_int();
		return max(a_width, b_width);
	 }

	 void split_addsub(Cell *cell, std::queue<Cell *>& q)
	 {
		auto width = width_addsub(cell);
		auto width_low = width / 2;
		auto width_high = width - width_low; // Handle odd widths

		auto a = cell->getPort(ID::A);
		auto b = cell->getPort(ID::B);
		bool aSigned = cell->parameters[ID::A_SIGNED].as_bool();
		bool bSigned = cell->parameters[ID::B_SIGNED].as_bool();
		SigSpec aHigh, aLow, bHigh, bLow;

		split_spec(width_high, width_low, aHigh, aLow, cell->getPort(ID::A), cell->getParam(ID::A_SIGNED).as_bool());
		split_spec(width_high, width_low, bHigh, bLow, cell->getPort(ID::B), cell->getParam(ID::B_SIGNED).as_bool());

		std::string yHighName = cell->name.str() + "_splitres1";
		std::string yCarryName = cell->name.str() + "_splitresc";
		std::string yLowName = cell->name.str() + "_splitres0";
		std::string nameHigh = cell->name.str() + "_split1";
		std::string nameLow = cell->name.str() + "_split0";
		std::string nameCarry = cell->name.str() + "_splitc";

		auto yCarry = module->addWire(yCarryName, width_high + 1);
		auto yHigh = module->addWire(yHighName, width_high + 1);
		auto yLow = module->addWire(yLowName, width_low + 1);

		auto backupResultSpec = cell->getPort(ID::Y);

		// Modify existing adder to be low
		module->rename(cell, nameLow);
		cell->setPort(ID::A, aLow);
		cell->setPort(ID::B, bLow);
		cell->setPort(ID::Y, yLow);
		cell->parameters[ID::A_WIDTH] = width_low;
		cell->parameters[ID::B_WIDTH] = width_low;
		cell->parameters[ID::Y_WIDTH] = width_low + 1;
		cell->parameters[ID::A_SIGNED] = 0;
		cell->parameters[ID::B_SIGNED] = 0;
		if (width_low > max_width) {
			q.emplace(cell);
		}

		// Create high adder
		auto highCell = module->addCell(nameHigh, cell); // copy type and parameters
		highCell->setPort(ID::A, aHigh);
		highCell->setPort(ID::B, bHigh);
		highCell->setPort(ID::Y, yHigh);
		highCell->parameters[ID::A_WIDTH] = width_high;
		highCell->parameters[ID::B_WIDTH] = width_high;
		highCell->parameters[ID::Y_WIDTH] = width_high + 1;
		highCell->parameters[ID::A_SIGNED] = aSigned;
		highCell->parameters[ID::B_SIGNED] = bSigned;
		if (width_high > max_width) {
			q.emplace(highCell);
		}

		// Create carry adder
		auto carryCell = module->addCell(nameCarry, highCell); // copy type and parameters
		auto carryBit = SigSpec(yLow).extract(width_low, 1);
		carryBit.extend_u0(2);

		carryCell->setPort(ID::A, yHigh);
		carryCell->parameters[ID::A_WIDTH] = width_high + 1;
		carryCell->parameters[ID::A_SIGNED] = aSigned || bSigned;
		carryCell->setPort(ID::B, carryBit);
		carryCell->parameters[ID::B_WIDTH] =  2;
		carryCell->parameters[ID::B_SIGNED] = aSigned || bSigned;
		carryCell->setPort(ID::Y, yCarry);
		if (width_high + 1 > max_width) {
			q.emplace(carryCell);
		}

		// Concatenate
		auto ySpec = SigSpec({yCarry, SigSpec(yLow).extract(0, width_low)});
		module->connect(backupResultSpec, ySpec.extract(0, backupResultSpec.size()));
	 }

	 void split()
	 {
		std::queue<Cell *> q;
		for (auto pair: module->cells_) {
			auto& cell = pair.second;
			if (cell->type == ID($add) && width_addsub(cell) > max_width) {
				q.emplace(cell);
			} else if (cell->type == ID($sub) && width_addsub(cell) > max_width) {
				q.emplace(cell);
			}
		}

		while (!q.empty()) {
			auto cell = q.front();
			q.pop();

			if (cell->type == ID($add)) {
				split_addsub(cell, q);
			}
			else if (cell->type == ID($sub)) {
				split_addsub(cell, q);
			}
		}
	 }

 };

 struct SplitlargePass : public Pass {
	SplitlargePass() : Pass("splitlarge", "splitting large arithmetic operators") { }
	 void help() override
	 {
		 //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		 log("\n");
		 log("    splitlarge [selection]\n");
		 log("\n");
		 log("    splits arithmetic operators (specifically $add, $sub) into a number of\n");
		 log("    operators with smaller widths. should be run after techmap/simplemap\n");
		 log("\n");
		 log("\n");
		 log("    -max_width n\n");
		 log("        max tolerable width of an $add or $sub operator.\n");
		 log("        * The width of $add/$sub is defined as max(a_width, b_width)\n");
		 log("        * If unset, 128 is used as a default value.\n");
		 log("\n");
	 }
	 void execute(std::vector<std::string> args, RTLIL::Design *design) override
	 {
		 int max_width = 128;
		 log_header(design, "Executing SPLITLARGE pass (splitting wide $add/$sub operators).\n");

		 size_t argidx;
		 for (argidx = 1; argidx < args.size(); argidx++)
		 {
			 if (args[argidx] == "-max_width" && argidx+1 < args.size()) {
				max_width = std::stoul(args[++argidx]);
				 continue;
			 }
			 break;
		 }
		 extra_args(args, argidx, design);

		 for (auto module : design->selected_modules())
		 {
			SplitlargeWorker worker(module, max_width);
			worker.split();
		 }

		 Pass::call(design, "clean *");
	 }
 } SplitfanoutPass;

 PRIVATE_NAMESPACE_END
