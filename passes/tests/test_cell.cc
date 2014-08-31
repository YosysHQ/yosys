/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2014  Johann Glaser <Johann.Glaser@gmx.at>
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
#include "kernel/consteval.h"
#include <algorithm>

static uint32_t xorshift32_state = 123456789;

static uint32_t xorshift32(uint32_t limit) {
	xorshift32_state ^= xorshift32_state << 13;
	xorshift32_state ^= xorshift32_state >> 17;
	xorshift32_state ^= xorshift32_state << 5;
	return xorshift32_state % limit;
}

static void create_gold_module(RTLIL::Design *design, RTLIL::IdString cell_type, std::string cell_type_flags)
{
	RTLIL::Module *module = design->addModule("\\gold");
	RTLIL::Cell *cell = module->addCell("\\UUT", cell_type);
	RTLIL::Wire *wire;

	if (cell_type == "$lut")
	{
		int width = 1 + xorshift32(6);

		wire = module->addWire("\\A");
		wire->width = width;
		wire->port_input = true;
		cell->setPort("\\A", wire);

		wire = module->addWire("\\Y");
		wire->port_output = true;
		cell->setPort("\\Y", wire);

		RTLIL::SigSpec config;
		for (int i = 0; i < (1 << width); i++)
			config.append(xorshift32(2) ? RTLIL::S1 : RTLIL::S0);

		cell->setParam("\\LUT", config.as_const());
	}

	if (cell_type_flags.find('A') != std::string::npos) {
		wire = module->addWire("\\A");
		wire->width = 1 + xorshift32(8);
		wire->port_input = true;
		cell->setPort("\\A", wire);
	}

	if (cell_type_flags.find('B') != std::string::npos) {
		wire = module->addWire("\\B");
		if (cell_type_flags.find('h') != std::string::npos)
			wire->width = 1 + xorshift32(6);
		else
			wire->width = 1 + xorshift32(8);
		wire->port_input = true;
		cell->setPort("\\B", wire);
	}

	if (cell_type_flags.find('S') != std::string::npos && xorshift32(2)) {
		if (cell_type_flags.find('A') != std::string::npos)
			cell->parameters["\\A_SIGNED"] = true;
		if (cell_type_flags.find('B') != std::string::npos)
			cell->parameters["\\B_SIGNED"] = true;
	}

	if (cell_type_flags.find('s') != std::string::npos) {
		if (cell_type_flags.find('A') != std::string::npos && xorshift32(2))
			cell->parameters["\\A_SIGNED"] = true;
		if (cell_type_flags.find('B') != std::string::npos && xorshift32(2))
			cell->parameters["\\B_SIGNED"] = true;
	}

	if (cell_type_flags.find('Y') != std::string::npos) {
		wire = module->addWire("\\Y");
		wire->width = 1 + xorshift32(8);
		wire->port_output = true;
		cell->setPort("\\Y", wire);
	}

	module->fixup_ports();
	cell->fixup_parameters();
	cell->check();
}

static void run_eval_test(RTLIL::Design *design)
{
	RTLIL::Module *gold_mod = design->module("\\gold");
	RTLIL::Module *gate_mod = design->module("\\gate");
	ConstEval gold_ce(gold_mod), gate_ce(gate_mod);

	log("Eval testing: ");

	for (int i = 0; i < 64; i++)
	{
		log(".");
		gold_ce.clear();
		gate_ce.clear();

		for (auto port : gold_mod->ports)
		{
			RTLIL::Wire *gold_wire = gold_mod->wire(port);
			RTLIL::Wire *gate_wire = gate_mod->wire(port);

			log_assert(gold_wire != nullptr);
			log_assert(gate_wire != nullptr);
			log_assert(gold_wire->port_input == gate_wire->port_input);
			log_assert(SIZE(gold_wire) == SIZE(gate_wire));

			if (!gold_wire->port_input)
				continue;

			RTLIL::Const in_value;
			for (int i = 0; i < SIZE(gold_wire); i++)
				in_value.bits.push_back(xorshift32(2) ? RTLIL::S1 : RTLIL::S0);

			if (xorshift32(4) == 0) {
				int inv_chance = 1 + xorshift32(8);
				for (int i = 0; i < SIZE(gold_wire); i++)
					if (xorshift32(inv_chance) == 0)
						in_value.bits[i] = RTLIL::Sx;
			}

			// log("%s: %s\n", log_id(gold_wire), log_signal(in_value));

			gold_ce.set(gold_wire, in_value);
			gate_ce.set(gate_wire, in_value);
		}

		for (auto port : gold_mod->ports)
		{
			RTLIL::Wire *gold_wire = gold_mod->wire(port);
			RTLIL::Wire *gate_wire = gate_mod->wire(port);

			log_assert(gold_wire != nullptr);
			log_assert(gate_wire != nullptr);
			log_assert(gold_wire->port_output == gate_wire->port_output);
			log_assert(SIZE(gold_wire) == SIZE(gate_wire));

			if (!gold_wire->port_output)
				continue;

			RTLIL::SigSpec gold_outval(gold_wire);
			RTLIL::SigSpec gate_outval(gate_wire);

			if (!gold_ce.eval(gold_outval))
				log_error("Failed to eval %s in gold module.\n", log_id(gold_wire));

			if (!gate_ce.eval(gate_outval))
				log_error("Failed to eval %s in gate module.\n", log_id(gate_wire));

			bool gold_gate_mismatch = false;
			for (int i = 0; i < SIZE(gold_wire); i++) {
				if (gold_outval[i] == RTLIL::Sx)
					continue;
				if (gold_outval[i] == gate_outval[i])
					continue;
				gold_gate_mismatch = true;
				break;
			}

			if (gold_gate_mismatch)
				log_error("Mismatch in output %s: gold:%s != gate:%s\n", log_id(gate_wire), log_signal(gold_outval), log_signal(gate_outval));

			// log("%s: %s\n", log_id(gold_wire), log_signal(gold_outval));
		}
	}

	log(" ok.\n");
}

struct TestCellPass : public Pass {
	TestCellPass() : Pass("test_cell", "automatically test the implementation of a cell type") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    test_cell [options] {cell-types}\n");
		log("\n");
		log("Tests the internal implementation of the given cell type (for example '$mux')\n");
		log("by comparing SAT solver, EVAL and TECHMAP implementations of the cell types..\n");
		log("\n");
		log("Run with 'all' instead of a cell type to run the test on all supported\n");
		log("cell types.\n");
		log("\n");
		log("    -n {integer}\n");
		log("        create this number of cell instances and test them (default = 100).\n");
		log("\n");
		log("    -s {positive_integer}\n");
		log("        use this value as rng seed value (default = unix time).\n");
		log("\n");
		log("    -f {ilang_file}\n");
		log("        don't generate circuits. instead load the specified ilang file.\n");
		log("\n");
		log("    -map {filename}\n");
		log("        pass this option to techmap.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design*)
	{
		int num_iter = 100;
		std::string techmap_cmd = "techmap -assert";
		std::string ilang_file;
		xorshift32_state = 0;

		int argidx;
		for (argidx = 1; argidx < SIZE(args); argidx++)
		{
			if (args[argidx] == "-n" && argidx+1 < SIZE(args)) {
				num_iter = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-s" && argidx+1 < SIZE(args)) {
				xorshift32_state = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-map" && argidx+1 < SIZE(args)) {
				techmap_cmd += " -map " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-f" && argidx+1 < SIZE(args)) {
				ilang_file = args[++argidx];
				num_iter = 1;
				continue;
			}
			break;
		}

		if (xorshift32_state == 0)
			xorshift32_state = time(NULL);

		std::map<std::string, std::string> cell_types;
		std::vector<std::string> selected_cell_types;

		cell_types["$not"] = "ASY";
		cell_types["$pos"] = "ASY";
		cell_types["$bu0"] = "ASY";
		cell_types["$neg"] = "ASY";

		cell_types["$and"]  = "ABSY";
		cell_types["$or"]   = "ABSY";
		cell_types["$xor"]  = "ABSY";
		cell_types["$xnor"] = "ABSY";

		cell_types["$reduce_and"]  = "ASY";
		cell_types["$reduce_or"]   = "ASY";
		cell_types["$reduce_xor"]  = "ASY";
		cell_types["$reduce_xnor"] = "ASY";
		cell_types["$reduce_bool"] = "ASY";

		cell_types["$shl"]    = "ABshY";
		cell_types["$shr"]    = "ABshY";
		cell_types["$sshl"]   = "ABshY";
		cell_types["$sshr"]   = "ABshY";
		cell_types["$shift"]  = "ABshY";
		cell_types["$shiftx"] = "ABshY";

		cell_types["$lt"]  = "ABSY";
		cell_types["$le"]  = "ABSY";
		cell_types["$eq"]  = "ABSY";
		cell_types["$ne"]  = "ABSY";
		// cell_types["$eqx"] = "ABSY";
		// cell_types["$nex"] = "ABSY";
		cell_types["$ge"]  = "ABSY";
		cell_types["$gt"]  = "ABSY";

		cell_types["$add"] = "ABSY";
		cell_types["$sub"] = "ABSY";
		cell_types["$mul"] = "ABSY";
		cell_types["$div"] = "ABSY";
		cell_types["$mod"] = "ABSY";
		// cell_types["$pow"] = "ABsY";

		cell_types["$logic_not"] = "ASY";
		cell_types["$logic_and"] = "ABSY";
		cell_types["$logic_or"]  = "ABSY";

		// cell_types["$mux"] = "A";
		// cell_types["$pmux"] = "A";
		// cell_types["$slice"] = "A";
		// cell_types["$concat"] = "A";
		// cell_types["$assert"] = "A";

		cell_types["$lut"] = "*";
		// cell_types["$alu"] = "*";

		for (; argidx < SIZE(args); argidx++)
		{
			if (args[argidx].rfind("-", 0) == 0)
				log_cmd_error("Unexpected option: %s\n", args[argidx].c_str());

			if (args[argidx] == "all") {
				for (auto &it : cell_types)
					if (std::count(selected_cell_types.begin(), selected_cell_types.end(), it.first) == 0)
						selected_cell_types.push_back(it.first);
				continue;
			}

			if (cell_types.count(args[argidx]) == 0) {
				std::string cell_type_list;
				int charcount = 100;
				for (auto &it : cell_types) {
					if (charcount > 60) {
						cell_type_list += "\n" + it.first;
						charcount = 0;
					} else
						cell_type_list += " " + it.first;
					charcount += SIZE(it.first);
				}
				log_cmd_error("The cell type `%s' is currently not supported. Try one of these:%s\n",
						args[argidx].c_str(), cell_type_list.c_str());
			}

			if (std::count(selected_cell_types.begin(), selected_cell_types.end(), args[argidx]) == 0)
				selected_cell_types.push_back(args[argidx]);
		}

		if (!ilang_file.empty()) {
			if (!selected_cell_types.empty())
				log_cmd_error("Do not specify any cell types when using -f.\n");
			selected_cell_types.push_back("ilang");
		}

		if (selected_cell_types.empty())
			log_cmd_error("No cell type to test specified.\n");

		for (auto cell_type : selected_cell_types)
			for (int i = 0; i < num_iter; i++)
			{
				RTLIL::Design *design = new RTLIL::Design;
				if (cell_type == "ilang")
					Frontend::frontend_call(design, NULL, std::string(), "ilang " + ilang_file);
				else
					create_gold_module(design, cell_type, cell_types.at(cell_type));
				Pass::call(design, stringf("copy gold gate; %s gate; opt gate", techmap_cmd.c_str()));
				Pass::call(design, "miter -equiv -flatten -make_outputs -ignore_gold_x gold gate miter; dump gold");
				Pass::call(design, "sat -verify -enable_undef -prove trigger 0 -show-inputs -show-outputs miter");
				run_eval_test(design);
				delete design;
			}
	}
} TestCellPass;

