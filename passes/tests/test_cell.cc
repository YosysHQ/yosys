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

#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

static uint32_t xorshift32(uint32_t limit) {
	static uint32_t x = 123456789;
	x ^= x << 13;
	x ^= x >> 17;
	x ^= x << 5;
	return x % limit;
}

static void create_gold_module(RTLIL::Design *design, std::string cell_type, std::string cell_type_flags)
{
	RTLIL::Module *module = design->addModule("\\gold");
	RTLIL::Cell *cell = module->addCell("\\UUT", cell_type);

	if (cell_type_flags.find('A') != std::string::npos) {
		RTLIL::Wire *wire = module->addWire("\\A");
		wire->width = 1 + xorshift32(8);
		wire->port_input = true;
		cell->set("\\A", wire);
	}

	if (cell_type_flags.find('B') != std::string::npos) {
		RTLIL::Wire *wire = module->addWire("\\B");
		if (cell_type_flags.find('h') != std::string::npos)
			wire->width = 1 + xorshift32(6);
		else
			wire->width = 1 + xorshift32(8);
		wire->port_input = true;
		cell->set("\\B", wire);
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
		RTLIL::Wire *wire = module->addWire("\\Y");
		wire->width = 1 + xorshift32(8);
		wire->port_output = true;
		cell->set("\\Y", wire);
	}

	module->fixup_ports();
	cell->fixup_parameters();
	cell->check();
}

struct TestCellPass : public Pass {
	TestCellPass() : Pass("test_cell", "automatically test the implementation of a cell type") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    test_cell {cell-type}\n");
		log("\n");
		log("Tests the internal implementation of the given cell type (for example '$mux')\n");
		log("by comparing SAT solver, EVAL and TECHMAP implementations of the cell type..\n");
		log("\n");
		log("Run with '-all' instead of a cell type to run the test on all supported\n");
		log("cell types.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *current_design)
	{
		if (SIZE(args) != 2)
			log_cmd_error("Expecting exactly one argument.\n");

		std::map<std::string, std::string> cell_types;
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
		// cell_types["$shift"]  = "ABshY";  <-- FIXME
		// cell_types["$shiftx"] = "ABshY";

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
		// cell_types["$safe_pmux"] = "A";
		// cell_types["$lut"] = "A";
		// cell_types["$assert"] = "A";

		if (args[1] == "-all") {
			for (auto &it : cell_types)
				Pass::call(current_design, "test_cell " + it.first);
			return;
		}

		if (cell_types.count(args[1]) == 0) {
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
			log_cmd_error("This cell type is currently not supported. Try one of these:%s\n", cell_type_list.c_str());
		}

		for (int i = 0; i < 100; i++)
		{
			RTLIL::Design *design = new RTLIL::Design;
			create_gold_module(design, args[1], cell_types.at(args[1]));
			Pass::call(design, "copy gold gate; techmap gate; opt gate; dump gold");
			Pass::call(design, "miter -equiv -flatten -ignore_gold_x gold gate miter");
			Pass::call(design, "sat -verify -enable_undef -prove trigger 0 miter");
			delete design;
		}
	}
} TestCellPass;

