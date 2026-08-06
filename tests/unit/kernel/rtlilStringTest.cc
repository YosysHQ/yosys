#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace RTLIL {

	TEST(RtlilStrTest, DesignToString) {
		Design design;
		Module *mod = design.addModule("\\my_module");
		mod->addWire("\\my_wire", 1);

		std::string design_str = design.to_rtlil_str();

		EXPECT_NE(design_str.find("module \\my_module"), std::string::npos);
		EXPECT_NE(design_str.find("end"), std::string::npos);
	}

	TEST(RtlilStrTest, ModuleToString) {
		Design design;
		Module *mod = design.addModule("\\test_mod");
		Wire *wire = mod->addWire("\\clk", 1);
		wire->port_input = true;

		std::string mod_str = mod->to_rtlil_str();

		EXPECT_NE(mod_str.find("module \\test_mod"), std::string::npos);
		EXPECT_NE(mod_str.find("wire"), std::string::npos);
		EXPECT_NE(mod_str.find("\\clk"), std::string::npos);
		EXPECT_NE(mod_str.find("input"), std::string::npos);
	}

	TEST(RtlilStrTest, WireToString) {
		Design design;
		Module *mod = design.addModule("\\m");
		Wire *wire = mod->addWire("\\data", 8);

		std::string wire_str = wire->to_rtlil_str();

		EXPECT_NE(wire_str.find("wire"), std::string::npos);
		EXPECT_NE(wire_str.find("width 8"), std::string::npos);
		EXPECT_NE(wire_str.find("\\data"), std::string::npos);
	}

	TEST(RtlilStrTest, CellToString) {
		Design design;
		Module *mod = design.addModule("\\m");
		Cell *cell = mod->addCell("\\u1", design.twines.add(std::string{"\\my_cell_type"}));

		std::string cell_str = cell->to_rtlil_str();

		EXPECT_NE(cell_str.find("cell"), std::string::npos);
		EXPECT_NE(cell_str.find("\\my_cell_type"), std::string::npos);
		EXPECT_NE(cell_str.find("\\u1"), std::string::npos);
	}

}

YOSYS_NAMESPACE_END
