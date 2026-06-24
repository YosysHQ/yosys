#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"
#include "tests/unit/yosysSetupEnv.h"

YOSYS_NAMESPACE_BEGIN

namespace RTLIL {

	TEST(RtlilStrTest, DesignToString) {
		Design design;
		Module *mod = design.addModule(design.twines.add(std::string{"\\my_module"}));
		mod->addWire(design.twines.add(std::string{"\\my_wire"}), 1);

		std::string design_str = design.to_rtlil_str();

		EXPECT_NE(design_str.find("module \\my_module"), std::string::npos);
		EXPECT_NE(design_str.find("end"), std::string::npos);
	}

	TEST(RtlilStrTest, ModuleToString) {
		Design design;
		Module *mod = design.addModule(design.twines.add(std::string{"\\test_mod"}));
		Wire *wire = mod->addWire(design.twines.add(std::string{"\\clk"}), 1);
		wire->port_input = true;

		std::string mod_str = mod->to_rtlil_str();

		EXPECT_NE(mod_str.find("module \\test_mod"), std::string::npos);
		EXPECT_NE(mod_str.find("wire"), std::string::npos);
		EXPECT_NE(mod_str.find("\\clk"), std::string::npos);
		EXPECT_NE(mod_str.find("input"), std::string::npos);
	}

	TEST(RtlilStrTest, WireToString) {
		Design design;
		Module *mod = design.addModule(design.twines.add(std::string{"\\m"}));
		Wire *wire = mod->addWire(design.twines.add(std::string{"\\data"}), 8);

		std::string wire_str = wire->to_rtlil_str();

		EXPECT_NE(wire_str.find("wire"), std::string::npos);
		EXPECT_NE(wire_str.find("width 8"), std::string::npos);
		EXPECT_NE(wire_str.find("\\data"), std::string::npos);
	}

	TEST(RtlilStrTest, CellToString) {
		Design design;
		Module *mod = design.addModule(design.twines.add(std::string{"\\m"}));
		Cell *cell = mod->addCell(design.twines.add(std::string{"\\u1"}), design.twines.add(std::string{"\\my_cell_type"}));

		std::string cell_str = cell->to_rtlil_str();

		EXPECT_NE(cell_str.find("cell"), std::string::npos);
		EXPECT_NE(cell_str.find("\\my_cell_type"), std::string::npos);
		EXPECT_NE(cell_str.find("\\u1"), std::string::npos);
	}

}

YOSYS_NAMESPACE_END
