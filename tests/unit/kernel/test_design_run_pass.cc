#include <gtest/gtest.h>
#include "kernel/rtlil.h"
#include "kernel/register.h"

YOSYS_NAMESPACE_BEGIN

class DesignRunPassTest : public testing::Test {
protected:
	DesignRunPassTest() {
		if (log_files.empty()) log_files.emplace_back(stdout);
	}
	virtual void SetUp() override {
		IdString::ensure_prepopulated();
	}
};

TEST_F(DesignRunPassTest, RunPassExecutesSuccessfully)
{
	// Create a design with a simple module
	RTLIL::Design *design = new RTLIL::Design;
	RTLIL::Module *module = new RTLIL::Module;
	module->name = RTLIL::IdString("\\test_module");
	design->add(module);

	// Add a simple wire to the module
	RTLIL::Wire *wire = module->addWire(RTLIL::IdString("\\test_wire"), 1);
	wire->port_input = true;
	wire->port_id = 1;
	module->fixup_ports();

	// Call run_pass with a simple pass
	// We use "check" which is a simple pass that just validates the design
	ASSERT_NO_THROW(design->run_pass("check"));

	// Verify the design still exists and has the module
	EXPECT_EQ(design->modules().size(), 1);
	EXPECT_NE(design->module(RTLIL::IdString("\\test_module")), nullptr);

	delete design;
}

TEST_F(DesignRunPassTest, RunPassWithHierarchy)
{
	// Create a design with a simple module
	RTLIL::Design *design = new RTLIL::Design;
	RTLIL::Module *module = new RTLIL::Module;
	module->name = RTLIL::IdString("\\top");
	design->add(module);

	// Call run_pass with hierarchy pass
	ASSERT_NO_THROW(design->run_pass("hierarchy"));

	// Verify the design still has the module
	EXPECT_EQ(design->modules().size(), 1);

	delete design;
}

YOSYS_NAMESPACE_END
