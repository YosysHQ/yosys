#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace {

TEST(DesignStateTest, HashidxPerDesign)
{
	RTLIL::Design old_d;
	RTLIL::Module *old_mod = old_d.addModule(std::string("\\m"));
	RTLIL::Wire *old_wire = old_mod->addWire(NEW_ID, 1);

	RTLIL::Design new_d;
	RTLIL::Module *new_mod = new_d.addModule(std::string("\\m"));
	RTLIL::Wire *new_wire = new_mod->addWire(NEW_ID, 1);

	// Both designs hash to the initial hasher value
	EXPECT_EQ(run_hash(old_d), 1454784245);
	EXPECT_EQ(run_hash(new_d), 1454784245);

	EXPECT_EQ(run_hash(old_mod), run_hash(new_mod));
	EXPECT_EQ(run_hash(old_wire), run_hash(new_wire));
}

} // namespace

YOSYS_NAMESPACE_END
