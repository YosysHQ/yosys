#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace {

TEST(DesignStateTest, AutoidxInTwinePool)
{
	TwinePool a, b;
	int start = a.autoidx();
	EXPECT_EQ(b.autoidx(), start);

	IdString first = a.add(NEW_ID);
	EXPECT_EQ(a.autoidx(), start + 1);
	EXPECT_EQ(b.autoidx(), start);

	IdString second = b.add(NEW_ID_SUFFIX("tail"));
	EXPECT_EQ(b.autoidx(), start + 1);

	EXPECT_TRUE(a.str(first).ends_with(std::to_string(start)));
	EXPECT_TRUE(b.str(second).ends_with("tail$" + std::to_string(start)));
}

TEST(DesignStateTest, HashidxPerDesign)
{
	RTLIL::Design old_d;
	RTLIL::Module *old_mod = old_d.addModule(std::string("\\m"));
	RTLIL::Wire *old_wire = old_mod->addWire(NEW_ID, 1);

	RTLIL::Design new_d;
	RTLIL::Module *new_mod = new_d.addModule(std::string("\\m"));
	RTLIL::Wire *new_wire = new_mod->addWire(NEW_ID, 1);

	EXPECT_EQ(run_hash(old_d), run_hash(LARGE_HASHIDX_COLLIDER));
	EXPECT_EQ(run_hash(new_d), run_hash(LARGE_HASHIDX_COLLIDER));

	EXPECT_EQ(run_hash(old_mod), run_hash(new_mod));
	EXPECT_EQ(run_hash(old_wire), run_hash(new_wire));
}

} // namespace

YOSYS_NAMESPACE_END
