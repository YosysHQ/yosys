#include <gtest/gtest.h>
#include "kernel/yosys.h"
#include "kernel/yosys_common.h"
#include "kernel/celltypes.h"
#include "kernel/newcelltypes.h"

#include <unordered_set>

YOSYS_NAMESPACE_BEGIN

TEST(CellTypesTest, basic)
{
	yosys_setup();
	log_files.push_back(stdout);
	CellTypes older;
	NewCellTypes newer;
	log("setup nullptr\n");
	older.setup(nullptr);
	newer.setup(nullptr);
	log("setup type bleh\n");
	older.setup_type(ID(bleh), {ID::G}, {ID::H, ID::I}, false, true);
	newer.setup_type(ID(bleh), {ID::G}, {ID::H, ID::I}, false, true);

	EXPECT_EQ(older.cell_known(ID(aaaaa)), newer.cell_known(ID(aaaaa)));
	EXPECT_EQ(older.cell_known(ID($and)), newer.cell_known(ID($and)));
	for (size_t i = 0; i < static_cast<size_t>(RTLIL::StaticId::STATIC_ID_END); i++) {
		IdString type;
		type.index_ = i;
		if (older.cell_known(type) != newer.cell_known(type))
			std::cout << i << " " << type.str() << "\n";
		EXPECT_EQ(older.cell_known(type), newer.cell_known(type));

		if (RTLIL::builtin_ff_cell_types().count(type) != StaticCellTypes::categories.is_ff(type))
			std::cout << i << " " << type.str() << "\n";
		EXPECT_EQ(RTLIL::builtin_ff_cell_types().count(type), StaticCellTypes::categories.is_ff(type));
	}
	yosys_shutdown();
}

YOSYS_NAMESPACE_END
