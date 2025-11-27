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
	older.setup(nullptr);
	newer.setup(nullptr);
	older.setup_type(ID(bleh), {ID::G}, {ID::H, ID::I}, false, true);
	newer.setup_type(ID(bleh), {ID::G}, {ID::H, ID::I}, false, true);

	EXPECT_EQ(older.cell_known(ID(aaaaa)), newer.cell_known(ID(aaaaa)));
	EXPECT_EQ(older.cell_known(ID($and)), newer.cell_known(ID($and)));
	auto check_port = [&](auto type, auto port) {
		EXPECT_EQ(older.cell_port_dir(type, port), newer.cell_port_dir(type, port));
		EXPECT_EQ(older.cell_input(type, port), newer.cell_input(type, port));
		EXPECT_EQ(older.cell_output(type, port), newer.cell_output(type, port));
	};
	for (size_t i = 0; i < static_cast<size_t>(RTLIL::StaticId::STATIC_ID_END); i++) {
		IdString type;
		type.index_ = i;
		EXPECT_EQ(older.cell_known(type), newer.cell_known(type));
		if (older.cell_evaluable(type) != newer.cell_evaluable(type))
			std::cout << type.str() << "\n";
		EXPECT_EQ(older.cell_evaluable(type), newer.cell_evaluable(type));
		for (auto port : StaticCellTypes::builder.cells.data()->inputs.ports)
			check_port(type, port);
		for (auto port : StaticCellTypes::builder.cells.data()->outputs.ports)
			check_port(type, port);

		EXPECT_EQ(RTLIL::builtin_ff_cell_types().count(type), StaticCellTypes::categories.is_ff(type));
	}
	yosys_shutdown();
}

YOSYS_NAMESPACE_END
