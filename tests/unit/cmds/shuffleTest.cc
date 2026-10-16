#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace {

RTLIL::Module *build_module(RTLIL::Design *design)
{
	RTLIL::Module *module = design->addModule("\\top");
	for (int i = 0; i < 8; i++) {
		RTLIL::Wire *a = module->addWire(stringf("\\a%d", i));
		RTLIL::Wire *y = module->addWire(stringf("\\y%d", i));
		module->addNot(stringf("\\not%d", i), a, y);
		module->connect(module->addWire(stringf("\\z%d", i)), y);
		module->addMemory(stringf("\\mem%d", i));
		module->addProcess(stringf("\\proc%d", i));
	}
	return module;
}

std::vector<std::vector<std::string>> snapshot(const RTLIL::Module *module)
{
	std::vector<std::vector<std::string>> result(5);
	for (const auto &it : module->wires_) result[0].push_back(std::string(module->twines().str(it.first)));
	for (const auto &it : module->cells_) result[1].push_back(std::string(module->twines().str(it.first)));
	for (const auto &it : module->memories) result[2].push_back(std::string(module->twines().str(it.first)));
	for (const auto &it : module->processes) result[3].push_back(std::string(module->twines().str(it.first)));
	for (const auto &it : module->connections_) result[4].push_back(log_signal(it.first) + "=" + log_signal(it.second));
	return result;
}

TEST(ShuffleTest, ReordersAndPreservesContents)
{
	RTLIL::Design design;
	RTLIL::Module *module = build_module(&design);
	auto before = snapshot(module);
	Pass::call(&design, "shuffle -seed 3");
	auto after = snapshot(module);

	for (size_t i = 0; i < before.size(); i++) {
		EXPECT_NE(before[i], after[i]);
		std::sort(before[i].begin(), before[i].end());
		std::sort(after[i].begin(), after[i].end());
		EXPECT_EQ(before[i], after[i]);
	}
	for (const auto &it : module->wires_)
		EXPECT_EQ(module->wire(it.first), it.second);
	for (const auto &it : module->cells_)
		EXPECT_EQ(module->cell(it.first), it.second);
}

TEST(ShuffleTest, SeedIsDeterministic)
{
	RTLIL::Design design_a, design_b;
	RTLIL::Module *a = build_module(&design_a);
	RTLIL::Module *b = build_module(&design_b);

	Pass::call(&design_a, "shuffle -seed 7");
	Pass::call(&design_b, "shuffle -seed 7");
	EXPECT_EQ(snapshot(a), snapshot(b));

	Pass::call(&design_b, "shuffle -seed 8");
	EXPECT_NE(snapshot(a), snapshot(b));
}

}

YOSYS_NAMESPACE_END
