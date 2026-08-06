#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

namespace {

struct MasqFixture {
	Design design;
	Module *mod;
	Wire *wire;
	Cell *cell;

	MasqFixture()
	{
		mod = design.addModule(std::string("\\zz_top"));
		wire = mod->addWire(std::string("\\zz_alu_result"), 4);
		cell = mod->addCell(std::string("\\zz_adder"), ID($and));
	}
};

}

TEST(NameMasqTest, StringQueries)
{
	MasqFixture f;
	const RTLIL::WireNameMasq &name = f.wire->name;

	EXPECT_TRUE(name.begins_with("\\zz_alu"));
	EXPECT_FALSE(name.begins_with("\\zz_alv"));
	EXPECT_TRUE(name.ends_with("result"));
	EXPECT_FALSE(name.ends_with("resulz"));
	EXPECT_TRUE(name.contains("alu"));
	EXPECT_FALSE(name.contains("mul"));
	EXPECT_EQ(name.substr(1, 2), "zz");
	EXPECT_EQ(name.substr(), name.escaped());
	EXPECT_EQ(name[0], '\\');
	EXPECT_EQ(name.size(), name.escaped().size());
	EXPECT_FALSE(name.empty());
}

TEST(NameMasqTest, SuffixQueries)
{
	Design design;
	Module *mod = design.addModule(std::string("\\zz_top"));
	IdString prefix = design.twines.add(std::string("\\zz_bus"));
	IdString suffixed = design.twines.add(Twine{Twine::Suffix{prefix, "_hi"}});
	Wire *w = mod->addWire(suffixed, 1);

	EXPECT_EQ(w->name.escaped(), "\\zz_bus_hi");
	EXPECT_TRUE(w->name.begins_with("\\zz_bus"));
	EXPECT_TRUE(w->name.begins_with("\\zz_bus_h"));
	EXPECT_TRUE(w->name.begins_with("\\zz_bus_hi"));
	EXPECT_FALSE(w->name.begins_with("\\zz_bus_hi_"));
	EXPECT_FALSE(w->name.begins_with("\\zz_buT"));
	EXPECT_FALSE(w->name.begins_with("\\zz_bus_i"));
	EXPECT_TRUE(w->name.ends_with("_hi"));
	EXPECT_EQ(w->name.size(), w->name.escaped().size());
	EXPECT_EQ(w->name.substr(4), "bus_hi");
}

TEST(NameMasqTest, PoollessMatchesPooled)
{
	Design design;
	IdString id = design.twines.add(std::string("\\zz_shared"));
	PooledName pooled(&design.twines, id);
	PooledName poolless(ID::A);

	EXPECT_EQ(pooled.pool(), &design.twines);
	EXPECT_EQ(poolless.pool(), nullptr);

	EXPECT_EQ(poolless.escaped(), "\\A");
	EXPECT_EQ(poolless.size(), poolless.escaped().size());
	EXPECT_TRUE(poolless.begins_with("\\A"));
	EXPECT_FALSE(poolless.begins_with("\\AB"));
	EXPECT_TRUE(poolless.ends_with("A"));

	PooledName same_content(&design.twines, design.twines.add(std::string("\\A")));
	EXPECT_EQ(same_content.escaped(), poolless.escaped());
	EXPECT_EQ(same_content.size(), poolless.size());
	EXPECT_EQ(same_content.begins_with("\\A"), poolless.begins_with("\\A"));
}

TEST(NameMasqTest, PoollessOrdering)
{
	PooledName a(ID::A);
	PooledName b(ID::B);

	EXPECT_EQ(a.pool(), nullptr);
	EXPECT_TRUE(a.lt_by_name(b));
	EXPECT_FALSE(b.lt_by_name(a));
	EXPECT_FALSE(a.lt_by_name(a));
}

TEST(NameMasqTest, PooledOrdering)
{
	Design design;
	Module *mod = design.addModule(std::string("\\zz_top"));
	Wire *first = mod->addWire(std::string("\\zz_aaa"), 1);
	Wire *second = mod->addWire(std::string("\\zz_bbb"), 1);

	EXPECT_TRUE(first->name.lt_by_name(second->name));
	EXPECT_FALSE(second->name.lt_by_name(first->name));
	EXPECT_FALSE(first->name.lt_by_name(first->name));

	EXPECT_NE(first->name < second->name, second->name < first->name);
	EXPECT_FALSE(first->name < first->name);
}

TEST(NameMasqTest, Membership)
{
	MasqFixture f;

	EXPECT_TRUE(f.cell->type.in(ID($and)));
	EXPECT_FALSE(f.cell->type.in(ID($or)));
	EXPECT_TRUE(f.cell->type.in(ID($or), ID($and)));
	EXPECT_FALSE(f.cell->type.in(ID($or), ID($xor)));
	EXPECT_TRUE(f.wire->name.in(IdString(f.wire->name)));
}

TEST(NameMasqTest, Equality)
{
	MasqFixture f;
	IdString id = f.wire->name;

	EXPECT_TRUE(f.wire->name == id);
	EXPECT_TRUE(id == f.wire->name);
	EXPECT_FALSE(f.wire->name != id);
	EXPECT_TRUE(f.wire->name != ID::A);

	EXPECT_TRUE(f.cell->type == ID($and));
	EXPECT_TRUE(f.cell->type != ID($or));

	EXPECT_TRUE(f.wire->name == std::string("\\zz_alu_result"));
	EXPECT_TRUE(f.wire->name != std::string("\\zz_other"));

	EXPECT_TRUE(f.wire->name == f.wire->name);
	EXPECT_TRUE(f.wire->name != f.cell->name);

	PooledName null_name;
	EXPECT_TRUE(null_name == IdString::Null);
	EXPECT_TRUE(null_name.empty());
	EXPECT_FALSE(f.wire->name == IdString::Null);
	EXPECT_TRUE(f.wire->name != IdString::Null);
}

TEST(NameMasqTest, CrossMasqEquality)
{
	Design design;
	Module *mod = design.addModule(std::string("\\zz_top"));
	Cell *recursive = mod->addCell(std::string("\\zz_self"), mod->name);
	Cell *other = mod->addCell(std::string("\\zz_and"), ID($and));

	EXPECT_TRUE(mod->name == recursive->type);
	EXPECT_TRUE(recursive->type == mod->name);
	EXPECT_FALSE(mod->name == other->type);
	EXPECT_TRUE(mod->name != other->type);
	EXPECT_TRUE(recursive->name != other->name);
}

TEST(NameMasqTest, Conversions)
{
	MasqFixture f;

	std::string as_string = f.wire->name;
	IdString as_id = f.wire->name;

	EXPECT_EQ(as_string, "\\zz_alu_result");
	EXPECT_EQ(as_string, f.wire->name.str());
	EXPECT_EQ(as_id, f.wire->name.ref());
	EXPECT_EQ(f.wire->name.pool(), &f.design.twines);
	EXPECT_EQ(f.cell->type.pool(), &f.design.twines);
	EXPECT_EQ(f.mod->name.pool(), &f.design.twines);
}

TEST(NameMasqTest, Hashing)
{
	MasqFixture f;

	EXPECT_EQ(run_hash(f.wire->name), run_hash(f.wire->name.ref()));
	EXPECT_EQ(run_hash(f.cell->type), run_hash(f.cell->type.ref()));
	EXPECT_EQ(run_hash(PooledName(f.wire->name)), run_hash(f.wire->name.ref()));
	EXPECT_NE(run_hash(f.wire->name), run_hash(f.cell->name.ref()));
}

TEST(NameMasqTest, WireAssignment)
{
	Design design;
	Module *mod = design.addModule(std::string("\\zz_top"));
	Wire *a = mod->addWire(std::string("\\zz_a"), 1);
	Wire *b = mod->addWire(std::string("\\zz_b"), 1);
	IdString renamed = design.twines.add(std::string("\\zz_renamed"));

	a->name = renamed;
	EXPECT_EQ(a->name.str(), "\\zz_renamed");

	b->name = a->name;
	EXPECT_EQ(b->name.str(), "\\zz_renamed");
	EXPECT_TRUE(a->name == b->name);

	Wire *c = mod->addWire(std::string("\\zz_c"), 1);
	c->name = std::move(b->name);
	EXPECT_EQ(c->name.str(), "\\zz_renamed");
}

TEST(NameMasqTest, TypeAssignment)
{
	MasqFixture f;
	Cell *other = f.mod->addCell(std::string("\\zz_other"), ID($or));

	f.cell->type = ID($xor);
	EXPECT_TRUE(f.cell->type == ID($xor));
	EXPECT_EQ(f.cell->type.str(), "$xor");

	other->type = f.cell->type;
	EXPECT_TRUE(other->type == ID($xor));

	Cell *third = f.mod->addCell(std::string("\\zz_third"), ID($not));
	third->type = std::move(other->type);
	EXPECT_TRUE(third->type == ID($xor));
}

TEST(NameMasqTest, ModuleAssignment)
{
	Design design;
	Module *mod = design.addModule(std::string("\\zz_top"));
	Module *sibling = design.addModule(std::string("\\zz_side"));
	IdString renamed = design.twines.add(std::string("\\zz_renamed"));

	mod->name = renamed;
	EXPECT_EQ(mod->name.str(), "\\zz_renamed");
	EXPECT_TRUE(mod->name == renamed);

	sibling->name = mod->name;
	EXPECT_EQ(sibling->name.str(), "\\zz_renamed");

	EXPECT_EQ(PooledName(mod->name).str(), "\\zz_renamed");
}

TEST(NameMasqTest, MakePair)
{
	MasqFixture f;

	auto left = make_pair(f.wire->name, 7);
	auto right = make_pair(7, f.wire->name);
	auto both = make_pair(f.wire->name, f.cell->type);

	EXPECT_TRUE((std::is_same_v<decltype(left.first), IdString>));
	EXPECT_TRUE((std::is_same_v<decltype(right.second), IdString>));
	EXPECT_TRUE((std::is_same_v<decltype(both.first), IdString>));
	EXPECT_TRUE((std::is_same_v<decltype(both.second), IdString>));

	EXPECT_EQ(left.first, f.wire->name.ref());
	EXPECT_EQ(left.second, 7);
	EXPECT_EQ(right.first, 7);
	EXPECT_EQ(right.second, f.wire->name.ref());
	EXPECT_EQ(both.first, f.wire->name.ref());
	EXPECT_EQ(both.second, f.cell->type.ref());
}

YOSYS_NAMESPACE_END
