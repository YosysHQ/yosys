#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

TEST(TwinePublicityTest, LeafEscape)
{
	TwinePool pool;
	IdString pub = pool.add(std::string("\\foo"));
	IdString priv = pool.add(std::string("$foo"));

	EXPECT_TRUE(pub.isPublic());
	EXPECT_FALSE(priv.isPublic());
	EXPECT_EQ(pool.str(pub), "\\foo");
	EXPECT_EQ(pool.unescaped_str(pub), "foo");
	EXPECT_EQ(pool.str(priv), "$foo");
	EXPECT_EQ(pool.unescaped_str(priv), "$foo");
}

TEST(TwinePublicityTest, EscapedDollar)
{
	// Verilog escaped identifier `\$foo` (public, content "$foo") must not
	// collide with the private name `$foo` as a dict key.
	TwinePool pool;
	IdString pub = pool.add(std::string("\\$foo"));
	IdString priv = pool.add(std::string("$foo"));

	EXPECT_EQ(pub.untag(), priv.untag()); // shared content node
	EXPECT_NE(pub, priv);                           // distinct handles
	EXPECT_EQ(pool.str(pub), "\\$foo");
	EXPECT_EQ(pool.str(priv), "$foo");
}

TEST(TwinePublicityTest, TagStability)
{
	TwinePool pool;
	IdString a = pool.add(std::string("\\foo"));
	IdString b = pool.add(std::string("\\foo"));
	EXPECT_EQ(a, b);
}

TEST(TwinePublicityTest, SuffixPublicity)
{
	TwinePool pool;
	IdString pub = pool.add(std::string("\\base"));
	IdString priv = pool.add(std::string("$base"));

	IdString pub_sfx = pool.add(TwineSpec{TwineSpec::Suffix{pub, "_1"}});
	IdString priv_sfx = pool.add(TwineSpec{TwineSpec::Suffix{priv, "_1"}});

	EXPECT_TRUE(pub_sfx.isPublic());
	EXPECT_FALSE(priv_sfx.isPublic());
	EXPECT_EQ(pool.str(pub_sfx), "\\base_1");
	EXPECT_EQ(pool.str(priv_sfx), "$base_1");
}

TEST(TwinePublicityTest, StaticTags)
{
	TwinePool pool;
	EXPECT_TRUE((ID::A).isPublic());
	EXPECT_EQ(pool.str(ID::A), "\\A");
	EXPECT_EQ(pool.unescaped_str(ID::A), "A");
	EXPECT_FALSE((ID($and)).isPublic());
	EXPECT_EQ(pool.str(ID($and)), "$and");
}

TEST(TwinePublicityTest, LookupTag)
{
	TwinePool pool;
	IdString pub = pool.add(std::string("\\net"));
	IdString priv = pool.add(std::string("$net"));

	TwineSearch search(&pool);
	EXPECT_EQ(search.find("\\net"), pub);
	EXPECT_EQ(search.find("$net"), priv);
	EXPECT_EQ(search.find("\\A"), ID::A);
	EXPECT_EQ(search.find("\\nonexistent"), IdString::Null);
}

TEST(TwinePublicityTest, SearchUnifies)
{
	TwinePool pool;
	IdString flat = pool.add(TwineSpec::Leaf{"$abc"});
	IdString head = pool.add(TwineSpec::Leaf{"$a"});
	IdString split = pool.add(TwineSpec::Suffix{head, "bc"});

	ASSERT_NE(flat, split);
	ASSERT_EQ(pool.str(flat), pool.str(split));

	TwineSearch search(&pool);
	EXPECT_EQ(search.index.count(flat), 1u);
	EXPECT_EQ(search.index.count(split), 1u);
	EXPECT_EQ(search.index.count(head), 1u);
	EXPECT_NE(search.find("$abc"), IdString::Null);
	EXPECT_EQ(search.find("$a"), head);
}

TEST(TwinePublicityTest, SearchPublicity)
{
	TwinePool pool;
	IdString priv = pool.add(TwineSpec::Leaf{"sig"});
	IdString pub = pool.add(std::string("\\sig"));

	ASSERT_EQ(priv, pub.untag());

	TwineSearch search(&pool);
	IdString found_pub = search.find("\\sig");
	IdString found_priv = search.find("sig");

	EXPECT_TRUE(found_pub.isPublic());
	EXPECT_FALSE(found_priv.isPublic());
	EXPECT_EQ(found_pub.untag(), found_priv.untag());
	EXPECT_EQ(found_pub, pub);
}

TEST(TwinePublicityTest, CopyTag)
{
	TwinePool src, dst;
	IdString pub = src.add(std::string("\\xfer"));
	IdString copied = dst.copy_from(src, pub);
	EXPECT_TRUE(copied.isPublic());
	EXPECT_EQ(dst.str(copied), "\\xfer");
	// Static handles pass through tag and all.
	EXPECT_EQ(dst.copy_from(src, ID::A), ID::A);
}

TEST(TwinePublicityTest, GcRoots)
{
	TwinePool twines;
	SrcPool srcs(&twines);
	IdString pub = twines.add(std::string("\\keep"));
	twines.add(std::string("\\drop"));
	Yosys::pool<SrcRef> live_srcs;
	Yosys::pool<IdString> roots{pub};
	EXPECT_EQ(srcs.gc_with_twines(live_srcs, roots), 1u);
	EXPECT_EQ(twines.str(pub), "\\keep");
}

TEST(TwinePublicityTest, WireMasquerade)
{
	RTLIL::Design design;
	RTLIL::Module *mod = design.addModule("\\top");

	RTLIL::Wire *pub = mod->addWire("\\sig");
	RTLIL::Wire *priv = mod->addWire("$sig");

	EXPECT_TRUE(pub->name.isPublic());
	EXPECT_FALSE(priv->name.isPublic());
	EXPECT_EQ(pub->name.escaped(), "\\sig");
	EXPECT_EQ(pub->name.unescape(), "sig");
	EXPECT_EQ(pub->name.str(), "\\sig");
	EXPECT_EQ(priv->name.escaped(), "$sig");
	EXPECT_EQ(priv->name.unescape(), "$sig");

	// Distinct dict keys despite shared content.
	EXPECT_NE(pub, priv);
	TwineSearch search(&design.twines);
	EXPECT_EQ(mod->wire(search.find("\\sig")), pub);
	EXPECT_EQ(mod->wire(search.find("$sig")), priv);

	// uniquify keeps publicity.
	IdString uniq = mod->uniquify(pub->name);
	EXPECT_TRUE(uniq.isPublic());
	EXPECT_EQ(design.twines.str(uniq), "\\sig_1");
}

YOSYS_NAMESPACE_END
