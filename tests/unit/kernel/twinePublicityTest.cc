#include <gtest/gtest.h>

#include "kernel/rtlil.h"
#include "kernel/yosys.h"
#include "tests/unit/yosysSetupEnv.h"

YOSYS_NAMESPACE_BEGIN

TEST(TwinePublicityTest, LeafEscapeParsing)
{
	TwinePool pool;
	TwineRef pub = pool.add(std::string("\\foo"));
	TwineRef priv = pool.add(std::string("$foo"));

	EXPECT_TRUE(twine_is_public(pub));
	EXPECT_FALSE(twine_is_public(priv));
	EXPECT_EQ(pool.str(pub), "\\foo");
	EXPECT_EQ(pool.unescaped_str(pub), "foo");
	EXPECT_EQ(pool.str(priv), "$foo");
	EXPECT_EQ(pool.unescaped_str(priv), "$foo");
}

TEST(TwinePublicityTest, EscapedDollarStaysDistinct)
{
	// Verilog escaped identifier `\$foo` (public, content "$foo") must not
	// collide with the private name `$foo` as a dict key.
	TwinePool pool;
	TwineRef pub = pool.add(std::string("\\$foo"));
	TwineRef priv = pool.add(std::string("$foo"));

	EXPECT_EQ(twine_untag(pub), twine_untag(priv)); // shared content node
	EXPECT_NE(pub, priv);                           // distinct handles
	EXPECT_EQ(pool.str(pub), "\\$foo");
	EXPECT_EQ(pool.str(priv), "$foo");
}

TEST(TwinePublicityTest, InterningIsStableAcrossTags)
{
	TwinePool pool;
	TwineRef a = pool.add(std::string("\\foo"));
	TwineRef b = pool.add(std::string("\\foo"));
	EXPECT_EQ(a, b);
}

TEST(TwinePublicityTest, SuffixInheritsPublicity)
{
	TwinePool pool;
	TwineRef pub = pool.add(std::string("\\base"));
	TwineRef priv = pool.add(std::string("$base"));

	TwineRef pub_sfx = pool.add(Twine{Twine::Suffix{pub, "_1"}});
	TwineRef priv_sfx = pool.add(Twine{Twine::Suffix{priv, "_1"}});

	EXPECT_TRUE(twine_is_public(pub_sfx));
	EXPECT_FALSE(twine_is_public(priv_sfx));
	EXPECT_EQ(pool.str(pub_sfx), "\\base_1");
	EXPECT_EQ(pool.str(priv_sfx), "$base_1");
}

TEST(TwinePublicityTest, StaticHandlesAreTagged)
{
	TwinePool pool;
	EXPECT_TRUE(twine_is_public(TW::A));
	EXPECT_EQ(pool.str(TW::A), "\\A");
	EXPECT_EQ(pool.unescaped_str(TW::A), "A");
	EXPECT_FALSE(twine_is_public(TW::$and));
	EXPECT_EQ(pool.str(TW::$and), "$and");
}

TEST(TwinePublicityTest, LookupReturnsTaggedHandle)
{
	TwinePool pool;
	TwineRef pub = pool.add(std::string("\\net"));
	TwineRef priv = pool.add(std::string("$net"));

	TwineSearch search(&pool);
	EXPECT_EQ(search.find("\\net"), pub);
	EXPECT_EQ(search.find("$net"), priv);
	EXPECT_EQ(search.find("\\A"), TW::A);
	EXPECT_EQ(search.find("\\nonexistent"), Twine::Null);
}

TEST(TwinePublicityTest, CopyFromPreservesTag)
{
	TwinePool src, dst;
	TwineRef pub = src.add(std::string("\\xfer"));
	TwineRef copied = dst.copy_from(src, pub);
	EXPECT_TRUE(twine_is_public(copied));
	EXPECT_EQ(dst.str(copied), "\\xfer");
	// Static handles pass through tag and all.
	EXPECT_EQ(dst.copy_from(src, TW::A), TW::A);
}

TEST(TwinePublicityTest, GcKeepsTaggedRoots)
{
	TwinePool pool;
	TwineRef pub = pool.add(std::string("\\keep"));
	pool.add(std::string("\\drop"));
	std::vector<TwineRef> roots{pub};
	EXPECT_EQ(pool.gc(roots), 1u);
	EXPECT_EQ(pool.str(pub), "\\keep");
}

TEST(TwinePublicityTest, WireNameMasquerade)
{
	RTLIL::Design design;
	RTLIL::Module *mod = design.addModule(design.twines.add(std::string("\\top")));

	RTLIL::Wire *pub = mod->addWire(design.twines.add(std::string("\\sig")));
	RTLIL::Wire *priv = mod->addWire(design.twines.add(std::string("$sig")));

	EXPECT_TRUE(pub->name.isPublic());
	EXPECT_FALSE(priv->name.isPublic());
	EXPECT_EQ(pub->name.escaped(), "\\sig");
	EXPECT_EQ(pub->name.unescaped(), "sig");
	EXPECT_EQ(pub->name.str(), "\\sig");
	EXPECT_EQ(priv->name.escaped(), "$sig");
	EXPECT_EQ(priv->name.unescaped(), "$sig");

	// Distinct dict keys despite shared content.
	EXPECT_NE(pub, priv);
	TwineSearch search(&design.twines);
	EXPECT_EQ(mod->wire(search.find("\\sig")), pub);
	EXPECT_EQ(mod->wire(search.find("$sig")), priv);

	// uniquify keeps publicity.
	TwineRef uniq = mod->uniquify(pub->meta_->name);
	EXPECT_TRUE(twine_is_public(uniq));
	EXPECT_EQ(design.twines.str(uniq), "\\sig_1");
}

YOSYS_NAMESPACE_END
