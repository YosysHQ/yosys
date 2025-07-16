#include <gtest/gtest.h>
#include "passes/techmap/libparse.h"

YOSYS_NAMESPACE_BEGIN

namespace RTLIL {

	class TechmapLibparseTest : public testing::Test {
	protected:
		TechmapLibparseTest() {
			if (log_files.empty()) log_files.emplace_back(stdout);
		}
		void checkAll(std::initializer_list<std::string> expressions, std::string expected) {
			for (const auto& e : expressions) {
				auto helper = LibertyExpression::Lexer(e);
				auto tree_s = LibertyExpression::parse(helper).str();
				EXPECT_EQ(tree_s, expected);
			}
		}
	};
	TEST_F(TechmapLibparseTest, LibertyExpressionSpace)
	{
		checkAll({
			"x",
			"x ",
			" x",
			" x ",
			"  x ",
		}, "(pin \"x\")");

		checkAll({
			"x y",
			" x y ",
			"x (y)",
			" x (y) ",
			"(x) y",
			" (x) y ",

			"x & y",
			"x&y",
			"x &y",
			"x& y",
			" x&y ",
			"x & (y)",
			"x&(y)",
			"x &(y)",
			"x& (y)",
			" x&(y) ",
			"(x) & y",
			"(x)&y",
			"(x) &y",
			"(x)& y",
			" (x)&y ",
		}, "(and (pin \"x\")\n"
		   "     (pin \"y\"))"
		);

		checkAll({
			"x ^ y",
			"x^y",
			"x ^y",
			"x^ y",
			" x^y ",
		}, "(xor (pin \"x\")\n"
		   "     (pin \"y\"))"
		);
		checkAll({
			"x !y",
			" x !y ",
			"x & !y",
			"x&!y",
			"x &!y",
			"x& !y",
			" x&!y ",
			"x y'",
			" x y' ",
			"x & y'",
			"x&y'",
			"x &y'",
			"x& y'",
			" x&y' ",
		}, "(and (pin \"x\")\n"
		   "     (not (pin \"y\")))"
		);
	}
}

YOSYS_NAMESPACE_END
