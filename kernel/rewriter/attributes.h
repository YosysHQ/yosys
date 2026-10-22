#pragma once

#include "kernel/rewriter/rule.h"

namespace Yosys::Rewriter::Rules {

struct BlackboxRule final : ModuleRewriteRule {
	bool rewrite(RTLIL::Module *module) const override;
};

struct FormalAttrRule final : WireRewriteRule {
	bool rewrite(RTLIL::Wire *wire) const override;
};

} // namespace Yosys::Rewriter::Rules
