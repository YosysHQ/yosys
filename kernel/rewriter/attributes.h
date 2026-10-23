#pragma once

#include "kernel/rewriter/rule.h"

namespace Yosys::Rewriter::Rules {

struct BlackboxRule final : ModuleRewriteRule {
protected:
	bool apply(RTLIL::Module *module, SigMap &sigmap) const override;
};

struct FormalAttrRule final : WireRewriteRule {
protected:
	bool apply(RTLIL::Wire *wire, SigMap &sigmap) const override;
};

} // namespace Yosys::Rewriter::Rules
