#pragma once

#include "kernel/rtlil.h"

namespace Yosys::Rewriter {

template<typename T>
struct RewriteRule {
	virtual ~RewriteRule() = default;
	virtual bool rewrite(T *target) const = 0;
};

using ModuleRewriteRule = RewriteRule<RTLIL::Module>;
using CellRewriteRule = RewriteRule<RTLIL::Cell>;
using WireRewriteRule = RewriteRule<RTLIL::Wire>;

} // namespace Yosys::Rewriter
