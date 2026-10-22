#pragma once

#include "kernel/rewriter/pipeline.h"

namespace Yosys::Rewriter {

class AttributeRewriter final : public RewritePipeline {
public:
	AttributeRewriter();
};

bool rewrite_attributes(Yosys::RTLIL::Module *module);
bool rewrite_attributes(Yosys::RTLIL::Design *design);

} // namespace Yosys::Rewriter
