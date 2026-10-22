#pragma once

#include "kernel/rewriter/pipeline.h"
#include "kernel/sigtools.h"

namespace Yosys::Rewriter {

class AttributeRewriter final : public RewritePipeline {
public:
	AttributeRewriter();
};

bool rewrite_attributes(Yosys::RTLIL::Module *module);
bool rewrite_attributes(Yosys::RTLIL::Design *design);

// Redirect existing drivers of `sig` to a dummy wire
void unset_drivers(RTLIL::Module *module, SigMap &sigmap, RTLIL::SigSpec &sig);
SigMap construct_sigmap(RTLIL::Module *module);

} // namespace Yosys::Rewriter
