#include "kernel/rewriter/rewriter.h"

#include "kernel/rewriter/attributes.h"

namespace Yosys::Rewriter {

AttributeRewriter::AttributeRewriter()
{
	add(std::make_unique<Rules::BlackboxRule>());
	add(std::make_unique<Rules::FormalAttrRule>());
}

bool rewrite_attributes(RTLIL::Module *module)
{
	return AttributeRewriter().run(module);
}

bool rewrite_attributes(RTLIL::Design *design)
{
	return AttributeRewriter().run(design);
}

} // namespace Yosys::Rewriter
