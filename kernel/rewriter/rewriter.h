#pragma once

#include <memory>
#include <vector>

#include "kernel/rewriter/rule.h"
#include "kernel/sigtools.h"

namespace Yosys::Rewriter {

class RewritePipeline {
	std::vector<std::unique_ptr<ModuleRewriteRule>> module_rules;
	std::vector<std::unique_ptr<CellRewriteRule>> cell_rules;
	std::vector<std::unique_ptr<WireRewriteRule>> wire_rules;

public:
	void add(std::unique_ptr<ModuleRewriteRule> rule);
	void add(std::unique_ptr<CellRewriteRule> rule);
	void add(std::unique_ptr<WireRewriteRule> rule);

	template<typename T>
	bool run(T *item) const;
};

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
