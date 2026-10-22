#pragma once

#include <memory>
#include <vector>

#include "kernel/rewriter/rule.h"

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

} // namespace Yosys::Rewriter
