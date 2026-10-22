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

	bool run(RTLIL::Module *module) const;
	bool run(RTLIL::Design *design) const;

private:
	template<typename T>
	bool rewrite_objects(T *item, const std::vector<std::unique_ptr<RewriteRule<T>>> &rules) const;
};

} // namespace Yosys::Rewriter
