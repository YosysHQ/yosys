#include "kernel/rewriter/pipeline.h"

namespace Yosys::Rewriter {

void RewritePipeline::add(std::unique_ptr<ModuleRewriteRule> rule)
{
	log_assert(rule != nullptr);
	module_rules.push_back(std::move(rule));
}

void RewritePipeline::add(std::unique_ptr<CellRewriteRule> rule)
{
	log_assert(rule != nullptr);
	cell_rules.push_back(std::move(rule));
}

void RewritePipeline::add(std::unique_ptr<WireRewriteRule> rule)
{
	log_assert(rule != nullptr);
	wire_rules.push_back(std::move(rule));
}

template<typename T>
bool RewritePipeline::run(T* item) const
{
	bool changed = false;
	for (auto &rule : module_rules)
		changed |= rule->rewrite(item);
	for (auto &rule : wire_rules)
		changed |= rule->rewrite(item);
	for (auto &rule : cell_rules)
		changed |= rule->rewrite(item);
	return changed;
}

template bool RewritePipeline::run<RTLIL::Module>(RTLIL::Module *item) const;
template bool RewritePipeline::run<RTLIL::Design>(RTLIL::Design *item) const;

} // namespace Yosys::Rewriter
