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
bool RewritePipeline::rewrite_objects(T *item, const std::vector<std::unique_ptr<RewriteRule<T>>> &rules) const
{
	bool changed = false;
	for (auto &rule : rules)
		changed |= rule->rewrite(item);
	return changed;
}

bool RewritePipeline::run(RTLIL::Module *module) const
{
	bool changed = false;
	for (auto &rule : module_rules)
		changed |= rule->rewrite(module);

	if (module->get_bool_attribute(ID::blackbox))
		return changed;

	for (RTLIL::Wire *wire : module->wires().to_vector())
		changed |= rewrite_objects(wire, wire_rules);

	for (RTLIL::Cell *cell : module->cells().to_vector())
		changed |= rewrite_objects(cell, cell_rules);

	return changed;
}

bool RewritePipeline::run(RTLIL::Design *design) const
{
	bool changed = false;
	for (RTLIL::Module *module : design->modules()) {
		changed |= run(module);
	}
	return changed;
}

} // namespace Yosys::Rewriter
