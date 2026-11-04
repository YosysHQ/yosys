#include "kernel/rewriter/rewriter.h"

#include "kernel/rewriter/attributes.h"
#include "kernel/celltypes.h"

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

bool RewritePipeline::rewrite_design(RTLIL::Design* design) const
{
	bool changed = false;
	for (RTLIL::Module *module : design->modules()) {
		SigMap sigmap = construct_sigmap(module);
		changed |= rewrite_module(module, sigmap);
	}
	return changed;
}

bool RewritePipeline::rewrite_module(RTLIL::Module* module, SigMap &sigmap) const
{
	bool changed = false;
	for (auto &rule : module_rules)
		changed |= rule->rewrite(module, sigmap);
	for (auto &rule : wire_rules)
		changed |= rule->rewrite(module, sigmap);
	for (auto &rule : cell_rules)
		changed |= rule->rewrite(module, sigmap);
	return changed;
}

// AttributeRewriter / rewrite_attributes(T* item) is meant to be the public interface for rewriter,
AttributeRewriter::AttributeRewriter()
{
	add(std::make_unique<Rules::BlackboxRule>());
	add(std::make_unique<Rules::FormalAttrRule>());
}

bool rewrite_attributes(RTLIL::Module *module)
{
	SigMap sigmap = construct_sigmap(module);
	return AttributeRewriter().rewrite_module(module, sigmap);
}

bool rewrite_attributes(RTLIL::Design *design)
{
	return AttributeRewriter().rewrite_design(design);
}


// Redirect existing drivers of `sig` to a dummy wire
// see connect.cc
void unset_drivers(RTLIL::Module *module, SigMap &sigmap, RTLIL::SigSpec &sig)
{
	RTLIL::Design* design = module->design;
	CellTypes ct(design);

	RTLIL::Wire *dummy_wire = module->addWire(NEW_ID, sig.size());

	for (auto cell : module->cells())
	for (auto &port : cell->connections_)
		if (ct.cell_output(cell->type, port.first))
			sigmap(port.second).replace(sig, dummy_wire, &port.second);

	for (auto &conn : module->connections_)
		sigmap(conn.first).replace(sig, dummy_wire, &conn.first);
}

SigMap construct_sigmap(RTLIL::Module *module) {
	// see connect.cc
	SigMap sigmap;
	for (auto &it : module->connections()) {
		std::vector<RTLIL::SigBit> lhs = it.first.to_sigbit_vector();
		std::vector<RTLIL::SigBit> rhs = it.second.to_sigbit_vector();
		for (size_t i = 0; i < lhs.size(); i++)
			if (rhs[i].wire != nullptr)
				sigmap.add(lhs[i], rhs[i]);
	}
	return sigmap;
}

} // namespace Yosys::Rewriter
