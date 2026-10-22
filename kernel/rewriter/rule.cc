#include "kernel/rewriter/rule.h"

#include <type_traits>

namespace Yosys::Rewriter {

template<typename T>
bool RewriteRule<T>::rewrite(RTLIL::Design *design) const
{
	bool changed = false;
	for (auto *module : design->modules())
		changed |= rewrite(module);
	return changed;
}

template<typename T>
bool RewriteRule<T>::rewrite(RTLIL::Module *module) const
{
	if constexpr (std::is_same_v<T, RTLIL::Module>)
		return apply(module);

	if (module->get_bool_attribute(ID::blackbox))
		return false;

	bool changed = false;
	if constexpr (std::is_same_v<T, RTLIL::Wire>)
		for (auto *wire : module->wires().to_vector())
			changed |= apply(wire);
	if constexpr (std::is_same_v<T, RTLIL::Cell>)
		for (auto *cell : module->cells().to_vector())
			changed |= apply(cell);
	return changed;
}

template struct RewriteRule<RTLIL::Module>;
template struct RewriteRule<RTLIL::Wire>;
template struct RewriteRule<RTLIL::Cell>;

} // namespace Yosys::Rewriter
