#include "kernel/rewriter/attributes.h"

namespace Yosys::Rewriter::Rules {


bool BlackboxRule::rewrite(RTLIL::Module *module) const {
	if (!module->get_bool_attribute(ID::blackbox))
		return false;

	module->makeblackbox();
	module->set_bool_attribute(ID::whitebox, false);
	return true;
}


bool FormalAttrRule::rewrite(RTLIL::Wire *wire) const {
	auto rewrite_attr = [&](RTLIL::IdString attr, auto create_cell) {
		if (!wire->get_bool_attribute(attr))
			return false;

		auto *cell = create_cell();
		cell->setParam(ID::WIDTH, wire->width);
		cell->setPort(ID::Y, wire);
		cell->set_src_attribute(wire->get_src_attribute());

		wire->attributes.erase(attr);
		return true;
	};

	return rewrite_attr(ID::anyconst, [&] { return wire->module->addCell(NEW_ID, ID($anyconst)); })
		|| rewrite_attr(ID::anyseq, [&] { return wire->module->addCell(NEW_ID, ID($anyseq)); })
		|| rewrite_attr(ID::allconst, [&] { return wire->module->addCell(NEW_ID, ID($allconst)); })
		|| rewrite_attr(ID::allseq, [&] { return wire->module->addCell(NEW_ID, ID($allseq)); });
}


} // namespace Yosys::Rewriter::Rules
