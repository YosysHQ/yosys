#include "kernel/rewriter/attributes.h"
#include "kernel/rewriter/rewriter.h"

namespace Yosys::Rewriter::Rules {


bool BlackboxRule::apply(RTLIL::Module *module) const {
	if (!module->get_bool_attribute(ID::blackbox))
		return false;

	module->makeblackbox();
	module->set_bool_attribute(ID::whitebox, false);
	return true;
}


// TODO: Decide whether explicit drivers on formal wires should be errors.
// e.g. decide the behavior of the following
// ```
// (* anyseq *)
// reg x;
// always @(posedge clk) begin
//     x <= 0
// end
// ```
// For now, redirect existing drivers, including slang's implicit initialization buffers.
bool FormalAttrRule::apply(RTLIL::Wire *wire) const {
	RTLIL::Module* module = wire->module;
	auto rewrite_attr = [&](RTLIL::IdString attr, auto create_sig) {
		if (!wire->get_bool_attribute(attr))
			return false;

		auto &twines = module->twines();
		auto name = module->uniquify(
			twines.add(wire->name, "$" + twines.unescaped_str(attr)));

		// see connect.cc
		// I really despise this
		SigMap sigmap = construct_sigmap(module);

		RTLIL::SigSpec target = sigmap(wire);
		unset_drivers(module, sigmap, target);
		module->connect(target, create_sig(name));
		wire->attributes.erase(attr);
		return true;
	};

	return rewrite_attr(ID::anyseq,   [&](auto name) { return module->Anyseq(name, GetSize(wire), wire->get_src_attribute()); })
		|| rewrite_attr(ID::anyconst, [&](auto name) { return module->Anyconst(name, GetSize(wire), wire->get_src_attribute()); })
		|| rewrite_attr(ID::allseq,   [&](auto name) { return module->Allseq(name, GetSize(wire), wire->get_src_attribute()); })
		|| rewrite_attr(ID::allconst, [&](auto name) { return module->Allconst(name, GetSize(wire), wire->get_src_attribute()); });
}


} // namespace Yosys::Rewriter::Rules
