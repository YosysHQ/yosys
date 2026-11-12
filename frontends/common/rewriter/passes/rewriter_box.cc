/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Nick Allison <nick@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "frontends/common/rewriter/rewriter.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"

namespace Yosys::Rewriter::Rules {

struct BoxRule final : ModuleRewriteRule {
public:
	BoxRule()
		: ModuleRewriteRule() {}
protected:
	bool apply(RTLIL::Module *module, SigMap &sigmap) const override;
};

bool BoxRule::apply([[maybe_unused]] RTLIL::Module *module, [[maybe_unused]] SigMap &sigmap) const {

	if (module->get_bool_attribute(ID::blackbox))
	{
		if (module->get_bool_attribute(ID::whitebox)) {
			module->set_bool_attribute(ID::whitebox, false);
		}

		if (module->get_bool_attribute(ID::lib_whitebox)) {
			module->set_bool_attribute(ID::lib_whitebox, false);
		}

		// prune everything except ports, params & specify cells
		pool<RTLIL::Wire*> remove_wires;
		for (RTLIL::Wire *wire : module->wires()) {
			if (!wire->port_input && !wire->port_output)
				remove_wires.insert(wire);
		}

		for (RTLIL::Cell *cell : module->cells().to_vector())
			if (!cell->type.in(ID($specify2), ID($specify3), ID($specrule)))
				module->remove(cell);

		while (!module->memories.empty())
			module->remove(module->memories.begin()->second);

		while (!module->processes.empty())
			module->remove(module->processes.begin()->second);

		module->connections_.clear();
		module->remove(remove_wires);
	}
}

} // namespace Yosys::Rewriter::Rules

USING_YOSYS_NAMESPACE

namespace {

struct RewriterBoxPass : public Pass {
	RewriterBoxPass() : Pass("rewriter_box", "apply blackbox / whitebox module attributes") { }

	void help() override
	{
		log("\n");
		log("    rewriter_bwbox [options] [selection]\n");
		log("\n");
		log("Remove contents of modules with the blackbox attribute and clear whitebox.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);
		Rewriter::Rules::BoxRule().rewrite(design);

	}
} RewriterBoxPass;

}
