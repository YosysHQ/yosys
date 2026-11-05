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
#include "kernel/sigtools.h"
#include "kernel/log.h"

namespace Yosys::Rewriter::Rules {

struct FormalAttrRule final : WireRewriteRule {
protected:
	bool apply(RTLIL::Wire *wire, SigMap &sigmap) const override;
};

// TODO: Decide whether explicit drivers on formal wires should be errors.
// e.g. decide the behavior of the following
// ```
// (* anyseq *)
// reg x;
// always @(posedge clk) begin
//     x <= 0
// end
// ```
// For now, redirect existing drivers as opposed to emitting an error
bool FormalAttrRule::apply(RTLIL::Wire *wire, SigMap &sigmap) const {
	RTLIL::Module* module = wire->module;
	auto rewrite_attr = [&](RTLIL::IdString attr, auto create_sig) {
		if (!wire->get_bool_attribute(attr))
			return false;

		auto &twines = module->twines();
		auto name = module->uniquify(
			twines.add(wire->name, "$" + twines.unescaped_str(attr)));

		RTLIL::SigSpec target = sigmap(wire);
		module->connect(target, create_sig(name));
		wire->attributes.erase(attr);
		return true;
	};

	return rewrite_attr(ID::anyseq,   [&](auto name) { return module->Anyseq  (name, GetSize(wire), wire->get_src_attribute()); })
		|| rewrite_attr(ID::anyconst, [&](auto name) { return module->Anyconst(name, GetSize(wire), wire->get_src_attribute()); })
		|| rewrite_attr(ID::allseq,   [&](auto name) { return module->Allseq  (name, GetSize(wire), wire->get_src_attribute()); })
		|| rewrite_attr(ID::allconst, [&](auto name) { return module->Allconst(name, GetSize(wire), wire->get_src_attribute()); });
}

} // namespace Yosys::Rewriter::Rules

USING_YOSYS_NAMESPACE

namespace {

struct RewriterAnyseqPass : public Pass {
	RewriterAnyseqPass() : Pass("rewriter_anyall_seqconst", "apply formal wire attributes") { }

	void help() override
	{
		log("\n");
		log("    rewriter_anyall_seqconst [selection]\n");
		log("\n");
		log("Replace anyseq, anyconst, allseq and allconst wire attributes with formal cells.\n");
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
		Rewriter::Rules::FormalAttrRule().rewrite(design);

	}
} RewriterAnyseqPass;

}
