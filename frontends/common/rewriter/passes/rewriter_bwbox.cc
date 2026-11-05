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

namespace Yosys::Rewriter::Rules {

struct BlackwhiteboxRule final : ModuleRewriteRule {
public:
	BlackwhiteboxRule(bool flag_noblackbox, bool flag_lib, bool flag_nowb)
		: flag_noblackbox(flag_noblackbox), flag_lib(flag_lib), flag_nowb(flag_nowb) {}
protected:
	bool apply(RTLIL::Module *module, SigMap &sigmap) const override;
private:
	bool flag_noblackbox = false;
	bool flag_lib = false;
	bool flag_nowb = false;
};

bool BlackwhiteboxRule::apply([[maybe_unused]] RTLIL::Module *module, [[maybe_unused]] SigMap &sigmap) const {
	// see ast.cc
	bool blackbox_module = flag_lib;

	// automatically blackbox empty modules
	// allow only ports, parameters, and specify cells
	if (!blackbox_module && !flag_noblackbox) {
		// blackbox_module = true;
		// for (const auto& child : ast->children) {
		// 	if (child->type == AST_WIRE && (child->is_input || child->is_output))
		// 		continue;
		// 	if (child->type == AST_PARAMETER || child->type == AST_LOCALPARAM)
		// 		continue;
		// 	if (child->type == AST_CELL && child->children.size() > 0 && child->children[0]->type == AST_CELLTYPE &&
		// 			(child->children[0]->str == "$specify2" || child->children[0]->str == "$specify3" || child->children[0]->str == "$specrule"))
		// 		continue;
		// 	blackbox_module = false;
		// 	break;
		// }
	}

	// erase whitebox attribute
	// if (flag_nowb && ast->attributes.count(ID::whitebox)) {
	// 	ast->attributes.erase(ID::whitebox);
	// }

	// whitebox = lib_whitebox if (flag_lib && !flag_nowb)
	// if (ast->attributes.count(ID::lib_whitebox)) {
	// 	if (flag_lib && !flag_nowb) {
	// 		ast->attributes[ID::whitebox] = std::move(
	// 			ast->attributes[ID::lib_whitebox]
	// 		);
	// 	}
	// 	ast->attributes.erase(ID::lib_whitebox);
	// }

	// invalid blackbox attr
	// if (!blackbox_module && ast->attributes.count(ID::blackbox)) {
	// 	auto& n = ast->attributes.at(ID::blackbox);
	// 	if (n->type != AST_CONSTANT)
	// 		ast->input_error("Got blackbox attribute with non-constant value!\n");
	// 	blackbox_module = n->asBool();
	// }

	// invalid whitebox attr
	// if (blackbox_module && ast->attributes.count(ID::whitebox)) {
	// 	auto& n = ast->attributes.at(ID::whitebox);
	// 	if (n->type != AST_CONSTANT)
	// 		ast->input_error("Got whitebox attribute with non-constant value!\n");
	// 	blackbox_module = !n->asBool();
	// }

	// invalid noblackbox attr
	// if (ast->attributes.count(ID::noblackbox)) {
	// 	if (blackbox_module) {
	// 		auto& n = ast->attributes.at(ID::noblackbox);
	// 		if (n->type != AST_CONSTANT)
	// 			ast->input_error("Got noblackbox attribute with non-constant value!\n");
	// 		blackbox_module = !n->asBool();
	// 	}
	// 	ast->attributes.erase(ID::noblackbox);
	// }

	if (blackbox_module)
	{
		// erase whitebox / lib_whitebox
		// if (ast->attributes.count(ID::whitebox)) {
		// 	ast->attributes.erase(ID::whitebox);
		// }

		// if (ast->attributes.count(ID::lib_whitebox)) {
		// 	ast->attributes.erase(ID::lib_whitebox);
		// }

		// prune everything except ports, params & specify cells
		// std::vector<std::unique_ptr<AstNode>> new_children;
		// for (auto& child : ast->children) {
		// 	if (child->type == AST_WIRE && (child->is_input || child->is_output)) {
		// 		new_children.push_back(std::move(child));
		// 	} else if (child->type == AST_PARAMETER) {
		// 		new_children.push_back(std::move(child));
		// 	} else if (child->type == AST_CELL && child->children.size() > 0 && child->children[0]->type == AST_CELLTYPE &&
		// 			(child->children[0]->str == "$specify2" || child->children[0]->str == "$specify3" || child->children[0]->str == "$specrule")) {
		// 		new_children.push_back(std::move(child));
		// 	}
		// }

		// ast->children.swap(new_children);

		// set blackbox attr
		// if (ast->attributes.count(ID::blackbox) == 0) {
		// 	ast->set_attribute(ID::blackbox, AstNode::mkconst_int(ast->location, 1, false));
		// }
	}

	// if (!module->get_bool_attribute(ID::blackbox))
	// 	return false;

	// module->makeblackbox();
	// module->set_bool_attribute(ID::whitebox, false);
	// return true;
}

} // namespace Yosys::Rewriter::Rules

USING_YOSYS_NAMESPACE

namespace {

struct RewriterBlackwhiteboxPass : public Pass {
	RewriterBlackwhiteboxPass() : Pass("rewriter_bwbox", "apply blackbox / whitebox module attributes") { }

	void help() override
	{
		log("\n");
		log("    rewriter_bwbox [options] [selection]\n");
		log("\n");
		log("Remove contents of modules with the blackbox attribute and clear whitebox.\n");
		log("\n");
		log("    -noblackbox\n");
		log("        do not automatically add a (* blackbox *) attribute to an\n");
		log("        empty module.\n");
		log("\n");
		log("    -lib\n");
		log("        only create empty blackbox modules. This implies -DBLACKBOX.\n");
		log("        modules with the (* whitebox *) attribute will be preserved.\n");
		log("        (* lib_whitebox *) will be treated like (* whitebox *).\n");
		log("\n");
		log("    -nowb\n");
		log("        delete (* whitebox *) and (* lib_whitebox *) attributes from\n");
		log("        all modules.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool flag_noblackbox = false;
		bool flag_lib = false;
		bool flag_nowb = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-noblackbox") {
				flag_noblackbox = true;
				continue;
			}
			if (arg == "-lib") {
				flag_lib = true;
				continue;
			}
			if (arg == "-nowb") {
				flag_nowb = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		Rewriter::Rules::BlackwhiteboxRule(flag_noblackbox, flag_lib, flag_nowb).rewrite(design);

	}
} RewriterBlackwhiteboxPass;

}
