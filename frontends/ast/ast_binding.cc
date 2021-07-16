/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "ast_binding.h"
#include "ast.h"

YOSYS_NAMESPACE_BEGIN

using namespace AST_INTERNAL;

AST::Binding::Binding(RTLIL::IdString  target_type,
                      RTLIL::IdString  target_name,
                      const AstNode   &cell)
	: RTLIL::Binding(target_type, target_name),
	  ast_node(cell.clone())
{
	log_assert(cell.type == AST_CELL);
}

std::string
AST::Binding::describe() const
{
	std::ostringstream oss;
	oss << "directive to bind " << ast_node->str
	    << " to " << target_name.str();
	if (!target_type.empty())
		oss << " (target type: "
		    << target_type.str()
		    << ")";
	return oss.str();
}

bool
AST::Binding::bind_into(RTLIL::Design &design, RTLIL::Module &target) const
{
	if (target.get_bool_attribute(attr_name))
		return false;

	// Dynamically cast the target module to an AstModule. If we can't,
	// we're trying to bind into a module that didn't come from parsing RTL
	// code and there's not really much we can do!
	AstModule *tgt_ast_mod = dynamic_cast<AstModule *>(&target);
	if (!tgt_ast_mod) {
		log_error("Cannot bind into module `%s' because it didn't originally come from RTL.\n",
		          target.name.c_str());
	}

	tgt_ast_mod->loadconfig();

	// Re-derive the module from its AstNode, after modifying the
	// target's AST by inserting a copy of our own AST node to
	// represent the thing being bound in.
	AstNode *new_ast = tgt_ast_mod->ast->clone();
	new_ast->children.push_back(ast_node->clone());

	RTLIL::Module *new_module =
		process_and_replace_module(&design, &target, new_ast);

	// Set attr_name so that we don't try to bind into this module again.
	new_module->set_bool_attribute(attr_name);

	return true;
}

void
AST::Binding::report_error(const std::string &msg) const
{
	log_file_error(ast_node->filename,
	               ast_node->location.first_line,
	               "%s\n",
	               msg.c_str());
}

PRIVATE_NAMESPACE_END
