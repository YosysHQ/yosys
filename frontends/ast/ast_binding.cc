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

PRIVATE_NAMESPACE_END
