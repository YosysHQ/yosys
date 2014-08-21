/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#include "ast.h"

AST::AstNode *AST::dpi_call(const std::string &rtype, const std::string &fname, const std::vector<std::string> &argtypes, const std::vector<AstNode*> &args)
{
	AST::AstNode *newNode = nullptr;

	log("Calling DPI function `%s' and returning `%s':\n", fname.c_str(), rtype.c_str());

	log_assert(SIZE(args) == SIZE(argtypes));
	for (int i = 0; i < SIZE(args); i++)
		if (argtypes[i] == "real" || argtypes[i] == "shortreal")
			log("  arg %d (%s): %f\n", i, argtypes[i].c_str(), args[i]->asReal(args[i]->is_signed));
		else
			log("  arg %d (%s): %lld\n", i, argtypes[i].c_str(), (long long)args[i]->asInt(args[i]->is_signed));

	if (rtype == "real" || rtype == "shortreal") {
		newNode = new AstNode(AST_REALVALUE);
		newNode->realvalue = 1234;
	} else {
		newNode = AstNode::mkconst_int(1234, false);
	}

	return newNode;
}

