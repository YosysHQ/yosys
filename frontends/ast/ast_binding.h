/* -*- c++ -*-
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
 *  ---
 *
 *  This header declares the AST::Binding class
 *
 *  This is used to support the bind directive and is to RTLIL::Binding as
 *  AST::AstModule is to RTLIL::Module, holding a syntax-level representation of
 *  cells until we get to a stage where they make sense. In the case of a bind
 *  directive, this is when we elaborate the design in the hierarchy pass.
 *
 */

#ifndef AST_BINDING_H
#define AST_BINDING_H

#include "kernel/rtlil.h"
#include "kernel/binding.h"

#include <memory>

YOSYS_NAMESPACE_BEGIN

namespace AST
{
	class Binding : public RTLIL::Binding
	{
	public:
		Binding(RTLIL::IdString  target_type,
		        RTLIL::IdString  target_name,
		        const AstNode   &cell);

		std::string describe() const override;

	private:
		// The syntax-level representation of the cell to be bound.
		std::unique_ptr<AstNode> ast_node;
	};
}

YOSYS_NAMESPACE_END

#endif
