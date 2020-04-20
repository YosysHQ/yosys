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
 */

#ifndef BINDING_H
#define BINDING_H

#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

struct RTLIL::Binding
{
	// Represents a bind construct.
	//
	// The target of the binding is represented by target_type and
	// target_name (see comments above the fields).

	Binding(RTLIL::IdString target_type,
	        RTLIL::IdString target_name);

	virtual ~Binding() {}

	// Return a string describing the binding
	virtual std::string describe() const = 0;

protected:
	// May be empty. If not, it's the name of the module or interface to
	// bind to.
	RTLIL::IdString target_type;

	// If target_type is nonempty (the usual case), this is a hierarchical
	// reference to the bind target. If target_type is empty, we have to
	// wait until the hierarchy pass to figure out whether this was the name
	// of a module/interface type or an instance.
	RTLIL::IdString target_name;

	// An attribute name which contains an ID that's unique across binding
	// instances (used to ensure we don't apply a binding twice to a module)
	RTLIL::IdString attr_name;
};

YOSYS_NAMESPACE_END

#endif
