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

	// A "path" for a bind that matches an instance. When we search for an
	// instance that needs changing, we return the path to it (which allows
	// the hierarchy code to insert bindings into target modules one at a
	// time).
	//
	// Each item is of the form (m, c) where c is a cell of the module m. A
	// path of [(m0, c0), (m1, c1)] means that the instance in question is
	// c1 in the module m1, where the relevant instance of m1 appears as
	// cell c0 in the module m0.
	typedef std::pair<RTLIL::Module *, RTLIL::Cell *> Item;
	typedef std::vector<Item> Path;

	// Search in the module given by the start argument for a cell with the
	// right name for target_name. Returns an empty path on no match.
	Path find_rel_cell(RTLIL::Design &design, RTLIL::Module &start) const;

	// Search from top-level for a cell with the right name for target_name.
	// This handles references like A.B.C, which can confusingly mean
	// "search for B.C inside a top-level module called A". There might be
	// multiple results because of parameter specialisation.
	//
	// If the target name contains no "." symbols, this won't return any
	// results (but find_concrete_module_targets might).
	std::vector<Path> find_tl_cells(RTLIL::Design &design) const;

	// Return a (possibly empty) list of non-abstract modules that should be
	// considered targets of this bind directive.
	std::vector<RTLIL::Module *>
	find_concrete_module_targets(RTLIL::Design &design) const;

	// Return a string describing the binding
	virtual std::string describe() const = 0;

	RTLIL::IdString get_attr_name() const { return attr_name; }

	// Apply this binding to the target module and return true. If the
	// binding has already been applied, return false. Implemented by
	// AST::Binding (which holds a syntax-level represention of what is to
	// be bound)
	virtual bool bind_into(RTLIL::Design &design,
			       RTLIL::Module &target) const = 0;

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

	// Check that a cell we've found matches any type we're expecting.
	void check_cell_type(RTLIL::Design &design, const RTLIL::Cell &cell) const;
};

YOSYS_NAMESPACE_END

#endif
