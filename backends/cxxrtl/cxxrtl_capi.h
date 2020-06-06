/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  whitequark <whitequark@whitequark.org>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted.
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

#ifndef CXXRTL_CAPI_H
#define CXXRTL_CAPI_H

// This file is a part of the CXXRTL C API. It should be used together with `cxxrtl_capi.cc`.
//
// The CXXRTL C API makes it possible to drive CXXRTL designs using C or any other language that
// supports the C ABI, for example, Python. It does not provide a way to implement black boxes.

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// Opaque reference to a design toplevel.
//
// A design toplevel can only be used to create a design handle.
typedef struct _cxxrtl_toplevel *cxxrtl_toplevel;

// The constructor for a design toplevel is provided as a part of generated code for that design.
// Its prototype matches:
//
// cxxrtl_toplevel <design-name>_create();

// Opaque reference to a design handle.
//
// A design handle is required by all operations in the C API.
typedef struct _cxxrtl_handle *cxxrtl_handle;

// Create a design handle from a design toplevel.
//
// The `design` is consumed by this operation and cannot be used afterwards.
cxxrtl_handle cxxrtl_create(cxxrtl_toplevel design);

// Release all resources used by a design and its handle.
void cxxrtl_destroy(cxxrtl_handle handle);

// Simulate the design to a fixed point.
//
// Returns the number of delta cycles.
size_t cxxrtl_step(cxxrtl_handle handle);

// Type of a simulated object.
enum cxxrtl_type {
	// Values correspond to singly buffered netlist nodes, i.e. nodes driven exclusively by
	// combinatorial cells, or toplevel input nodes.
	//
	// Values can be inspected via the `curr` pointer and modified via the `next` pointer (which are
	// equal for values); however, note that changes to the bits driven by combinatorial cells will
	// be ignored.
	//
	// Values always have depth 1.
	CXXRTL_VALUE = 0,

	// Wires correspond to doubly buffered netlist nodes, i.e. nodes driven, at least in part, by
	// storage cells, or by combinatorial cells that are a part of a feedback path.
	//
	// Wires can be inspected via the `curr` pointer and modified via the `next` pointer (which are
	// distinct for wires); however, note that changes to the bits driven by combinatorial cells will
	// be ignored.
	//
	// Wires always have depth 1.
	CXXRTL_WIRE = 1,

	// Memories correspond to memory cells.
	//
	// Memories can be inspected and modified via the `curr` pointer. Due to a limitation of this
	// API, memories cannot yet be modified in a guaranteed race-free way, and the `next` pointer is
	// always NULL.
	CXXRTL_MEMORY = 2,

	// More object types will be added in the future, but the existing ones will never change.
};

// Description of a simulated object.
//
// The `data` array can be accessed directly to inspect and, if applicable, modify the bits
// stored in the object.
struct cxxrtl_object {
	// Type of the object.
	//
	// All objects have the same memory layout determined by `width` and `depth`, but the type
	// determines all other properties of the object.
	uint32_t type; // actually `enum cxxrtl_type`

	// Width of the object in bits.
	size_t width;

	// Depth of the object. Only meaningful for memories; for other objects, always 1.
	size_t depth;

	// Bits stored in the object, as 32-bit chunks, least significant bits first.
	//
	// The width is rounded up to a multiple of 32; the padding bits are always set to 0 by
	// the simulation code, and must be always written as 0 when modified by user code.
	// In memories, every element is stored contiguously. Therefore, the total number of chunks
	// in any object is `((width + 31) / 32) * depth`.
	//
	// To allow the simulation to be partitioned into multiple independent units communicating
	// through wires, the bits are double buffered. To avoid race conditions, user code should
	// always read from `curr` and write to `next`. The `curr` pointer is always valid; for objects
	// that cannot be modified, or cannot be modified in a race-free way, `next` is NULL.
	uint32_t *curr;
	uint32_t *next;

	// More description fields will be added in the future, but the existing ones will never change.
};

// Retrieve description of a simulated object.
//
// The `name` is the full hierarchical name of the object in the Yosys notation, where public names
// have a `\` prefix and hierarchy levels are separated by single spaces. For example, if
// the top-level module instantiates a module `foo`, which in turn contains a wire `bar`, the full
// hierarchical name is `\foo \bar`.
//
// Returns the object if it was found, NULL otherwise. The returned value is valid until the design
// is destroyed.
struct cxxrtl_object *cxxrtl_get(cxxrtl_handle handle, const char *name);

// Enumerate simulated objects.
//
// For every object in the simulation, `callback` is called with the provided `data`, the full
// hierarchical name of the object (see `cxxrtl_get` for details), and the object description.
// The provided `name` and `object` values are valid until the design is destroyed.
void cxxrtl_enum(cxxrtl_handle handle, void *data,
                 void (*callback)(void *data, const char *name, struct cxxrtl_object *object));

#ifdef __cplusplus
}
#endif

#endif
