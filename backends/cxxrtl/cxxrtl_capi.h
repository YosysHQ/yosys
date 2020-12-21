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
#include <assert.h>

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

// Create a design handle at a given hierarchy position from a design toplevel.
//
// This operation is similar to `cxxrtl_create`, except the full hierarchical name of every object
// is prepended with `root`.
cxxrtl_handle cxxrtl_create_at(cxxrtl_toplevel design, const char *root);

// Release all resources used by a design and its handle.
void cxxrtl_destroy(cxxrtl_handle handle);

// Reinitialize the design, replacing the internal state with the reset values while preserving
// black boxes.
//
// This operation is essentially equivalent to a power-on reset. Values, wires, and memories are
// returned to their reset state while preserving the state of black boxes and keeping all of
// the interior pointers obtained with e.g. `cxxrtl_get` valid.
void cxxrtl_reset(cxxrtl_handle handle);

// Evaluate the design, propagating changes on inputs to the `next` value of internal state and
// output wires.
//
// Returns 1 if the design is known to immediately converge, 0 otherwise.
int cxxrtl_eval(cxxrtl_handle handle);

// Commit the design, replacing the `curr` value of internal state and output wires with the `next`
// value.
//
// Return 1 if any of the `curr` values were updated, 0 otherwise.
int cxxrtl_commit(cxxrtl_handle handle);

// Simulate the design to a fixed point.
//
// Returns the number of delta cycles.
size_t cxxrtl_step(cxxrtl_handle handle);

// Type of a simulated object.
//
// The type of a simulated object indicates the way it is stored and the operations that are legal
// to perform on it (i.e. won't crash the simulation). It says very little about object semantics,
// which is specified through flags.
enum cxxrtl_type {
	// Values correspond to singly buffered netlist nodes, i.e. nodes driven exclusively by
	// combinatorial cells, or toplevel input nodes.
	//
	// Values can be inspected via the `curr` pointer. If the `next` pointer is NULL, the value is
	// driven by a constant and can never be modified. Otherwise, the value can be modified through
	// the `next` pointer (which is equal to `curr` if not NULL). Note that changes to the bits
	// driven by combinatorial cells will be ignored.
	//
	// Values always have depth 1.
	CXXRTL_VALUE = 0,

	// Wires correspond to doubly buffered netlist nodes, i.e. nodes driven, at least in part, by
	// storage cells, or by combinatorial cells that are a part of a feedback path. They are also
	// present in non-optimized builds.
	//
	// Wires can be inspected via the `curr` pointer and modified via the `next` pointer (which are
	// distinct for wires). Note that changes to the bits driven by combinatorial cells will be
	// ignored.
	//
	// Wires always have depth 1.
	CXXRTL_WIRE = 1,

	// Memories correspond to memory cells.
	//
	// Memories can be inspected and modified via the `curr` pointer. Due to a limitation of this
	// API, memories cannot yet be modified in a guaranteed race-free way, and the `next` pointer is
	// always NULL.
	CXXRTL_MEMORY = 2,

	// Aliases correspond to netlist nodes driven by another node such that their value is always
	// exactly equal.
	//
	// Aliases can be inspected via the `curr` pointer. They cannot be modified, and the `next`
	// pointer is always NULL.
	CXXRTL_ALIAS = 3,

	// Outlines correspond to netlist nodes that were optimized in a way that makes them inaccessible
	// outside of a module's `eval()` function. At the highest debug information level, every inlined
	// node has a corresponding outline object.
	//
	// Outlines can be inspected via the `curr` pointer and can never be modified; the `next` pointer
	// is always NULL. Unlike all other objects, the bits of an outline object are meaningful only
	// after a call to `cxxrtl_outline_eval` and until any subsequent modification to the netlist.
	// Observing this requirement is the responsibility of the caller; it is not enforced.
	//
	// Outlines always correspond to combinatorial netlist nodes that are not ports.
	CXXRTL_OUTLINE = 4,

	// More object types may be added in the future, but the existing ones will never change.
};

// Flags of a simulated object.
//
// The flags of a simulated object indicate its role in the netlist:
//  * The flags `CXXRTL_INPUT` and `CXXRTL_OUTPUT` designate module ports.
//  * The flags `CXXRTL_DRIVEN_SYNC`, `CXXRTL_DRIVEN_COMB`, and `CXXRTL_UNDRIVEN` specify
//    the semantics of node state. An object with several of these flags set has different bits
//    follow different semantics.
enum cxxrtl_flag {
	// Node is a module input port.
	//
	// This flag can be set on objects of type `CXXRTL_VALUE` and `CXXRTL_WIRE`. It may be combined
	// with `CXXRTL_OUTPUT`, as well as other flags.
	CXXRTL_INPUT = 1 << 0,

	// Node is a module output port.
	//
	// This flag can be set on objects of type `CXXRTL_WIRE`. It may be combined with `CXXRTL_INPUT`,
	// as well as other flags.
	CXXRTL_OUTPUT = 1 << 1,

	// Node is a module inout port.
	//
	// This flag can be set on objects of type `CXXRTL_WIRE`. It may be combined with other flags.
	CXXRTL_INOUT = (CXXRTL_INPUT|CXXRTL_OUTPUT),

	// Node has bits that are driven by a storage cell.
	//
	// This flag can be set on objects of type `CXXRTL_WIRE`. It may be combined with
	// `CXXRTL_DRIVEN_COMB` and `CXXRTL_UNDRIVEN`, as well as other flags.
	//
	// This flag is set on wires that have bits connected directly to the output of a flip-flop or
	// a latch, and hold its state. Many `CXXRTL_WIRE` objects may not have the `CXXRTL_DRIVEN_SYNC`
	// flag set; for example, output ports and feedback wires generally won't. Writing to the `next`
	// pointer of these wires updates stored state, and for designs without combinatorial loops,
	// capturing the value from every of these wires through the `curr` pointer creates a complete
	// snapshot of the design state.
	CXXRTL_DRIVEN_SYNC = 1 << 2,

	// Node has bits that are driven by a combinatorial cell or another node.
	//
	// This flag can be set on objects of type `CXXRTL_VALUE`, `CXXRTL_WIRE`, and `CXXRTL_OUTLINE`.
	// It may be combined with `CXXRTL_DRIVEN_SYNC` and `CXXRTL_UNDRIVEN`, as well as other flags.
	//
	// This flag is set on objects that have bits connected to the output of a combinatorial cell,
	// or directly to another node. For designs without combinatorial loops, writing to such bits
	// through the `next` pointer (if it is not NULL) has no effect.
	CXXRTL_DRIVEN_COMB = 1 << 3,

	// Node has bits that are not driven.
	//
	// This flag can be set on objects of type `CXXRTL_VALUE` and `CXXRTL_WIRE`. It may be combined
	// with `CXXRTL_DRIVEN_SYNC` and `CXXRTL_DRIVEN_COMB`, as well as other flags.
	//
	// This flag is set on objects that have bits not driven by an output of any cell or by another
	// node, such as inputs and dangling wires.
	CXXRTL_UNDRIVEN = 1 << 4,

	// More object flags may be added in the future, but the existing ones will never change.
};

// Description of a simulated object.
//
// The `curr` and `next` arrays can be accessed directly to inspect and, if applicable, modify
// the bits stored in the object.
struct cxxrtl_object {
	// Type of the object.
	//
	// All objects have the same memory layout determined by `width` and `depth`, but the type
	// determines all other properties of the object.
	uint32_t type; // actually `enum cxxrtl_type`

	// Flags of the object.
	uint32_t flags; // actually bit mask of `enum cxxrtl_flags`

	// Width of the object in bits.
	size_t width;

	// Index of the least significant bit.
	size_t lsb_at;

	// Depth of the object. Only meaningful for memories; for other objects, always 1.
	size_t depth;

	// Index of the first word. Only meaningful for memories; for other objects, always 0;
	size_t zero_at;

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

	// Opaque reference to an outline. Only meaningful for outline objects.
	//
	// See the documentation of `cxxrtl_outline` for details. When creating a `cxxrtl_object`, set
	// this field to NULL.
	struct _cxxrtl_outline *outline;

	// More description fields may be added in the future, but the existing ones will never change.
};

// Retrieve description of a simulated object.
//
// The `name` is the full hierarchical name of the object in the Yosys notation, where public names
// have a `\` prefix and hierarchy levels are separated by single spaces. For example, if
// the top-level module instantiates a module `foo`, which in turn contains a wire `bar`, the full
// hierarchical name is `\foo \bar`.
//
// The storage of a single abstract object may be split (usually with the `splitnets` pass) into
// many physical parts, all of which correspond to the same hierarchical name. To handle such cases,
// this function returns an array and writes its length to `parts`. The array is sorted by `lsb_at`.
//
// Returns the object parts if it was found, NULL otherwise. The returned parts are valid until
// the design is destroyed.
struct cxxrtl_object *cxxrtl_get_parts(cxxrtl_handle handle, const char *name, size_t *parts);

// Retrieve description of a single part simulated object.
//
// This function is a shortcut for the most common use of `cxxrtl_get_parts`. It asserts that,
// if the object exists, it consists of a single part. If assertions are disabled, it returns NULL
// for multi-part objects.
static inline struct cxxrtl_object *cxxrtl_get(cxxrtl_handle handle, const char *name) {
	size_t parts = 0;
	struct cxxrtl_object *object = cxxrtl_get_parts(handle, name, &parts);
	assert(object == NULL || parts == 1);
	if (object == NULL || parts == 1)
		return object;
	return NULL;
}

// Enumerate simulated objects.
//
// For every object in the simulation, `callback` is called with the provided `data`, the full
// hierarchical name of the object (see `cxxrtl_get` for details), and the object parts.
// The provided `name` and `object` values are valid until the design is destroyed.
void cxxrtl_enum(cxxrtl_handle handle, void *data,
                 void (*callback)(void *data, const char *name,
                                  struct cxxrtl_object *object, size_t parts));

// Opaque reference to an outline.
//
// An outline is a group of outline objects that are evaluated simultaneously. The identity of
// an outline can be compared to determine whether any two objects belong to the same outline.
typedef struct _cxxrtl_outline *cxxrtl_outline;

// Evaluate an outline.
//
// After evaluating an outline, the bits of every outline object contained in it are consistent
// with the current state of the netlist. In general, any further modification to the netlist
// causes every outline object to become stale, after which the corresponding outline must be
// re-evaluated, otherwise the bits read from that object are meaningless.
void cxxrtl_outline_eval(cxxrtl_outline outline);

#ifdef __cplusplus
}
#endif

#endif
