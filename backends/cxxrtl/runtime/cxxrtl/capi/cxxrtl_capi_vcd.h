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

#ifndef CXXRTL_CAPI_VCD_H
#define CXXRTL_CAPI_VCD_H

// This file is a part of the CXXRTL C API. It should be used together with `cxxrtl_vcd_capi.cc`.
//
// The CXXRTL C API for VCD writing makes it possible to insert virtual probes into designs and
// dump waveforms to Value Change Dump files.

#include <stddef.h>
#include <stdint.h>

#include <cxxrtl/capi/cxxrtl_capi.h>

#ifdef __cplusplus
extern "C" {
#endif

// Opaque reference to a VCD writer.
typedef struct _cxxrtl_vcd *cxxrtl_vcd;

// Create a VCD writer.
cxxrtl_vcd cxxrtl_vcd_create();

// Release all resources used by a VCD writer.
void cxxrtl_vcd_destroy(cxxrtl_vcd vcd);

// Set VCD timescale.
//
// The `number` must be 1, 10, or 100, and the `unit` must be one of `"s"`, `"ms"`, `"us"`, `"ns"`,
// `"ps"`, or `"fs"`.
//
// Timescale can only be set before the first call to `cxxrtl_vcd_sample`.
void cxxrtl_vcd_timescale(cxxrtl_vcd vcd, int number, const char *unit);

// Schedule a specific CXXRTL object to be sampled.
//
// The `name` is a full hierarchical name as described for `cxxrtl_get`; it does not need to match
// the original name of `object`, if any. The `object` must outlive the VCD writer, but there are
// no other requirements; if desired, it can be provided by user code, rather than come from
// a design.
//
// Objects can only be scheduled before the first call to `cxxrtl_vcd_sample`.
void cxxrtl_vcd_add(cxxrtl_vcd vcd, const char *name, struct cxxrtl_object *object);

// Schedule all CXXRTL objects in a simulation.
//
// The design `handle` must outlive the VCD writer.
//
// Objects can only be scheduled before the first call to `cxxrtl_vcd_sample`.
void cxxrtl_vcd_add_from(cxxrtl_vcd vcd, cxxrtl_handle handle);

// Schedule CXXRTL objects in a simulation that match a given predicate.
//
// For every object in the simulation, `filter` is called with the provided `data`, the full
// hierarchical name of the object (see `cxxrtl_get` for details), and the object description.
// The object will be sampled if the predicate returns a non-zero value.
//
// Objects can only be scheduled before the first call to `cxxrtl_vcd_sample`.
void cxxrtl_vcd_add_from_if(cxxrtl_vcd vcd, cxxrtl_handle handle, void *data,
                            int (*filter)(void *data, const char *name,
                                          const struct cxxrtl_object *object));

// Schedule all CXXRTL objects in a simulation except for memories.
//
// The design `handle` must outlive the VCD writer.
//
// Objects can only be scheduled before the first call to `cxxrtl_vcd_sample`.
void cxxrtl_vcd_add_from_without_memories(cxxrtl_vcd vcd, cxxrtl_handle handle);

// Sample all scheduled objects.
//
// First, `time` is written to the internal buffer. Second, the values of every signal changed since
// the previous call to `cxxrtl_vcd_sample` (all values if this is the first call) are written to
// the internal buffer. The contents of the buffer can be retrieved with `cxxrtl_vcd_read`.
void cxxrtl_vcd_sample(cxxrtl_vcd vcd, uint64_t time);

// Retrieve buffered VCD data.
//
// The pointer to the start of the next chunk of VCD data is assigned to `*data`, and the length
// of that chunk is assigned to `*size`. The pointer to the data is valid until the next call to
// `cxxrtl_vcd_sample` or `cxxrtl_vcd_read`. Once all of the buffered data has been retrieved,
// this function will always return zero sized chunks.
void cxxrtl_vcd_read(cxxrtl_vcd vcd, const char **data, size_t *size);

#ifdef __cplusplus
}
#endif

#endif
