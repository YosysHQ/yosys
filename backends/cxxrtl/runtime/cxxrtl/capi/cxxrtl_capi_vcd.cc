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

// This file is a part of the CXXRTL C API. It should be used together with `cxxrtl/capi/cxxrtl_capi_vcd.h`.

#include <cxxrtl/capi/cxxrtl_capi_vcd.h>
#include <cxxrtl/cxxrtl_vcd.h>

extern const cxxrtl::debug_items &cxxrtl_debug_items_from_handle(cxxrtl_handle handle);

struct _cxxrtl_vcd {
	cxxrtl::vcd_writer writer;
	bool flush = false;
};

cxxrtl_vcd cxxrtl_vcd_create() {
	return new _cxxrtl_vcd;
}

void cxxrtl_vcd_destroy(cxxrtl_vcd vcd) {
	delete vcd;
}

void cxxrtl_vcd_timescale(cxxrtl_vcd vcd, int number, const char *unit) {
	vcd->writer.timescale(number, unit);
}

void cxxrtl_vcd_add(cxxrtl_vcd vcd, const char *name, cxxrtl_object *object) {
	// Note the copy. We don't know whether `object` came from a design (in which case it is
	// an instance of `debug_item`), or from user code (in which case it is an instance of
	// `cxxrtl_object`), so casting the pointer wouldn't be safe.
	vcd->writer.add(name, cxxrtl::debug_item(*object));
}

void cxxrtl_vcd_add_from(cxxrtl_vcd vcd, cxxrtl_handle handle) {
	vcd->writer.add(cxxrtl_debug_items_from_handle(handle));
}

void cxxrtl_vcd_add_from_if(cxxrtl_vcd vcd, cxxrtl_handle handle, void *data,
														int (*filter)(void *data, const char *name,
														              const cxxrtl_object *object)) {
	vcd->writer.add(cxxrtl_debug_items_from_handle(handle),
		[=](const std::string &name, const cxxrtl::debug_item &item) {
			return filter(data, name.c_str(), static_cast<const cxxrtl_object*>(&item));
		});
}

void cxxrtl_vcd_add_from_without_memories(cxxrtl_vcd vcd, cxxrtl_handle handle) {
	vcd->writer.add_without_memories(cxxrtl_debug_items_from_handle(handle));
}

void cxxrtl_vcd_sample(cxxrtl_vcd vcd, uint64_t time) {
	if (vcd->flush) {
		vcd->writer.buffer.clear();
		vcd->flush = false;
	}
	vcd->writer.sample(time);
}

void cxxrtl_vcd_read(cxxrtl_vcd vcd, const char **data, size_t *size) {
	if (vcd->flush) {
		vcd->writer.buffer.clear();
		vcd->flush = false;
	}
	*data = vcd->writer.buffer.c_str();
	*size = vcd->writer.buffer.size();
	vcd->flush = true;
}
