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

// This file is a part of the CXXRTL C API. It should be used together with `cxxrtl/capi/cxxrtl_capi.h`.

#include <cxxrtl/capi/cxxrtl_capi.h>
#include <cxxrtl/cxxrtl.h>

struct _cxxrtl_handle {
	std::unique_ptr<cxxrtl::module> module;
	cxxrtl::debug_items objects;
};

// Private function for use by other units of the C API.
const cxxrtl::debug_items &cxxrtl_debug_items_from_handle(cxxrtl_handle handle) {
	return handle->objects;
}

cxxrtl_handle cxxrtl_create(cxxrtl_toplevel design) {
	return cxxrtl_create_at(design, "");
}

cxxrtl_handle cxxrtl_create_at(cxxrtl_toplevel design, const char *top_path_) {
	std::string top_path = top_path_;
	if (!top_path.empty()) {
		// module::debug_info() accepts either an empty path, or a path ending in space to simplify
		// the logic in generated code. While this is sketchy at best to expose in the C++ API, this
		// would be a lot worse in the C API, so don't expose it here.
		assert(top_path.back() != ' ');
		top_path += ' ';
	}

	cxxrtl_handle handle = new _cxxrtl_handle;
	handle->module = std::move(design->module);
	handle->module->debug_info(&handle->objects, nullptr, top_path);
	delete design;
	return handle;
}

void cxxrtl_destroy(cxxrtl_handle handle) {
	delete handle;
}

void cxxrtl_reset(cxxrtl_handle handle) {
	handle->module->reset();
}

int cxxrtl_eval(cxxrtl_handle handle) {
	return handle->module->eval();
}

int cxxrtl_commit(cxxrtl_handle handle) {
	return handle->module->commit();
}

size_t cxxrtl_step(cxxrtl_handle handle) {
	return handle->module->step();
}

struct cxxrtl_object *cxxrtl_get_parts(cxxrtl_handle handle, const char *name, size_t *parts) {
	auto it = handle->objects.table.find(name);
	if (it == handle->objects.table.end())
		return nullptr;
	*parts = it->second.size();
	return static_cast<cxxrtl_object*>(&it->second[0]);
}

void cxxrtl_enum(cxxrtl_handle handle, void *data,
                 void (*callback)(void *data, const char *name,
                                  cxxrtl_object *object, size_t parts)) {
	for (auto &it : handle->objects.table)
		callback(data, it.first.c_str(), static_cast<cxxrtl_object*>(&it.second[0]), it.second.size());
}

void cxxrtl_outline_eval(cxxrtl_outline outline) {
	outline->eval();
}

int cxxrtl_attr_type(cxxrtl_attr_set attrs_, const char *name) {
	auto attrs = (cxxrtl::metadata_map*)attrs_;
	if (!attrs->count(name))
		return CXXRTL_ATTR_NONE;
	switch (attrs->at(name).value_type) {
		case cxxrtl::metadata::UINT:
			return CXXRTL_ATTR_UNSIGNED_INT;
		case cxxrtl::metadata::SINT:
			return CXXRTL_ATTR_SIGNED_INT;
		case cxxrtl::metadata::STRING:
			return CXXRTL_ATTR_STRING;
		case cxxrtl::metadata::DOUBLE:
			return CXXRTL_ATTR_DOUBLE;
		default:
			// Present unsupported attribute type the same way as no attribute at all.
			return CXXRTL_ATTR_NONE;
	}
}

uint64_t cxxrtl_attr_get_unsigned_int(cxxrtl_attr_set attrs_, const char *name) {
	auto &attrs = *(cxxrtl::metadata_map*)attrs_;
	assert(attrs.count(name) && attrs.at(name).value_type == cxxrtl::metadata::UINT);
	return attrs[name].as_uint();
}

int64_t cxxrtl_attr_get_signed_int(cxxrtl_attr_set attrs_, const char *name) {
	auto &attrs = *(cxxrtl::metadata_map*)attrs_;
	assert(attrs.count(name) && attrs.at(name).value_type == cxxrtl::metadata::SINT);
	return attrs[name].as_sint();
}

const char *cxxrtl_attr_get_string(cxxrtl_attr_set attrs_, const char *name) {
	auto &attrs = *(cxxrtl::metadata_map*)attrs_;
	assert(attrs.count(name) && attrs.at(name).value_type == cxxrtl::metadata::STRING);
	return attrs[name].as_string().c_str();
}

double cxxrtl_attr_get_double(cxxrtl_attr_set attrs_, const char *name) {
	auto &attrs = *(cxxrtl::metadata_map*)attrs_;
	assert(attrs.count(name) && attrs.at(name).value_type == cxxrtl::metadata::DOUBLE);
	return attrs[name].as_double();
}
