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

#ifdef YOSYS_ENABLE_PLUGINS

#include <dlfcn.h>
#include <ffi.h>

YOSYS_NAMESPACE_BEGIN

typedef void (*ffi_fptr) ();

static ffi_fptr resolve_fn (std::string symbol_name)
{
	if (symbol_name.find(':') != std::string::npos)
	{
		int pos = symbol_name.find(':');
		std::string plugin_name = symbol_name.substr(0, pos);
		std::string real_symbol_name = symbol_name.substr(pos+1);

		while (loaded_plugin_aliases.count(plugin_name))
			plugin_name = loaded_plugin_aliases.at(plugin_name);

		if (loaded_plugins.count(plugin_name) == 0)
			log_error("unable to resolve '%s': can't find plugin `%s'\n", symbol_name.c_str(), plugin_name.c_str());

		void *symbol = dlsym(loaded_plugins.at(plugin_name), real_symbol_name.c_str());

		if (symbol == nullptr)
			log_error("unable to resolve '%s': can't find symbol `%s' in plugin `%s'\n",
					symbol_name.c_str(), real_symbol_name.c_str(), plugin_name.c_str());

		return (ffi_fptr) symbol;
	}

	for (auto &it : loaded_plugins) {
		void *symbol = dlsym(it.second, symbol_name.c_str());
		if (symbol != nullptr)
			return (ffi_fptr) symbol;
	}

	void *symbol = dlsym(RTLD_DEFAULT, symbol_name.c_str());
	if (symbol != nullptr)
		return (ffi_fptr) symbol;

	log_error("unable to resolve '%s'.\n", symbol_name.c_str());
}

AST::AstNode *AST::dpi_call(const std::string &rtype, const std::string &fname, const std::vector<std::string> &argtypes, const std::vector<AstNode*> &args)
{
	AST::AstNode *newNode = nullptr;
	union { double f64; float f32; int32_t i32; } value_store [args.size() + 1];
	ffi_type *types [args.size() + 1];
	void *values [args.size() + 1];
	ffi_cif cif;
	int status;

	log("Calling DPI function `%s' and returning `%s':\n", fname.c_str(), rtype.c_str());

	log_assert(GetSize(args) == GetSize(argtypes));
	for (int i = 0; i < GetSize(args); i++) {
		if (argtypes[i] == "real") {
			log("  arg %d (%s): %f\n", i, argtypes[i].c_str(), args[i]->asReal(args[i]->is_signed));
			value_store[i].f64 = args[i]->asReal(args[i]->is_signed);
			values[i] = &value_store[i].f64;
			types[i] = &ffi_type_double;
		} else if (argtypes[i] == "shortreal") {
			log("  arg %d (%s): %f\n", i, argtypes[i].c_str(), args[i]->asReal(args[i]->is_signed));
			value_store[i].f32 = args[i]->asReal(args[i]->is_signed);
			values[i] = &value_store[i].f32;
			types[i] = &ffi_type_double;
		} else if (argtypes[i] == "integer") {
			log("  arg %d (%s): %lld\n", i, argtypes[i].c_str(), (long long)args[i]->asInt(args[i]->is_signed));
			value_store[i].i32 = args[i]->asInt(args[i]->is_signed);
			values[i] = &value_store[i].i32;
			types[i] = &ffi_type_sint32;
		} else {
			log_error("invalid argtype '%s' for argument %d.\n", argtypes[i].c_str(), i);
		}
	}

        if (rtype == "integer") {
                types[args.size()] = &ffi_type_slong;
                values[args.size()] = &value_store[args.size()].i32;
        } else if (rtype == "shortreal") {
                types[args.size()] = &ffi_type_float;
                values[args.size()] = &value_store[args.size()].f32;
        } else if (rtype == "real") {
                types[args.size()] = &ffi_type_double;
                values[args.size()] = &value_store[args.size()].f64;
        } else {
                log_error("invalid rtype '%s'.\n", rtype.c_str());
        }

        if ((status = ffi_prep_cif(&cif, FFI_DEFAULT_ABI, args.size(), types[args.size()], types)) != FFI_OK)
                log_error("ffi_prep_cif failed: status %d.\n", status);

        ffi_call(&cif, resolve_fn(fname.c_str()), values[args.size()], values);

	if (rtype == "real") {
		newNode = new AstNode(AST_REALVALUE);
		newNode->realvalue = value_store[args.size()].f64;
		log("  return realvalue: %g\n", newNode->asReal(true));
	} else if (rtype == "shortreal") {
		newNode = new AstNode(AST_REALVALUE);
		newNode->realvalue = value_store[args.size()].f32;
		log("  return realvalue: %g\n", newNode->asReal(true));
	} else {
		newNode = AstNode::mkconst_int(value_store[args.size()].i32, false);
		log("  return integer: %lld\n", (long long)newNode->asInt(true));
	}

	return newNode;
}

YOSYS_NAMESPACE_END

#else /* YOSYS_ENABLE_PLUGINS */

YOSYS_NAMESPACE_BEGIN

AST::AstNode *AST::dpi_call(const std::string&, const std::string &fname, const std::vector<std::string>&, const std::vector<AstNode*>&)
{
	log_error("Can't call DPI function `%s': this version of yosys is built without plugin support\n", fname.c_str());
}

YOSYS_NAMESPACE_END

#endif /* YOSYS_ENABLE_PLUGINS */

