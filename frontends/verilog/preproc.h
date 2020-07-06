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
 *  ---
 *
 *  The Verilog preprocessor.
 *
 */
#ifndef VERILOG_PREPROC_H
#define VERILOG_PREPROC_H

#include "kernel/yosys.h"

#include <iosfwd>
#include <list>
#include <memory>
#include <string>

YOSYS_NAMESPACE_BEGIN

struct define_body_t;
struct arg_map_t;

struct define_map_t
{
	define_map_t();
	~ define_map_t();

	// Add a definition, overwriting any existing definition for name.
	void add(const std::string &name, const std::string &txt, const arg_map_t *args = nullptr);

	// Merge in another map of definitions (which take precedence
	// over anything currently defined).
	void merge(const define_map_t &map);

	// Find a definition by name. If no match, returns null.
	const define_body_t *find(const std::string &name) const;

	// Erase a definition by name (no effect if not defined).
	void erase(const std::string &name);

	// Clear any existing definitions
	void clear();

	// Print a list of definitions, using the log function
	void log() const;

	std::map<std::string, std::unique_ptr<define_body_t>> defines;
};


struct define_map_t;

std::string
frontend_verilog_preproc(std::istream                 &f,
                         std::string                   filename,
                         const define_map_t           &pre_defines,
                         define_map_t                 &global_defines_cache,
                         const std::list<std::string> &include_dirs);

YOSYS_NAMESPACE_END

#endif
