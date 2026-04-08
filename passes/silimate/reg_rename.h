/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Stan Lee <stan@silimate.com>
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

#ifndef REG_RENAME_H
#define REG_RENAME_H

#include <string>

YOSYS_NAMESPACE_BEGIN

// Normalize scope path: replace '/' with '.' and remove leading and trailing '.'
inline std::string normalize_scope(std::string scope)
{
	if (scope.empty())
		return scope;
	
	// Replace all '/' with '.'
	for (size_t i = 0; i < scope.length(); i++) {
		if (scope[i] == '/') {
			if (i > 0 && scope[i-1] == '\\') continue; // skip escaped '/'
			scope[i] = '.';
		}
	}
	
	// Remove leading '.' if present
	if (scope[0] == '.')
		scope = scope.substr(1);

	// Remove trailing '.' if present (from a trailing '/')
	if (!scope.empty() && scope.back() == '.')
		scope = scope.substr(0, scope.size() - 1);
	
	return scope;
}

YOSYS_NAMESPACE_END

#endif
