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

#ifndef PATMATCH_H
#define PATMATCH_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

// this is very similar to fnmatch(). the exact rules used by this
// function are:
//
//    ?        matches any character except
//    *        matches any sequence of characters
//    [...]    matches any of the characters in the list
//    [!..]    matches any of the characters not in the list
//
// a backslash may be used to escape the next characters in the
// pattern. each special character can also simply match itself.
//
static bool patmatch(const char *pattern, const char *string)
{
	if (*pattern == 0)
		return *string == 0;

	if (*pattern == '\\') {
		if (pattern[1] == string[0] && patmatch(pattern+2, string+1))
			return true;
	}

	if (*pattern == '?') {
		if (*string == 0)
			return false;
		return patmatch(pattern+1, string+1);
	}

	if (*pattern == '*') {
		while (*string) {
			if (patmatch(pattern+1, string++))
				return true;
		}
		return pattern[1] == 0;
	}

	if (*pattern == '[') {
		bool found_match = false;
		bool inverted_list = pattern[1] == '!';
		const char *p = pattern + (inverted_list ? 1 : 0);

		while (*++p) {
			if (*p == ']') {
				if (found_match != inverted_list && patmatch(p+1, string+1))
					return true;
				break;
			}

			if (*p == '\\') {
				if (*++p == *string)
					found_match = true;
			} else
			if (*p == *string)
				found_match = true;
		}
	}

	if (*pattern == *string)
		return patmatch(pattern+1, string+1);

	return false;
}

YOSYS_NAMESPACE_END

#endif
