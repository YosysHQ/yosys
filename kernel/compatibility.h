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

#ifndef COMPATIBILITY_H
#define COMPATIBILITY_H

#if !(_XOPEN_SOURCE >= 700 || _POSIX_C_SOURCE >= 200809L)
#include <stdio.h>
#include <stdlib.h>

#define open_memstream compat_open_memstream
#define fmemopen compat_fmemopen

FILE * compat_open_memstream (char ** bufp, size_t * sizep);
FILE * compat_fmemopen (void * buf, size_t size, const char * mode);

#endif /* !(_XOPEN_SOURCE >= 700 || _POSIX_C_SOURCE >= 200809L) */

#endif /* COMPATIBILITY_H */

