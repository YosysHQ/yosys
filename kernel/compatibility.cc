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

/**
 *  POSIX.2008 fake implementation for pre-POSIX.2008 systems. (OSX, BSD, MINGW, CYGWIN, older Linux &c.)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#if !(_XOPEN_SOURCE >= 700 || _POSIX_C_SOURCE >= 200809L)

typedef struct memstream {
	off_t pos;
	off_t size;
	char * buffer;
	char ** bufp;
	size_t * sizep;
	bool realloc;
} memstream_t;

static int memstream_read (void * cookie, char * buf, int size)
{
	memstream_t * mem = (memstream_t *) cookie;
	off_t available = mem->size - mem->pos;
	if (available < 0)
		available = 0;
	if (size > available)
		size = available;
	memcpy(buf, mem->buffer + mem->pos, size);
	mem->pos += size;
	return size;
}

static int memstream_write (void * cookie, const char * buf, int size)
{
	memstream_t * mem = (memstream_t *) cookie;
	off_t available = mem->size - mem->pos;
	if (size > available) {
		if (mem->realloc) {
			mem->buffer = (char *) realloc(mem->buffer, mem->pos + size + 1);
			memset(mem->buffer + mem->size, 0, mem->pos + size + 1 - mem->size);
			mem->size = mem->pos + size;
			if (mem->bufp)
				*(mem->bufp) = mem->buffer;
			if (mem->sizep)
				*(mem->sizep) = mem->size;
		} else {
			size = available;
		}
	}
	memcpy(mem->buffer + mem->pos, buf, sizeof(char) * size);
	mem->pos += size;
	return size;
}

static fpos_t memstream_seek (void * cookie, fpos_t offset, int whence)
{
	memstream_t * mem = (memstream_t *) cookie;
	switch (whence) {
	case SEEK_SET:
		if (offset < 0)
			goto error_inval;
		mem->pos = offset;
		return 0;
	case SEEK_CUR:
		if (mem->pos + offset < 0)
			goto error_inval;
		mem->pos += offset;
		return 0;
	case SEEK_END:
		if (mem->size + offset < 0)
			goto error_inval;
		mem->pos = mem->size + offset;
		break;
	default:
		goto error_inval;
	}
	return mem->pos;
error_inval:
	errno = EINVAL;
	return -1;
}

static int memstream_close (void * cookie)
{
	memstream_t * mem = (memstream_t *) cookie;
	if (mem->bufp)
		*(mem->bufp) = mem->buffer;
	if (mem->sizep)
		*(mem->sizep) = mem->size;
	free(cookie);
	return 0;
}

FILE * compat_fmemopen (void * buf, size_t size, const char * mode)
{
	memstream_t * mem = (memstream_t *) malloc(sizeof(memstream_t));
	memset(mem, 0, sizeof(memstream_t));
	mem->size = size;
	mem->buffer = (char *) buf;
	(void) mode;
	return funopen(mem, memstream_read, memstream_write, memstream_seek, memstream_close);
}

FILE * compat_open_memstream (char ** bufp, size_t * sizep)
{
	memstream_t * mem = (memstream_t *) malloc(sizeof(memstream_t));
	memset(mem, 0, sizeof(memstream_t));
	mem->bufp = bufp;
	mem->sizep = sizep;
	mem->realloc = true;
	return funopen(mem, memstream_read, memstream_write, memstream_seek, memstream_close);
}

#endif /* !(_XOPEN_SOURCE >= 700 || _POSIX_C_SOURCE >= 200809L) */

