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
#ifndef GDB_H
#define GDB_H

/* Default empty definition */
#define DEFINE_GDB_PY_SCRIPT(script_name)

/* If supported by your compiler + system, add autoloading of GDB Python pretty
 * printing scripts.
 * More information at
 *  https://sourceware.org/gdb/onlinedocs/gdb/dotdebug_005fgdb_005fscripts-section.html#dotdebug_005fgdb_005fscripts-section
 */
#if (defined(__GNUC__) || defined(__clang__))
#ifndef _WIN32

#undef DEFINE_GDB_PY_SCRIPT

/* Note: The "MS" section flags are to remove duplicates.  */
#define _DEFINE_GDB_PY_SCRIPT(script_name) \
  asm("\
.pushsection \".debug_gdb_scripts\", \"MS\",@progbits,1\n\
.byte 1 /* Python */\n\
.asciz \"" script_name "\"\n\
.popsection \n\
");

#define DEFINE_GDB_PY_SCRIPT(script_name) \
    _DEFINE_GDB_PY_SCRIPT(script_name) \
    _DEFINE_GDB_PY_SCRIPT("misc/gdb/" script_name) \


#endif
