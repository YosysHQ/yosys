#ifdef DEBUG

/* Autoloading of GDB Python pretty printing scripts.
 * More information at
 * https://sourceware.org/gdb/onlinedocs/gdb/dotdebug_005fgdb_005fscripts-section.html#dotdebug_005fgdb_005fscripts-section
 */

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


#else

#define DEFINE_GDB_PY_SCRIPT(script_name)

#endif
