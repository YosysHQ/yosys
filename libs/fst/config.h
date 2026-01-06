/* Define to 1 if you have <alloca.h> and it should be used (not on Ultrix).
 */
#define HAVE_ALLOCA_H 1

/* Define to 1 if fseeko (and presumably ftello) exists and is declared. */
#define HAVE_FSEEKO 1

/* Define to 1 if you have the `pthread' library (-lpthread). */
#define HAVE_LIBPTHREAD 1

/* Define to 1 if you have the `realpath' function. */
#define HAVE_REALPATH 1

#if defined(__MINGW32__)
#undef HAVE_ALLOCA_H
#undef HAVE_REALPATH
#endif
#if defined(_MSC_VER)
#undef HAVE_ALLOCA_H
#undef HAVE_REALPATH
#undef HAVE_LIBPTHREAD
#undef HAVE_FSEEKO
#endif
#if defined(__FreeBSD__) || defined(__OpenBSD__) || defined(__NetBSD__)
#undef HAVE_ALLOCA_H
#endif

# ifndef __STDC_FORMAT_MACROS
#  define __STDC_FORMAT_MACROS 1
# endif
