/*
 * Copyright (c) 2009-2018 Tony Bybell.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 *
 * SPDX-License-Identifier: MIT
 */

/*
 * possible disables:
 *
 * FST_DYNAMIC_ALIAS_DISABLE : dynamic aliases are not processed
 * FST_DYNAMIC_ALIAS2_DISABLE : new encoding for dynamic aliases is not generated
 * FST_WRITEX_DISABLE : fast write I/O routines are disabled
 *
 * possible enables:
 *
 * FST_DEBUG : not for production use, only enable for development
 * FST_REMOVE_DUPLICATE_VC : glitch removal (has writer performance impact)
 * HAVE_LIBPTHREAD -> FST_WRITER_PARALLEL : enables inclusion of parallel writer code
 * FST_DO_MISALIGNED_OPS (defined automatically for x86 and some others) : CPU architecture can handle misaligned
 * loads/stores _WAVE_HAVE_JUDY : use Judy arrays instead of Jenkins (undefine if LGPL is not acceptable)
 *
 */

#ifndef FST_CONFIG_INCLUDE
#define FST_CONFIG_INCLUDE "config.h"
#endif
#include FST_CONFIG_INCLUDE

#include "fstapi.h"
#include "fastlz.h"
#include "lz4.h"
#include <errno.h>

#ifndef HAVE_LIBPTHREAD
#undef FST_WRITER_PARALLEL
#endif

#ifdef FST_WRITER_PARALLEL
#include <pthread.h>
#endif

#ifdef __MINGW32__
#include <windows.h>
#endif

#ifdef HAVE_ALLOCA_H
#include <alloca.h>
#elif defined(__GNUC__)
#ifndef __MINGW32__
#ifndef alloca
#define alloca __builtin_alloca
#endif
#else
#include <malloc.h>
#endif
#elif defined(_MSC_VER)
#include <malloc.h>
#define alloca _alloca
#endif

#ifndef PATH_MAX
#define PATH_MAX (4096)
#endif

#if defined(_MSC_VER)
typedef int64_t fst_off_t;
#else
typedef off_t fst_off_t;
#endif

/* note that Judy versus Jenkins requires more experimentation: they are  */
/* functionally equivalent though it appears Jenkins is slightly faster.  */
/* in addition, Jenkins is not bound by the LGPL.                         */
#ifdef _WAVE_HAVE_JUDY
#include <Judy.h>
#else
/* should be more than enough for fstWriterSetSourceStem() */
#define FST_PATH_HASHMASK ((1UL << 16) - 1)
typedef const void *Pcvoid_t;
typedef void *Pvoid_t;
typedef void **PPvoid_t;
#define JudyHSIns(a, b, c, d) JenkinsIns((a), (b), (c), (hashmask))
#define JudyHSFreeArray(a, b) JenkinsFree((a), (hashmask))
void JenkinsFree(void *base_i, uint32_t hashmask);
void **JenkinsIns(void *base_i, const unsigned char *mem, uint32_t length, uint32_t hashmask);
#endif

#ifndef FST_WRITEX_DISABLE
#define FST_WRITEX_MAX (64 * 1024)
#else
#define fstWritex(a, b, c) fstFwrite((b), (c), 1, fv)
#endif

/* these defines have a large impact on writer speed when a model has a */
/* huge number of symbols.  as a default, use 128MB and increment when  */
/* every 1M signals are defined.                                        */
#define FST_BREAK_SIZE (1UL << 27)
#define FST_BREAK_ADD_SIZE (1UL << 22)
#define FST_BREAK_SIZE_MAX (1UL << 31)
#define FST_ACTIVATE_HUGE_BREAK (1000000)
#define FST_ACTIVATE_HUGE_INC (1000000)

#define FST_WRITER_STR "fstWriter"
#define FST_ID_NAM_SIZ (512)
#define FST_ID_NAM_ATTR_SIZ (65536 + 4096)
#define FST_DOUBLE_ENDTEST (2.7182818284590452354)
#define FST_HDR_SIM_VERSION_SIZE (128)
#define FST_HDR_DATE_SIZE (119)
#define FST_HDR_FILETYPE_SIZE (1)
#define FST_HDR_TIMEZERO_SIZE (8)
#define FST_GZIO_LEN (32768)
#define FST_HDR_FOURPACK_DUO_SIZE (4 * 1024 * 1024)

#if defined(__i386__) || defined(__x86_64__) || defined(_AIX)
#define FST_DO_MISALIGNED_OPS
#endif

#if defined(__APPLE__) && defined(__MACH__)
#define FST_MACOSX
#include <sys/sysctl.h>
#endif

#ifdef __GNUC__
/* Boolean expression more often true than false */
#define FST_LIKELY(x) __builtin_expect(!!(x), 1)
/* Boolean expression more often false than true */
#define FST_UNLIKELY(x) __builtin_expect(!!(x), 0)
#else
#define FST_LIKELY(x) (!!(x))
#define FST_UNLIKELY(x) (!!(x))
#endif

#define FST_APIMESS "FSTAPI  | "

/***********************/
/***                 ***/
/*** common function ***/
/***                 ***/
/***********************/

#if defined(__MINGW32__) || defined(_MSC_VER)
#include <io.h>
#ifndef HAVE_FSEEKO
#define ftello _ftelli64
#define fseeko _fseeki64
#endif
#endif

/*
 * the recoded "extra" values...
 * note that FST_RCV_Q is currently unused and is for future expansion.
 * its intended use is as another level of escape such that any arbitrary
 * value can be stored as the value: { time_delta, 8 bits, FST_RCV_Q }.
 * this is currently not implemented so that the branchless decode is:
 * uint32_t shcnt = 2 << (vli & 1); tdelta = vli >> shcnt;
 */
#define FST_RCV_X (1 | (0 << 1))
#define FST_RCV_Z (1 | (1 << 1))
#define FST_RCV_H (1 | (2 << 1))
#define FST_RCV_U (1 | (3 << 1))
#define FST_RCV_W (1 | (4 << 1))
#define FST_RCV_L (1 | (5 << 1))
#define FST_RCV_D (1 | (6 << 1))
#define FST_RCV_Q (1 | (7 << 1))

#define FST_RCV_STR "xzhuwl-?"
/*                   01234567 */

/*
 * prevent old file overwrite when currently being read
 */
static FILE *unlink_fopen(const char *nam, const char *mode)
{
    unlink(nam);
    return (fopen(nam, mode));
}

/*
 * system-specific temp file handling
 */
#ifdef __MINGW32__

static FILE *tmpfile_open(char **nam)
{
    char *fname = NULL;
    TCHAR szTempFileName[MAX_PATH];
    TCHAR lpTempPathBuffer[MAX_PATH];
    DWORD dwRetVal = 0;
    UINT uRetVal = 0;
    FILE *fh = NULL;

    if (nam) /* cppcheck warning fix: nam is always defined, so this is not needed */
    {
        dwRetVal = GetTempPath(MAX_PATH, lpTempPathBuffer);
        if ((dwRetVal > MAX_PATH) || (dwRetVal == 0)) {
            fprintf(stderr, FST_APIMESS "GetTempPath() failed in " __FILE__ " line %d, exiting.\n", __LINE__);
            exit(255);
        } else {
            uRetVal = GetTempFileName(lpTempPathBuffer, TEXT("FSTW"), 0, szTempFileName);
            if (uRetVal == 0) {
                fprintf(stderr, FST_APIMESS "GetTempFileName() failed in " __FILE__ " line %d, exiting.\n", __LINE__);
                exit(255);
            } else {
                fname = strdup(szTempFileName);
            }
        }

        if (fname) {
            *nam = fname;
            fh = unlink_fopen(fname, "w+b");
        }
    }

    return (fh);
}

#else

static FILE *tmpfile_open(char **nam)
{
    FILE *f = tmpfile(); /* replace with mkstemp() + fopen(), etc if this is not good enough */
    if (nam) {
        *nam = NULL;
    }
    return (f);
}

#endif

static void tmpfile_close(FILE **f, char **nam)
{
    if (f) {
        if (*f) {
            fclose(*f);
            *f = NULL;
        }
    }

    if (nam) {
        if (*nam) {
            unlink(*nam);
            free(*nam);
            *nam = NULL;
        }
    }
}

/*****************************************/

/*
 * to remove warn_unused_result compile time messages
 * (in the future there needs to be results checking)
 */
static size_t fstFread(void *buf, size_t siz, size_t cnt, FILE *fp) { return (fread(buf, siz, cnt, fp)); }

static size_t fstFwrite(const void *buf, size_t siz, size_t cnt, FILE *fp) { return (fwrite(buf, siz, cnt, fp)); }

static int fstFtruncate(int fd, fst_off_t length) { return (ftruncate(fd, length)); }

/*
 * realpath compatibility
 */
static char *fstRealpath(const char *path, char *resolved_path)
{
#if defined __USE_BSD || defined __USE_XOPEN_EXTENDED || defined __CYGWIN__ || defined HAVE_REALPATH
#if (defined(__MACH__) && defined(__APPLE__))
    if (!resolved_path) {
        resolved_path = (char *)malloc(PATH_MAX + 1); /* fixes bug on Leopard when resolved_path == NULL */
    }
#endif

    return (realpath(path, resolved_path));

#else
#ifdef __MINGW32__
    if (!resolved_path) {
        resolved_path = (char *)malloc(PATH_MAX + 1);
    }
    return (_fullpath(resolved_path, path, PATH_MAX));
#else
    (void)path;
    (void)resolved_path;
    return (NULL);
#endif
#endif
}

/*
 * mmap compatibility
 */
#if defined __CYGWIN__ || defined __MINGW32__ || defined _MSC_VER
#include <limits.h>
#define fstMmap(__addr, __len, __prot, __flags, __fd, __off) fstMmap2((__len), (__fd), (__off))
#define fstMunmap(__addr, __len) free(__addr)

static void *fstMmap2(size_t __len, int __fd, fst_off_t __off)
{
    (void)__off;

    unsigned char *pnt = (unsigned char *)malloc(__len);
    fst_off_t cur_offs = lseek(__fd, 0, SEEK_CUR);
    size_t i;

    lseek(__fd, 0, SEEK_SET);
    for (i = 0; i < __len; i += SSIZE_MAX) {
        read(__fd, pnt + i, ((__len - i) >= SSIZE_MAX) ? SSIZE_MAX : (__len - i));
    }
    lseek(__fd, cur_offs, SEEK_SET);
    return (pnt);
}
#else
#include <sys/mman.h>
#if defined(__SUNPRO_C)
#define FST_CADDR_T_CAST (caddr_t)
#else
#define FST_CADDR_T_CAST
#endif
#define fstMmap(__addr, __len, __prot, __flags, __fd, __off)                                                           \
    (void *)mmap(FST_CADDR_T_CAST(__addr), (__len), (__prot), (__flags), (__fd), (__off))
#define fstMunmap(__addr, __len)                                                                                       \
    {                                                                                                                  \
        if (__addr)                                                                                                    \
            munmap(FST_CADDR_T_CAST(__addr), (__len));                                                                 \
    }
#endif

/*
 * regular and variable-length integer access functions
 */
#ifdef FST_DO_MISALIGNED_OPS
#define fstGetUint32(x) (*(uint32_t *)(x))
#else
static uint32_t fstGetUint32(unsigned char *mem)
{
    uint32_t u32;
    unsigned char *buf = (unsigned char *)(&u32);

    buf[0] = mem[0];
    buf[1] = mem[1];
    buf[2] = mem[2];
    buf[3] = mem[3];

    return (*(uint32_t *)buf);
}
#endif

static int fstWriterUint64(FILE *handle, uint64_t v)
{
    unsigned char buf[8];
    int i;

    for (i = 7; i >= 0; i--) {
        buf[i] = v & 0xff;
        v >>= 8;
    }

    fstFwrite(buf, 8, 1, handle);
    return (8);
}

static uint64_t fstReaderUint64(FILE *f)
{
    uint64_t val = 0;
    unsigned char buf[sizeof(uint64_t)];
    unsigned int i;

    fstFread(buf, sizeof(uint64_t), 1, f);
    for (i = 0; i < sizeof(uint64_t); i++) {
        val <<= 8;
        val |= buf[i];
    }

    return (val);
}

static uint32_t fstGetVarint32(unsigned char *mem, int *skiplen)
{
    unsigned char *mem_orig = mem;
    uint32_t rc = 0;
    while (*mem & 0x80) {
        mem++;
    }

    *skiplen = mem - mem_orig + 1;
    for (;;) {
        rc <<= 7;
        rc |= (uint32_t)(*mem & 0x7f);
        if (mem == mem_orig) {
            break;
        }
        mem--;
    }

    return (rc);
}

static uint32_t fstGetVarint32Length(unsigned char *mem)
{
    unsigned char *mem_orig = mem;

    while (*mem & 0x80) {
        mem++;
    }

    return (mem - mem_orig + 1);
}

static uint32_t fstGetVarint32NoSkip(unsigned char *mem)
{
    unsigned char *mem_orig = mem;
    uint32_t rc = 0;
    while (*mem & 0x80) {
        mem++;
    }

    for (;;) {
        rc <<= 7;
        rc |= (uint32_t)(*mem & 0x7f);
        if (mem == mem_orig) {
            break;
        }
        mem--;
    }

    return (rc);
}

static unsigned char *fstCopyVarint32ToLeft(unsigned char *pnt, uint32_t v)
{
    unsigned char *spnt;
    uint32_t nxt = v;
    int cnt = 1;
    int i;

    while ((nxt = nxt >> 7)) /* determine len to avoid temp buffer copying to cut down on load-hit-store */
    {
        cnt++;
    }

    pnt -= cnt;
    spnt = pnt;
    cnt--;

    for (i = 0; i < cnt; i++) /* now generate left to right as normal */
    {
        nxt = v >> 7;
        *(spnt++) = ((unsigned char)v) | 0x80;
        v = nxt;
    }
    *spnt = (unsigned char)v;

    return (pnt);
}

static unsigned char *fstCopyVarint64ToRight(unsigned char *pnt, uint64_t v)
{
    uint64_t nxt;

    while ((nxt = v >> 7)) {
        *(pnt++) = ((unsigned char)v) | 0x80;
        v = nxt;
    }
    *(pnt++) = (unsigned char)v;

    return (pnt);
}

static uint64_t fstGetVarint64(unsigned char *mem, int *skiplen)
{
    unsigned char *mem_orig = mem;
    uint64_t rc = 0;
    while (*mem & 0x80) {
        mem++;
    }

    *skiplen = mem - mem_orig + 1;
    for (;;) {
        rc <<= 7;
        rc |= (uint64_t)(*mem & 0x7f);
        if (mem == mem_orig) {
            break;
        }
        mem--;
    }

    return (rc);
}

static uint32_t fstReaderVarint32(FILE *f)
{
    unsigned char buf[5];
    unsigned char *mem = buf;
    uint32_t rc = 0;
    int ch;

    do {
        ch = fgetc(f);
        *(mem++) = ch;
    } while (ch & 0x80);
    mem--;

    for (;;) {
        rc <<= 7;
        rc |= (uint32_t)(*mem & 0x7f);
        if (mem == buf) {
            break;
        }
        mem--;
    }

    return (rc);
}

static uint32_t fstReaderVarint32WithSkip(FILE *f, uint32_t *skiplen)
{
    unsigned char buf[5];
    unsigned char *mem = buf;
    uint32_t rc = 0;
    int ch;

    do {
        ch = fgetc(f);
        *(mem++) = ch;
    } while (ch & 0x80);
    *skiplen = mem - buf;
    mem--;

    for (;;) {
        rc <<= 7;
        rc |= (uint32_t)(*mem & 0x7f);
        if (mem == buf) {
            break;
        }
        mem--;
    }

    return (rc);
}

static uint64_t fstReaderVarint64(FILE *f)
{
    unsigned char buf[16];
    unsigned char *mem = buf;
    uint64_t rc = 0;
    int ch;

    do {
        ch = fgetc(f);
        *(mem++) = ch;
    } while (ch & 0x80);
    mem--;

    for (;;) {
        rc <<= 7;
        rc |= (uint64_t)(*mem & 0x7f);
        if (mem == buf) {
            break;
        }
        mem--;
    }

    return (rc);
}

static int fstWriterVarint(FILE *handle, uint64_t v)
{
    uint64_t nxt;
    unsigned char buf[10]; /* ceil(64/7) = 10 */
    unsigned char *pnt = buf;
    int len;

    while ((nxt = v >> 7)) {
        *(pnt++) = ((unsigned char)v) | 0x80;
        v = nxt;
    }
    *(pnt++) = (unsigned char)v;

    len = pnt - buf;
    fstFwrite(buf, len, 1, handle);
    return (len);
}

/* signed integer read/write routines are currently unused */
static int64_t fstGetSVarint64(unsigned char *mem, int *skiplen)
{
    unsigned char *mem_orig = mem;
    int64_t rc = 0;
    const int64_t one = 1;
    const int siz = sizeof(int64_t) * 8;
    int shift = 0;
    unsigned char byt;

    do {
        byt = *(mem++);
        rc |= ((int64_t)(byt & 0x7f)) << shift;
        shift += 7;

    } while (byt & 0x80);

    if ((shift < siz) && (byt & 0x40)) {
        rc |= -(one << shift); /* sign extend */
    }

    *skiplen = mem - mem_orig;

    return (rc);
}

#ifndef FST_DYNAMIC_ALIAS2_DISABLE
static int fstWriterSVarint(FILE *handle, int64_t v)
{
    unsigned char buf[15]; /* ceil(64/7) = 10 + sign byte padded way up */
    unsigned char byt;
    unsigned char *pnt = buf;
    int more = 1;
    int len;

    do {
        byt = v | 0x80;
        v >>= 7;

        if (((!v) && (!(byt & 0x40))) || ((v == -1) && (byt & 0x40))) {
            more = 0;
            byt &= 0x7f;
        }

        *(pnt++) = byt;
    } while (more);

    len = pnt - buf;
    fstFwrite(buf, len, 1, handle);
    return (len);
}
#endif

/***********************/
/***                 ***/
/*** writer function ***/
/***                 ***/
/***********************/

/*
 * private structs
 */
struct fstBlackoutChain
{
    struct fstBlackoutChain *next;
    uint64_t tim;
    unsigned active : 1;
};

struct fstWriterContext
{
    FILE *handle;
    FILE *hier_handle;
    FILE *geom_handle;
    FILE *valpos_handle;
    FILE *curval_handle;
    FILE *tchn_handle;

    unsigned char *vchg_mem;

    fst_off_t hier_file_len;

    uint32_t *valpos_mem;
    unsigned char *curval_mem;

    unsigned char *outval_mem; /* for two-state / Verilator-style value changes */
    uint32_t outval_alloc_siz;

    char *filename;

    fstHandle maxhandle;
    fstHandle numsigs;
    uint32_t maxvalpos;

    unsigned vc_emitted : 1;
    unsigned is_initial_time : 1;
    unsigned fourpack : 1;
    unsigned fastpack : 1;

    int64_t timezero;
    fst_off_t section_header_truncpos;
    uint32_t tchn_cnt, tchn_idx;
    uint64_t curtime;
    uint64_t firsttime;
    uint32_t vchg_siz;
    uint32_t vchg_alloc_siz;

    uint32_t secnum;
    fst_off_t section_start;

    uint32_t numscopes;
    double nan; /* nan value for uninitialized doubles */

    struct fstBlackoutChain *blackout_head;
    struct fstBlackoutChain *blackout_curr;
    uint32_t num_blackouts;

    uint64_t dump_size_limit;

    unsigned char filetype; /* default is 0, FST_FT_VERILOG */

    unsigned compress_hier : 1;
    unsigned repack_on_close : 1;
    unsigned skip_writing_section_hdr : 1;
    unsigned size_limit_locked : 1;
    unsigned section_header_only : 1;
    unsigned flush_context_pending : 1;
    unsigned parallel_enabled : 1;
    unsigned parallel_was_enabled : 1;

    /* should really be semaphores, but are bytes to cut down on read-modify-write window size */
    unsigned char already_in_flush; /* in case control-c handlers interrupt */
    unsigned char already_in_close; /* in case control-c handlers interrupt */

#ifdef FST_WRITER_PARALLEL
    pthread_mutex_t mutex;
    pthread_t thread;
    pthread_attr_t thread_attr;
    struct fstWriterContext *xc_parent;
#endif
    unsigned in_pthread : 1;

    size_t fst_orig_break_size;
    size_t fst_orig_break_add_size;

    size_t fst_break_size;
    size_t fst_break_add_size;

    size_t fst_huge_break_size;

    fstHandle next_huge_break;

    Pvoid_t path_array;
    uint32_t path_array_count;

    unsigned fseek_failed : 1;

    char *geom_handle_nam;
    char *valpos_handle_nam;
    char *curval_handle_nam;
    char *tchn_handle_nam;

    fstEnumHandle max_enumhandle;
};

static int fstWriterFseeko(struct fstWriterContext *xc, FILE *stream, fst_off_t offset, int whence)
{
    int rc = fseeko(stream, offset, whence);

    if (rc < 0) {
        xc->fseek_failed = 1;
#ifdef FST_DEBUG
        fprintf(stderr, FST_APIMESS "Seek to #%" PRId64 " (whence = %d) failed!\n", offset, whence);
        perror("Why");
#endif
    }

    return (rc);
}

static uint32_t fstWriterUint32WithVarint32(struct fstWriterContext *xc, uint32_t *u, uint32_t v, const void *dbuf,
                                            uint32_t siz)
{
    unsigned char *buf = xc->vchg_mem + xc->vchg_siz;
    unsigned char *pnt = buf;
    uint32_t nxt;
    uint32_t len;

#ifdef FST_DO_MISALIGNED_OPS
    (*(uint32_t *)(pnt)) = (*(uint32_t *)(u));
#else
    memcpy(pnt, u, sizeof(uint32_t));
#endif
    pnt += 4;

    while ((nxt = v >> 7)) {
        *(pnt++) = ((unsigned char)v) | 0x80;
        v = nxt;
    }
    *(pnt++) = (unsigned char)v;
    memcpy(pnt, dbuf, siz);

    len = pnt - buf + siz;
    return (len);
}

static uint32_t fstWriterUint32WithVarint32AndLength(struct fstWriterContext *xc, uint32_t *u, uint32_t v,
                                                     const void *dbuf, uint32_t siz)
{
    unsigned char *buf = xc->vchg_mem + xc->vchg_siz;
    unsigned char *pnt = buf;
    uint32_t nxt;
    uint32_t len;

#ifdef FST_DO_MISALIGNED_OPS
    (*(uint32_t *)(pnt)) = (*(uint32_t *)(u));
#else
    memcpy(pnt, u, sizeof(uint32_t));
#endif
    pnt += 4;

    while ((nxt = v >> 7)) {
        *(pnt++) = ((unsigned char)v) | 0x80;
        v = nxt;
    }
    *(pnt++) = (unsigned char)v;

    v = siz;
    while ((nxt = v >> 7)) {
        *(pnt++) = ((unsigned char)v) | 0x80;
        v = nxt;
    }
    *(pnt++) = (unsigned char)v;

    memcpy(pnt, dbuf, siz);

    len = pnt - buf + siz;
    return (len);
}

/*
 * header bytes, write here so defines are set up before anything else
 * that needs to use them
 */
static void fstWriterEmitHdrBytes(struct fstWriterContext *xc)
{
    char vbuf[FST_HDR_SIM_VERSION_SIZE];
    char dbuf[FST_HDR_DATE_SIZE];
    double endtest = FST_DOUBLE_ENDTEST;
    time_t walltime;

#define FST_HDR_OFFS_TAG (0)
    fputc(FST_BL_HDR, xc->handle); /* +0 tag */

#define FST_HDR_OFFS_SECLEN (FST_HDR_OFFS_TAG + 1)
    fstWriterUint64(xc->handle, 329); /* +1 section length */

#define FST_HDR_OFFS_START_TIME (FST_HDR_OFFS_SECLEN + 8)
    fstWriterUint64(xc->handle, 0); /* +9 start time */

#define FST_HDR_OFFS_END_TIME (FST_HDR_OFFS_START_TIME + 8)
    fstWriterUint64(xc->handle, 0); /* +17 end time */

#define FST_HDR_OFFS_ENDIAN_TEST (FST_HDR_OFFS_END_TIME + 8)
    fstFwrite(&endtest, 8, 1, xc->handle); /* +25 endian test for reals */

#define FST_HDR_OFFS_MEM_USED (FST_HDR_OFFS_ENDIAN_TEST + 8)
    fstWriterUint64(xc->handle, xc->fst_break_size); /* +33 memory used by writer */

#define FST_HDR_OFFS_NUM_SCOPES (FST_HDR_OFFS_MEM_USED + 8)
    fstWriterUint64(xc->handle, 0); /* +41 scope creation count */

#define FST_HDR_OFFS_NUM_VARS (FST_HDR_OFFS_NUM_SCOPES + 8)
    fstWriterUint64(xc->handle, 0); /* +49 var creation count */

#define FST_HDR_OFFS_MAXHANDLE (FST_HDR_OFFS_NUM_VARS + 8)
    fstWriterUint64(xc->handle, 0); /* +57 max var idcode */

#define FST_HDR_OFFS_SECTION_CNT (FST_HDR_OFFS_MAXHANDLE + 8)
    fstWriterUint64(xc->handle, 0); /* +65 vc section count */

#define FST_HDR_OFFS_TIMESCALE (FST_HDR_OFFS_SECTION_CNT + 8)
    fputc((-9) & 255, xc->handle); /* +73 timescale 1ns */

#define FST_HDR_OFFS_SIM_VERSION (FST_HDR_OFFS_TIMESCALE + 1)
    memset(vbuf, 0, FST_HDR_SIM_VERSION_SIZE);
    strcpy(vbuf, FST_WRITER_STR);
    fstFwrite(vbuf, FST_HDR_SIM_VERSION_SIZE, 1, xc->handle); /* +74 version */

#define FST_HDR_OFFS_DATE (FST_HDR_OFFS_SIM_VERSION + FST_HDR_SIM_VERSION_SIZE)
    memset(dbuf, 0, FST_HDR_DATE_SIZE);
    time(&walltime);
    strcpy(dbuf, asctime(localtime(&walltime)));
    fstFwrite(dbuf, FST_HDR_DATE_SIZE, 1, xc->handle); /* +202 date */

    /* date size is deliberately overspecified at 119 bytes (originally 128) in order to provide backfill for new args
     */

#define FST_HDR_OFFS_FILETYPE (FST_HDR_OFFS_DATE + FST_HDR_DATE_SIZE)
    fputc(xc->filetype, xc->handle); /* +321 filetype */

#define FST_HDR_OFFS_TIMEZERO (FST_HDR_OFFS_FILETYPE + FST_HDR_FILETYPE_SIZE)
    fstWriterUint64(xc->handle, xc->timezero); /* +322 timezero */

#define FST_HDR_LENGTH (FST_HDR_OFFS_TIMEZERO + FST_HDR_TIMEZERO_SIZE)
    /* +330 next section starts here */
    fflush(xc->handle);
}

/*
 * mmap functions
 */
static void fstWriterMmapSanity(void *pnt, const char *file, int line, const char *usage)
{
#if !defined(__CYGWIN__) && !defined(__MINGW32__) && !defined(_MSC_VER)
    if (pnt == MAP_FAILED) {
        fprintf(stderr, "fstMmap() assigned to %s failed: errno: %d, file %s, line %d.\n", usage, errno, file, line);
        perror("Why");
        pnt = NULL;
    }
#endif
}

static void fstWriterCreateMmaps(struct fstWriterContext *xc)
{
    fst_off_t curpos = ftello(xc->handle);

    fflush(xc->hier_handle);

    /* write out intermediate header */
    fstWriterFseeko(xc, xc->handle, FST_HDR_OFFS_START_TIME, SEEK_SET);
    fstWriterUint64(xc->handle, xc->firsttime);
    fstWriterUint64(xc->handle, xc->curtime);
    fstWriterFseeko(xc, xc->handle, FST_HDR_OFFS_NUM_SCOPES, SEEK_SET);
    fstWriterUint64(xc->handle, xc->numscopes);
    fstWriterUint64(xc->handle, xc->numsigs);
    fstWriterUint64(xc->handle, xc->maxhandle);
    fstWriterUint64(xc->handle, xc->secnum);
    fstWriterFseeko(xc, xc->handle, curpos, SEEK_SET);
    fflush(xc->handle);

    /* do mappings */
    if (!xc->valpos_mem) {
        fflush(xc->valpos_handle);
        errno = 0;
        if (xc->maxhandle) {
            fstWriterMmapSanity(xc->valpos_mem = (uint32_t *)fstMmap(NULL, xc->maxhandle * 4 * sizeof(uint32_t),
                                                                     PROT_READ | PROT_WRITE, MAP_SHARED,
                                                                     fileno(xc->valpos_handle), 0),
                                __FILE__, __LINE__, "xc->valpos_mem");
        }
    }
    if (!xc->curval_mem) {
        fflush(xc->curval_handle);
        errno = 0;
        if (xc->maxvalpos) {
            fstWriterMmapSanity(xc->curval_mem = (unsigned char *)fstMmap(NULL, xc->maxvalpos, PROT_READ | PROT_WRITE,
                                                                          MAP_SHARED, fileno(xc->curval_handle), 0),
                                __FILE__, __LINE__, "xc->curval_handle");
        }
    }
}

static void fstDestroyMmaps(struct fstWriterContext *xc, int is_closing)
{
#if !defined __CYGWIN__ && !defined __MINGW32__
    (void)is_closing;
#endif

    fstMunmap(xc->valpos_mem, xc->maxhandle * 4 * sizeof(uint32_t));
    xc->valpos_mem = NULL;

#if defined __CYGWIN__ || defined __MINGW32__
    if (xc->curval_mem) {
        if (!is_closing) /* need to flush out for next emulated mmap() read */
        {
            unsigned char *pnt = xc->curval_mem;
            int __fd = fileno(xc->curval_handle);
            fst_off_t cur_offs = lseek(__fd, 0, SEEK_CUR);
            size_t i;
            size_t __len = xc->maxvalpos;

            lseek(__fd, 0, SEEK_SET);
            for (i = 0; i < __len; i += SSIZE_MAX) {
                write(__fd, pnt + i, ((__len - i) >= SSIZE_MAX) ? SSIZE_MAX : (__len - i));
            }
            lseek(__fd, cur_offs, SEEK_SET);
        }
    }
#endif

    fstMunmap(xc->curval_mem, xc->maxvalpos);
    xc->curval_mem = NULL;
}

/*
 * set up large and small memory usages
 * crossover point in model is FST_ACTIVATE_HUGE_BREAK number of signals
 */
static void fstDetermineBreakSize(struct fstWriterContext *xc)
{
#if defined(__linux__) || defined(FST_MACOSX)
    int was_set = 0;

#ifdef __linux__
    FILE *f = fopen("/proc/meminfo", "rb");

    if (f) {
        char buf[257];
        char *s;
        while (!feof(f)) {
            buf[0] = 0;
            s = fgets(buf, 256, f);
            if (s && *s) {
                if (!strncmp(s, "MemTotal:", 9)) {
                    size_t v = atol(s + 10);
                    v *= 1024; /* convert to bytes */
                    v /= 8;    /* chop down to 1/8 physical memory */
                    if (v > FST_BREAK_SIZE) {
                        if (v > FST_BREAK_SIZE_MAX) {
                            v = FST_BREAK_SIZE_MAX;
                        }

                        xc->fst_huge_break_size = v;
                        was_set = 1;
                        break;
                    }
                }
            }
        }

        fclose(f);
    }

    if (!was_set) {
        xc->fst_huge_break_size = FST_BREAK_SIZE;
    }
#else
    int mib[2];
    int64_t v;
    size_t length;

    mib[0] = CTL_HW;
    mib[1] = HW_MEMSIZE;
    length = sizeof(int64_t);
    if (!sysctl(mib, 2, &v, &length, NULL, 0)) {
        v /= 8;

        if (v > (int64_t)FST_BREAK_SIZE) {
            if (v > (int64_t)FST_BREAK_SIZE_MAX) {
                v = FST_BREAK_SIZE_MAX;
            }

            xc->fst_huge_break_size = v;
            was_set = 1;
        }
    }

    if (!was_set) {
        xc->fst_huge_break_size = FST_BREAK_SIZE;
    }
#endif
#else
    xc->fst_huge_break_size = FST_BREAK_SIZE;
#endif

    xc->fst_break_size = xc->fst_orig_break_size = FST_BREAK_SIZE;
    xc->fst_break_add_size = xc->fst_orig_break_add_size = FST_BREAK_ADD_SIZE;
    xc->next_huge_break = FST_ACTIVATE_HUGE_BREAK;
}

/*
 * file creation and close
 */
void *fstWriterCreate(const char *nam, int use_compressed_hier)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)calloc(1, sizeof(struct fstWriterContext));

    xc->compress_hier = use_compressed_hier;
    fstDetermineBreakSize(xc);

    if ((!nam) || (!(xc->handle = unlink_fopen(nam, "w+b")))) {
        free(xc);
        xc = NULL;
    } else {
        int flen = strlen(nam);
        char *hf = (char *)calloc(1, flen + 6);

        memcpy(hf, nam, flen);
        strcpy(hf + flen, ".hier");
        xc->hier_handle = unlink_fopen(hf, "w+b");

        xc->geom_handle = tmpfile_open(&xc->geom_handle_nam);     /* .geom */
        xc->valpos_handle = tmpfile_open(&xc->valpos_handle_nam); /* .offs */
        xc->curval_handle = tmpfile_open(&xc->curval_handle_nam); /* .bits */
        xc->tchn_handle = tmpfile_open(&xc->tchn_handle_nam);     /* .tchn */
        xc->vchg_alloc_siz = xc->fst_break_size + xc->fst_break_add_size;
        xc->vchg_mem = (unsigned char *)malloc(xc->vchg_alloc_siz);

        if (xc->hier_handle && xc->geom_handle && xc->valpos_handle && xc->curval_handle && xc->vchg_mem &&
            xc->tchn_handle) {
            xc->filename = strdup(nam);
            xc->is_initial_time = 1;

            fstWriterEmitHdrBytes(xc);
            xc->nan = strtod("NaN", NULL);
#ifdef FST_WRITER_PARALLEL
            pthread_mutex_init(&xc->mutex, NULL);
            pthread_attr_init(&xc->thread_attr);
            pthread_attr_setdetachstate(&xc->thread_attr, PTHREAD_CREATE_DETACHED);
#endif
        } else {
            fclose(xc->handle);
            if (xc->hier_handle) {
                fclose(xc->hier_handle);
                unlink(hf);
            }
            tmpfile_close(&xc->geom_handle, &xc->geom_handle_nam);
            tmpfile_close(&xc->valpos_handle, &xc->valpos_handle_nam);
            tmpfile_close(&xc->curval_handle, &xc->curval_handle_nam);
            tmpfile_close(&xc->tchn_handle, &xc->tchn_handle_nam);
            free(xc->vchg_mem);
            free(xc);
            xc = NULL;
        }

        free(hf);
    }

    return (xc);
}

/*
 * generation and writing out of value change data sections
 */
static void fstWriterEmitSectionHeader(void *ctx)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

    if (xc) {
        unsigned long destlen;
        unsigned char *dmem;
        int rc;

        destlen = xc->maxvalpos;
        dmem = (unsigned char *)malloc(compressBound(destlen));
        rc = compress2(dmem, &destlen, xc->curval_mem, xc->maxvalpos,
                       4); /* was 9...which caused performance drag on traces with many signals */

        fputc(FST_BL_SKIP, xc->handle); /* temporarily tag the section, use FST_BL_VCDATA on finalize */
        xc->section_start = ftello(xc->handle);
#ifdef FST_WRITER_PARALLEL
        if (xc->xc_parent)
            xc->xc_parent->section_start = xc->section_start;
#endif
        xc->section_header_only = 1;    /* indicates truncate might be needed */
        fstWriterUint64(xc->handle, 0); /* placeholder = section length */
        fstWriterUint64(xc->handle, xc->is_initial_time ? xc->firsttime : xc->curtime); /* begin time of section */
        fstWriterUint64(xc->handle, xc->curtime); /* end time of section (placeholder) */
        fstWriterUint64(xc->handle,
                        0); /* placeholder = amount of buffer memory required in reader for full vc traversal */
        fstWriterVarint(xc->handle, xc->maxvalpos); /* maxvalpos = length of uncompressed data */

        if ((rc == Z_OK) && (destlen < xc->maxvalpos)) {
            fstWriterVarint(xc->handle, destlen); /* length of compressed data */
        } else {
            fstWriterVarint(xc->handle, xc->maxvalpos); /* length of (unable to be) compressed data */
        }
        fstWriterVarint(xc->handle,
                        xc->maxhandle); /* max handle associated with this data (in case of dynamic facility adds) */

        if ((rc == Z_OK) && (destlen < xc->maxvalpos)) {
            fstFwrite(dmem, destlen, 1, xc->handle);
        } else /* comparison between compressed / decompressed len tells if compressed */
        {
            fstFwrite(xc->curval_mem, xc->maxvalpos, 1, xc->handle);
        }

        free(dmem);
    }
}

/*
 * only to be called directly by fst code...otherwise must
 * be synced up with time changes
 */
#ifdef FST_WRITER_PARALLEL
static void fstWriterFlushContextPrivate2(void *ctx)
#else
static void fstWriterFlushContextPrivate(void *ctx)
#endif
{
#ifdef FST_DEBUG
    int cnt = 0;
#endif
    unsigned int i;
    unsigned char *vchg_mem;
    FILE *f;
    fst_off_t fpos, indxpos, endpos;
    uint32_t prevpos;
    int zerocnt;
    unsigned char *scratchpad;
    unsigned char *scratchpnt;
    unsigned char *tmem;
    fst_off_t tlen;
    fst_off_t unc_memreq = 0; /* for reader */
    unsigned char *packmem;
    unsigned int packmemlen;
    uint32_t *vm4ip;
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
#ifdef FST_WRITER_PARALLEL
    struct fstWriterContext *xc2 = xc->xc_parent;
#else
    struct fstWriterContext *xc2 = xc;
#endif

#ifndef FST_DYNAMIC_ALIAS_DISABLE
    Pvoid_t PJHSArray = (Pvoid_t)NULL;
#ifndef _WAVE_HAVE_JUDY
    uint32_t hashmask = xc->maxhandle;
    hashmask |= hashmask >> 1;
    hashmask |= hashmask >> 2;
    hashmask |= hashmask >> 4;
    hashmask |= hashmask >> 8;
    hashmask |= hashmask >> 16;
#endif
#endif

    if ((xc->vchg_siz <= 1) || (xc->already_in_flush))
        return;
    xc->already_in_flush = 1; /* should really do this with a semaphore */

    xc->section_header_only = 0;
    scratchpad = (unsigned char *)malloc(xc->vchg_siz);

    vchg_mem = xc->vchg_mem;

    f = xc->handle;
    fstWriterVarint(f, xc->maxhandle); /* emit current number of handles */
    fputc(xc->fourpack ? '4' : (xc->fastpack ? 'F' : 'Z'), f);
    fpos = 1;

    packmemlen = 1024;                             /* maintain a running "longest" allocation to */
    packmem = (unsigned char *)malloc(packmemlen); /* prevent continual malloc...free every loop iter */

    for (i = 0; i < xc->maxhandle; i++) {
        vm4ip = &(xc->valpos_mem[4 * i]);

        if (vm4ip[2]) {
            uint32_t offs = vm4ip[2];
            uint32_t next_offs;
            unsigned int wrlen;

            vm4ip[2] = fpos;

            scratchpnt = scratchpad + xc->vchg_siz; /* build this buffer backwards */
            if (vm4ip[1] <= 1) {
                if (vm4ip[1] == 1) {
                    wrlen = fstGetVarint32Length(vchg_mem + offs + 4); /* used to advance and determine wrlen */
#ifndef FST_REMOVE_DUPLICATE_VC
                    xc->curval_mem[vm4ip[0]] = vchg_mem[offs + 4 + wrlen]; /* checkpoint variable */
#endif
                    while (offs) {
                        unsigned char val;
                        uint32_t time_delta, rcv;
                        next_offs = fstGetUint32(vchg_mem + offs);
                        offs += 4;

                        time_delta = fstGetVarint32(vchg_mem + offs, (int *)&wrlen);
                        val = vchg_mem[offs + wrlen];
                        offs = next_offs;

                        switch (val) {
                        case '0':
                        case '1':
                            rcv = ((val & 1) << 1) | (time_delta << 2);
                            break; /* pack more delta bits in for 0/1 vchs */

                        case 'x':
                        case 'X':
                            rcv = FST_RCV_X | (time_delta << 4);
                            break;
                        case 'z':
                        case 'Z':
                            rcv = FST_RCV_Z | (time_delta << 4);
                            break;
                        case 'h':
                        case 'H':
                            rcv = FST_RCV_H | (time_delta << 4);
                            break;
                        case 'u':
                        case 'U':
                            rcv = FST_RCV_U | (time_delta << 4);
                            break;
                        case 'w':
                        case 'W':
                            rcv = FST_RCV_W | (time_delta << 4);
                            break;
                        case 'l':
                        case 'L':
                            rcv = FST_RCV_L | (time_delta << 4);
                            break;
                        default:
                            rcv = FST_RCV_D | (time_delta << 4);
                            break;
                        }

                        scratchpnt = fstCopyVarint32ToLeft(scratchpnt, rcv);
                    }
                } else {
                    /* variable length */
                    /* fstGetUint32 (next_offs) + fstGetVarint32 (time_delta) + fstGetVarint32 (len) + payload */
                    unsigned char *pnt;
                    uint32_t record_len;
                    uint32_t time_delta;

                    while (offs) {
                        next_offs = fstGetUint32(vchg_mem + offs);
                        offs += 4;
                        pnt = vchg_mem + offs;
                        offs = next_offs;
                        time_delta = fstGetVarint32(pnt, (int *)&wrlen);
                        pnt += wrlen;
                        record_len = fstGetVarint32(pnt, (int *)&wrlen);
                        pnt += wrlen;

                        scratchpnt -= record_len;
                        memcpy(scratchpnt, pnt, record_len);

                        scratchpnt = fstCopyVarint32ToLeft(scratchpnt, record_len);
                        scratchpnt = fstCopyVarint32ToLeft(
                                scratchpnt, (time_delta << 1)); /* reserve | 1 case for future expansion */
                    }
                }
            } else {
                wrlen = fstGetVarint32Length(vchg_mem + offs + 4); /* used to advance and determine wrlen */
#ifndef FST_REMOVE_DUPLICATE_VC
                memcpy(xc->curval_mem + vm4ip[0], vchg_mem + offs + 4 + wrlen, vm4ip[1]); /* checkpoint variable */
#endif
                while (offs) {
                    unsigned int idx;
                    char is_binary = 1;
                    unsigned char *pnt;
                    uint32_t time_delta;

                    next_offs = fstGetUint32(vchg_mem + offs);
                    offs += 4;

                    time_delta = fstGetVarint32(vchg_mem + offs, (int *)&wrlen);

                    pnt = vchg_mem + offs + wrlen;
                    offs = next_offs;

                    for (idx = 0; idx < vm4ip[1]; idx++) {
                        if ((pnt[idx] == '0') || (pnt[idx] == '1')) {
                            continue;
                        } else {
                            is_binary = 0;
                            break;
                        }
                    }

                    if (is_binary) {
                        unsigned char acc = 0;
                        /* new algorithm */
                        idx = ((vm4ip[1] + 7) & ~7);
                        switch (vm4ip[1] & 7) {
                        case 0:
                            do {
                                acc = (pnt[idx + 7 - 8] & 1) << 0; /* fallthrough */
                            case 7:
                                acc |= (pnt[idx + 6 - 8] & 1) << 1; /* fallthrough */
                            case 6:
                                acc |= (pnt[idx + 5 - 8] & 1) << 2; /* fallthrough */
                            case 5:
                                acc |= (pnt[idx + 4 - 8] & 1) << 3; /* fallthrough */
                            case 4:
                                acc |= (pnt[idx + 3 - 8] & 1) << 4; /* fallthrough */
                            case 3:
                                acc |= (pnt[idx + 2 - 8] & 1) << 5; /* fallthrough */
                            case 2:
                                acc |= (pnt[idx + 1 - 8] & 1) << 6; /* fallthrough */
                            case 1:
                                acc |= (pnt[idx + 0 - 8] & 1) << 7;
                                *(--scratchpnt) = acc;
                                idx -= 8;
                            } while (idx);
                        }

                        scratchpnt = fstCopyVarint32ToLeft(scratchpnt, (time_delta << 1));
                    } else {
                        scratchpnt -= vm4ip[1];
                        memcpy(scratchpnt, pnt, vm4ip[1]);

                        scratchpnt = fstCopyVarint32ToLeft(scratchpnt, (time_delta << 1) | 1);
                    }
                }
            }

            wrlen = scratchpad + xc->vchg_siz - scratchpnt;
            unc_memreq += wrlen;
            if (wrlen > 32) {
                unsigned long destlen = wrlen;
                unsigned char *dmem;
                unsigned int rc;

                if (!xc->fastpack) {
                    if (wrlen <= packmemlen) {
                        dmem = packmem;
                    } else {
                        free(packmem);
                        dmem = packmem = (unsigned char *)malloc(compressBound(packmemlen = wrlen));
                    }

                    rc = compress2(dmem, &destlen, scratchpnt, wrlen, 4);
                    if (rc == Z_OK) {
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                        PPvoid_t pv = JudyHSIns(&PJHSArray, dmem, destlen, NULL);
                        if (*pv) {
                            uint32_t pvi = (intptr_t)(*pv);
                            vm4ip[2] = -pvi;
                        } else {
                            *pv = (void *)(intptr_t)(i + 1);
#endif
                            fpos += fstWriterVarint(f, wrlen);
                            fpos += destlen;
                            fstFwrite(dmem, destlen, 1, f);
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                        }
#endif
                    } else {
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                        PPvoid_t pv = JudyHSIns(&PJHSArray, scratchpnt, wrlen, NULL);
                        if (*pv) {
                            uint32_t pvi = (intptr_t)(*pv);
                            vm4ip[2] = -pvi;
                        } else {
                            *pv = (void *)(intptr_t)(i + 1);
#endif
                            fpos += fstWriterVarint(f, 0);
                            fpos += wrlen;
                            fstFwrite(scratchpnt, wrlen, 1, f);
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                        }
#endif
                    }
                } else {
                    /* this is extremely conservative: fastlz needs +5% for worst case, lz4 needs siz+(siz/255)+16 */
                    if (((wrlen * 2) + 2) <= packmemlen) {
                        dmem = packmem;
                    } else {
                        free(packmem);
                        dmem = packmem = (unsigned char *)malloc(packmemlen = (wrlen * 2) + 2);
                    }

                    rc = (xc->fourpack) ? LZ4_compress((char *)scratchpnt, (char *)dmem, wrlen)
                                        : fastlz_compress(scratchpnt, wrlen, dmem);
                    if (rc < destlen) {
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                        PPvoid_t pv = JudyHSIns(&PJHSArray, dmem, rc, NULL);
                        if (*pv) {
                            uint32_t pvi = (intptr_t)(*pv);
                            vm4ip[2] = -pvi;
                        } else {
                            *pv = (void *)(intptr_t)(i + 1);
#endif
                            fpos += fstWriterVarint(f, wrlen);
                            fpos += rc;
                            fstFwrite(dmem, rc, 1, f);
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                        }
#endif
                    } else {
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                        PPvoid_t pv = JudyHSIns(&PJHSArray, scratchpnt, wrlen, NULL);
                        if (*pv) {
                            uint32_t pvi = (intptr_t)(*pv);
                            vm4ip[2] = -pvi;
                        } else {
                            *pv = (void *)(intptr_t)(i + 1);
#endif
                            fpos += fstWriterVarint(f, 0);
                            fpos += wrlen;
                            fstFwrite(scratchpnt, wrlen, 1, f);
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                        }
#endif
                    }
                }
            } else {
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                PPvoid_t pv = JudyHSIns(&PJHSArray, scratchpnt, wrlen, NULL);
                if (*pv) {
                    uint32_t pvi = (intptr_t)(*pv);
                    vm4ip[2] = -pvi;
                } else {
                    *pv = (void *)(intptr_t)(i + 1);
#endif
                    fpos += fstWriterVarint(f, 0);
                    fpos += wrlen;
                    fstFwrite(scratchpnt, wrlen, 1, f);
#ifndef FST_DYNAMIC_ALIAS_DISABLE
                }
#endif
            }

            /* vm4ip[3] = 0; ...redundant with clearing below */
#ifdef FST_DEBUG
            cnt++;
#endif
        }
    }

#ifndef FST_DYNAMIC_ALIAS_DISABLE
    JudyHSFreeArray(&PJHSArray, NULL);
#endif

    free(packmem);
    packmem = NULL; /* packmemlen = 0; */ /* scan-build */

    prevpos = 0;
    zerocnt = 0;
    free(scratchpad);
    scratchpad = NULL;

    indxpos = ftello(f);
    xc->secnum++;

#ifndef FST_DYNAMIC_ALIAS2_DISABLE
    if (1) {
        uint32_t prev_alias = 0;

        for (i = 0; i < xc->maxhandle; i++) {
            vm4ip = &(xc->valpos_mem[4 * i]);

            if (vm4ip[2]) {
                if (zerocnt) {
                    fpos += fstWriterVarint(f, (zerocnt << 1));
                    zerocnt = 0;
                }

                if (vm4ip[2] & 0x80000000) {
                    if (vm4ip[2] != prev_alias) {
                        fpos += fstWriterSVarint(f, (((int64_t)((int32_t)(prev_alias = vm4ip[2]))) << 1) | 1);
                    } else {
                        fpos += fstWriterSVarint(f, (0 << 1) | 1);
                    }
                } else {
                    fpos += fstWriterSVarint(f, ((vm4ip[2] - prevpos) << 1) | 1);
                    prevpos = vm4ip[2];
                }
                vm4ip[2] = 0;
                vm4ip[3] = 0; /* clear out tchn idx */
            } else {
                zerocnt++;
            }
        }
    } else
#endif
    {
        for (i = 0; i < xc->maxhandle; i++) {
            vm4ip = &(xc->valpos_mem[4 * i]);

            if (vm4ip[2]) {
                if (zerocnt) {
                    fpos += fstWriterVarint(f, (zerocnt << 1));
                    zerocnt = 0;
                }

                if (vm4ip[2] & 0x80000000) {
                    fpos += fstWriterVarint(f, 0); /* signal, note that using a *signed* varint would be more efficient
                                                      than this byte escape! */
                    fpos += fstWriterVarint(f, (-(int32_t)vm4ip[2]));
                } else {
                    fpos += fstWriterVarint(f, ((vm4ip[2] - prevpos) << 1) | 1);
                    prevpos = vm4ip[2];
                }
                vm4ip[2] = 0;
                vm4ip[3] = 0; /* clear out tchn idx */
            } else {
                zerocnt++;
            }
        }
    }

    if (zerocnt) {
        /* fpos += */ fstWriterVarint(f, (zerocnt << 1)); /* scan-build */
    }
#ifdef FST_DEBUG
    fprintf(stderr, FST_APIMESS "value chains: %d\n", cnt);
#endif

    xc->vchg_mem[0] = '!';
    xc->vchg_siz = 1;

    endpos = ftello(xc->handle);
    fstWriterUint64(xc->handle, endpos - indxpos); /* write delta index position at very end of block */

    /*emit time changes for block */
    fflush(xc->tchn_handle);
    tlen = ftello(xc->tchn_handle);
    fstWriterFseeko(xc, xc->tchn_handle, 0, SEEK_SET);

    errno = 0;
    fstWriterMmapSanity(
            tmem = (unsigned char *)fstMmap(NULL, tlen, PROT_READ | PROT_WRITE, MAP_SHARED, fileno(xc->tchn_handle), 0),
            __FILE__, __LINE__, "tmem");
    if (tmem) {
        unsigned long destlen = tlen;
        unsigned char *dmem = (unsigned char *)malloc(compressBound(destlen));
        int rc = compress2(dmem, &destlen, tmem, tlen, 9);

        if ((rc == Z_OK) && (((fst_off_t)destlen) < tlen)) {
            fstFwrite(dmem, destlen, 1, xc->handle);
        } else /* comparison between compressed / decompressed len tells if compressed */
        {
            fstFwrite(tmem, tlen, 1, xc->handle);
            destlen = tlen;
        }
        free(dmem);
        fstMunmap(tmem, tlen);
        fstWriterUint64(xc->handle, tlen);         /* uncompressed */
        fstWriterUint64(xc->handle, destlen);      /* compressed */
        fstWriterUint64(xc->handle, xc->tchn_cnt); /* number of time items */
    }

    xc->tchn_cnt = xc->tchn_idx = 0;
    fstWriterFseeko(xc, xc->tchn_handle, 0, SEEK_SET);
    fstFtruncate(fileno(xc->tchn_handle), 0);

    /* write block trailer */
    endpos = ftello(xc->handle);
    fstWriterFseeko(xc, xc->handle, xc->section_start, SEEK_SET);
    fstWriterUint64(xc->handle, endpos - xc->section_start); /* write block length */
    fstWriterFseeko(xc, xc->handle, 8, SEEK_CUR);            /* skip begin time */
    fstWriterUint64(xc->handle, xc->curtime);                /* write end time for section */
    fstWriterUint64(xc->handle, unc_memreq); /* amount of buffer memory required in reader for full traversal */
    fflush(xc->handle);

    fstWriterFseeko(xc, xc->handle, xc->section_start - 1, SEEK_SET); /* write out FST_BL_VCDATA over FST_BL_SKIP */

#ifndef FST_DYNAMIC_ALIAS_DISABLE
#ifndef FST_DYNAMIC_ALIAS2_DISABLE
    fputc(FST_BL_VCDATA_DYN_ALIAS2, xc->handle);
#else
    fputc(FST_BL_VCDATA_DYN_ALIAS, xc->handle);
#endif
#else
    fputc(FST_BL_VCDATA, xc->handle);
#endif

    fflush(xc->handle);

    fstWriterFseeko(xc, xc->handle, endpos, SEEK_SET); /* seek to end of file */

    xc2->section_header_truncpos = endpos; /* cache in case of need to truncate */
    if (xc->dump_size_limit) {
        if (endpos >= ((fst_off_t)xc->dump_size_limit)) {
            xc2->skip_writing_section_hdr = 1;
            xc2->size_limit_locked = 1;
            xc2->is_initial_time = 1; /* to trick emit value and emit time change */
#ifdef FST_DEBUG
            fprintf(stderr, FST_APIMESS "<< dump file size limit reached, stopping dumping >>\n");
#endif
        }
    }

    if (!xc2->skip_writing_section_hdr) {
        fstWriterEmitSectionHeader(xc); /* emit next section header */
    }
    fflush(xc->handle);

    xc->already_in_flush = 0;
}

#ifdef FST_WRITER_PARALLEL
static void *fstWriterFlushContextPrivate1(void *ctx)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    struct fstWriterContext *xc_parent;

    pthread_mutex_lock(&(xc->xc_parent->mutex));
    fstWriterFlushContextPrivate2(xc);

#ifdef FST_REMOVE_DUPLICATE_VC
    free(xc->curval_mem);
#endif
    free(xc->valpos_mem);
    free(xc->vchg_mem);
    tmpfile_close(&xc->tchn_handle, &xc->tchn_handle_nam);
    xc_parent = xc->xc_parent;
    free(xc);

    xc_parent->in_pthread = 0;
    pthread_mutex_unlock(&(xc_parent->mutex));

    return (NULL);
}

static void fstWriterFlushContextPrivate(void *ctx)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

    if (xc->parallel_enabled) {
        struct fstWriterContext *xc2 = (struct fstWriterContext *)malloc(sizeof(struct fstWriterContext));
        unsigned int i;

        pthread_mutex_lock(&xc->mutex);
        pthread_mutex_unlock(&xc->mutex);

        xc->xc_parent = xc;
        memcpy(xc2, xc, sizeof(struct fstWriterContext));

        xc2->valpos_mem = (uint32_t *)malloc(xc->maxhandle * 4 * sizeof(uint32_t));
        memcpy(xc2->valpos_mem, xc->valpos_mem, xc->maxhandle * 4 * sizeof(uint32_t));

        /* curval mem is updated in the thread */
#ifdef FST_REMOVE_DUPLICATE_VC
        xc2->curval_mem = (unsigned char *)malloc(xc->maxvalpos);
        memcpy(xc2->curval_mem, xc->curval_mem, xc->maxvalpos);
#endif

        xc->vchg_mem = (unsigned char *)malloc(xc->vchg_alloc_siz);
        xc->vchg_mem[0] = '!';
        xc->vchg_siz = 1;

        for (i = 0; i < xc->maxhandle; i++) {
            uint32_t *vm4ip = &(xc->valpos_mem[4 * i]);
            vm4ip[2] = 0; /* zero out offset val */
            vm4ip[3] = 0; /* zero out last time change val */
        }

        xc->tchn_cnt = xc->tchn_idx = 0;
        xc->tchn_handle = tmpfile_open(&xc->tchn_handle_nam); /* child thread will deallocate file/name */
        fstWriterFseeko(xc, xc->tchn_handle, 0, SEEK_SET);
        fstFtruncate(fileno(xc->tchn_handle), 0);

        xc->section_header_only = 0;
        xc->secnum++;

        while (xc->in_pthread) {
            pthread_mutex_lock(&xc->mutex);
            pthread_mutex_unlock(&xc->mutex);
        };

        pthread_mutex_lock(&xc->mutex);
        xc->in_pthread = 1;
        pthread_mutex_unlock(&xc->mutex);

        pthread_create(&xc->thread, &xc->thread_attr, fstWriterFlushContextPrivate1, xc2);
    } else {
        if (xc->parallel_was_enabled) /* conservatively block */
        {
            pthread_mutex_lock(&xc->mutex);
            pthread_mutex_unlock(&xc->mutex);
        }

        xc->xc_parent = xc;
        fstWriterFlushContextPrivate2(xc);
    }
}
#endif

/*
 * queues up a flush context operation
 */
void fstWriterFlushContext(void *ctx)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        if (xc->tchn_idx > 1) {
            xc->flush_context_pending = 1;
        }
    }
}

/*
 * close out FST file
 */
void fstWriterClose(void *ctx)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

#ifdef FST_WRITER_PARALLEL
    if (xc) {
        pthread_mutex_lock(&xc->mutex);
        pthread_mutex_unlock(&xc->mutex);
    }
#endif

    if (xc && !xc->already_in_close && !xc->already_in_flush) {
        unsigned char *tmem = NULL;
        fst_off_t fixup_offs, tlen, hlen;

        xc->already_in_close = 1; /* never need to zero this out as it is freed at bottom */

        if (xc->section_header_only && xc->section_header_truncpos && (xc->vchg_siz <= 1) && (!xc->is_initial_time)) {
            fstFtruncate(fileno(xc->handle), xc->section_header_truncpos);
            fstWriterFseeko(xc, xc->handle, xc->section_header_truncpos, SEEK_SET);
            xc->section_header_only = 0;
        } else {
            xc->skip_writing_section_hdr = 1;
            if (!xc->size_limit_locked) {
                if (FST_UNLIKELY(xc->is_initial_time)) /* simulation time never advanced so mock up the changes as time
                                                          zero ones */
                {
                    fstHandle dupe_idx;

                    fstWriterEmitTimeChange(xc, 0); /* emit some time change just to have one */
                    for (dupe_idx = 0; dupe_idx < xc->maxhandle; dupe_idx++) /* now clone the values */
                    {
                        fstWriterEmitValueChange(xc, dupe_idx + 1, xc->curval_mem + xc->valpos_mem[4 * dupe_idx]);
                    }
                }
                fstWriterFlushContextPrivate(xc);
#ifdef FST_WRITER_PARALLEL
                pthread_mutex_lock(&xc->mutex);
                pthread_mutex_unlock(&xc->mutex);

                while (xc->in_pthread) {
                    pthread_mutex_lock(&xc->mutex);
                    pthread_mutex_unlock(&xc->mutex);
                };
#endif
            }
        }
        fstDestroyMmaps(xc, 1);
        if (xc->outval_mem) {
            free(xc->outval_mem);
            xc->outval_mem = NULL;
            xc->outval_alloc_siz = 0;
        }

        /* write out geom section */
        fflush(xc->geom_handle);
        tlen = ftello(xc->geom_handle);
        errno = 0;
        if (tlen) {
            fstWriterMmapSanity(tmem = (unsigned char *)fstMmap(NULL, tlen, PROT_READ | PROT_WRITE, MAP_SHARED,
                                                                fileno(xc->geom_handle), 0),
                                __FILE__, __LINE__, "tmem");
        }

        if (tmem) {
            unsigned long destlen = tlen;
            unsigned char *dmem = (unsigned char *)malloc(compressBound(destlen));
            int rc = compress2(dmem, &destlen, tmem, tlen, 9);

            if ((rc != Z_OK) || (((fst_off_t)destlen) > tlen)) {
                destlen = tlen;
            }

            fixup_offs = ftello(xc->handle);
            fputc(FST_BL_SKIP, xc->handle);             /* temporary tag */
            fstWriterUint64(xc->handle, destlen + 24);  /* section length */
            fstWriterUint64(xc->handle, tlen);          /* uncompressed */
                                                        /* compressed len is section length - 24 */
            fstWriterUint64(xc->handle, xc->maxhandle); /* maxhandle */
            fstFwrite((((fst_off_t)destlen) != tlen) ? dmem : tmem, destlen, 1, xc->handle);
            fflush(xc->handle);

            fstWriterFseeko(xc, xc->handle, fixup_offs, SEEK_SET);
            fputc(FST_BL_GEOM, xc->handle); /* actual tag */

            fstWriterFseeko(xc, xc->handle, 0, SEEK_END); /* move file pointer to end for any section adds */
            fflush(xc->handle);

            free(dmem);
            fstMunmap(tmem, tlen);
        }

        if (xc->num_blackouts) {
            uint64_t cur_bl = 0;
            fst_off_t bpos, eos;
            uint32_t i;

            fixup_offs = ftello(xc->handle);
            fputc(FST_BL_SKIP, xc->handle); /* temporary tag */
            bpos = fixup_offs + 1;
            fstWriterUint64(xc->handle, 0); /* section length */
            fstWriterVarint(xc->handle, xc->num_blackouts);

            for (i = 0; i < xc->num_blackouts; i++) {
                fputc(xc->blackout_head->active, xc->handle);
                fstWriterVarint(xc->handle, xc->blackout_head->tim - cur_bl);
                cur_bl = xc->blackout_head->tim;
                xc->blackout_curr = xc->blackout_head->next;
                free(xc->blackout_head);
                xc->blackout_head = xc->blackout_curr;
            }

            eos = ftello(xc->handle);
            fstWriterFseeko(xc, xc->handle, bpos, SEEK_SET);
            fstWriterUint64(xc->handle, eos - bpos);
            fflush(xc->handle);

            fstWriterFseeko(xc, xc->handle, fixup_offs, SEEK_SET);
            fputc(FST_BL_BLACKOUT, xc->handle); /* actual tag */

            fstWriterFseeko(xc, xc->handle, 0, SEEK_END); /* move file pointer to end for any section adds */
            fflush(xc->handle);
        }

        if (xc->compress_hier) {
            fst_off_t hl, eos;
            gzFile zhandle;
            int zfd;
            int fourpack_duo = 0;
#ifndef __MINGW32__
            char *fnam = (char *)malloc(strlen(xc->filename) + 5 + 1);
#endif

            fixup_offs = ftello(xc->handle);
            fputc(FST_BL_SKIP, xc->handle); /* temporary tag */
            hlen = ftello(xc->handle);
            fstWriterUint64(xc->handle, 0);                 /* section length */
            fstWriterUint64(xc->handle, xc->hier_file_len); /* uncompressed length */

            if (!xc->fourpack) {
                unsigned char *mem = (unsigned char *)malloc(FST_GZIO_LEN);
                zfd = dup(fileno(xc->handle));
                fflush(xc->handle);
                zhandle = gzdopen(zfd, "wb4");
                if (zhandle) {
                    fstWriterFseeko(xc, xc->hier_handle, 0, SEEK_SET);
                    for (hl = 0; hl < xc->hier_file_len; hl += FST_GZIO_LEN) {
                        unsigned len =
                                ((xc->hier_file_len - hl) > FST_GZIO_LEN) ? FST_GZIO_LEN : (xc->hier_file_len - hl);
                        fstFread(mem, len, 1, xc->hier_handle);
                        gzwrite(zhandle, mem, len);
                    }
                    gzclose(zhandle);
                } else {
                    close(zfd);
                }
                free(mem);
            } else {
                int lz4_maxlen;
                unsigned char *mem;
                unsigned char *hmem = NULL;
                int packed_len;

                fflush(xc->handle);

                lz4_maxlen = LZ4_compressBound(xc->hier_file_len);
                mem = (unsigned char *)malloc(lz4_maxlen);
                errno = 0;
                if (xc->hier_file_len) {
                    fstWriterMmapSanity(hmem = (unsigned char *)fstMmap(NULL, xc->hier_file_len, PROT_READ | PROT_WRITE,
                                                                        MAP_SHARED, fileno(xc->hier_handle), 0),
                                        __FILE__, __LINE__, "hmem");
                }
                packed_len = LZ4_compress((char *)hmem, (char *)mem, xc->hier_file_len);
                fstMunmap(hmem, xc->hier_file_len);

                fourpack_duo =
                        (!xc->repack_on_close) &&
                        (xc->hier_file_len > FST_HDR_FOURPACK_DUO_SIZE); /* double pack when hierarchy is large */

                if (fourpack_duo) /* double packing with LZ4 is faster than gzip */
                {
                    unsigned char *mem_duo;
                    int lz4_maxlen_duo;
                    int packed_len_duo;

                    lz4_maxlen_duo = LZ4_compressBound(packed_len);
                    mem_duo = (unsigned char *)malloc(lz4_maxlen_duo);
                    packed_len_duo = LZ4_compress((char *)mem, (char *)mem_duo, packed_len);

                    fstWriterVarint(xc->handle, packed_len); /* 1st round compressed length */
                    fstFwrite(mem_duo, packed_len_duo, 1, xc->handle);
                    free(mem_duo);
                } else {
                    fstFwrite(mem, packed_len, 1, xc->handle);
                }

                free(mem);
            }

            fstWriterFseeko(xc, xc->handle, 0, SEEK_END);
            eos = ftello(xc->handle);
            fstWriterFseeko(xc, xc->handle, hlen, SEEK_SET);
            fstWriterUint64(xc->handle, eos - hlen);
            fflush(xc->handle);

            fstWriterFseeko(xc, xc->handle, fixup_offs, SEEK_SET);
            fputc(xc->fourpack ? (fourpack_duo ? FST_BL_HIER_LZ4DUO : FST_BL_HIER_LZ4) : FST_BL_HIER,
                  xc->handle); /* actual tag now also == compression type */

            fstWriterFseeko(xc, xc->handle, 0, SEEK_END); /* move file pointer to end for any section adds */
            fflush(xc->handle);

#ifndef __MINGW32__
            sprintf(fnam, "%s.hier", xc->filename);
            unlink(fnam);
            free(fnam);
#endif
        }

        /* finalize out header */
        fstWriterFseeko(xc, xc->handle, FST_HDR_OFFS_START_TIME, SEEK_SET);
        fstWriterUint64(xc->handle, xc->firsttime);
        fstWriterUint64(xc->handle, xc->curtime);
        fstWriterFseeko(xc, xc->handle, FST_HDR_OFFS_NUM_SCOPES, SEEK_SET);
        fstWriterUint64(xc->handle, xc->numscopes);
        fstWriterUint64(xc->handle, xc->numsigs);
        fstWriterUint64(xc->handle, xc->maxhandle);
        fstWriterUint64(xc->handle, xc->secnum);
        fflush(xc->handle);

        tmpfile_close(&xc->tchn_handle, &xc->tchn_handle_nam);
        free(xc->vchg_mem);
        xc->vchg_mem = NULL;
        tmpfile_close(&xc->curval_handle, &xc->curval_handle_nam);
        tmpfile_close(&xc->valpos_handle, &xc->valpos_handle_nam);
        tmpfile_close(&xc->geom_handle, &xc->geom_handle_nam);
        if (xc->hier_handle) {
            fclose(xc->hier_handle);
            xc->hier_handle = NULL;
        }
        if (xc->handle) {
            if (xc->repack_on_close) {
                FILE *fp;
                fst_off_t offpnt, uclen;
                int flen = strlen(xc->filename);
                char *hf = (char *)calloc(1, flen + 5);

                strcpy(hf, xc->filename);
                strcpy(hf + flen, ".pak");
                fp = fopen(hf, "wb");

                if (fp) {
                    gzFile dsth;
                    int zfd;
                    char gz_membuf[FST_GZIO_LEN];

                    fstWriterFseeko(xc, xc->handle, 0, SEEK_END);
                    uclen = ftello(xc->handle);

                    fputc(FST_BL_ZWRAPPER, fp);
                    fstWriterUint64(fp, 0);
                    fstWriterUint64(fp, uclen);
                    fflush(fp);

                    fstWriterFseeko(xc, xc->handle, 0, SEEK_SET);
                    zfd = dup(fileno(fp));
                    dsth = gzdopen(zfd, "wb4");
                    if (dsth) {
                        for (offpnt = 0; offpnt < uclen; offpnt += FST_GZIO_LEN) {
                            size_t this_len = ((uclen - offpnt) > FST_GZIO_LEN) ? FST_GZIO_LEN : (uclen - offpnt);
                            fstFread(gz_membuf, this_len, 1, xc->handle);
                            gzwrite(dsth, gz_membuf, this_len);
                        }
                        gzclose(dsth);
                    } else {
                        close(zfd);
                    }
                    fstWriterFseeko(xc, fp, 0, SEEK_END);
                    offpnt = ftello(fp);
                    fstWriterFseeko(xc, fp, 1, SEEK_SET);
                    fstWriterUint64(fp, offpnt - 1);
                    fclose(fp);
                    fclose(xc->handle);
                    xc->handle = NULL;

                    unlink(xc->filename);
                    rename(hf, xc->filename);
                } else {
                    xc->repack_on_close = 0;
                    fclose(xc->handle);
                    xc->handle = NULL;
                }

                free(hf);
            } else {
                fclose(xc->handle);
                xc->handle = NULL;
            }
        }

#ifdef __MINGW32__
        {
            int flen = strlen(xc->filename);
            char *hf = (char *)calloc(1, flen + 6);
            strcpy(hf, xc->filename);

            if (xc->compress_hier) {
                strcpy(hf + flen, ".hier");
                unlink(hf); /* no longer needed as a section now exists for this */
            }

            free(hf);
        }
#endif

#ifdef FST_WRITER_PARALLEL
        pthread_mutex_destroy(&xc->mutex);
        pthread_attr_destroy(&xc->thread_attr);
#endif

        if (xc->path_array) {
#ifndef _WAVE_HAVE_JUDY
            const uint32_t hashmask = FST_PATH_HASHMASK;
#endif
            JudyHSFreeArray(&(xc->path_array), NULL);
        }

        free(xc->filename);
        xc->filename = NULL;
        free(xc);
    }
}

/*
 * functions to set miscellaneous header/block information
 */
void fstWriterSetDate(void *ctx, const char *dat)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        char s[FST_HDR_DATE_SIZE];
        fst_off_t fpos = ftello(xc->handle);
        int len = strlen(dat);

        fstWriterFseeko(xc, xc->handle, FST_HDR_OFFS_DATE, SEEK_SET);
        memset(s, 0, FST_HDR_DATE_SIZE);
        memcpy(s, dat, (len < FST_HDR_DATE_SIZE) ? len : FST_HDR_DATE_SIZE);
        fstFwrite(s, FST_HDR_DATE_SIZE, 1, xc->handle);
        fflush(xc->handle);
        fstWriterFseeko(xc, xc->handle, fpos, SEEK_SET);
    }
}

void fstWriterSetVersion(void *ctx, const char *vers)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc && vers) {
        char s[FST_HDR_SIM_VERSION_SIZE];
        fst_off_t fpos = ftello(xc->handle);
        int len = strlen(vers);

        fstWriterFseeko(xc, xc->handle, FST_HDR_OFFS_SIM_VERSION, SEEK_SET);
        memset(s, 0, FST_HDR_SIM_VERSION_SIZE);
        memcpy(s, vers, (len < FST_HDR_SIM_VERSION_SIZE) ? len : FST_HDR_SIM_VERSION_SIZE);
        fstFwrite(s, FST_HDR_SIM_VERSION_SIZE, 1, xc->handle);
        fflush(xc->handle);
        fstWriterFseeko(xc, xc->handle, fpos, SEEK_SET);
    }
}

void fstWriterSetFileType(void *ctx, enum fstFileType filetype)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        if (/*(filetype >= FST_FT_MIN) &&*/ (filetype <= FST_FT_MAX)) {
            fst_off_t fpos = ftello(xc->handle);

            xc->filetype = filetype;

            fstWriterFseeko(xc, xc->handle, FST_HDR_OFFS_FILETYPE, SEEK_SET);
            fputc(xc->filetype, xc->handle);
            fflush(xc->handle);
            fstWriterFseeko(xc, xc->handle, fpos, SEEK_SET);
        }
    }
}

static void fstWriterSetAttrDoubleArgGeneric(void *ctx, int typ, uint64_t arg1, uint64_t arg2)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        unsigned char buf[11]; /* ceil(64/7) = 10 + null term */
        unsigned char *pnt = fstCopyVarint64ToRight(buf, arg1);
        if (arg1) {
            *pnt = 0; /* this converts any *nonzero* arg1 when made a varint into a null-term string */
        }

        fstWriterSetAttrBegin(xc, FST_AT_MISC, typ, (char *)buf, arg2);
    }
}

static void fstWriterSetAttrGeneric(void *ctx, const char *comm, int typ, uint64_t arg)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc && comm) {
        char *s = strdup(comm);
        char *sf = s;

        while (*s) {
            if ((*s == '\n') || (*s == '\r'))
                *s = ' ';
            s++;
        }

        fstWriterSetAttrBegin(xc, FST_AT_MISC, typ, sf, arg);
        free(sf);
    }
}

static void fstWriterSetSourceStem_2(void *ctx, const char *path, unsigned int line, unsigned int use_realpath, int typ)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

    if (xc && path && path[0]) {
        uint64_t sidx = 0;
        int slen = strlen(path);
#ifndef _WAVE_HAVE_JUDY
        const uint32_t hashmask = FST_PATH_HASHMASK;
        const unsigned char *path2 = (const unsigned char *)path;
        PPvoid_t pv;
#else
        char *path2 = (char *)alloca(slen + 1); /* judy lacks const qualifier in its JudyHSIns definition */
        PPvoid_t pv;
        strcpy(path2, path);
#endif

        pv = JudyHSIns(&(xc->path_array), path2, slen, NULL);
        if (*pv) {
            sidx = (intptr_t)(*pv);
        } else {
            char *rp = NULL;

            sidx = ++xc->path_array_count;
            *pv = (void *)(intptr_t)(xc->path_array_count);

            if (use_realpath) {
                rp = fstRealpath(
#ifndef _WAVE_HAVE_JUDY
                        (const char *)
#endif
                                path2,
                        NULL);
            }

            fstWriterSetAttrGeneric(xc,
                                    rp ? rp :
#ifndef _WAVE_HAVE_JUDY
                                       (const char *)
#endif
                                                    path2,
                                    FST_MT_PATHNAME, sidx);

            if (rp) {
                free(rp);
            }
        }

        fstWriterSetAttrDoubleArgGeneric(xc, typ, sidx, line);
    }
}

void fstWriterSetSourceStem(void *ctx, const char *path, unsigned int line, unsigned int use_realpath)
{
    fstWriterSetSourceStem_2(ctx, path, line, use_realpath, FST_MT_SOURCESTEM);
}

void fstWriterSetSourceInstantiationStem(void *ctx, const char *path, unsigned int line, unsigned int use_realpath)
{
    fstWriterSetSourceStem_2(ctx, path, line, use_realpath, FST_MT_SOURCEISTEM);
}

void fstWriterSetComment(void *ctx, const char *comm) { fstWriterSetAttrGeneric(ctx, comm, FST_MT_COMMENT, 0); }

void fstWriterSetValueList(void *ctx, const char *vl) { fstWriterSetAttrGeneric(ctx, vl, FST_MT_VALUELIST, 0); }

void fstWriterSetEnvVar(void *ctx, const char *envvar) { fstWriterSetAttrGeneric(ctx, envvar, FST_MT_ENVVAR, 0); }

void fstWriterSetTimescale(void *ctx, int ts)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        fst_off_t fpos = ftello(xc->handle);
        fstWriterFseeko(xc, xc->handle, FST_HDR_OFFS_TIMESCALE, SEEK_SET);
        fputc(ts & 255, xc->handle);
        fflush(xc->handle);
        fstWriterFseeko(xc, xc->handle, fpos, SEEK_SET);
    }
}

void fstWriterSetTimescaleFromString(void *ctx, const char *s)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc && s) {
        int mat = 0;
        int seconds_exp = -9;
        int tv = atoi(s);
        const char *pnt = s;

        while (*pnt) {
            switch (*pnt) {
            case 'm':
                seconds_exp = -3;
                mat = 1;
                break;
            case 'u':
                seconds_exp = -6;
                mat = 1;
                break;
            case 'n':
                seconds_exp = -9;
                mat = 1;
                break;
            case 'p':
                seconds_exp = -12;
                mat = 1;
                break;
            case 'f':
                seconds_exp = -15;
                mat = 1;
                break;
            case 'a':
                seconds_exp = -18;
                mat = 1;
                break;
            case 'z':
                seconds_exp = -21;
                mat = 1;
                break;
            case 's':
                seconds_exp = 0;
                mat = 1;
                break;
            default:
                break;
            }

            if (mat)
                break;
            pnt++;
        }

        if (tv == 10) {
            seconds_exp++;
        } else if (tv == 100) {
            seconds_exp += 2;
        }

        fstWriterSetTimescale(ctx, seconds_exp);
    }
}

void fstWriterSetTimezero(void *ctx, int64_t tim)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        fst_off_t fpos = ftello(xc->handle);
        fstWriterFseeko(xc, xc->handle, FST_HDR_OFFS_TIMEZERO, SEEK_SET);
        fstWriterUint64(xc->handle, (xc->timezero = tim));
        fflush(xc->handle);
        fstWriterFseeko(xc, xc->handle, fpos, SEEK_SET);
    }
}

void fstWriterSetPackType(void *ctx, enum fstWriterPackType typ)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        xc->fastpack = (typ != FST_WR_PT_ZLIB);
        xc->fourpack = (typ == FST_WR_PT_LZ4);
    }
}

void fstWriterSetRepackOnClose(void *ctx, int enable)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        xc->repack_on_close = (enable != 0);
    }
}

void fstWriterSetParallelMode(void *ctx, int enable)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        xc->parallel_was_enabled |= xc->parallel_enabled; /* make sticky */
        xc->parallel_enabled = (enable != 0);
#ifndef FST_WRITER_PARALLEL
        if (xc->parallel_enabled) {
            fprintf(stderr, FST_APIMESS
                    "fstWriterSetParallelMode(), FST_WRITER_PARALLEL not enabled during compile, exiting.\n");
            exit(255);
        }
#endif
    }
}

void fstWriterSetDumpSizeLimit(void *ctx, uint64_t numbytes)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        xc->dump_size_limit = numbytes;
    }
}

int fstWriterGetDumpSizeLimitReached(void *ctx)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        return (xc->size_limit_locked != 0);
    }

    return (0);
}

int fstWriterGetFseekFailed(void *ctx)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc) {
        return (xc->fseek_failed != 0);
    }

    return (0);
}

/*
 * writer attr/scope/var creation:
 * fstWriterCreateVar2() is used to dump VHDL or other languages, but the
 * underlying variable needs to map to Verilog/SV via the proper fstVarType vt
 */
fstHandle fstWriterCreateVar2(void *ctx, enum fstVarType vt, enum fstVarDir vd, uint32_t len, const char *nam,
                              fstHandle aliasHandle, const char *type, enum fstSupplementalVarType svt,
                              enum fstSupplementalDataType sdt)
{
    fstWriterSetAttrGeneric(ctx, type ? type : "", FST_MT_SUPVAR,
                            (svt << FST_SDT_SVT_SHIFT_COUNT) | (sdt & FST_SDT_ABS_MAX));
    return (fstWriterCreateVar(ctx, vt, vd, len, nam, aliasHandle));
}

fstHandle fstWriterCreateVar(void *ctx, enum fstVarType vt, enum fstVarDir vd, uint32_t len, const char *nam,
                             fstHandle aliasHandle)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    unsigned int i;
    int nlen, is_real;

    if (xc && nam) {
        if (xc->valpos_mem) {
            fstDestroyMmaps(xc, 0);
        }

        fputc(vt, xc->hier_handle);
        fputc(vd, xc->hier_handle);
        nlen = strlen(nam);
        fstFwrite(nam, nlen, 1, xc->hier_handle);
        fputc(0, xc->hier_handle);
        xc->hier_file_len += (nlen + 3);

        if ((vt == FST_VT_VCD_REAL) || (vt == FST_VT_VCD_REAL_PARAMETER) || (vt == FST_VT_VCD_REALTIME) ||
            (vt == FST_VT_SV_SHORTREAL)) {
            is_real = 1;
            len = 8; /* recast number of bytes to that of what a double is */
        } else {
            is_real = 0;
            if (vt == FST_VT_GEN_STRING) {
                len = 0;
            }
        }

        xc->hier_file_len += fstWriterVarint(xc->hier_handle, len);

        if (aliasHandle > xc->maxhandle)
            aliasHandle = 0;
        xc->hier_file_len += fstWriterVarint(xc->hier_handle, aliasHandle);
        xc->numsigs++;
        if (xc->numsigs == xc->next_huge_break) {
            if (xc->fst_break_size < xc->fst_huge_break_size) {
                xc->next_huge_break += FST_ACTIVATE_HUGE_INC;
                xc->fst_break_size += xc->fst_orig_break_size;
                xc->fst_break_add_size += xc->fst_orig_break_add_size;

                xc->vchg_alloc_siz = xc->fst_break_size + xc->fst_break_add_size;
                if (xc->vchg_mem) {
                    xc->vchg_mem = (unsigned char *)realloc(xc->vchg_mem, xc->vchg_alloc_siz);
                }
            }
        }

        if (!aliasHandle) {
            uint32_t zero = 0;

            if (len) {
                fstWriterVarint(xc->geom_handle, !is_real ? len : 0); /* geom section encodes reals as zero byte */
            } else {
                fstWriterVarint(xc->geom_handle, 0xFFFFFFFF); /* geom section encodes zero len as 32b -1 */
            }

            fstFwrite(&xc->maxvalpos, sizeof(uint32_t), 1, xc->valpos_handle);
            fstFwrite(&len, sizeof(uint32_t), 1, xc->valpos_handle);
            fstFwrite(&zero, sizeof(uint32_t), 1, xc->valpos_handle);
            fstFwrite(&zero, sizeof(uint32_t), 1, xc->valpos_handle);

            if (!is_real) {
                for (i = 0; i < len; i++) {
                    fputc('x', xc->curval_handle);
                }
            } else {
                fstFwrite(&xc->nan, 8, 1, xc->curval_handle); /* initialize doubles to NaN rather than x */
            }

            xc->maxvalpos += len;
            xc->maxhandle++;
            return (xc->maxhandle);
        } else {
            return (aliasHandle);
        }
    }

    return (0);
}

void fstWriterSetScope(void *ctx, enum fstScopeType scopetype, const char *scopename, const char *scopecomp)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

    if (xc) {
        fputc(FST_ST_VCD_SCOPE, xc->hier_handle);
        if (/*(scopetype < FST_ST_VCD_MODULE) ||*/ (scopetype > FST_ST_MAX)) {
            scopetype = FST_ST_VCD_MODULE;
        }
        fputc(scopetype, xc->hier_handle);
        fprintf(xc->hier_handle, "%s%c%s%c", scopename ? scopename : "", 0, scopecomp ? scopecomp : "", 0);

        if (scopename) {
            xc->hier_file_len += strlen(scopename);
        }
        if (scopecomp) {
            xc->hier_file_len += strlen(scopecomp);
        }

        xc->hier_file_len += 4; /* FST_ST_VCD_SCOPE + scopetype + two string terminating zeros */
        xc->numscopes++;
    }
}

void fstWriterSetUpscope(void *ctx)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

    if (xc) {
        fputc(FST_ST_VCD_UPSCOPE, xc->hier_handle);
        xc->hier_file_len++;
    }
}

void fstWriterSetAttrBegin(void *ctx, enum fstAttrType attrtype, int subtype, const char *attrname, uint64_t arg)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

    if (xc) {
        fputc(FST_ST_GEN_ATTRBEGIN, xc->hier_handle);
        if (/*(attrtype < FST_AT_MISC) ||*/ (attrtype > FST_AT_MAX)) {
            attrtype = FST_AT_MISC;
            subtype = FST_MT_UNKNOWN;
        }
        fputc(attrtype, xc->hier_handle);

        switch (attrtype) {
        case FST_AT_ARRAY:
            if ((subtype < FST_AR_NONE) || (subtype > FST_AR_MAX))
                subtype = FST_AR_NONE;
            break;
        case FST_AT_ENUM:
            if ((subtype < FST_EV_SV_INTEGER) || (subtype > FST_EV_MAX))
                subtype = FST_EV_SV_INTEGER;
            break;
        case FST_AT_PACK:
            if ((subtype < FST_PT_NONE) || (subtype > FST_PT_MAX))
                subtype = FST_PT_NONE;
            break;

        case FST_AT_MISC:
        default:
            break;
        }

        fputc(subtype, xc->hier_handle);
        fprintf(xc->hier_handle, "%s%c", attrname ? attrname : "", 0);

        if (attrname) {
            xc->hier_file_len += strlen(attrname);
        }

        xc->hier_file_len += 4; /* FST_ST_GEN_ATTRBEGIN + type + subtype + string terminating zero */
        xc->hier_file_len += fstWriterVarint(xc->hier_handle, arg);
    }
}

void fstWriterSetAttrEnd(void *ctx)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

    if (xc) {
        fputc(FST_ST_GEN_ATTREND, xc->hier_handle);
        xc->hier_file_len++;
    }
}

fstEnumHandle fstWriterCreateEnumTable(void *ctx, const char *name, uint32_t elem_count, unsigned int min_valbits,
                                       const char **literal_arr, const char **val_arr)
{
    fstEnumHandle handle = 0;
    unsigned int *literal_lens = NULL;
    unsigned int *val_lens = NULL;
    int lit_len_tot = 0;
    int val_len_tot = 0;
    int name_len;
    char elem_count_buf[16];
    int elem_count_len;
    int total_len;
    int pos = 0;
    char *attr_str = NULL;

    if (ctx && name && literal_arr && val_arr && (elem_count != 0)) {
        struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

        uint32_t i;

        name_len = strlen(name);
        elem_count_len = sprintf(elem_count_buf, "%" PRIu32, elem_count);

        literal_lens = (unsigned int *)calloc(elem_count, sizeof(unsigned int));
        val_lens = (unsigned int *)calloc(elem_count, sizeof(unsigned int));

        for (i = 0; i < elem_count; i++) {
            literal_lens[i] = strlen(literal_arr[i]);
            lit_len_tot += fstUtilityBinToEscConvertedLen((unsigned char *)literal_arr[i], literal_lens[i]);

            val_lens[i] = strlen(val_arr[i]);
            val_len_tot += fstUtilityBinToEscConvertedLen((unsigned char *)val_arr[i], val_lens[i]);

            if (min_valbits > 0) {
                if (val_lens[i] < min_valbits) {
                    val_len_tot += (min_valbits - val_lens[i]); /* additional converted len is same for '0' character */
                }
            }
        }

        total_len = name_len + 1 + elem_count_len + 1 + lit_len_tot + elem_count + val_len_tot + elem_count;

        attr_str = (char *)malloc(total_len);
        pos = 0;

        memcpy(attr_str + pos, name, name_len);
        pos += name_len;
        attr_str[pos++] = ' ';

        memcpy(attr_str + pos, elem_count_buf, elem_count_len);
        pos += elem_count_len;
        attr_str[pos++] = ' ';

        for (i = 0; i < elem_count; i++) {
            pos += fstUtilityBinToEsc((unsigned char *)attr_str + pos, (unsigned char *)literal_arr[i],
                                      literal_lens[i]);
            attr_str[pos++] = ' ';
        }

        for (i = 0; i < elem_count; i++) {
            if (min_valbits > 0) {
                if (val_lens[i] < min_valbits) {
                    memset(attr_str + pos, '0', min_valbits - val_lens[i]);
                    pos += (min_valbits - val_lens[i]);
                }
            }

            pos += fstUtilityBinToEsc((unsigned char *)attr_str + pos, (unsigned char *)val_arr[i], val_lens[i]);
            attr_str[pos++] = ' ';
        }

        attr_str[pos - 1] = 0;

#ifdef FST_DEBUG
        fprintf(stderr, FST_APIMESS "fstWriterCreateEnumTable() total_len: %d, pos: %d\n", total_len, pos);
        fprintf(stderr, FST_APIMESS "*%s*\n", attr_str);
#endif

        fstWriterSetAttrBegin(xc, FST_AT_MISC, FST_MT_ENUMTABLE, attr_str, handle = ++xc->max_enumhandle);

        free(attr_str);
        free(val_lens);
        free(literal_lens);
    }

    return (handle);
}

void fstWriterEmitEnumTableRef(void *ctx, fstEnumHandle handle)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (xc && handle) {
        fstWriterSetAttrBegin(xc, FST_AT_MISC, FST_MT_ENUMTABLE, NULL, handle);
    }
}

/*
 * value and time change emission
 */
void fstWriterEmitValueChange(void *ctx, fstHandle handle, const void *val)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    const unsigned char *buf = (const unsigned char *)val;
    uint32_t offs;
    int len;

    if (FST_LIKELY((xc) && (handle <= xc->maxhandle))) {
        uint32_t fpos;
        uint32_t *vm4ip;

        if (FST_UNLIKELY(!xc->valpos_mem)) {
            xc->vc_emitted = 1;
            fstWriterCreateMmaps(xc);
        }

        handle--; /* move starting at 1 index to starting at 0 */
        vm4ip = &(xc->valpos_mem[4 * handle]);

        len = vm4ip[1];
        if (FST_LIKELY(len)) /* len of zero = variable length, use fstWriterEmitVariableLengthValueChange */
        {
            if (FST_LIKELY(!xc->is_initial_time)) {
                fpos = xc->vchg_siz;

                if (FST_UNLIKELY((fpos + len + 10) > xc->vchg_alloc_siz)) {
                    xc->vchg_alloc_siz +=
                            (xc->fst_break_add_size +
                             len); /* +len added in the case of extremely long vectors and small break add sizes */
                    xc->vchg_mem = (unsigned char *)realloc(xc->vchg_mem, xc->vchg_alloc_siz);
                    if (FST_UNLIKELY(!xc->vchg_mem)) {
                        fprintf(stderr, FST_APIMESS "Could not realloc() in fstWriterEmitValueChange, exiting.\n");
                        exit(255);
                    }
                }
#ifdef FST_REMOVE_DUPLICATE_VC
                offs = vm4ip[0];

                if (len != 1) {
                    if ((vm4ip[3] == xc->tchn_idx) && (vm4ip[2])) {
                        unsigned char *old_value = xc->vchg_mem + vm4ip[2] + 4; /* the +4 skips old vm4ip[2] value */
                        while (*(old_value++) & 0x80) { /* skips over varint encoded "xc->tchn_idx - vm4ip[3]" */
                        }
                        memcpy(old_value, buf, len); /* overlay new value */

                        memcpy(xc->curval_mem + offs, buf, len);
                        return;
                    } else {
                        if (!memcmp(xc->curval_mem + offs, buf, len)) {
                            if (!xc->curtime) {
                                int i;
                                for (i = 0; i < len; i++) {
                                    if (buf[i] != 'x')
                                        break;
                                }

                                if (i < len)
                                    return;
                            } else {
                                return;
                            }
                        }
                    }

                    memcpy(xc->curval_mem + offs, buf, len);
                } else {
                    if ((vm4ip[3] == xc->tchn_idx) && (vm4ip[2])) {
                        unsigned char *old_value = xc->vchg_mem + vm4ip[2] + 4; /* the +4 skips old vm4ip[2] value */
                        while (*(old_value++) & 0x80) { /* skips over varint encoded "xc->tchn_idx - vm4ip[3]" */
                        }
                        *old_value = *buf; /* overlay new value */

                        *(xc->curval_mem + offs) = *buf;
                        return;
                    } else {
                        if ((*(xc->curval_mem + offs)) == (*buf)) {
                            if (!xc->curtime) {
                                if (*buf != 'x')
                                    return;
                            } else {
                                return;
                            }
                        }
                    }

                    *(xc->curval_mem + offs) = *buf;
                }
#endif
                xc->vchg_siz += fstWriterUint32WithVarint32(xc, &vm4ip[2], xc->tchn_idx - vm4ip[3], buf,
                                                            len); /* do one fwrite op only */
                vm4ip[3] = xc->tchn_idx;
                vm4ip[2] = fpos;
            } else {
                offs = vm4ip[0];
                memcpy(xc->curval_mem + offs, buf, len);
            }
        }
    }
}

void fstWriterEmitValueChange32(void *ctx, fstHandle handle, uint32_t bits, uint32_t val)
{
    char buf[32];
    char *s = buf;
    uint32_t i;
    for (i = 0; i < bits; ++i) {
        *s++ = '0' + ((val >> (bits - i - 1)) & 1);
    }
    fstWriterEmitValueChange(ctx, handle, buf);
}
void fstWriterEmitValueChange64(void *ctx, fstHandle handle, uint32_t bits, uint64_t val)
{
    char buf[64];
    char *s = buf;
    uint32_t i;
    for (i = 0; i < bits; ++i) {
        *s++ = '0' + ((val >> (bits - i - 1)) & 1);
    }
    fstWriterEmitValueChange(ctx, handle, buf);
}
void fstWriterEmitValueChangeVec32(void *ctx, fstHandle handle, uint32_t bits, const uint32_t *val)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (FST_UNLIKELY(bits <= 32)) {
        fstWriterEmitValueChange32(ctx, handle, bits, val[0]);
    } else if (FST_LIKELY(xc)) {
        int bq = bits / 32;
        int br = bits & 31;
        int i;
        int w;
        uint32_t v;
        unsigned char *s;
        if (FST_UNLIKELY(bits > xc->outval_alloc_siz)) {
            xc->outval_alloc_siz = bits * 2 + 1;
            xc->outval_mem = (unsigned char *)realloc(xc->outval_mem, xc->outval_alloc_siz);
            if (FST_UNLIKELY(!xc->outval_mem)) {
                fprintf(stderr, FST_APIMESS "Could not realloc() in fstWriterEmitValueChangeVec32, exiting.\n");
                exit(255);
            }
        }
        s = xc->outval_mem;
        {
            w = bq;
            v = val[w];
            for (i = 0; i < br; ++i) {
                *s++ = '0' + ((v >> (br - i - 1)) & 1);
            }
        }
        for (w = bq - 1; w >= 0; --w) {
            v = val[w];
            for (i = (32 - 4); i >= 0; i -= 4) {
                s[0] = '0' + ((v >> (i + 3)) & 1);
                s[1] = '0' + ((v >> (i + 2)) & 1);
                s[2] = '0' + ((v >> (i + 1)) & 1);
                s[3] = '0' + ((v >> (i + 0)) & 1);
                s += 4;
            }
        }
        fstWriterEmitValueChange(ctx, handle, xc->outval_mem);
    }
}
void fstWriterEmitValueChangeVec64(void *ctx, fstHandle handle, uint32_t bits, const uint64_t *val)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    if (FST_UNLIKELY(bits <= 64)) {
        fstWriterEmitValueChange64(ctx, handle, bits, val[0]);
    } else if (FST_LIKELY(xc)) {
        int bq = bits / 64;
        int br = bits & 63;
        int i;
        int w;
        uint32_t v;
        unsigned char *s;
        if (FST_UNLIKELY(bits > xc->outval_alloc_siz)) {
            xc->outval_alloc_siz = bits * 2 + 1;
            xc->outval_mem = (unsigned char *)realloc(xc->outval_mem, xc->outval_alloc_siz);
            if (FST_UNLIKELY(!xc->outval_mem)) {
                fprintf(stderr, FST_APIMESS "Could not realloc() in fstWriterEmitValueChangeVec64, exiting.\n");
                exit(255);
            }
        }
        s = xc->outval_mem;
        {
            w = bq;
            v = val[w];
            for (i = 0; i < br; ++i) {
                *s++ = '0' + ((v >> (br - i - 1)) & 1);
            }
        }
        for (w = bq - 1; w >= 0; --w) {
            v = val[w];
            for (i = (64 - 4); i >= 0; i -= 4) {
                s[0] = '0' + ((v >> (i + 3)) & 1);
                s[1] = '0' + ((v >> (i + 2)) & 1);
                s[2] = '0' + ((v >> (i + 1)) & 1);
                s[3] = '0' + ((v >> (i + 0)) & 1);
                s += 4;
            }
        }
        fstWriterEmitValueChange(ctx, handle, xc->outval_mem);
    }
}

void fstWriterEmitVariableLengthValueChange(void *ctx, fstHandle handle, const void *val, uint32_t len)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    const unsigned char *buf = (const unsigned char *)val;

    if (FST_LIKELY((xc) && (handle <= xc->maxhandle))) {
        uint32_t fpos;
        uint32_t *vm4ip;

        if (FST_UNLIKELY(!xc->valpos_mem)) {
            xc->vc_emitted = 1;
            fstWriterCreateMmaps(xc);
        }

        handle--; /* move starting at 1 index to starting at 0 */
        vm4ip = &(xc->valpos_mem[4 * handle]);

        /* there is no initial time dump for variable length value changes */
        if (FST_LIKELY(!vm4ip[1])) /* len of zero = variable length */
        {
            fpos = xc->vchg_siz;

            if (FST_UNLIKELY((fpos + len + 10 + 5) > xc->vchg_alloc_siz)) {
                xc->vchg_alloc_siz +=
                        (xc->fst_break_add_size + len +
                         5); /* +len added in the case of extremely long vectors and small break add sizes */
                xc->vchg_mem = (unsigned char *)realloc(xc->vchg_mem, xc->vchg_alloc_siz);
                if (FST_UNLIKELY(!xc->vchg_mem)) {
                    fprintf(stderr,
                            FST_APIMESS "Could not realloc() in fstWriterEmitVariableLengthValueChange, exiting.\n");
                    exit(255);
                }
            }

            xc->vchg_siz += fstWriterUint32WithVarint32AndLength(xc, &vm4ip[2], xc->tchn_idx - vm4ip[3], buf,
                                                                 len); /* do one fwrite op only */
            vm4ip[3] = xc->tchn_idx;
            vm4ip[2] = fpos;
        }
    }
}

void fstWriterEmitTimeChange(void *ctx, uint64_t tim)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;
    unsigned int i;
    int skip = 0;
    if (xc) {
        if (FST_UNLIKELY(xc->is_initial_time)) {
            if (xc->size_limit_locked) /* this resets xc->is_initial_time to one */
            {
                return;
            }

            if (!xc->valpos_mem) {
                fstWriterCreateMmaps(xc);
            }

            skip = 1;

            xc->firsttime = (xc->vc_emitted) ? 0 : tim;
            xc->curtime = 0;
            xc->vchg_mem[0] = '!';
            xc->vchg_siz = 1;
            fstWriterEmitSectionHeader(xc);
            for (i = 0; i < xc->maxhandle; i++) {
                xc->valpos_mem[4 * i + 2] = 0; /* zero out offset val */
                xc->valpos_mem[4 * i + 3] = 0; /* zero out last time change val */
            }
            xc->is_initial_time = 0;
        } else {
            if ((xc->vchg_siz >= xc->fst_break_size) || (xc->flush_context_pending)) {
                xc->flush_context_pending = 0;
                fstWriterFlushContextPrivate(xc);
                xc->tchn_cnt++;
                fstWriterVarint(xc->tchn_handle, xc->curtime);
            }
        }

        if (!skip) {
            xc->tchn_idx++;
        }
        fstWriterVarint(xc->tchn_handle, tim - xc->curtime);
        xc->tchn_cnt++;
        xc->curtime = tim;
    }
}

void fstWriterEmitDumpActive(void *ctx, int enable)
{
    struct fstWriterContext *xc = (struct fstWriterContext *)ctx;

    if (xc) {
        struct fstBlackoutChain *b = (struct fstBlackoutChain *)calloc(1, sizeof(struct fstBlackoutChain));

        b->tim = xc->curtime;
        b->active = (enable != 0);

        xc->num_blackouts++;
        if (xc->blackout_curr) {
            xc->blackout_curr->next = b;
            xc->blackout_curr = b;
        } else {
            xc->blackout_head = b;
            xc->blackout_curr = b;
        }
    }
}

/***********************/
/***                 ***/
/*** reader function ***/
/***                 ***/
/***********************/

/*
 * private structs
 */
static const char *vartypes[] = {"event",   "integer",  "parameter", "real",   "real_parameter", "reg",     "supply0",
                                 "supply1", "time",     "tri",       "triand", "trior",          "trireg",  "tri0",
                                 "tri1",    "wand",     "wire",      "wor",    "port",           "sparray", "realtime",
                                 "string",  "bit",      "logic",     "int",    "shortint",       "longint", "byte",
                                 "enum",    "shortreal"};

static const char *modtypes[] = {"module",
                                 "task",
                                 "function",
                                 "begin",
                                 "fork",
                                 "generate",
                                 "struct",
                                 "union",
                                 "class",
                                 "interface",
                                 "package",
                                 "program",
                                 "vhdl_architecture",
                                 "vhdl_procedure",
                                 "vhdl_function",
                                 "vhdl_record",
                                 "vhdl_process",
                                 "vhdl_block",
                                 "vhdl_for_generate",
                                 "vhdl_if_generate",
                                 "vhdl_generate",
                                 "vhdl_package"};

static const char *attrtypes[] = {"misc", "array", "enum", "class"};

static const char *arraytypes[] = {"none", "unpacked", "packed", "sparse"};

static const char *enumvaluetypes[] = {"integer",
                                       "bit",
                                       "logic",
                                       "int",
                                       "shortint",
                                       "longint",
                                       "byte",
                                       "unsigned_integer",
                                       "unsigned_bit",
                                       "unsigned_logic",
                                       "unsigned_int",
                                       "unsigned_shortint",
                                       "unsigned_longint",
                                       "unsigned_byte"};

static const char *packtypes[] = {"none", "unpacked", "packed", "tagged_packed"};

struct fstCurrHier
{
    struct fstCurrHier *prev;
    void *user_info;
    int len;
};

struct fstReaderContext
{
    /* common entries */

    FILE *f, *fh;

    uint64_t start_time, end_time;
    uint64_t mem_used_by_writer;
    uint64_t scope_count;
    uint64_t var_count;
    fstHandle maxhandle;
    uint64_t num_alias;
    uint64_t vc_section_count;

    uint32_t *signal_lens;                /* maxhandle sized */
    unsigned char *signal_typs;           /* maxhandle sized */
    unsigned char *process_mask;          /* maxhandle-based, bitwise sized */
    uint32_t longest_signal_value_len;    /* longest len value encountered */
    unsigned char *temp_signal_value_buf; /* malloced for len in longest_signal_value_len */

    signed char timescale;
    unsigned char filetype;

    unsigned use_vcd_extensions : 1;
    unsigned double_endian_match : 1;
    unsigned native_doubles_for_cb : 1;
    unsigned contains_geom_section : 1;
    unsigned contains_hier_section : 1;        /* valid for hier_pos */
    unsigned contains_hier_section_lz4duo : 1; /* valid for hier_pos (contains_hier_section_lz4 always also set) */
    unsigned contains_hier_section_lz4 : 1;    /* valid for hier_pos */
    unsigned limit_range_valid : 1;            /* valid for limit_range_start, limit_range_end */

    char version[FST_HDR_SIM_VERSION_SIZE + 1];
    char date[FST_HDR_DATE_SIZE + 1];
    int64_t timezero;

    char *filename, *filename_unpacked;
    fst_off_t hier_pos;

    uint32_t num_blackouts;
    uint64_t *blackout_times;
    unsigned char *blackout_activity;

    uint64_t limit_range_start, limit_range_end;

    /* entries specific to read value at time functions */

    unsigned rvat_data_valid : 1;
    uint64_t *rvat_time_table;
    uint64_t rvat_beg_tim, rvat_end_tim;
    unsigned char *rvat_frame_data;
    uint64_t rvat_frame_maxhandle;
    fst_off_t *rvat_chain_table;
    uint32_t *rvat_chain_table_lengths;
    uint64_t rvat_vc_maxhandle;
    fst_off_t rvat_vc_start;
    uint32_t *rvat_sig_offs;
    int rvat_packtype;

    uint32_t rvat_chain_len;
    unsigned char *rvat_chain_mem;
    fstHandle rvat_chain_facidx;

    uint32_t rvat_chain_pos_tidx;
    uint32_t rvat_chain_pos_idx;
    uint64_t rvat_chain_pos_time;
    unsigned rvat_chain_pos_valid : 1;

    /* entries specific to hierarchy traversal */

    struct fstHier hier;
    struct fstCurrHier *curr_hier;
    fstHandle current_handle;
    char *curr_flat_hier_nam;
    int flat_hier_alloc_len;
    unsigned do_rewind : 1;
    char str_scope_nam[FST_ID_NAM_SIZ + 1];
    char str_scope_comp[FST_ID_NAM_SIZ + 1];

    unsigned fseek_failed : 1;

    /* self-buffered I/O for writes */

#ifndef FST_WRITEX_DISABLE
    int writex_pos;
    int writex_fd;
    unsigned char writex_buf[FST_WRITEX_MAX];
#endif

    char *f_nam;
    char *fh_nam;
};

int fstReaderFseeko(struct fstReaderContext *xc, FILE *stream, fst_off_t offset, int whence)
{
    int rc = fseeko(stream, offset, whence);

    if (rc < 0) {
        xc->fseek_failed = 1;
#ifdef FST_DEBUG
        fprintf(stderr, FST_APIMESS "Seek to #%" PRId64 " (whence = %d) failed!\n", offset, whence);
        perror("Why");
#endif
    }

    return (rc);
}

#ifndef FST_WRITEX_DISABLE
static void fstWritex(struct fstReaderContext *xc, void *v, int len)
{
    unsigned char *s = (unsigned char *)v;

    if (len) {
        if (len < FST_WRITEX_MAX) {
            if (xc->writex_pos + len >= FST_WRITEX_MAX) {
                fstWritex(xc, NULL, 0);
            }

            memcpy(xc->writex_buf + xc->writex_pos, s, len);
            xc->writex_pos += len;
        } else {
            fstWritex(xc, NULL, 0);
            if (write(xc->writex_fd, s, len)) {
            };
        }
    } else {
        if (xc->writex_pos) {
            if (write(xc->writex_fd, xc->writex_buf, xc->writex_pos)) {
            };
            xc->writex_pos = 0;
        }
    }
}
#endif

/*
 * scope -> flat name handling
 */
static void fstReaderDeallocateScopeData(struct fstReaderContext *xc)
{
    struct fstCurrHier *chp;

    free(xc->curr_flat_hier_nam);
    xc->curr_flat_hier_nam = NULL;
    while (xc->curr_hier) {
        chp = xc->curr_hier->prev;
        free(xc->curr_hier);
        xc->curr_hier = chp;
    }
}

const char *fstReaderGetCurrentFlatScope(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    if (xc) {
        return (xc->curr_flat_hier_nam ? xc->curr_flat_hier_nam : "");
    } else {
        return (NULL);
    }
}

void *fstReaderGetCurrentScopeUserInfo(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    if (xc) {
        return (xc->curr_hier ? xc->curr_hier->user_info : NULL);
    } else {
        return (NULL);
    }
}

const char *fstReaderPopScope(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    if (xc && xc->curr_hier) {
        struct fstCurrHier *ch = xc->curr_hier;
        if (xc->curr_hier->prev) {
            xc->curr_flat_hier_nam[xc->curr_hier->prev->len] = 0;
        } else {
            *xc->curr_flat_hier_nam = 0;
        }
        xc->curr_hier = xc->curr_hier->prev;
        free(ch);
        return (xc->curr_flat_hier_nam ? xc->curr_flat_hier_nam : "");
    }

    return (NULL);
}

void fstReaderResetScope(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        while (fstReaderPopScope(xc))
            ; /* remove any already-built scoping info */
    }
}

const char *fstReaderPushScope(void *ctx, const char *nam, void *user_info)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    if (xc) {
        struct fstCurrHier *ch = (struct fstCurrHier *)malloc(sizeof(struct fstCurrHier));
        int chl = xc->curr_hier ? xc->curr_hier->len : 0;
        int len = chl + 1 + strlen(nam);
        if (len >= xc->flat_hier_alloc_len) {
            xc->curr_flat_hier_nam =
                    xc->curr_flat_hier_nam ? (char *)realloc(xc->curr_flat_hier_nam, len + 1) : (char *)malloc(len + 1);
        }

        if (chl) {
            xc->curr_flat_hier_nam[chl] = '.';
            strcpy(xc->curr_flat_hier_nam + chl + 1, nam);
        } else {
            strcpy(xc->curr_flat_hier_nam, nam);
            len--;
        }

        ch->len = len;
        ch->prev = xc->curr_hier;
        ch->user_info = user_info;
        xc->curr_hier = ch;
        return (xc->curr_flat_hier_nam);
    }

    return (NULL);
}

int fstReaderGetCurrentScopeLen(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc && xc->curr_hier) {
        return (xc->curr_hier->len);
    }

    return (0);
}

int fstReaderGetFseekFailed(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    if (xc) {
        return (xc->fseek_failed != 0);
    }

    return (0);
}

/*
 * iter mask manipulation util functions
 */
int fstReaderGetFacProcessMask(void *ctx, fstHandle facidx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        facidx--;
        if (facidx < xc->maxhandle) {
            int process_idx = facidx / 8;
            int process_bit = facidx & 7;

            return ((xc->process_mask[process_idx] & (1 << process_bit)) != 0);
        }
    }
    return (0);
}

void fstReaderSetFacProcessMask(void *ctx, fstHandle facidx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        facidx--;
        if (facidx < xc->maxhandle) {
            int idx = facidx / 8;
            int bitpos = facidx & 7;

            xc->process_mask[idx] |= (1 << bitpos);
        }
    }
}

void fstReaderClrFacProcessMask(void *ctx, fstHandle facidx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        facidx--;
        if (facidx < xc->maxhandle) {
            int idx = facidx / 8;
            int bitpos = facidx & 7;

            xc->process_mask[idx] &= (~(1 << bitpos));
        }
    }
}

void fstReaderSetFacProcessMaskAll(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        memset(xc->process_mask, 0xff, (xc->maxhandle + 7) / 8);
    }
}

void fstReaderClrFacProcessMaskAll(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        memset(xc->process_mask, 0x00, (xc->maxhandle + 7) / 8);
    }
}

/*
 * various utility read/write functions
 */
signed char fstReaderGetTimescale(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->timescale : 0);
}

uint64_t fstReaderGetStartTime(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->start_time : 0);
}

uint64_t fstReaderGetEndTime(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->end_time : 0);
}

uint64_t fstReaderGetMemoryUsedByWriter(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->mem_used_by_writer : 0);
}

uint64_t fstReaderGetScopeCount(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->scope_count : 0);
}

uint64_t fstReaderGetVarCount(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->var_count : 0);
}

fstHandle fstReaderGetMaxHandle(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->maxhandle : 0);
}

uint64_t fstReaderGetAliasCount(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->num_alias : 0);
}

uint64_t fstReaderGetValueChangeSectionCount(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->vc_section_count : 0);
}

int fstReaderGetDoubleEndianMatchState(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->double_endian_match : 0);
}

const char *fstReaderGetVersionString(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->version : NULL);
}

const char *fstReaderGetDateString(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->date : NULL);
}

int fstReaderGetFileType(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? (int)xc->filetype : (int)FST_FT_VERILOG);
}

int64_t fstReaderGetTimezero(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->timezero : 0);
}

uint32_t fstReaderGetNumberDumpActivityChanges(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    return (xc ? xc->num_blackouts : 0);
}

uint64_t fstReaderGetDumpActivityChangeTime(void *ctx, uint32_t idx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc && (idx < xc->num_blackouts) && (xc->blackout_times)) {
        return (xc->blackout_times[idx]);
    } else {
        return (0);
    }
}

unsigned char fstReaderGetDumpActivityChangeValue(void *ctx, uint32_t idx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc && (idx < xc->num_blackouts) && (xc->blackout_activity)) {
        return (xc->blackout_activity[idx]);
    } else {
        return (0);
    }
}

void fstReaderSetLimitTimeRange(void *ctx, uint64_t start_time, uint64_t end_time)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        xc->limit_range_valid = 1;
        xc->limit_range_start = start_time;
        xc->limit_range_end = end_time;
    }
}

void fstReaderSetUnlimitedTimeRange(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        xc->limit_range_valid = 0;
    }
}

void fstReaderSetVcdExtensions(void *ctx, int enable)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        xc->use_vcd_extensions = (enable != 0);
    }
}

void fstReaderIterBlocksSetNativeDoublesOnCallback(void *ctx, int enable)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    if (xc) {
        xc->native_doubles_for_cb = (enable != 0);
    }
}

/*
 * hierarchy processing
 */
static void fstVcdID(char *buf, unsigned int value)
{
    char *pnt = buf;

    /* zero is illegal for a value...it is assumed they start at one */
    while (value) {
        value--;
        *(pnt++) = (char)('!' + value % 94);
        value = value / 94;
    }

    *pnt = 0;
}

static int fstVcdIDForFwrite(char *buf, unsigned int value)
{
    char *pnt = buf;

    /* zero is illegal for a value...it is assumed they start at one */
    while (value) {
        value--;
        *(pnt++) = (char)('!' + value % 94);
        value = value / 94;
    }

    return (pnt - buf);
}

static int fstReaderRecreateHierFile(struct fstReaderContext *xc)
{
    int pass_status = 1;

    if (!xc->fh) {
        fst_off_t offs_cache = ftello(xc->f);
        char *fnam = (char *)malloc(strlen(xc->filename) + 6 + 16 + 32 + 1);
        unsigned char *mem = (unsigned char *)malloc(FST_GZIO_LEN);
        fst_off_t hl, uclen;
        fst_off_t clen = 0;
        gzFile zhandle = NULL;
        int zfd;
        int htyp = FST_BL_SKIP;

        /* can't handle both set at once should never happen in a real file */
        if (!xc->contains_hier_section_lz4 && xc->contains_hier_section) {
            htyp = FST_BL_HIER;
        } else if (xc->contains_hier_section_lz4 && !xc->contains_hier_section) {
            htyp = xc->contains_hier_section_lz4duo ? FST_BL_HIER_LZ4DUO : FST_BL_HIER_LZ4;
        }

        sprintf(fnam, "%s.hier_%d_%p", xc->filename, getpid(), (void *)xc);
        fstReaderFseeko(xc, xc->f, xc->hier_pos, SEEK_SET);
        uclen = fstReaderUint64(xc->f);
#ifndef __MINGW32__
        fflush(xc->f);
#endif
        if (htyp == FST_BL_HIER) {
            fstReaderFseeko(xc, xc->f, xc->hier_pos, SEEK_SET);
            uclen = fstReaderUint64(xc->f);
#ifndef __MINGW32__
            fflush(xc->f);
#endif
            zfd = dup(fileno(xc->f));
	    lseek(zfd, ftell(xc->f), SEEK_SET);
            zhandle = gzdopen(zfd, "rb");
            if (!zhandle) {
                close(zfd);
                free(mem);
                free(fnam);
                return (0);
            }
        } else if ((htyp == FST_BL_HIER_LZ4) || (htyp == FST_BL_HIER_LZ4DUO)) {
            fstReaderFseeko(xc, xc->f, xc->hier_pos - 8, SEEK_SET); /* get section len */
            clen = fstReaderUint64(xc->f) - 16;
            uclen = fstReaderUint64(xc->f);
#ifndef __MINGW32__
            fflush(xc->f);
#endif
        }

#ifndef __MINGW32__
        xc->fh = fopen(fnam, "w+b");
        if (!xc->fh)
#endif
        {
            xc->fh = tmpfile_open(&xc->fh_nam);
            free(fnam);
            fnam = NULL;
            if (!xc->fh) {
                tmpfile_close(&xc->fh, &xc->fh_nam);
                free(mem);
                return (0);
            }
        }

#ifndef __MINGW32__
        if (fnam)
            unlink(fnam);
#endif

        if (htyp == FST_BL_HIER) {
            for (hl = 0; hl < uclen; hl += FST_GZIO_LEN) {
                size_t len = ((uclen - hl) > FST_GZIO_LEN) ? FST_GZIO_LEN : (uclen - hl);
                size_t gzreadlen = gzread(zhandle, mem, len); /* rc should equal len... */
                size_t fwlen;

                if (gzreadlen != len) {
                    pass_status = 0;
                    break;
                }

                fwlen = fstFwrite(mem, len, 1, xc->fh);
                if (fwlen != 1) {
                    pass_status = 0;
                    break;
                }
            }
            gzclose(zhandle);
        } else if (htyp == FST_BL_HIER_LZ4DUO) {
            unsigned char *lz4_cmem = (unsigned char *)malloc(clen);
            unsigned char *lz4_ucmem = (unsigned char *)malloc(uclen);
            unsigned char *lz4_ucmem2;
            uint64_t uclen2;
            int skiplen2 = 0;

            fstFread(lz4_cmem, clen, 1, xc->f);

            uclen2 = fstGetVarint64(lz4_cmem, &skiplen2);
            lz4_ucmem2 = (unsigned char *)malloc(uclen2);
            pass_status =
                    (uclen2 == (uint64_t)LZ4_decompress_safe_partial((char *)lz4_cmem + skiplen2, (char *)lz4_ucmem2,
                                                                     clen - skiplen2, uclen2, uclen2));
            if (pass_status) {
                pass_status = (uclen == LZ4_decompress_safe_partial((char *)lz4_ucmem2, (char *)lz4_ucmem, uclen2,
                                                                    uclen, uclen));

                if (fstFwrite(lz4_ucmem, uclen, 1, xc->fh) != 1) {
                    pass_status = 0;
                }
            }

            free(lz4_ucmem2);
            free(lz4_ucmem);
            free(lz4_cmem);
        } else if (htyp == FST_BL_HIER_LZ4) {
            unsigned char *lz4_cmem = (unsigned char *)malloc(clen);
            unsigned char *lz4_ucmem = (unsigned char *)malloc(uclen);

            fstFread(lz4_cmem, clen, 1, xc->f);
            pass_status =
                    (uclen == LZ4_decompress_safe_partial((char *)lz4_cmem, (char *)lz4_ucmem, clen, uclen, uclen));

            if (fstFwrite(lz4_ucmem, uclen, 1, xc->fh) != 1) {
                pass_status = 0;
            }

            free(lz4_ucmem);
            free(lz4_cmem);
        } else /* FST_BL_SKIP */
        {
            pass_status = 0;
            if (xc->fh) {
                fclose(xc->fh);
                xc->fh = NULL; /* needed in case .hier file is missing and there are no hier sections */
            }
        }

        free(mem);
        free(fnam);

        fstReaderFseeko(xc, xc->f, offs_cache, SEEK_SET);
    }

    return (pass_status);
}

int fstReaderIterateHierRewind(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    int pass_status = 0;

    if (xc) {
        pass_status = 1;
        if (!xc->fh) {
            pass_status = fstReaderRecreateHierFile(xc);
        }

        xc->do_rewind = 1;
    }

    return (pass_status);
}

struct fstHier *fstReaderIterateHier(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    int isfeof;
    fstHandle alias;
    char *pnt;
    int ch;

    if (!xc)
        return (NULL);

    if (!xc->fh) {
        if (!fstReaderRecreateHierFile(xc)) {
            return (NULL);
        }
    }

    if (xc->do_rewind) {
        xc->do_rewind = 0;
        xc->current_handle = 0;
        fstReaderFseeko(xc, xc->fh, 0, SEEK_SET);
        clearerr(xc->fh);
    }

    if (!(isfeof = feof(xc->fh))) {
        int tag = fgetc(xc->fh);
        switch (tag) {
        case FST_ST_VCD_SCOPE:
            xc->hier.htyp = FST_HT_SCOPE;
            xc->hier.u.scope.typ = fgetc(xc->fh);
            xc->hier.u.scope.name = pnt = xc->str_scope_nam;
            while ((ch = fgetc(xc->fh))) {
                *(pnt++) = ch;
            }; /* scopename */
            *pnt = 0;
            xc->hier.u.scope.name_length = pnt - xc->hier.u.scope.name;

            xc->hier.u.scope.component = pnt = xc->str_scope_comp;
            while ((ch = fgetc(xc->fh))) {
                *(pnt++) = ch;
            }; /* scopecomp */
            *pnt = 0;
            xc->hier.u.scope.component_length = pnt - xc->hier.u.scope.component;
            break;

        case FST_ST_VCD_UPSCOPE:
            xc->hier.htyp = FST_HT_UPSCOPE;
            break;

        case FST_ST_GEN_ATTRBEGIN:
            xc->hier.htyp = FST_HT_ATTRBEGIN;
            xc->hier.u.attr.typ = fgetc(xc->fh);
            xc->hier.u.attr.subtype = fgetc(xc->fh);
            xc->hier.u.attr.name = pnt = xc->str_scope_nam;
            while ((ch = fgetc(xc->fh))) {
                *(pnt++) = ch;
            }; /* scopename */
            *pnt = 0;
            xc->hier.u.attr.name_length = pnt - xc->hier.u.scope.name;

            xc->hier.u.attr.arg = fstReaderVarint64(xc->fh);

            if (xc->hier.u.attr.typ == FST_AT_MISC) {
                if ((xc->hier.u.attr.subtype == FST_MT_SOURCESTEM) || (xc->hier.u.attr.subtype == FST_MT_SOURCEISTEM)) {
                    int sidx_skiplen_dummy = 0;
                    xc->hier.u.attr.arg_from_name =
                            fstGetVarint64((unsigned char *)xc->str_scope_nam, &sidx_skiplen_dummy);
                }
            }
            break;

        case FST_ST_GEN_ATTREND:
            xc->hier.htyp = FST_HT_ATTREND;
            break;

        case FST_VT_VCD_EVENT:
        case FST_VT_VCD_INTEGER:
        case FST_VT_VCD_PARAMETER:
        case FST_VT_VCD_REAL:
        case FST_VT_VCD_REAL_PARAMETER:
        case FST_VT_VCD_REG:
        case FST_VT_VCD_SUPPLY0:
        case FST_VT_VCD_SUPPLY1:
        case FST_VT_VCD_TIME:
        case FST_VT_VCD_TRI:
        case FST_VT_VCD_TRIAND:
        case FST_VT_VCD_TRIOR:
        case FST_VT_VCD_TRIREG:
        case FST_VT_VCD_TRI0:
        case FST_VT_VCD_TRI1:
        case FST_VT_VCD_WAND:
        case FST_VT_VCD_WIRE:
        case FST_VT_VCD_WOR:
        case FST_VT_VCD_PORT:
        case FST_VT_VCD_SPARRAY:
        case FST_VT_VCD_REALTIME:
        case FST_VT_GEN_STRING:
        case FST_VT_SV_BIT:
        case FST_VT_SV_LOGIC:
        case FST_VT_SV_INT:
        case FST_VT_SV_SHORTINT:
        case FST_VT_SV_LONGINT:
        case FST_VT_SV_BYTE:
        case FST_VT_SV_ENUM:
        case FST_VT_SV_SHORTREAL:
            xc->hier.htyp = FST_HT_VAR;
            xc->hier.u.var.svt_workspace = FST_SVT_NONE;
            xc->hier.u.var.sdt_workspace = FST_SDT_NONE;
            xc->hier.u.var.sxt_workspace = 0;
            xc->hier.u.var.typ = tag;
            xc->hier.u.var.direction = fgetc(xc->fh);
            xc->hier.u.var.name = pnt = xc->str_scope_nam;
            while ((ch = fgetc(xc->fh))) {
                *(pnt++) = ch;
            }; /* varname */
            *pnt = 0;
            xc->hier.u.var.name_length = pnt - xc->hier.u.var.name;
            xc->hier.u.var.length = fstReaderVarint32(xc->fh);
            if (tag == FST_VT_VCD_PORT) {
                xc->hier.u.var.length -= 2; /* removal of delimiting spaces */
                xc->hier.u.var.length /= 3; /* port -> signal size adjust */
            }

            alias = fstReaderVarint32(xc->fh);

            if (!alias) {
                xc->current_handle++;
                xc->hier.u.var.handle = xc->current_handle;
                xc->hier.u.var.is_alias = 0;
            } else {
                xc->hier.u.var.handle = alias;
                xc->hier.u.var.is_alias = 1;
            }

            break;

        default:
            isfeof = 1;
            break;
        }
    }

    return (!isfeof ? &xc->hier : NULL);
}

int fstReaderProcessHier(void *ctx, FILE *fv)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    char *str;
    char *pnt;
    int ch, scopetype;
    int vartype;
    uint32_t len, alias;
    /* uint32_t maxvalpos=0; */
    unsigned int num_signal_dyn = 65536;
    int attrtype, subtype;
    uint64_t attrarg;
    fstHandle maxhandle_scanbuild;

    if (!xc)
        return (0);

    xc->longest_signal_value_len = 32; /* arbitrarily set at 32...this is much longer than an expanded double */

    if (!xc->fh) {
        if (!fstReaderRecreateHierFile(xc)) {
            return (0);
        }
    }

    str = (char *)malloc(FST_ID_NAM_ATTR_SIZ + 1);

    if (fv) {
        char time_dimension[2] = {0, 0};
        int time_scale = 1;

        fprintf(fv, "$date\n\t%s\n$end\n", xc->date);
        fprintf(fv, "$version\n\t%s\n$end\n", xc->version);
        if (xc->timezero)
            fprintf(fv, "$timezero\n\t%" PRId64 "\n$end\n", xc->timezero);

        switch (xc->timescale) {
        case 2:
            time_scale = 100;
            time_dimension[0] = 0;
            break;
        case 1:
            time_scale = 10; /* fallthrough */
        case 0:
            time_dimension[0] = 0;
            break;

        case -1:
            time_scale = 100;
            time_dimension[0] = 'm';
            break;
        case -2:
            time_scale = 10; /* fallthrough */
        case -3:
            time_dimension[0] = 'm';
            break;

        case -4:
            time_scale = 100;
            time_dimension[0] = 'u';
            break;
        case -5:
            time_scale = 10; /* fallthrough */
        case -6:
            time_dimension[0] = 'u';
            break;

        case -10:
            time_scale = 100;
            time_dimension[0] = 'p';
            break;
        case -11:
            time_scale = 10; /* fallthrough */
        case -12:
            time_dimension[0] = 'p';
            break;

        case -13:
            time_scale = 100;
            time_dimension[0] = 'f';
            break;
        case -14:
            time_scale = 10; /* fallthrough */
        case -15:
            time_dimension[0] = 'f';
            break;

        case -16:
            time_scale = 100;
            time_dimension[0] = 'a';
            break;
        case -17:
            time_scale = 10; /* fallthrough */
        case -18:
            time_dimension[0] = 'a';
            break;

        case -19:
            time_scale = 100;
            time_dimension[0] = 'z';
            break;
        case -20:
            time_scale = 10; /* fallthrough */
        case -21:
            time_dimension[0] = 'z';
            break;

        case -7:
            time_scale = 100;
            time_dimension[0] = 'n';
            break;
        case -8:
            time_scale = 10; /* fallthrough */
        case -9:
        default:
            time_dimension[0] = 'n';
            break;
        }

        if (fv)
            fprintf(fv, "$timescale\n\t%d%ss\n$end\n", time_scale, time_dimension);
    }

    xc->maxhandle = 0;
    xc->num_alias = 0;

    free(xc->signal_lens);
    xc->signal_lens = (uint32_t *)malloc(num_signal_dyn * sizeof(uint32_t));

    free(xc->signal_typs);
    xc->signal_typs = (unsigned char *)malloc(num_signal_dyn * sizeof(unsigned char));

    fstReaderFseeko(xc, xc->fh, 0, SEEK_SET);
    while (!feof(xc->fh)) {
        int tag = fgetc(xc->fh);
        switch (tag) {
        case FST_ST_VCD_SCOPE:
            scopetype = fgetc(xc->fh);
            if ((scopetype < FST_ST_MIN) || (scopetype > FST_ST_MAX))
                scopetype = FST_ST_VCD_MODULE;
            pnt = str;
            while ((ch = fgetc(xc->fh))) {
                *(pnt++) = ch;
            }; /* scopename */
            *pnt = 0;
            while (fgetc(xc->fh)) {
            }; /* scopecomp */

            if (fv)
                fprintf(fv, "$scope %s %s $end\n", modtypes[scopetype], str);
            break;

        case FST_ST_VCD_UPSCOPE:
            if (fv)
                fprintf(fv, "$upscope $end\n");
            break;

        case FST_ST_GEN_ATTRBEGIN:
            attrtype = fgetc(xc->fh);
            subtype = fgetc(xc->fh);
            pnt = str;
            while ((ch = fgetc(xc->fh))) {
                *(pnt++) = ch;
            }; /* attrname */
            *pnt = 0;

            if (!str[0]) {
                strcpy(str, "\"\"");
            }

            attrarg = fstReaderVarint64(xc->fh);

            if (fv && xc->use_vcd_extensions) {
                switch (attrtype) {
                case FST_AT_ARRAY:
                    if ((subtype < FST_AR_NONE) || (subtype > FST_AR_MAX))
                        subtype = FST_AR_NONE;
                    fprintf(fv, "$attrbegin %s %s %s %" PRId64 " $end\n", attrtypes[attrtype], arraytypes[subtype], str,
                            attrarg);
                    break;
                case FST_AT_ENUM:
                    if ((subtype < FST_EV_SV_INTEGER) || (subtype > FST_EV_MAX))
                        subtype = FST_EV_SV_INTEGER;
                    fprintf(fv, "$attrbegin %s %s %s %" PRId64 " $end\n", attrtypes[attrtype], enumvaluetypes[subtype],
                            str, attrarg);
                    break;
                case FST_AT_PACK:
                    if ((subtype < FST_PT_NONE) || (subtype > FST_PT_MAX))
                        subtype = FST_PT_NONE;
                    fprintf(fv, "$attrbegin %s %s %s %" PRId64 " $end\n", attrtypes[attrtype], packtypes[subtype], str,
                            attrarg);
                    break;
                case FST_AT_MISC:
                default:
                    attrtype = FST_AT_MISC;
                    if (subtype == FST_MT_COMMENT) {
                        fprintf(fv, "$comment\n\t%s\n$end\n", str);
                    } else {
                        if ((subtype == FST_MT_SOURCESTEM) || (subtype == FST_MT_SOURCEISTEM)) {
                            int sidx_skiplen_dummy = 0;
                            uint64_t sidx = fstGetVarint64((unsigned char *)str, &sidx_skiplen_dummy);

                            fprintf(fv, "$attrbegin %s %02x %" PRId64 " %" PRId64 " $end\n", attrtypes[attrtype],
                                    subtype, sidx, attrarg);
                        } else {
                            fprintf(fv, "$attrbegin %s %02x %s %" PRId64 " $end\n", attrtypes[attrtype], subtype, str,
                                    attrarg);
                        }
                    }
                    break;
                }
            }
            break;

        case FST_ST_GEN_ATTREND:
            if (fv && xc->use_vcd_extensions)
                fprintf(fv, "$attrend $end\n");
            break;

        case FST_VT_VCD_EVENT:
        case FST_VT_VCD_INTEGER:
        case FST_VT_VCD_PARAMETER:
        case FST_VT_VCD_REAL:
        case FST_VT_VCD_REAL_PARAMETER:
        case FST_VT_VCD_REG:
        case FST_VT_VCD_SUPPLY0:
        case FST_VT_VCD_SUPPLY1:
        case FST_VT_VCD_TIME:
        case FST_VT_VCD_TRI:
        case FST_VT_VCD_TRIAND:
        case FST_VT_VCD_TRIOR:
        case FST_VT_VCD_TRIREG:
        case FST_VT_VCD_TRI0:
        case FST_VT_VCD_TRI1:
        case FST_VT_VCD_WAND:
        case FST_VT_VCD_WIRE:
        case FST_VT_VCD_WOR:
        case FST_VT_VCD_PORT:
        case FST_VT_VCD_SPARRAY:
        case FST_VT_VCD_REALTIME:
        case FST_VT_GEN_STRING:
        case FST_VT_SV_BIT:
        case FST_VT_SV_LOGIC:
        case FST_VT_SV_INT:
        case FST_VT_SV_SHORTINT:
        case FST_VT_SV_LONGINT:
        case FST_VT_SV_BYTE:
        case FST_VT_SV_ENUM:
        case FST_VT_SV_SHORTREAL:
            vartype = tag;
            /* vardir = */ fgetc(xc->fh); /* unused in VCD reader, but need to advance read pointer */
            pnt = str;
            while ((ch = fgetc(xc->fh))) {
                *(pnt++) = ch;
            }; /* varname */
            *pnt = 0;
            len = fstReaderVarint32(xc->fh);
            alias = fstReaderVarint32(xc->fh);

            if (!alias) {
                if (xc->maxhandle == num_signal_dyn) {
                    num_signal_dyn *= 2;
                    xc->signal_lens = (uint32_t *)realloc(xc->signal_lens, num_signal_dyn * sizeof(uint32_t));
                    xc->signal_typs = (unsigned char *)realloc(xc->signal_typs, num_signal_dyn * sizeof(unsigned char));
                }
                xc->signal_lens[xc->maxhandle] = len;
                xc->signal_typs[xc->maxhandle] = vartype;

                /* maxvalpos+=len; */
                if (len > xc->longest_signal_value_len) {
                    xc->longest_signal_value_len = len;
                }

                if ((vartype == FST_VT_VCD_REAL) || (vartype == FST_VT_VCD_REAL_PARAMETER) ||
                    (vartype == FST_VT_VCD_REALTIME) || (vartype == FST_VT_SV_SHORTREAL)) {
                    len = (vartype != FST_VT_SV_SHORTREAL) ? 64 : 32;
                    xc->signal_typs[xc->maxhandle] = FST_VT_VCD_REAL;
                }
                if (fv) {
                    char vcdid_buf[16];
                    uint32_t modlen = (vartype != FST_VT_VCD_PORT) ? len : ((len - 2) / 3);
                    fstVcdID(vcdid_buf, xc->maxhandle + 1);
                    fprintf(fv, "$var %s %" PRIu32 " %s %s $end\n", vartypes[vartype], modlen, vcdid_buf, str);
                }
                xc->maxhandle++;
            } else {
                if ((vartype == FST_VT_VCD_REAL) || (vartype == FST_VT_VCD_REAL_PARAMETER) ||
                    (vartype == FST_VT_VCD_REALTIME) || (vartype == FST_VT_SV_SHORTREAL)) {
                    len = (vartype != FST_VT_SV_SHORTREAL) ? 64 : 32;
                    xc->signal_typs[xc->maxhandle] = FST_VT_VCD_REAL;
                }
                if (fv) {
                    char vcdid_buf[16];
                    uint32_t modlen = (vartype != FST_VT_VCD_PORT) ? len : ((len - 2) / 3);
                    fstVcdID(vcdid_buf, alias);
                    fprintf(fv, "$var %s %" PRIu32 " %s %s $end\n", vartypes[vartype], modlen, vcdid_buf, str);
                }
                xc->num_alias++;
            }

            break;

        default:
            break;
        }
    }
    if (fv)
        fprintf(fv, "$enddefinitions $end\n");

    maxhandle_scanbuild = xc->maxhandle ? xc->maxhandle
                                        : 1; /*scan-build warning suppression, in reality we have at least one signal */

    xc->signal_lens = (uint32_t *)realloc(xc->signal_lens, maxhandle_scanbuild * sizeof(uint32_t));
    xc->signal_typs = (unsigned char *)realloc(xc->signal_typs, maxhandle_scanbuild * sizeof(unsigned char));

    free(xc->process_mask);
    xc->process_mask = (unsigned char *)calloc(1, (maxhandle_scanbuild + 7) / 8);

    free(xc->temp_signal_value_buf);
    xc->temp_signal_value_buf = (unsigned char *)malloc(xc->longest_signal_value_len + 1);

    xc->var_count = xc->maxhandle + xc->num_alias;

    free(str);
    return (1);
}

/*
 * reader file open/close functions
 */
int fstReaderInit(struct fstReaderContext *xc)
{
    fst_off_t blkpos = 0;
    fst_off_t endfile;
    uint64_t seclen;
    int sectype;
    uint64_t vc_section_count_actual = 0;
    int hdr_incomplete = 0;
    int hdr_seen = 0;
    int gzread_pass_status = 1;

    sectype = fgetc(xc->f);
    if (sectype == FST_BL_ZWRAPPER) {
        FILE *fcomp;
        fst_off_t offpnt, uclen;
        char gz_membuf[FST_GZIO_LEN];
        gzFile zhandle;
        int zfd;
        int flen = strlen(xc->filename);
        char *hf;

        seclen = fstReaderUint64(xc->f);
        uclen = fstReaderUint64(xc->f);

        if (!seclen)
            return (0); /* not finished compressing, this is a failed read */

        hf = (char *)calloc(1, flen + 16 + 32 + 1);

        sprintf(hf, "%s.upk_%d_%p", xc->filename, getpid(), (void *)xc);
        fcomp = fopen(hf, "w+b");
        if (!fcomp) {
            fcomp = tmpfile_open(&xc->f_nam);
            free(hf);
            hf = NULL;
            if (!fcomp) {
                tmpfile_close(&fcomp, &xc->f_nam);
                return (0);
            }
        }

#if defined(FST_MACOSX)
        setvbuf(fcomp, (char *)NULL, _IONBF, 0); /* keeps gzip from acting weird in tandem with fopen */
#endif

#ifdef __MINGW32__
        setvbuf(fcomp, (char *)NULL, _IONBF, 0); /* keeps gzip from acting weird in tandem with fopen */
        xc->filename_unpacked = hf;
#else
        if (hf) {
            unlink(hf);
            free(hf);
        }
#endif

        fstReaderFseeko(xc, xc->f, 1 + 8 + 8, SEEK_SET);
#ifndef __MINGW32__
        fflush(xc->f);
#endif

        zfd = dup(fileno(xc->f));
	lseek(zfd, ftell(xc->f), SEEK_SET);
        zhandle = gzdopen(zfd, "rb");
        if (zhandle) {
            for (offpnt = 0; offpnt < uclen; offpnt += FST_GZIO_LEN) {
                size_t this_len = ((uclen - offpnt) > FST_GZIO_LEN) ? FST_GZIO_LEN : (uclen - offpnt);
                size_t gzreadlen = gzread(zhandle, gz_membuf, this_len);
                size_t fwlen;

                if (gzreadlen != this_len) {
                    gzread_pass_status = 0;
                    break;
                }
                fwlen = fstFwrite(gz_membuf, this_len, 1, fcomp);
                if (fwlen != 1) {
                    gzread_pass_status = 0;
                    break;
                }
            }
            gzclose(zhandle);
        } else {
            close(zfd);
        }
        fflush(fcomp);
        fclose(xc->f);
        xc->f = fcomp;
    }

    if (gzread_pass_status) {
        fstReaderFseeko(xc, xc->f, 0, SEEK_END);
        endfile = ftello(xc->f);

        while (blkpos < endfile) {
            fstReaderFseeko(xc, xc->f, blkpos, SEEK_SET);

            sectype = fgetc(xc->f);
            seclen = fstReaderUint64(xc->f);

            if (sectype == EOF) {
                break;
            }

            if ((hdr_incomplete) && (!seclen)) {
                break;
            }

            if (!hdr_seen && (sectype != FST_BL_HDR)) {
                break;
            }

            blkpos++;
            if (sectype == FST_BL_HDR) {
                if (!hdr_seen) {
                    int ch;
                    double dcheck;

                    xc->start_time = fstReaderUint64(xc->f);
                    xc->end_time = fstReaderUint64(xc->f);

                    hdr_incomplete = (xc->start_time == 0) && (xc->end_time == 0);

                    fstFread(&dcheck, 8, 1, xc->f);
                    xc->double_endian_match = (dcheck == FST_DOUBLE_ENDTEST);
                    if (!xc->double_endian_match) {
                        union
                        {
                            unsigned char rvs_buf[8];
                            double d;
                        } vu;

                        unsigned char *dcheck_alias = (unsigned char *)&dcheck;
                        int rvs_idx;

                        for (rvs_idx = 0; rvs_idx < 8; rvs_idx++) {
                            vu.rvs_buf[rvs_idx] = dcheck_alias[7 - rvs_idx];
                        }
                        if (vu.d != FST_DOUBLE_ENDTEST) {
                            break; /* either corrupt file or wrong architecture (offset +33 also functions as matchword)
                                    */
                        }
                    }

                    hdr_seen = 1;

                    xc->mem_used_by_writer = fstReaderUint64(xc->f);
                    xc->scope_count = fstReaderUint64(xc->f);
                    xc->var_count = fstReaderUint64(xc->f);
                    xc->maxhandle = fstReaderUint64(xc->f);
                    xc->num_alias = xc->var_count - xc->maxhandle;
                    xc->vc_section_count = fstReaderUint64(xc->f);
                    ch = fgetc(xc->f);
                    xc->timescale = (signed char)ch;
                    fstFread(xc->version, FST_HDR_SIM_VERSION_SIZE, 1, xc->f);
                    xc->version[FST_HDR_SIM_VERSION_SIZE] = 0;
                    fstFread(xc->date, FST_HDR_DATE_SIZE, 1, xc->f);
                    xc->date[FST_HDR_DATE_SIZE] = 0;
                    ch = fgetc(xc->f);
                    xc->filetype = (unsigned char)ch;
                    xc->timezero = fstReaderUint64(xc->f);
                }
            } else if ((sectype == FST_BL_VCDATA) || (sectype == FST_BL_VCDATA_DYN_ALIAS) ||
                       (sectype == FST_BL_VCDATA_DYN_ALIAS2)) {
                if (hdr_incomplete) {
                    uint64_t bt = fstReaderUint64(xc->f);
                    xc->end_time = fstReaderUint64(xc->f);

                    if (!vc_section_count_actual) {
                        xc->start_time = bt;
                    }
                }

                vc_section_count_actual++;
            } else if (sectype == FST_BL_GEOM) {
                if (!hdr_incomplete) {
                    uint64_t clen = seclen - 24;
                    uint64_t uclen = fstReaderUint64(xc->f);
                    unsigned char *ucdata = (unsigned char *)malloc(uclen);
                    unsigned char *pnt = ucdata;
                    unsigned int i;

                    xc->contains_geom_section = 1;
                    xc->maxhandle = fstReaderUint64(xc->f);
                    xc->longest_signal_value_len =
                            32; /* arbitrarily set at 32...this is much longer than an expanded double */

                    free(xc->process_mask);
                    xc->process_mask = (unsigned char *)calloc(1, (xc->maxhandle + 7) / 8);

                    if (clen != uclen) {
                        unsigned char *cdata = (unsigned char *)malloc(clen);
                        unsigned long destlen = uclen;
                        unsigned long sourcelen = clen;
                        int rc;

                        fstFread(cdata, clen, 1, xc->f);
                        rc = uncompress(ucdata, &destlen, cdata, sourcelen);

                        if (rc != Z_OK) {
                            fprintf(stderr, FST_APIMESS "fstReaderInit(), geom uncompress rc = %d, exiting.\n", rc);
                            exit(255);
                        }

                        free(cdata);
                    } else {
                        fstFread(ucdata, uclen, 1, xc->f);
                    }

                    free(xc->signal_lens);
                    xc->signal_lens = (uint32_t *)malloc(sizeof(uint32_t) * xc->maxhandle);
                    free(xc->signal_typs);
                    xc->signal_typs = (unsigned char *)malloc(sizeof(unsigned char) * xc->maxhandle);

                    for (i = 0; i < xc->maxhandle; i++) {
                        int skiplen;
                        uint64_t val = fstGetVarint32(pnt, &skiplen);

                        pnt += skiplen;

                        if (val) {
                            xc->signal_lens[i] = (val != 0xFFFFFFFF) ? val : 0;
                            xc->signal_typs[i] = FST_VT_VCD_WIRE;
                            if (xc->signal_lens[i] > xc->longest_signal_value_len) {
                                xc->longest_signal_value_len = xc->signal_lens[i];
                            }
                        } else {
                            xc->signal_lens[i] = 8; /* backpatch in real */
                            xc->signal_typs[i] = FST_VT_VCD_REAL;
                            /* xc->longest_signal_value_len handled above by overly large init size */
                        }
                    }

                    free(xc->temp_signal_value_buf);
                    xc->temp_signal_value_buf = (unsigned char *)malloc(xc->longest_signal_value_len + 1);

                    free(ucdata);
                }
            } else if (sectype == FST_BL_HIER) {
                xc->contains_hier_section = 1;
                xc->hier_pos = ftello(xc->f);
            } else if (sectype == FST_BL_HIER_LZ4DUO) {
                xc->contains_hier_section_lz4 = 1;
                xc->contains_hier_section_lz4duo = 1;
                xc->hier_pos = ftello(xc->f);
            } else if (sectype == FST_BL_HIER_LZ4) {
                xc->contains_hier_section_lz4 = 1;
                xc->hier_pos = ftello(xc->f);
            } else if (sectype == FST_BL_BLACKOUT) {
                uint32_t i;
                uint64_t cur_bl = 0;
                uint64_t delta;

                xc->num_blackouts = fstReaderVarint32(xc->f);
                free(xc->blackout_times);
                xc->blackout_times = (uint64_t *)calloc(xc->num_blackouts, sizeof(uint64_t));
                free(xc->blackout_activity);
                xc->blackout_activity = (unsigned char *)calloc(xc->num_blackouts, sizeof(unsigned char));

                for (i = 0; i < xc->num_blackouts; i++) {
                    xc->blackout_activity[i] = fgetc(xc->f) != 0;
                    delta = fstReaderVarint64(xc->f);
                    cur_bl += delta;
                    xc->blackout_times[i] = cur_bl;
                }
            }

            blkpos += seclen;
            if (!hdr_seen)
                break;
        }

        if (hdr_seen) {
            if (xc->vc_section_count != vc_section_count_actual) {
                xc->vc_section_count = vc_section_count_actual;
            }

            if (!xc->contains_geom_section) {
                fstReaderProcessHier(xc, NULL); /* recreate signal_lens/signal_typs info */
            }
        }
    }

    return (hdr_seen);
}

void *fstReaderOpenForUtilitiesOnly(void)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)calloc(1, sizeof(struct fstReaderContext));

    return (xc);
}

void *fstReaderOpen(const char *nam)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)calloc(1, sizeof(struct fstReaderContext));

    if ((!nam) || (!(xc->f = fopen(nam, "rb")))) {
        free(xc);
        xc = NULL;
    } else {
        int flen = strlen(nam);
        char *hf = (char *)calloc(1, flen + 6);
        int rc;

#if defined(__MINGW32__) || defined(FST_MACOSX)
        setvbuf(xc->f, (char *)NULL, _IONBF, 0); /* keeps gzip from acting weird in tandem with fopen */
#endif

        memcpy(hf, nam, flen);
        strcpy(hf + flen, ".hier");
        xc->fh = fopen(hf, "rb");

        free(hf);
        xc->filename = strdup(nam);
        rc = fstReaderInit(xc);

        if ((rc) && (xc->vc_section_count) && (xc->maxhandle) &&
            ((xc->fh) || (xc->contains_hier_section || (xc->contains_hier_section_lz4)))) {
            /* more init */
            xc->do_rewind = 1;
        } else {
            fstReaderClose(xc);
            xc = NULL;
        }
    }

    return (xc);
}

static void fstReaderDeallocateRvatData(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    if (xc) {
        free(xc->rvat_chain_mem);
        xc->rvat_chain_mem = NULL;
        free(xc->rvat_frame_data);
        xc->rvat_frame_data = NULL;
        free(xc->rvat_time_table);
        xc->rvat_time_table = NULL;
        free(xc->rvat_chain_table);
        xc->rvat_chain_table = NULL;
        free(xc->rvat_chain_table_lengths);
        xc->rvat_chain_table_lengths = NULL;

        xc->rvat_data_valid = 0;
    }
}

void fstReaderClose(void *ctx)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    if (xc) {
        fstReaderDeallocateScopeData(xc);
        fstReaderDeallocateRvatData(xc);
        free(xc->rvat_sig_offs);
        xc->rvat_sig_offs = NULL;

        free(xc->process_mask);
        xc->process_mask = NULL;
        free(xc->blackout_times);
        xc->blackout_times = NULL;
        free(xc->blackout_activity);
        xc->blackout_activity = NULL;
        free(xc->temp_signal_value_buf);
        xc->temp_signal_value_buf = NULL;
        free(xc->signal_typs);
        xc->signal_typs = NULL;
        free(xc->signal_lens);
        xc->signal_lens = NULL;
        free(xc->filename);
        xc->filename = NULL;

        if (xc->fh) {
            tmpfile_close(&xc->fh, &xc->fh_nam);
        }

        if (xc->f) {
            tmpfile_close(&xc->f, &xc->f_nam);
            if (xc->filename_unpacked) {
                unlink(xc->filename_unpacked);
                free(xc->filename_unpacked);
            }
        }

        free(xc);
    }
}

/*
 * read processing
 */

/* normal read which re-interleaves the value change data */
int fstReaderIterBlocks(void *ctx,
                        void (*value_change_callback)(void *user_callback_data_pointer, uint64_t time, fstHandle facidx,
                                                      const unsigned char *value),
                        void *user_callback_data_pointer, FILE *fv)
{
    return (fstReaderIterBlocks2(ctx, value_change_callback, NULL, user_callback_data_pointer, fv));
}

int fstReaderIterBlocks2(void *ctx,
                         void (*value_change_callback)(void *user_callback_data_pointer, uint64_t time,
                                                       fstHandle facidx, const unsigned char *value),
                         void (*value_change_callback_varlen)(void *user_callback_data_pointer, uint64_t time,
                                                              fstHandle facidx, const unsigned char *value,
                                                              uint32_t len),
                         void *user_callback_data_pointer, FILE *fv)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;

    uint64_t previous_time = UINT64_MAX;
    uint64_t *time_table = NULL;
    uint64_t tsec_nitems;
    unsigned int secnum = 0;
    int blocks_skipped = 0;
    fst_off_t blkpos = 0;
    uint64_t seclen, beg_tim;
    uint64_t end_tim;
    uint64_t frame_uclen, frame_clen, frame_maxhandle, vc_maxhandle;
    fst_off_t vc_start;
    fst_off_t indx_pntr, indx_pos;
    fst_off_t *chain_table = NULL;
    uint32_t *chain_table_lengths = NULL;
    unsigned char *chain_cmem;
    unsigned char *pnt;
    long chain_clen;
    fstHandle idx, pidx = 0, i;
    uint64_t pval;
    uint64_t vc_maxhandle_largest = 0;
    uint64_t tsec_uclen = 0, tsec_clen = 0;
    int sectype;
    uint64_t mem_required_for_traversal;
    unsigned char *mem_for_traversal = NULL;
    uint32_t traversal_mem_offs;
    uint32_t *scatterptr, *headptr, *length_remaining;
    uint32_t cur_blackout = 0;
    int packtype;
    unsigned char *mc_mem = NULL;
    uint32_t mc_mem_len; /* corresponds to largest value encountered in chain_table_lengths[i] */
    int dumpvars_state = 0;

    if (!xc)
        return (0);

    scatterptr = (uint32_t *)calloc(xc->maxhandle, sizeof(uint32_t));
    headptr = (uint32_t *)calloc(xc->maxhandle, sizeof(uint32_t));
    length_remaining = (uint32_t *)calloc(xc->maxhandle, sizeof(uint32_t));

    if (fv) {
#ifndef FST_WRITEX_DISABLE
        fflush(fv);
        setvbuf(fv, (char *)NULL, _IONBF,
                0); /* even buffered IO is slow so disable it and use our own routines that don't need seeking */
        xc->writex_fd = fileno(fv);
#endif
    }

    for (;;) {
        uint32_t *tc_head = NULL;
        traversal_mem_offs = 0;

        fstReaderFseeko(xc, xc->f, blkpos, SEEK_SET);

        sectype = fgetc(xc->f);
        seclen = fstReaderUint64(xc->f);

        if ((sectype == EOF) || (sectype == FST_BL_SKIP)) {
#ifdef FST_DEBUG
            fprintf(stderr, FST_APIMESS "<< EOF >>\n");
#endif
            break;
        }

        blkpos++;
        if ((sectype != FST_BL_VCDATA) && (sectype != FST_BL_VCDATA_DYN_ALIAS) &&
            (sectype != FST_BL_VCDATA_DYN_ALIAS2)) {
            blkpos += seclen;
            continue;
        }

        if (!seclen)
            break;

        beg_tim = fstReaderUint64(xc->f);
        end_tim = fstReaderUint64(xc->f);

        if (xc->limit_range_valid) {
            if (end_tim < xc->limit_range_start) {
                blocks_skipped++;
                blkpos += seclen;
                continue;
            }

            if (beg_tim >
                xc->limit_range_end) /* likely the compare in for(i=0;i<tsec_nitems;i++) below would do this earlier */
            {
                break;
            }
        }

        mem_required_for_traversal = fstReaderUint64(xc->f);
        mem_for_traversal =
                (unsigned char *)malloc(mem_required_for_traversal + 66); /* add in potential fastlz overhead */
#ifdef FST_DEBUG
        fprintf(stderr, FST_APIMESS "sec: %u seclen: %d begtim: %d endtim: %d\n", secnum, (int)seclen, (int)beg_tim,
                (int)end_tim);
        fprintf(stderr, FST_APIMESS "mem_required_for_traversal: %d\n", (int)mem_required_for_traversal);
#endif
        /* process time block */
        {
            unsigned char *ucdata;
            unsigned char *cdata;
            unsigned long destlen /* = tsec_uclen */; /* scan-build */
            unsigned long sourcelen /*= tsec_clen */; /* scan-build */
            int rc;
            unsigned char *tpnt;
            uint64_t tpval;
            unsigned int ti;

            if (fstReaderFseeko(xc, xc->f, blkpos + seclen - 24, SEEK_SET) != 0)
                break;
            tsec_uclen = fstReaderUint64(xc->f);
            tsec_clen = fstReaderUint64(xc->f);
            tsec_nitems = fstReaderUint64(xc->f);
#ifdef FST_DEBUG
            fprintf(stderr, FST_APIMESS "time section unc: %d, com: %d (%d items)\n", (int)tsec_uclen, (int)tsec_clen,
                    (int)tsec_nitems);
#endif
            if (tsec_clen > seclen)
                break; /* corrupted tsec_clen: by definition it can't be larger than size of section */
            ucdata = (unsigned char *)malloc(tsec_uclen);
            if (!ucdata)
                break; /* malloc fail as tsec_uclen out of range from corrupted file */
            destlen = tsec_uclen;
            sourcelen = tsec_clen;

            fstReaderFseeko(xc, xc->f, -24 - ((fst_off_t)tsec_clen), SEEK_CUR);

            if (tsec_uclen != tsec_clen) {
                cdata = (unsigned char *)malloc(tsec_clen);
                fstFread(cdata, tsec_clen, 1, xc->f);

                rc = uncompress(ucdata, &destlen, cdata, sourcelen);

                if (rc != Z_OK) {
                    fprintf(stderr, FST_APIMESS "fstReaderIterBlocks2(), tsec uncompress rc = %d, exiting.\n", rc);
                    exit(255);
                }

                free(cdata);
            } else {
                fstFread(ucdata, tsec_uclen, 1, xc->f);
            }

            free(time_table);
            time_table = (uint64_t *)calloc(tsec_nitems, sizeof(uint64_t));
            tpnt = ucdata;
            tpval = 0;
            for (ti = 0; ti < tsec_nitems; ti++) {
                int skiplen;
                uint64_t val = fstGetVarint64(tpnt, &skiplen);
                tpval = time_table[ti] = tpval + val;
                tpnt += skiplen;
            }

            tc_head = (uint32_t *)calloc(tsec_nitems /* scan-build */ ? tsec_nitems : 1, sizeof(uint32_t));
            free(ucdata);
        }

        fstReaderFseeko(xc, xc->f, blkpos + 32, SEEK_SET);

        frame_uclen = fstReaderVarint64(xc->f);
        frame_clen = fstReaderVarint64(xc->f);
        frame_maxhandle = fstReaderVarint64(xc->f);

        if (secnum == 0) {
            if ((beg_tim != time_table[0]) || (blocks_skipped)) {
                unsigned char *mu = (unsigned char *)malloc(frame_uclen);
                uint32_t sig_offs = 0;

                if (fv) {
                    char wx_buf[32];
                    int wx_len;

                    if (beg_tim) {
                        if (dumpvars_state == 1) {
                            wx_len = sprintf(wx_buf, "$end\n");
                            fstWritex(xc, wx_buf, wx_len);
                            dumpvars_state = 2;
                        }
                        wx_len = sprintf(wx_buf, "#%" PRIu64 "\n", beg_tim);
                        fstWritex(xc, wx_buf, wx_len);
                        if (!dumpvars_state) {
                            wx_len = sprintf(wx_buf, "$dumpvars\n");
                            fstWritex(xc, wx_buf, wx_len);
                            dumpvars_state = 1;
                        }
                    }
                    if ((xc->num_blackouts) && (cur_blackout != xc->num_blackouts)) {
                        if (beg_tim == xc->blackout_times[cur_blackout]) {
                            wx_len = sprintf(wx_buf, "$dump%s $end\n",
                                             (xc->blackout_activity[cur_blackout++]) ? "on" : "off");
                            fstWritex(xc, wx_buf, wx_len);
                        }
                    }
                }

                if (frame_uclen == frame_clen) {
                    fstFread(mu, frame_uclen, 1, xc->f);
                } else {
                    unsigned char *mc = (unsigned char *)malloc(frame_clen);
                    int rc;

                    unsigned long destlen = frame_uclen;
                    unsigned long sourcelen = frame_clen;

                    fstFread(mc, sourcelen, 1, xc->f);
                    rc = uncompress(mu, &destlen, mc, sourcelen);
                    if (rc != Z_OK) {
                        fprintf(stderr, FST_APIMESS "fstReaderIterBlocks2(), frame uncompress rc: %d, exiting.\n", rc);
                        exit(255);
                    }
                    free(mc);
                }

                for (idx = 0; idx < frame_maxhandle; idx++) {
                    int process_idx = idx / 8;
                    int process_bit = idx & 7;

                    if (xc->process_mask[process_idx] & (1 << process_bit)) {
                        if (xc->signal_lens[idx] <= 1) {
                            if (xc->signal_lens[idx] == 1) {
                                unsigned char val = mu[sig_offs];
                                if (value_change_callback) {
                                    xc->temp_signal_value_buf[0] = val;
                                    xc->temp_signal_value_buf[1] = 0;
                                    value_change_callback(user_callback_data_pointer, beg_tim, idx + 1,
                                                          xc->temp_signal_value_buf);
                                } else {
                                    if (fv) {
                                        char vcd_id[16];

                                        int vcdid_len = fstVcdIDForFwrite(vcd_id + 1, idx + 1);
                                        vcd_id[0] = val; /* collapse 3 writes into one I/O call */
                                        vcd_id[vcdid_len + 1] = '\n';
                                        fstWritex(xc, vcd_id, vcdid_len + 2);
                                    }
                                }
                            } else {
                                /* variable-length ("0" length) records have no initial state */
                            }
                        } else {
                            if (xc->signal_typs[idx] != FST_VT_VCD_REAL) {
                                if (value_change_callback) {
                                    memcpy(xc->temp_signal_value_buf, mu + sig_offs, xc->signal_lens[idx]);
                                    xc->temp_signal_value_buf[xc->signal_lens[idx]] = 0;
                                    value_change_callback(user_callback_data_pointer, beg_tim, idx + 1,
                                                          xc->temp_signal_value_buf);
                                } else {
                                    if (fv) {
                                        char vcd_id[16];
                                        int vcdid_len = fstVcdIDForFwrite(vcd_id + 1, idx + 1);

                                        vcd_id[0] = (xc->signal_typs[idx] != FST_VT_VCD_PORT) ? 'b' : 'p';
                                        fstWritex(xc, vcd_id, 1);
                                        fstWritex(xc, mu + sig_offs, xc->signal_lens[idx]);

                                        vcd_id[0] = ' '; /* collapse 3 writes into one I/O call */
                                        vcd_id[vcdid_len + 1] = '\n';
                                        fstWritex(xc, vcd_id, vcdid_len + 2);
                                    }
                                }
                            } else {
                                double d;
                                unsigned char *clone_d;
                                unsigned char *srcdata = mu + sig_offs;

                                if (value_change_callback) {
                                    if (xc->native_doubles_for_cb) {
                                        if (xc->double_endian_match) {
                                            clone_d = srcdata;
                                        } else {
                                            int j;

                                            clone_d = (unsigned char *)&d;
                                            for (j = 0; j < 8; j++) {
                                                clone_d[j] = srcdata[7 - j];
                                            }
                                        }
                                        value_change_callback(user_callback_data_pointer, beg_tim, idx + 1, clone_d);
                                    } else {
                                        clone_d = (unsigned char *)&d;
                                        if (xc->double_endian_match) {
                                            memcpy(clone_d, srcdata, 8);
                                        } else {
                                            int j;

                                            for (j = 0; j < 8; j++) {
                                                clone_d[j] = srcdata[7 - j];
                                            }
                                        }
                                        sprintf((char *)xc->temp_signal_value_buf, "%.16g", d);
                                        value_change_callback(user_callback_data_pointer, beg_tim, idx + 1,
                                                              xc->temp_signal_value_buf);
                                    }
                                } else {
                                    if (fv) {
                                        char vcdid_buf[16];
                                        char wx_buf[64];
                                        int wx_len;

                                        clone_d = (unsigned char *)&d;
                                        if (xc->double_endian_match) {
                                            memcpy(clone_d, srcdata, 8);
                                        } else {
                                            int j;

                                            for (j = 0; j < 8; j++) {
                                                clone_d[j] = srcdata[7 - j];
                                            }
                                        }

                                        fstVcdID(vcdid_buf, idx + 1);
                                        wx_len = sprintf(wx_buf, "r%.16g %s\n", d, vcdid_buf);
                                        fstWritex(xc, wx_buf, wx_len);
                                    }
                                }
                            }
                        }
                    }

                    sig_offs += xc->signal_lens[idx];
                }

                free(mu);
                fstReaderFseeko(xc, xc->f, -((fst_off_t)frame_clen), SEEK_CUR);
            }
        }

        fstReaderFseeko(xc, xc->f, (fst_off_t)frame_clen, SEEK_CUR); /* skip past compressed data */

        vc_maxhandle = fstReaderVarint64(xc->f);
        vc_start = ftello(xc->f); /* points to '!' character */
        packtype = fgetc(xc->f);

#ifdef FST_DEBUG
        fprintf(stderr, FST_APIMESS "frame_uclen: %d, frame_clen: %d, frame_maxhandle: %d\n", (int)frame_uclen,
                (int)frame_clen, (int)frame_maxhandle);
        fprintf(stderr, FST_APIMESS "vc_maxhandle: %d, packtype: %c\n", (int)vc_maxhandle, packtype);
#endif

        indx_pntr = blkpos + seclen - 24 - tsec_clen - 8;
        fstReaderFseeko(xc, xc->f, indx_pntr, SEEK_SET);
        chain_clen = fstReaderUint64(xc->f);
        indx_pos = indx_pntr - chain_clen;
#ifdef FST_DEBUG
        fprintf(stderr, FST_APIMESS "indx_pos: %d (%d bytes)\n", (int)indx_pos, (int)chain_clen);
#endif
        chain_cmem = (unsigned char *)malloc(chain_clen);
        if (!chain_cmem)
            goto block_err;
        fstReaderFseeko(xc, xc->f, indx_pos, SEEK_SET);
        fstFread(chain_cmem, chain_clen, 1, xc->f);

        if (vc_maxhandle > vc_maxhandle_largest) {
            free(chain_table);
            free(chain_table_lengths);

            vc_maxhandle_largest = vc_maxhandle;
            chain_table = (fst_off_t *)calloc((vc_maxhandle + 1), sizeof(fst_off_t));
            chain_table_lengths = (uint32_t *)calloc((vc_maxhandle + 1), sizeof(uint32_t));
        }

        if (!chain_table || !chain_table_lengths)
            goto block_err;

        pnt = chain_cmem;
        idx = 0;
        pval = 0;

        if (sectype == FST_BL_VCDATA_DYN_ALIAS2) {
            uint32_t prev_alias = 0;

            do {
                int skiplen;

                if (*pnt & 0x01) {
                    int64_t shval = fstGetSVarint64(pnt, &skiplen) >> 1;
                    if (shval > 0) {
                        pval = chain_table[idx] = pval + shval;
                        if (idx) {
                            chain_table_lengths[pidx] = pval - chain_table[pidx];
                        }
                        pidx = idx++;
                    } else if (shval < 0) {
                        chain_table[idx] = 0; /* need to explicitly zero as calloc above might not run */
                        chain_table_lengths[idx] = prev_alias =
                                shval; /* because during this loop iter would give stale data! */
                        idx++;
                    } else {
                        chain_table[idx] = 0; /* need to explicitly zero as calloc above might not run */
                        chain_table_lengths[idx] =
                                prev_alias; /* because during this loop iter would give stale data! */
                        idx++;
                    }
                } else {
                    uint64_t val = fstGetVarint32(pnt, &skiplen);

                    fstHandle loopcnt = val >> 1;
                    for (i = 0; i < loopcnt; i++) {
                        chain_table[idx++] = 0;
                    }
                }

                pnt += skiplen;
            } while (pnt != (chain_cmem + chain_clen));
        } else {
            do {
                int skiplen;
                uint64_t val = fstGetVarint32(pnt, &skiplen);

                if (!val) {
                    pnt += skiplen;
                    val = fstGetVarint32(pnt, &skiplen);
                    chain_table[idx] = 0;            /* need to explicitly zero as calloc above might not run */
                    chain_table_lengths[idx] = -val; /* because during this loop iter would give stale data! */
                    idx++;
                } else if (val & 1) {
                    pval = chain_table[idx] = pval + (val >> 1);
                    if (idx) {
                        chain_table_lengths[pidx] = pval - chain_table[pidx];
                    }
                    pidx = idx++;
                } else {
                    fstHandle loopcnt = val >> 1;
                    for (i = 0; i < loopcnt; i++) {
                        chain_table[idx++] = 0;
                    }
                }

                pnt += skiplen;
            } while (pnt != (chain_cmem + chain_clen));
        }

        chain_table[idx] = indx_pos - vc_start;
        chain_table_lengths[pidx] = chain_table[idx] - chain_table[pidx];

        for (i = 0; i < idx; i++) {
            int32_t v32 = chain_table_lengths[i];
            if ((v32 < 0) && (!chain_table[i])) {
                v32 = -v32;
                v32--;
                if (((uint32_t)v32) < i) /* sanity check */
                {
                    chain_table[i] = chain_table[v32];
                    chain_table_lengths[i] = chain_table_lengths[v32];
                }
            }
        }

#ifdef FST_DEBUG
        fprintf(stderr, FST_APIMESS "decompressed chain idx len: %" PRIu32 "\n", idx);
#endif

        mc_mem_len = 16384;
        mc_mem = (unsigned char *)malloc(mc_mem_len); /* buffer for compressed reads */

        /* check compressed VC data */
        if (idx > xc->maxhandle)
            idx = xc->maxhandle;
        for (i = 0; i < idx; i++) {
            if (chain_table[i]) {
                int process_idx = i / 8;
                int process_bit = i & 7;

                if (xc->process_mask[process_idx] & (1 << process_bit)) {
                    int rc = Z_OK;
                    uint32_t val;
                    uint32_t skiplen;
                    uint32_t tdelta;

                    fstReaderFseeko(xc, xc->f, vc_start + chain_table[i], SEEK_SET);
                    val = fstReaderVarint32WithSkip(xc->f, &skiplen);
                    if (val) {
                        unsigned char *mu = mem_for_traversal + traversal_mem_offs; /* uncomp: dst */
                        unsigned char *mc;                                          /* comp:   src */
                        unsigned long destlen = val;
                        unsigned long sourcelen = chain_table_lengths[i];

                        if (mc_mem_len < chain_table_lengths[i]) {
                            free(mc_mem);
                            mc_mem = (unsigned char *)malloc(mc_mem_len = chain_table_lengths[i]);
                        }
                        mc = mc_mem;

                        fstFread(mc, chain_table_lengths[i], 1, xc->f);

                        switch (packtype) {
                        case '4':
                            rc = (destlen == (unsigned long)LZ4_decompress_safe_partial((char *)mc, (char *)mu,
                                                                                        sourcelen, destlen, destlen))
                                         ? Z_OK
                                         : Z_DATA_ERROR;
                            break;
                        case 'F':
                            fastlz_decompress(mc, sourcelen, mu, destlen); /* rc appears unreliable */
                            break;
                        default:
                            rc = uncompress(mu, &destlen, mc, sourcelen);
                            break;
                        }

                        /* data to process is for(j=0;j<destlen;j++) in mu[j] */
                        headptr[i] = traversal_mem_offs;
                        length_remaining[i] = val;
                        traversal_mem_offs += val;
                    } else {
                        int destlen = chain_table_lengths[i] - skiplen;
                        unsigned char *mu = mem_for_traversal + traversal_mem_offs;
                        fstFread(mu, destlen, 1, xc->f);
                        /* data to process is for(j=0;j<destlen;j++) in mu[j] */
                        headptr[i] = traversal_mem_offs;
                        length_remaining[i] = destlen;
                        traversal_mem_offs += destlen;
                    }

                    if (rc != Z_OK) {
                        fprintf(stderr, FST_APIMESS "fstReaderIterBlocks2(), fac: %d clen: %d (rc=%d), exiting.\n",
                                (int)i, (int)val, rc);
                        exit(255);
                    }

                    if (xc->signal_lens[i] == 1) {
                        uint32_t vli = fstGetVarint32NoSkip(mem_for_traversal + headptr[i]);
                        uint32_t shcnt = 2 << (vli & 1);
                        tdelta = vli >> shcnt;
                    } else {
                        uint32_t vli = fstGetVarint32NoSkip(mem_for_traversal + headptr[i]);
                        tdelta = vli >> 1;
                    }

                    scatterptr[i] = tc_head[tdelta];
                    tc_head[tdelta] = i + 1;
                }
            }
        }

        free(mc_mem); /* there is no usage below for this, no real need to clear out mc_mem or mc_mem_len */

        for (i = 0; i < tsec_nitems; i++) {
            uint32_t tdelta;
            int skiplen, skiplen2;
            uint32_t vli;

            if (fv) {
                char wx_buf[32];
                int wx_len;

                if (time_table[i] != previous_time) {
                    if (xc->limit_range_valid) {
                        if (time_table[i] > xc->limit_range_end) {
                            break;
                        }
                    }

                    if (dumpvars_state == 1) {
                        wx_len = sprintf(wx_buf, "$end\n");
                        fstWritex(xc, wx_buf, wx_len);
                        dumpvars_state = 2;
                    }
                    wx_len = sprintf(wx_buf, "#%" PRIu64 "\n", time_table[i]);
                    fstWritex(xc, wx_buf, wx_len);
                    if (!dumpvars_state) {
                        wx_len = sprintf(wx_buf, "$dumpvars\n");
                        fstWritex(xc, wx_buf, wx_len);
                        dumpvars_state = 1;
                    }

                    if ((xc->num_blackouts) && (cur_blackout != xc->num_blackouts)) {
                        if (time_table[i] == xc->blackout_times[cur_blackout]) {
                            wx_len = sprintf(wx_buf, "$dump%s $end\n",
                                             (xc->blackout_activity[cur_blackout++]) ? "on" : "off");
                            fstWritex(xc, wx_buf, wx_len);
                        }
                    }
                    previous_time = time_table[i];
                }
            } else {
                if (time_table[i] != previous_time) {
                    if (xc->limit_range_valid) {
                        if (time_table[i] > xc->limit_range_end) {
                            break;
                        }
                    }
                    previous_time = time_table[i];
                }
            }

            while (tc_head[i]) {
                idx = tc_head[i] - 1;
                vli = fstGetVarint32(mem_for_traversal + headptr[idx], &skiplen);

                if (xc->signal_lens[idx] <= 1) {
                    if (xc->signal_lens[idx] == 1) {
                        unsigned char val;
                        if (!(vli & 1)) {
                            /* tdelta = vli >> 2; */ /* scan-build */
                            val = ((vli >> 1) & 1) | '0';
                        } else {
                            /* tdelta = vli >> 4; */ /* scan-build */
                            val = FST_RCV_STR[((vli >> 1) & 7)];
                        }

                        if (value_change_callback) {
                            xc->temp_signal_value_buf[0] = val;
                            xc->temp_signal_value_buf[1] = 0;
                            value_change_callback(user_callback_data_pointer, time_table[i], idx + 1,
                                                  xc->temp_signal_value_buf);
                        } else {
                            if (fv) {
                                char vcd_id[16];
                                int vcdid_len = fstVcdIDForFwrite(vcd_id + 1, idx + 1);

                                vcd_id[0] = val;
                                vcd_id[vcdid_len + 1] = '\n';
                                fstWritex(xc, vcd_id, vcdid_len + 2);
                            }
                        }
                        headptr[idx] += skiplen;
                        length_remaining[idx] -= skiplen;

                        tc_head[i] = scatterptr[idx];
                        scatterptr[idx] = 0;

                        if (length_remaining[idx]) {
                            int shamt;
                            vli = fstGetVarint32NoSkip(mem_for_traversal + headptr[idx]);
                            shamt = 2 << (vli & 1);
                            tdelta = vli >> shamt;

                            scatterptr[idx] = tc_head[i + tdelta];
                            tc_head[i + tdelta] = idx + 1;
                        }
                    } else {
                        unsigned char *vdata;
                        uint32_t len;

                        vli = fstGetVarint32(mem_for_traversal + headptr[idx], &skiplen);
                        len = fstGetVarint32(mem_for_traversal + headptr[idx] + skiplen, &skiplen2);
                        /* tdelta = vli >> 1; */ /* scan-build */
                        skiplen += skiplen2;
                        vdata = mem_for_traversal + headptr[idx] + skiplen;

                        if (!(vli & 1)) {
                            if (value_change_callback_varlen) {
                                value_change_callback_varlen(user_callback_data_pointer, time_table[i], idx + 1, vdata,
                                                             len);
                            } else {
                                if (fv) {
                                    char vcd_id[16];
                                    int vcdid_len;

                                    vcd_id[0] = 's';
                                    fstWritex(xc, vcd_id, 1);

                                    vcdid_len = fstVcdIDForFwrite(vcd_id + 1, idx + 1);
                                    {
                                        unsigned char *vesc = (unsigned char *)malloc(len * 4 + 1);
                                        int vlen = fstUtilityBinToEsc(vesc, vdata, len);
                                        fstWritex(xc, vesc, vlen);
                                        free(vesc);
                                    }

                                    vcd_id[0] = ' ';
                                    vcd_id[vcdid_len + 1] = '\n';
                                    fstWritex(xc, vcd_id, vcdid_len + 2);
                                }
                            }
                        }

                        skiplen += len;
                        headptr[idx] += skiplen;
                        length_remaining[idx] -= skiplen;

                        tc_head[i] = scatterptr[idx];
                        scatterptr[idx] = 0;

                        if (length_remaining[idx]) {
                            vli = fstGetVarint32NoSkip(mem_for_traversal + headptr[idx]);
                            tdelta = vli >> 1;

                            scatterptr[idx] = tc_head[i + tdelta];
                            tc_head[i + tdelta] = idx + 1;
                        }
                    }
                } else {
                    uint32_t len = xc->signal_lens[idx];
                    unsigned char *vdata;

                    vli = fstGetVarint32(mem_for_traversal + headptr[idx], &skiplen);
                    /* tdelta = vli >> 1; */ /* scan-build */
                    vdata = mem_for_traversal + headptr[idx] + skiplen;

                    if (xc->signal_typs[idx] != FST_VT_VCD_REAL) {
                        if (!(vli & 1)) {
                            int byte = 0;
                            int bit;
                            unsigned int j;

                            for (j = 0; j < len; j++) {
                                unsigned char ch;
                                byte = j / 8;
                                bit = 7 - (j & 7);
                                ch = ((vdata[byte] >> bit) & 1) | '0';
                                xc->temp_signal_value_buf[j] = ch;
                            }
                            xc->temp_signal_value_buf[j] = 0;

                            if (value_change_callback) {
                                value_change_callback(user_callback_data_pointer, time_table[i], idx + 1,
                                                      xc->temp_signal_value_buf);
                            } else {
                                if (fv) {
                                    unsigned char ch_bp = (xc->signal_typs[idx] != FST_VT_VCD_PORT) ? 'b' : 'p';

                                    fstWritex(xc, &ch_bp, 1);
                                    fstWritex(xc, xc->temp_signal_value_buf, len);
                                }
                            }

                            len = byte + 1;
                        } else {
                            if (value_change_callback) {
                                memcpy(xc->temp_signal_value_buf, vdata, len);
                                xc->temp_signal_value_buf[len] = 0;
                                value_change_callback(user_callback_data_pointer, time_table[i], idx + 1,
                                                      xc->temp_signal_value_buf);
                            } else {
                                if (fv) {
                                    unsigned char ch_bp = (xc->signal_typs[idx] != FST_VT_VCD_PORT) ? 'b' : 'p';

                                    fstWritex(xc, &ch_bp, 1);
                                    fstWritex(xc, vdata, len);
                                }
                            }
                        }
                    } else {
                        double d;
                        unsigned char *clone_d /*= (unsigned char *)&d */; /* scan-build */
                        unsigned char buf[8];
                        unsigned char *srcdata;

                        if (!(vli & 1)) /* very rare case, but possible */
                        {
                            int bit;
                            int j;

                            for (j = 0; j < 8; j++) {
                                unsigned char ch;
                                bit = 7 - (j & 7);
                                ch = ((vdata[0] >> bit) & 1) | '0';
                                buf[j] = ch;
                            }

                            len = 1;
                            srcdata = buf;
                        } else {
                            srcdata = vdata;
                        }

                        if (value_change_callback) {
                            if (xc->native_doubles_for_cb) {
                                if (xc->double_endian_match) {
                                    clone_d = srcdata;
                                } else {
                                    int j;

                                    clone_d = (unsigned char *)&d;
                                    for (j = 0; j < 8; j++) {
                                        clone_d[j] = srcdata[7 - j];
                                    }
                                }
                                value_change_callback(user_callback_data_pointer, time_table[i], idx + 1, clone_d);
                            } else {
                                clone_d = (unsigned char *)&d;
                                if (xc->double_endian_match) {
                                    memcpy(clone_d, srcdata, 8);
                                } else {
                                    int j;

                                    for (j = 0; j < 8; j++) {
                                        clone_d[j] = srcdata[7 - j];
                                    }
                                }
                                sprintf((char *)xc->temp_signal_value_buf, "%.16g", d);
                                value_change_callback(user_callback_data_pointer, time_table[i], idx + 1,
                                                      xc->temp_signal_value_buf);
                            }
                        } else {
                            if (fv) {
                                char wx_buf[32];
                                int wx_len;

                                clone_d = (unsigned char *)&d;
                                if (xc->double_endian_match) {
                                    memcpy(clone_d, srcdata, 8);
                                } else {
                                    int j;

                                    for (j = 0; j < 8; j++) {
                                        clone_d[j] = srcdata[7 - j];
                                    }
                                }

                                wx_len = sprintf(wx_buf, "r%.16g", d);
                                fstWritex(xc, wx_buf, wx_len);
                            }
                        }
                    }

                    if (fv) {
                        char vcd_id[16];
                        int vcdid_len = fstVcdIDForFwrite(vcd_id + 1, idx + 1);
                        vcd_id[0] = ' ';
                        vcd_id[vcdid_len + 1] = '\n';
                        fstWritex(xc, vcd_id, vcdid_len + 2);
                    }

                    skiplen += len;
                    headptr[idx] += skiplen;
                    length_remaining[idx] -= skiplen;

                    tc_head[i] = scatterptr[idx];
                    scatterptr[idx] = 0;

                    if (length_remaining[idx]) {
                        vli = fstGetVarint32NoSkip(mem_for_traversal + headptr[idx]);
                        tdelta = vli >> 1;

                        scatterptr[idx] = tc_head[i + tdelta];
                        tc_head[i + tdelta] = idx + 1;
                    }
                }
            }
        }

    block_err:
        free(tc_head);
        free(chain_cmem);
        free(mem_for_traversal);
        mem_for_traversal = NULL;

        secnum++;
        if (secnum == xc->vc_section_count)
            break; /* in case file is growing, keep with original block count */
        blkpos += seclen;
    }

    if (mem_for_traversal)
        free(mem_for_traversal); /* scan-build */
    free(length_remaining);
    free(headptr);
    free(scatterptr);

    if (chain_table)
        free(chain_table);
    if (chain_table_lengths)
        free(chain_table_lengths);

    free(time_table);

#ifndef FST_WRITEX_DISABLE
    if (fv) {
        fstWritex(xc, NULL, 0);
    }
#endif

    return (1);
}

/* rvat functions */

static char *fstExtractRvatDataFromFrame(struct fstReaderContext *xc, fstHandle facidx, char *buf)
{
    if (facidx >= xc->rvat_frame_maxhandle) {
        return (NULL);
    }

    if (xc->signal_lens[facidx] == 1) {
        buf[0] = (char)xc->rvat_frame_data[xc->rvat_sig_offs[facidx]];
        buf[1] = 0;
    } else {
        if (xc->signal_typs[facidx] != FST_VT_VCD_REAL) {
            memcpy(buf, xc->rvat_frame_data + xc->rvat_sig_offs[facidx], xc->signal_lens[facidx]);
            buf[xc->signal_lens[facidx]] = 0;
        } else {
            double d;
            unsigned char *clone_d = (unsigned char *)&d;
            unsigned char *srcdata = xc->rvat_frame_data + xc->rvat_sig_offs[facidx];

            if (xc->double_endian_match) {
                memcpy(clone_d, srcdata, 8);
            } else {
                int j;

                for (j = 0; j < 8; j++) {
                    clone_d[j] = srcdata[7 - j];
                }
            }

            sprintf((char *)buf, "%.16g", d);
        }
    }

    return (buf);
}

char *fstReaderGetValueFromHandleAtTime(void *ctx, uint64_t tim, fstHandle facidx, char *buf)
{
    struct fstReaderContext *xc = (struct fstReaderContext *)ctx;
    fst_off_t blkpos = 0, prev_blkpos;
    uint64_t beg_tim, end_tim, beg_tim2, end_tim2;
    int sectype;
    unsigned int secnum = 0;
    uint64_t seclen;
    uint64_t tsec_uclen = 0, tsec_clen = 0;
    uint64_t tsec_nitems;
    uint64_t frame_uclen, frame_clen;
#ifdef FST_DEBUG
    uint64_t mem_required_for_traversal;
#endif
    fst_off_t indx_pntr, indx_pos;
    long chain_clen;
    unsigned char *chain_cmem;
    unsigned char *pnt;
    fstHandle idx, pidx = 0, i;
    uint64_t pval;

    if ((!xc) || (!facidx) || (facidx > xc->maxhandle) || (!buf) || (!xc->signal_lens[facidx - 1])) {
        return (NULL);
    }

    if (!xc->rvat_sig_offs) {
        uint32_t cur_offs = 0;

        xc->rvat_sig_offs = (uint32_t *)calloc(xc->maxhandle, sizeof(uint32_t));
        for (i = 0; i < xc->maxhandle; i++) {
            xc->rvat_sig_offs[i] = cur_offs;
            cur_offs += xc->signal_lens[i];
        }
    }

    if (xc->rvat_data_valid) {
        if ((xc->rvat_beg_tim <= tim) && (tim <= xc->rvat_end_tim)) {
            goto process_value;
        }

        fstReaderDeallocateRvatData(xc);
    }

    xc->rvat_chain_pos_valid = 0;

    for (;;) {
        fstReaderFseeko(xc, xc->f, (prev_blkpos = blkpos), SEEK_SET);

        sectype = fgetc(xc->f);
        seclen = fstReaderUint64(xc->f);

        if ((sectype == EOF) || (sectype == FST_BL_SKIP) || (!seclen)) {
            return (NULL); /* if this loop exits on break, it's successful */
        }

        blkpos++;
        if ((sectype != FST_BL_VCDATA) && (sectype != FST_BL_VCDATA_DYN_ALIAS) &&
            (sectype != FST_BL_VCDATA_DYN_ALIAS2)) {
            blkpos += seclen;
            continue;
        }

        beg_tim = fstReaderUint64(xc->f);
        end_tim = fstReaderUint64(xc->f);

        if ((beg_tim <= tim) && (tim <= end_tim)) {
            if ((tim == end_tim) && (tim != xc->end_time)) {
                fst_off_t cached_pos = ftello(xc->f);
                fstReaderFseeko(xc, xc->f, blkpos, SEEK_SET);

                sectype = fgetc(xc->f);
                seclen = fstReaderUint64(xc->f);

                beg_tim2 = fstReaderUint64(xc->f);
                end_tim2 = fstReaderUint64(xc->f);

                if (((sectype != FST_BL_VCDATA) && (sectype != FST_BL_VCDATA_DYN_ALIAS) &&
                     (sectype != FST_BL_VCDATA_DYN_ALIAS2)) ||
                    (!seclen) || (beg_tim2 != tim)) {
                    blkpos = prev_blkpos;
                    break;
                }
                beg_tim = beg_tim2;
                end_tim = end_tim2;
                fstReaderFseeko(xc, xc->f, cached_pos, SEEK_SET);
            }
            break;
        }

        blkpos += seclen;
        secnum++;
    }

    xc->rvat_beg_tim = beg_tim;
    xc->rvat_end_tim = end_tim;

#ifdef FST_DEBUG
    mem_required_for_traversal =
#endif
            fstReaderUint64(xc->f);

#ifdef FST_DEBUG
    fprintf(stderr, FST_APIMESS "rvat sec: %u seclen: %d begtim: %d endtim: %d\n", secnum, (int)seclen, (int)beg_tim,
            (int)end_tim);
    fprintf(stderr, FST_APIMESS "mem_required_for_traversal: %d\n", (int)mem_required_for_traversal);
#endif

    /* process time block */
    {
        unsigned char *ucdata;
        unsigned char *cdata;
        unsigned long destlen /* = tsec_uclen */;  /* scan-build */
        unsigned long sourcelen /* = tsec_clen */; /* scan-build */
        int rc;
        unsigned char *tpnt;
        uint64_t tpval;
        unsigned int ti;

        fstReaderFseeko(xc, xc->f, blkpos + seclen - 24, SEEK_SET);
        tsec_uclen = fstReaderUint64(xc->f);
        tsec_clen = fstReaderUint64(xc->f);
        tsec_nitems = fstReaderUint64(xc->f);
#ifdef FST_DEBUG
        fprintf(stderr, FST_APIMESS "time section unc: %d, com: %d (%d items)\n", (int)tsec_uclen, (int)tsec_clen,
                (int)tsec_nitems);
#endif
        ucdata = (unsigned char *)malloc(tsec_uclen);
        destlen = tsec_uclen;
        sourcelen = tsec_clen;

        fstReaderFseeko(xc, xc->f, -24 - ((fst_off_t)tsec_clen), SEEK_CUR);
        if (tsec_uclen != tsec_clen) {
            cdata = (unsigned char *)malloc(tsec_clen);
            fstFread(cdata, tsec_clen, 1, xc->f);

            rc = uncompress(ucdata, &destlen, cdata, sourcelen);

            if (rc != Z_OK) {
                fprintf(stderr, FST_APIMESS "fstReaderGetValueFromHandleAtTime(), tsec uncompress rc = %d, exiting.\n",
                        rc);
                exit(255);
            }

            free(cdata);
        } else {
            fstFread(ucdata, tsec_uclen, 1, xc->f);
        }

        xc->rvat_time_table = (uint64_t *)calloc(tsec_nitems, sizeof(uint64_t));
        tpnt = ucdata;
        tpval = 0;
        for (ti = 0; ti < tsec_nitems; ti++) {
            int skiplen;
            uint64_t val = fstGetVarint64(tpnt, &skiplen);
            tpval = xc->rvat_time_table[ti] = tpval + val;
            tpnt += skiplen;
        }

        free(ucdata);
    }

    fstReaderFseeko(xc, xc->f, blkpos + 32, SEEK_SET);

    frame_uclen = fstReaderVarint64(xc->f);
    frame_clen = fstReaderVarint64(xc->f);
    xc->rvat_frame_maxhandle = fstReaderVarint64(xc->f);
    xc->rvat_frame_data = (unsigned char *)malloc(frame_uclen);

    if (frame_uclen == frame_clen) {
        fstFread(xc->rvat_frame_data, frame_uclen, 1, xc->f);
    } else {
        unsigned char *mc = (unsigned char *)malloc(frame_clen);
        int rc;

        unsigned long destlen = frame_uclen;
        unsigned long sourcelen = frame_clen;

        fstFread(mc, sourcelen, 1, xc->f);
        rc = uncompress(xc->rvat_frame_data, &destlen, mc, sourcelen);
        if (rc != Z_OK) {
            fprintf(stderr, FST_APIMESS "fstReaderGetValueFromHandleAtTime(), frame decompress rc: %d, exiting.\n", rc);
            exit(255);
        }
        free(mc);
    }

    xc->rvat_vc_maxhandle = fstReaderVarint64(xc->f);
    xc->rvat_vc_start = ftello(xc->f); /* points to '!' character */
    xc->rvat_packtype = fgetc(xc->f);

#ifdef FST_DEBUG
    fprintf(stderr, FST_APIMESS "frame_uclen: %d, frame_clen: %d, frame_maxhandle: %d\n", (int)frame_uclen,
            (int)frame_clen, (int)xc->rvat_frame_maxhandle);
    fprintf(stderr, FST_APIMESS "vc_maxhandle: %d\n", (int)xc->rvat_vc_maxhandle);
#endif

    indx_pntr = blkpos + seclen - 24 - tsec_clen - 8;
    fstReaderFseeko(xc, xc->f, indx_pntr, SEEK_SET);
    chain_clen = fstReaderUint64(xc->f);
    indx_pos = indx_pntr - chain_clen;
#ifdef FST_DEBUG
    fprintf(stderr, FST_APIMESS "indx_pos: %d (%d bytes)\n", (int)indx_pos, (int)chain_clen);
#endif
    chain_cmem = (unsigned char *)malloc(chain_clen);
    fstReaderFseeko(xc, xc->f, indx_pos, SEEK_SET);
    fstFread(chain_cmem, chain_clen, 1, xc->f);

    xc->rvat_chain_table = (fst_off_t *)calloc((xc->rvat_vc_maxhandle + 1), sizeof(fst_off_t));
    xc->rvat_chain_table_lengths = (uint32_t *)calloc((xc->rvat_vc_maxhandle + 1), sizeof(uint32_t));

    pnt = chain_cmem;
    idx = 0;
    pval = 0;

    if (sectype == FST_BL_VCDATA_DYN_ALIAS2) {
        uint32_t prev_alias = 0;

        do {
            int skiplen;

            if (*pnt & 0x01) {
                int64_t shval = fstGetSVarint64(pnt, &skiplen) >> 1;
                if (shval > 0) {
                    pval = xc->rvat_chain_table[idx] = pval + shval;
                    if (idx) {
                        xc->rvat_chain_table_lengths[pidx] = pval - xc->rvat_chain_table[pidx];
                    }
                    pidx = idx++;
                } else if (shval < 0) {
                    xc->rvat_chain_table[idx] = 0; /* need to explicitly zero as calloc above might not run */
                    xc->rvat_chain_table_lengths[idx] = prev_alias =
                            shval; /* because during this loop iter would give stale data! */
                    idx++;
                } else {
                    xc->rvat_chain_table[idx] = 0; /* need to explicitly zero as calloc above might not run */
                    xc->rvat_chain_table_lengths[idx] =
                            prev_alias; /* because during this loop iter would give stale data! */
                    idx++;
                }
            } else {
                uint64_t val = fstGetVarint32(pnt, &skiplen);

                fstHandle loopcnt = val >> 1;
                for (i = 0; i < loopcnt; i++) {
                    xc->rvat_chain_table[idx++] = 0;
                }
            }

            pnt += skiplen;
        } while (pnt != (chain_cmem + chain_clen));
    } else {
        do {
            int skiplen;
            uint64_t val = fstGetVarint32(pnt, &skiplen);

            if (!val) {
                pnt += skiplen;
                val = fstGetVarint32(pnt, &skiplen);
                xc->rvat_chain_table[idx] = 0;
                xc->rvat_chain_table_lengths[idx] = -val;
                idx++;
            } else if (val & 1) {
                pval = xc->rvat_chain_table[idx] = pval + (val >> 1);
                if (idx) {
                    xc->rvat_chain_table_lengths[pidx] = pval - xc->rvat_chain_table[pidx];
                }
                pidx = idx++;
            } else {
                fstHandle loopcnt = val >> 1;
                for (i = 0; i < loopcnt; i++) {
                    xc->rvat_chain_table[idx++] = 0;
                }
            }

            pnt += skiplen;
        } while (pnt != (chain_cmem + chain_clen));
    }

    free(chain_cmem);
    xc->rvat_chain_table[idx] = indx_pos - xc->rvat_vc_start;
    xc->rvat_chain_table_lengths[pidx] = xc->rvat_chain_table[idx] - xc->rvat_chain_table[pidx];

    for (i = 0; i < idx; i++) {
        int32_t v32 = xc->rvat_chain_table_lengths[i];
        if ((v32 < 0) && (!xc->rvat_chain_table[i])) {
            v32 = -v32;
            v32--;
            if (((uint32_t)v32) < i) /* sanity check */
            {
                xc->rvat_chain_table[i] = xc->rvat_chain_table[v32];
                xc->rvat_chain_table_lengths[i] = xc->rvat_chain_table_lengths[v32];
            }
        }
    }

#ifdef FST_DEBUG
    fprintf(stderr, FST_APIMESS "decompressed chain idx len: %" PRIu32 "\n", idx);
#endif

    xc->rvat_data_valid = 1;

/* all data at this point is loaded or resident in fst cache, process and return appropriate value */
process_value:
    if (facidx > xc->rvat_vc_maxhandle) {
        return (NULL);
    }

    facidx--; /* scale down for array which starts at zero */

    if (((tim == xc->rvat_beg_tim) && (!xc->rvat_chain_table[facidx])) || (!xc->rvat_chain_table[facidx])) {
        return (fstExtractRvatDataFromFrame(xc, facidx, buf));
    }

    if (facidx != xc->rvat_chain_facidx) {
        if (xc->rvat_chain_mem) {
            free(xc->rvat_chain_mem);
            xc->rvat_chain_mem = NULL;

            xc->rvat_chain_pos_valid = 0;
        }
    }

    if (!xc->rvat_chain_mem) {
        uint32_t skiplen;
        fstReaderFseeko(xc, xc->f, xc->rvat_vc_start + xc->rvat_chain_table[facidx], SEEK_SET);
        xc->rvat_chain_len = fstReaderVarint32WithSkip(xc->f, &skiplen);
        if (xc->rvat_chain_len) {
            unsigned char *mu = (unsigned char *)malloc(xc->rvat_chain_len);
            unsigned char *mc = (unsigned char *)malloc(xc->rvat_chain_table_lengths[facidx]);
            unsigned long destlen = xc->rvat_chain_len;
            unsigned long sourcelen = xc->rvat_chain_table_lengths[facidx];
            int rc = Z_OK;

            fstFread(mc, xc->rvat_chain_table_lengths[facidx], 1, xc->f);

            switch (xc->rvat_packtype) {
            case '4':
                rc = (destlen ==
                      (unsigned long)LZ4_decompress_safe_partial((char *)mc, (char *)mu, sourcelen, destlen, destlen))
                             ? Z_OK
                             : Z_DATA_ERROR;
                break;
            case 'F':
                fastlz_decompress(mc, sourcelen, mu, destlen); /* rc appears unreliable */
                break;
            default:
                rc = uncompress(mu, &destlen, mc, sourcelen);
                break;
            }

            free(mc);

            if (rc != Z_OK) {
                fprintf(stderr,
                        FST_APIMESS "fstReaderGetValueFromHandleAtTime(), rvat decompress clen: %d (rc=%d), exiting.\n",
                        (int)xc->rvat_chain_len, rc);
                exit(255);
            }

            /* data to process is for(j=0;j<destlen;j++) in mu[j] */
            xc->rvat_chain_mem = mu;
        } else {
            int destlen = xc->rvat_chain_table_lengths[facidx] - skiplen;
            unsigned char *mu = (unsigned char *)malloc(xc->rvat_chain_len = destlen);
            fstFread(mu, destlen, 1, xc->f);
            /* data to process is for(j=0;j<destlen;j++) in mu[j] */
            xc->rvat_chain_mem = mu;
        }

        xc->rvat_chain_facidx = facidx;
    }

    /* process value chain here */

    {
        uint32_t tidx = 0, ptidx = 0;
        uint32_t tdelta;
        int skiplen;
        unsigned int iprev = xc->rvat_chain_len;
        uint32_t pvli = 0;
        int pskip = 0;

        if ((xc->rvat_chain_pos_valid) && (tim >= xc->rvat_chain_pos_time)) {
            i = xc->rvat_chain_pos_idx;
            tidx = xc->rvat_chain_pos_tidx;
        } else {
            i = 0;
            tidx = 0;
            xc->rvat_chain_pos_time = xc->rvat_beg_tim;
        }

        if (xc->signal_lens[facidx] == 1) {
            while (i < xc->rvat_chain_len) {
                uint32_t vli = fstGetVarint32(xc->rvat_chain_mem + i, &skiplen);
                uint32_t shcnt = 2 << (vli & 1);
                tdelta = vli >> shcnt;

                if (xc->rvat_time_table[tidx + tdelta] <= tim) {
                    iprev = i;
                    pvli = vli;
                    ptidx = tidx;
                    /* pskip = skiplen; */ /* scan-build */

                    tidx += tdelta;
                    i += skiplen;
                } else {
                    break;
                }
            }
            if (iprev != xc->rvat_chain_len) {
                xc->rvat_chain_pos_tidx = ptidx;
                xc->rvat_chain_pos_idx = iprev;
                xc->rvat_chain_pos_time = tim;
                xc->rvat_chain_pos_valid = 1;

                if (!(pvli & 1)) {
                    buf[0] = ((pvli >> 1) & 1) | '0';
                } else {
                    buf[0] = FST_RCV_STR[((pvli >> 1) & 7)];
                }
                buf[1] = 0;
                return (buf);
            } else {
                return (fstExtractRvatDataFromFrame(xc, facidx, buf));
            }
        } else {
            while (i < xc->rvat_chain_len) {
                uint32_t vli = fstGetVarint32(xc->rvat_chain_mem + i, &skiplen);
                tdelta = vli >> 1;

                if (xc->rvat_time_table[tidx + tdelta] <= tim) {
                    iprev = i;
                    pvli = vli;
                    ptidx = tidx;
                    pskip = skiplen;

                    tidx += tdelta;
                    i += skiplen;

                    if (!(pvli & 1)) {
                        i += ((xc->signal_lens[facidx] + 7) / 8);
                    } else {
                        i += xc->signal_lens[facidx];
                    }
                } else {
                    break;
                }
            }

            if (iprev != xc->rvat_chain_len) {
                unsigned char *vdata = xc->rvat_chain_mem + iprev + pskip;

                xc->rvat_chain_pos_tidx = ptidx;
                xc->rvat_chain_pos_idx = iprev;
                xc->rvat_chain_pos_time = tim;
                xc->rvat_chain_pos_valid = 1;

                if (xc->signal_typs[facidx] != FST_VT_VCD_REAL) {
                    if (!(pvli & 1)) {
                        int byte = 0;
                        int bit;
                        unsigned int j;

                        for (j = 0; j < xc->signal_lens[facidx]; j++) {
                            unsigned char ch;
                            byte = j / 8;
                            bit = 7 - (j & 7);
                            ch = ((vdata[byte] >> bit) & 1) | '0';
                            buf[j] = ch;
                        }
                        buf[j] = 0;

                        return (buf);
                    } else {
                        memcpy(buf, vdata, xc->signal_lens[facidx]);
                        buf[xc->signal_lens[facidx]] = 0;
                        return (buf);
                    }
                } else {
                    double d;
                    unsigned char *clone_d = (unsigned char *)&d;
                    unsigned char bufd[8];
                    unsigned char *srcdata;

                    if (!(pvli & 1)) /* very rare case, but possible */
                    {
                        int bit;
                        int j;

                        for (j = 0; j < 8; j++) {
                            unsigned char ch;
                            bit = 7 - (j & 7);
                            ch = ((vdata[0] >> bit) & 1) | '0';
                            bufd[j] = ch;
                        }

                        srcdata = bufd;
                    } else {
                        srcdata = vdata;
                    }

                    if (xc->double_endian_match) {
                        memcpy(clone_d, srcdata, 8);
                    } else {
                        int j;

                        for (j = 0; j < 8; j++) {
                            clone_d[j] = srcdata[7 - j];
                        }
                    }

                    sprintf(buf, "r%.16g", d);
                    return (buf);
                }
            } else {
                return (fstExtractRvatDataFromFrame(xc, facidx, buf));
            }
        }
    }

    /* return(NULL); */
}

/**********************************************************************/
#ifndef _WAVE_HAVE_JUDY

/***********************/
/***                 ***/
/***  jenkins hash   ***/
/***                 ***/
/***********************/

/*
--------------------------------------------------------------------
mix -- mix 3 32-bit values reversibly.
For every delta with one or two bits set, and the deltas of all three
  high bits or all three low bits, whether the original value of a,b,c
  is almost all zero or is uniformly distributed,
* If mix() is run forward or backward, at least 32 bits in a,b,c
  have at least 1/4 probability of changing.
* If mix() is run forward, every bit of c will change between 1/3 and
  2/3 of the time.  (Well, 22/100 and 78/100 for some 2-bit deltas.)
mix() was built out of 36 single-cycle latency instructions in a
  structure that could supported 2x parallelism, like so:
      a -= b;
      a -= c; x = (c>>13);
      b -= c; a ^= x;
      b -= a; x = (a<<8);
      c -= a; b ^= x;
      c -= b; x = (b>>13);
      ...
  Unfortunately, superscalar Pentiums and Sparcs can't take advantage
  of that parallelism.  They've also turned some of those single-cycle
  latency instructions into multi-cycle latency instructions.  Still,
  this is the fastest good hash I could find.  There were about 2^^68
  to choose from.  I only looked at a billion or so.
--------------------------------------------------------------------
*/
#define mix(a, b, c)                                                                                                   \
    {                                                                                                                  \
        a -= b;                                                                                                        \
        a -= c;                                                                                                        \
        a ^= (c >> 13);                                                                                                \
        b -= c;                                                                                                        \
        b -= a;                                                                                                        \
        b ^= (a << 8);                                                                                                 \
        c -= a;                                                                                                        \
        c -= b;                                                                                                        \
        c ^= (b >> 13);                                                                                                \
        a -= b;                                                                                                        \
        a -= c;                                                                                                        \
        a ^= (c >> 12);                                                                                                \
        b -= c;                                                                                                        \
        b -= a;                                                                                                        \
        b ^= (a << 16);                                                                                                \
        c -= a;                                                                                                        \
        c -= b;                                                                                                        \
        c ^= (b >> 5);                                                                                                 \
        a -= b;                                                                                                        \
        a -= c;                                                                                                        \
        a ^= (c >> 3);                                                                                                 \
        b -= c;                                                                                                        \
        b -= a;                                                                                                        \
        b ^= (a << 10);                                                                                                \
        c -= a;                                                                                                        \
        c -= b;                                                                                                        \
        c ^= (b >> 15);                                                                                                \
    }

/*
--------------------------------------------------------------------
j_hash() -- hash a variable-length key into a 32-bit value
  k       : the key (the unaligned variable-length array of bytes)
  len     : the length of the key, counting by bytes
  initval : can be any 4-byte value
Returns a 32-bit value.  Every bit of the key affects every bit of
the return value.  Every 1-bit and 2-bit delta achieves avalanche.
About 6*len+35 instructions.

The best hash table sizes are powers of 2.  There is no need to do
mod a prime (mod is sooo slow!).  If you need less than 32 bits,
use a bitmask.  For example, if you need only 10 bits, do
  h = (h & hashmask(10));
In which case, the hash table should have hashsize(10) elements.

If you are hashing n strings (uint8_t **)k, do it like this:
  for (i=0, h=0; i<n; ++i) h = hash( k[i], len[i], h);

By Bob Jenkins, 1996.  bob_jenkins@burtleburtle.net.  You may use this
code any way you wish, private, educational, or commercial.  It's free.

See http://burtleburtle.net/bob/hash/evahash.html
Use for hash table lookup, or anything where one collision in 2^^32 is
acceptable.  Do NOT use for cryptographic purposes.
--------------------------------------------------------------------
*/

static uint32_t j_hash(const uint8_t *k, uint32_t length, uint32_t initval)
{
    uint32_t a, b, c, len;

    /* Set up the internal state */
    len = length;
    a = b = 0x9e3779b9; /* the golden ratio; an arbitrary value */
    c = initval;        /* the previous hash value */

    /*---------------------------------------- handle most of the key */
    while (len >= 12) {
        a += (k[0] + ((uint32_t)k[1] << 8) + ((uint32_t)k[2] << 16) + ((uint32_t)k[3] << 24));
        b += (k[4] + ((uint32_t)k[5] << 8) + ((uint32_t)k[6] << 16) + ((uint32_t)k[7] << 24));
        c += (k[8] + ((uint32_t)k[9] << 8) + ((uint32_t)k[10] << 16) + ((uint32_t)k[11] << 24));
        mix(a, b, c);
        k += 12;
        len -= 12;
    }

    /*------------------------------------- handle the last 11 bytes */
    c += length;
    switch (len) /* all the case statements fall through */
    {
    case 11:
        c += ((uint32_t)k[10] << 24); /* fallthrough */
    case 10:
        c += ((uint32_t)k[9] << 16); /* fallthrough */
    case 9:
        c += ((uint32_t)k[8] << 8); /* fallthrough */
                                    /* the first byte of c is reserved for the length */
    case 8:
        b += ((uint32_t)k[7] << 24); /* fallthrough */
    case 7:
        b += ((uint32_t)k[6] << 16); /* fallthrough */
    case 6:
        b += ((uint32_t)k[5] << 8); /* fallthrough */
    case 5:
        b += k[4]; /* fallthrough */
    case 4:
        a += ((uint32_t)k[3] << 24); /* fallthrough */
    case 3:
        a += ((uint32_t)k[2] << 16); /* fallthrough */
    case 2:
        a += ((uint32_t)k[1] << 8); /* fallthrough */
    case 1:
        a += k[0];
        /* case 0: nothing left to add */
    }
    mix(a, b, c);
    /*-------------------------------------------- report the result */
    return (c);
}

/********************************************************************/

/***************************/
/***                     ***/
/***  judy HS emulation  ***/
/***                     ***/
/***************************/

struct collchain_t
{
    struct collchain_t *next;
    void *payload;
    uint32_t fullhash, length;
    unsigned char mem[1];
};

void **JenkinsIns(void *base_i, const unsigned char *mem, uint32_t length, uint32_t hashmask)
{
    struct collchain_t ***base = (struct collchain_t ***)base_i;
    uint32_t hf, h;
    struct collchain_t **ar;
    struct collchain_t *chain, *pchain;

    if (!*base) {
        *base = (struct collchain_t **)calloc(1, (hashmask + 1) * sizeof(void *));
    }
    ar = *base;

    h = (hf = j_hash(mem, length, length)) & hashmask;
    pchain = chain = ar[h];
    while (chain) {
        if ((chain->fullhash == hf) && (chain->length == length) && !memcmp(chain->mem, mem, length)) {
            if (pchain != chain) /* move hit to front */
            {
                pchain->next = chain->next;
                chain->next = ar[h];
                ar[h] = chain;
            }
            return (&(chain->payload));
        }

        pchain = chain;
        chain = chain->next;
    }

    chain = (struct collchain_t *)calloc(1, sizeof(struct collchain_t) + length - 1);
    memcpy(chain->mem, mem, length);
    chain->fullhash = hf;
    chain->length = length;
    chain->next = ar[h];
    ar[h] = chain;
    return (&(chain->payload));
}

void JenkinsFree(void *base_i, uint32_t hashmask)
{
    struct collchain_t ***base = (struct collchain_t ***)base_i;
    uint32_t h;
    struct collchain_t **ar;
    struct collchain_t *chain, *chain_next;

    if (base && *base) {
        ar = *base;
        for (h = 0; h <= hashmask; h++) {
            chain = ar[h];
            while (chain) {
                chain_next = chain->next;
                free(chain);
                chain = chain_next;
            }
        }

        free(*base);
        *base = NULL;
    }
}

#endif

/**********************************************************************/

/************************/
/***                  ***/
/*** utility function ***/
/***                  ***/
/************************/

int fstUtilityBinToEscConvertedLen(const unsigned char *s, int len)
{
    const unsigned char *src = s;
    int dlen = 0;
    int i;

    for (i = 0; i < len; i++) {
        switch (src[i]) {
        case '\a': /* fallthrough */
        case '\b': /* fallthrough */
        case '\f': /* fallthrough */
        case '\n': /* fallthrough */
        case '\r': /* fallthrough */
        case '\t': /* fallthrough */
        case '\v': /* fallthrough */
        case '\'': /* fallthrough */
        case '\"': /* fallthrough */
        case '\\': /* fallthrough */
        case '\?':
            dlen += 2;
            break;
        default:
            if ((src[i] > ' ') && (src[i] <= '~')) /* no white spaces in output */
            {
                dlen++;
            } else {
                dlen += 4;
            }
            break;
        }
    }

    return (dlen);
}

int fstUtilityBinToEsc(unsigned char *d, const unsigned char *s, int len)
{
    const unsigned char *src = s;
    unsigned char *dst = d;
    unsigned char val;
    int i;

    for (i = 0; i < len; i++) {
        switch (src[i]) {
        case '\a':
            *(dst++) = '\\';
            *(dst++) = 'a';
            break;
        case '\b':
            *(dst++) = '\\';
            *(dst++) = 'b';
            break;
        case '\f':
            *(dst++) = '\\';
            *(dst++) = 'f';
            break;
        case '\n':
            *(dst++) = '\\';
            *(dst++) = 'n';
            break;
        case '\r':
            *(dst++) = '\\';
            *(dst++) = 'r';
            break;
        case '\t':
            *(dst++) = '\\';
            *(dst++) = 't';
            break;
        case '\v':
            *(dst++) = '\\';
            *(dst++) = 'v';
            break;
        case '\'':
            *(dst++) = '\\';
            *(dst++) = '\'';
            break;
        case '\"':
            *(dst++) = '\\';
            *(dst++) = '\"';
            break;
        case '\\':
            *(dst++) = '\\';
            *(dst++) = '\\';
            break;
        case '\?':
            *(dst++) = '\\';
            *(dst++) = '\?';
            break;
        default:
            if ((src[i] > ' ') && (src[i] <= '~')) /* no white spaces in output */
            {
                *(dst++) = src[i];
            } else {
                val = src[i];
                *(dst++) = '\\';
                *(dst++) = (val / 64) + '0';
                val = val & 63;
                *(dst++) = (val / 8) + '0';
                val = val & 7;
                *(dst++) = (val) + '0';
            }
            break;
        }
    }

    return (dst - d);
}

/*
 * this overwrites the original string if the destination pointer is NULL
 */
int fstUtilityEscToBin(unsigned char *d, unsigned char *s, int len)
{
    unsigned char *src = s;
    unsigned char *dst = (!d) ? s : (s = d);
    unsigned char val[3];
    int i;

    for (i = 0; i < len; i++) {
        if (src[i] != '\\') {
            *(dst++) = src[i];
        } else {
            switch (src[++i]) {
            case 'a':
                *(dst++) = '\a';
                break;
            case 'b':
                *(dst++) = '\b';
                break;
            case 'f':
                *(dst++) = '\f';
                break;
            case 'n':
                *(dst++) = '\n';
                break;
            case 'r':
                *(dst++) = '\r';
                break;
            case 't':
                *(dst++) = '\t';
                break;
            case 'v':
                *(dst++) = '\v';
                break;
            case '\'':
                *(dst++) = '\'';
                break;
            case '\"':
                *(dst++) = '\"';
                break;
            case '\\':
                *(dst++) = '\\';
                break;
            case '\?':
                *(dst++) = '\?';
                break;

            case 'x':
                val[0] = toupper(src[++i]);
                val[1] = toupper(src[++i]);
                val[0] = ((val[0] >= 'A') && (val[0] <= 'F')) ? (val[0] - 'A' + 10) : (val[0] - '0');
                val[1] = ((val[1] >= 'A') && (val[1] <= 'F')) ? (val[1] - 'A' + 10) : (val[1] - '0');
                *(dst++) = val[0] * 16 + val[1];
                break;

            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
                val[0] = src[i] - '0';
                val[1] = src[++i] - '0';
                val[2] = src[++i] - '0';
                *(dst++) = val[0] * 64 + val[1] * 8 + val[2];
                break;

            default:
                *(dst++) = src[i];
                break;
            }
        }
    }

    return (dst - s);
}

struct fstETab *fstUtilityExtractEnumTableFromString(const char *s)
{
    struct fstETab *et = NULL;
    int num_spaces = 0;
    int i;
    int newlen;

    if (s) {
        const char *csp = strchr(s, ' ');
        int cnt = atoi(csp + 1);

        for (;;) {
            csp = strchr(csp + 1, ' ');
            if (csp) {
                num_spaces++;
            } else {
                break;
            }
        }

        if (num_spaces == (2 * cnt)) {
            char *sp, *sp2;

            et = (struct fstETab *)calloc(1, sizeof(struct fstETab));
            et->elem_count = cnt;
            et->name = strdup(s);
            et->literal_arr = (char **)calloc(cnt, sizeof(char *));
            et->val_arr = (char **)calloc(cnt, sizeof(char *));

            sp = strchr(et->name, ' ');
            *sp = 0;

            sp = strchr(sp + 1, ' ');

            for (i = 0; i < cnt; i++) {
                sp2 = strchr(sp + 1, ' ');
                *(char *)sp2 = 0;
                et->literal_arr[i] = sp + 1;
                sp = sp2;

                newlen = fstUtilityEscToBin(NULL, (unsigned char *)et->literal_arr[i], strlen(et->literal_arr[i]));
                et->literal_arr[i][newlen] = 0;
            }

            for (i = 0; i < cnt; i++) {
                sp2 = strchr(sp + 1, ' ');
                if (sp2) {
                    *sp2 = 0;
                }
                et->val_arr[i] = sp + 1;
                sp = sp2;

                newlen = fstUtilityEscToBin(NULL, (unsigned char *)et->val_arr[i], strlen(et->val_arr[i]));
                et->val_arr[i][newlen] = 0;
            }
        }
    }

    return (et);
}

void fstUtilityFreeEnumTable(struct fstETab *etab)
{
    if (etab) {
        free(etab->literal_arr);
        free(etab->val_arr);
        free(etab->name);
        free(etab);
    }
}
