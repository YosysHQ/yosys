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

#ifndef FST_API_H
#define FST_API_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <zlib.h>
#include <inttypes.h>
#if defined(_MSC_VER)
    #include "fst_win_unistd.h"
#else
    #include <unistd.h>
#endif
#include <time.h>

#define FST_RDLOAD "FSTLOAD | "

typedef uint32_t fstHandle;
typedef uint32_t fstEnumHandle;

enum fstWriterPackType {
    FST_WR_PT_ZLIB             = 0,
    FST_WR_PT_FASTLZ           = 1,
    FST_WR_PT_LZ4              = 2
};

enum fstFileType {
    FST_FT_MIN                 = 0,

    FST_FT_VERILOG             = 0,
    FST_FT_VHDL                = 1,
    FST_FT_VERILOG_VHDL        = 2,

    FST_FT_MAX                 = 2
};

enum fstBlockType {
    FST_BL_HDR                 = 0,
    FST_BL_VCDATA              = 1,
    FST_BL_BLACKOUT            = 2,
    FST_BL_GEOM                = 3,
    FST_BL_HIER                = 4,
    FST_BL_VCDATA_DYN_ALIAS    = 5,
    FST_BL_HIER_LZ4            = 6,
    FST_BL_HIER_LZ4DUO         = 7,
    FST_BL_VCDATA_DYN_ALIAS2   = 8,

    FST_BL_ZWRAPPER            = 254,   /* indicates that whole trace is gz wrapped */
    FST_BL_SKIP                = 255    /* used while block is being written */
};

enum fstScopeType {
    FST_ST_MIN                 = 0,

    FST_ST_VCD_MODULE          = 0,
    FST_ST_VCD_TASK            = 1,
    FST_ST_VCD_FUNCTION        = 2,
    FST_ST_VCD_BEGIN           = 3,
    FST_ST_VCD_FORK            = 4,
    FST_ST_VCD_GENERATE        = 5,
    FST_ST_VCD_STRUCT          = 6,
    FST_ST_VCD_UNION           = 7,
    FST_ST_VCD_CLASS           = 8,
    FST_ST_VCD_INTERFACE       = 9,
    FST_ST_VCD_PACKAGE         = 10,
    FST_ST_VCD_PROGRAM         = 11,

    FST_ST_VHDL_ARCHITECTURE   = 12,
    FST_ST_VHDL_PROCEDURE      = 13,
    FST_ST_VHDL_FUNCTION       = 14,
    FST_ST_VHDL_RECORD         = 15,
    FST_ST_VHDL_PROCESS        = 16,
    FST_ST_VHDL_BLOCK          = 17,
    FST_ST_VHDL_FOR_GENERATE   = 18,
    FST_ST_VHDL_IF_GENERATE    = 19,
    FST_ST_VHDL_GENERATE       = 20,
    FST_ST_VHDL_PACKAGE        = 21,

    FST_ST_MAX                 = 21,

    FST_ST_GEN_ATTRBEGIN       = 252,
    FST_ST_GEN_ATTREND         = 253,

    FST_ST_VCD_SCOPE           = 254,
    FST_ST_VCD_UPSCOPE         = 255
};

enum fstVarType {
    FST_VT_MIN                 = 0,     /* start of vartypes */

    FST_VT_VCD_EVENT           = 0,
    FST_VT_VCD_INTEGER         = 1,
    FST_VT_VCD_PARAMETER       = 2,
    FST_VT_VCD_REAL            = 3,
    FST_VT_VCD_REAL_PARAMETER  = 4,
    FST_VT_VCD_REG             = 5,
    FST_VT_VCD_SUPPLY0         = 6,
    FST_VT_VCD_SUPPLY1         = 7,
    FST_VT_VCD_TIME            = 8,
    FST_VT_VCD_TRI             = 9,
    FST_VT_VCD_TRIAND          = 10,
    FST_VT_VCD_TRIOR           = 11,
    FST_VT_VCD_TRIREG          = 12,
    FST_VT_VCD_TRI0            = 13,
    FST_VT_VCD_TRI1            = 14,
    FST_VT_VCD_WAND            = 15,
    FST_VT_VCD_WIRE            = 16,
    FST_VT_VCD_WOR             = 17,
    FST_VT_VCD_PORT            = 18,
    FST_VT_VCD_SPARRAY         = 19,    /* used to define the rownum (index) port for a sparse array */
    FST_VT_VCD_REALTIME        = 20,

    FST_VT_GEN_STRING          = 21,    /* generic string type   (max len is defined dynamically via fstWriterEmitVariableLengthValueChange) */

    FST_VT_SV_BIT              = 22,
    FST_VT_SV_LOGIC            = 23,
    FST_VT_SV_INT              = 24,    /* declare as size = 32 */
    FST_VT_SV_SHORTINT         = 25,    /* declare as size = 16 */
    FST_VT_SV_LONGINT          = 26,    /* declare as size = 64 */
    FST_VT_SV_BYTE             = 27,    /* declare as size = 8  */
    FST_VT_SV_ENUM             = 28,    /* declare as appropriate type range */
    FST_VT_SV_SHORTREAL        = 29,    /* declare and emit same as FST_VT_VCD_REAL (needs to be emitted as double, not a float) */

    FST_VT_MAX                 = 29     /* end of vartypes */
};

enum fstVarDir {
    FST_VD_MIN         = 0,

    FST_VD_IMPLICIT    = 0,
    FST_VD_INPUT       = 1,
    FST_VD_OUTPUT      = 2,
    FST_VD_INOUT       = 3,
    FST_VD_BUFFER      = 4,
    FST_VD_LINKAGE     = 5,

    FST_VD_MAX         = 5
};

enum fstHierType {
    FST_HT_MIN         = 0,

    FST_HT_SCOPE       = 0,
    FST_HT_UPSCOPE     = 1,
    FST_HT_VAR         = 2,
    FST_HT_ATTRBEGIN   = 3,
    FST_HT_ATTREND     = 4,

    /* FST_HT_TREEBEGIN and FST_HT_TREEEND are not yet used by FST but are currently used when fstHier bridges other formats */
    FST_HT_TREEBEGIN   = 5,
    FST_HT_TREEEND     = 6,

    FST_HT_MAX         = 6
};

enum fstAttrType {
    FST_AT_MIN         = 0,

    FST_AT_MISC        = 0,     /* self-contained: does not need matching FST_HT_ATTREND */
    FST_AT_ARRAY       = 1,
    FST_AT_ENUM        = 2,
    FST_AT_PACK        = 3,

    FST_AT_MAX         = 3
};

enum fstMiscType {
    FST_MT_MIN         = 0,

    FST_MT_COMMENT     = 0,     /* use fstWriterSetComment() to emit */
    FST_MT_ENVVAR      = 1,     /* use fstWriterSetEnvVar() to emit */
    FST_MT_SUPVAR      = 2,     /* use fstWriterCreateVar2() to emit */
    FST_MT_PATHNAME    = 3,     /* reserved for fstWriterSetSourceStem() string -> number management */
    FST_MT_SOURCESTEM  = 4,     /* use fstWriterSetSourceStem() to emit */
    FST_MT_SOURCEISTEM = 5,     /* use fstWriterSetSourceInstantiationStem() to emit */
    FST_MT_VALUELIST   = 6,	/* use fstWriterSetValueList() to emit, followed by fstWriterCreateVar*() */
    FST_MT_ENUMTABLE   = 7,	/* use fstWriterCreateEnumTable() and fstWriterEmitEnumTableRef() to emit */
    FST_MT_UNKNOWN     = 8,

    FST_MT_MAX         = 8
};

enum fstArrayType {
    FST_AR_MIN         = 0,

    FST_AR_NONE        = 0,
    FST_AR_UNPACKED    = 1,
    FST_AR_PACKED      = 2,
    FST_AR_SPARSE      = 3,

    FST_AR_MAX         = 3
};

enum fstEnumValueType {
    FST_EV_SV_INTEGER           = 0,
    FST_EV_SV_BIT               = 1,
    FST_EV_SV_LOGIC             = 2,
    FST_EV_SV_INT               = 3,
    FST_EV_SV_SHORTINT          = 4,
    FST_EV_SV_LONGINT           = 5,
    FST_EV_SV_BYTE              = 6,
    FST_EV_SV_UNSIGNED_INTEGER  = 7,
    FST_EV_SV_UNSIGNED_BIT      = 8,
    FST_EV_SV_UNSIGNED_LOGIC    = 9,
    FST_EV_SV_UNSIGNED_INT      = 10,
    FST_EV_SV_UNSIGNED_SHORTINT = 11,
    FST_EV_SV_UNSIGNED_LONGINT  = 12,
    FST_EV_SV_UNSIGNED_BYTE     = 13,

    FST_EV_REG			= 14,
    FST_EV_TIME			= 15,

    FST_EV_MAX                  = 15
};

enum fstPackType {
    FST_PT_NONE          = 0,
    FST_PT_UNPACKED      = 1,
    FST_PT_PACKED        = 2,
    FST_PT_TAGGED_PACKED = 3,

    FST_PT_MAX           = 3
};

enum fstSupplementalVarType {
    FST_SVT_MIN                    = 0,

    FST_SVT_NONE                   = 0,

    FST_SVT_VHDL_SIGNAL            = 1,
    FST_SVT_VHDL_VARIABLE          = 2,
    FST_SVT_VHDL_CONSTANT          = 3,
    FST_SVT_VHDL_FILE              = 4,
    FST_SVT_VHDL_MEMORY            = 5,

    FST_SVT_MAX                    = 5
};

enum fstSupplementalDataType {
    FST_SDT_MIN                    = 0,

    FST_SDT_NONE                   = 0,

    FST_SDT_VHDL_BOOLEAN           = 1,
    FST_SDT_VHDL_BIT               = 2,
    FST_SDT_VHDL_BIT_VECTOR        = 3,
    FST_SDT_VHDL_STD_ULOGIC        = 4,
    FST_SDT_VHDL_STD_ULOGIC_VECTOR = 5,
    FST_SDT_VHDL_STD_LOGIC         = 6,
    FST_SDT_VHDL_STD_LOGIC_VECTOR  = 7,
    FST_SDT_VHDL_UNSIGNED          = 8,
    FST_SDT_VHDL_SIGNED            = 9,
    FST_SDT_VHDL_INTEGER           = 10,
    FST_SDT_VHDL_REAL              = 11,
    FST_SDT_VHDL_NATURAL           = 12,
    FST_SDT_VHDL_POSITIVE          = 13,
    FST_SDT_VHDL_TIME              = 14,
    FST_SDT_VHDL_CHARACTER         = 15,
    FST_SDT_VHDL_STRING            = 16,

    FST_SDT_MAX                    = 16,

    FST_SDT_SVT_SHIFT_COUNT        = 10, /* FST_SVT_* is ORed in by fstWriterCreateVar2() to the left after shifting FST_SDT_SVT_SHIFT_COUNT */
    FST_SDT_ABS_MAX                = ((1<<(FST_SDT_SVT_SHIFT_COUNT))-1)
};


struct fstHier
{
unsigned char htyp;

union {
        /* if htyp == FST_HT_SCOPE */
        struct fstHierScope {
                unsigned char typ; /* FST_ST_MIN ... FST_ST_MAX */
                const char *name;
                const char *component;
                uint32_t name_length;           /* strlen(u.scope.name) */
                uint32_t component_length;      /* strlen(u.scope.component) */
                } scope;

        /* if htyp == FST_HT_VAR */
        struct fstHierVar {
                unsigned char typ; /* FST_VT_MIN ... FST_VT_MAX */
                unsigned char direction; /* FST_VD_MIN ... FST_VD_MAX */
                unsigned char svt_workspace; /* zeroed out by FST reader, for client code use */
                unsigned char sdt_workspace; /* zeroed out by FST reader, for client code use */
                unsigned int  sxt_workspace; /* zeroed out by FST reader, for client code use */
                const char *name;
                uint32_t length;
                fstHandle handle;
                uint32_t name_length; /* strlen(u.var.name) */
                unsigned is_alias : 1;
                } var;

        /* if htyp == FST_HT_ATTRBEGIN */
        struct fstHierAttr {
                unsigned char typ; /* FST_AT_MIN ... FST_AT_MAX */
                unsigned char subtype; /* from fstMiscType, fstArrayType, fstEnumValueType, fstPackType */
                const char *name;
                uint64_t arg; /* number of array elements, struct members, or some other payload (possibly ignored) */
                uint64_t arg_from_name; /* for when name is overloaded as a variable-length integer (FST_AT_MISC + FST_MT_SOURCESTEM) */
                uint32_t name_length; /* strlen(u.attr.name) */
                } attr;
        } u;
};


struct fstETab
{
char *name;
uint32_t elem_count;
char **literal_arr;
char **val_arr;
};


/*
 * writer functions
 */
void            fstWriterClose(void *ctx);
void *          fstWriterCreate(const char *nam, int use_compressed_hier);
fstEnumHandle   fstWriterCreateEnumTable(void *ctx, const char *name, uint32_t elem_count, unsigned int min_valbits, const char **literal_arr, const char **val_arr);
                /* used for Verilog/SV */
fstHandle       fstWriterCreateVar(void *ctx, enum fstVarType vt, enum fstVarDir vd,
                        uint32_t len, const char *nam, fstHandle aliasHandle);
                /* future expansion for VHDL and other languages.  The variable type, data type, etc map onto
                   the current Verilog/SV one.  The "type" string is optional for a more verbose or custom description */
fstHandle       fstWriterCreateVar2(void *ctx, enum fstVarType vt, enum fstVarDir vd,
                        uint32_t len, const char *nam, fstHandle aliasHandle,
                        const char *type, enum fstSupplementalVarType svt, enum fstSupplementalDataType sdt);
void            fstWriterEmitDumpActive(void *ctx, int enable);
void 		fstWriterEmitEnumTableRef(void *ctx, fstEnumHandle handle);
void            fstWriterEmitValueChange(void *ctx, fstHandle handle, const void *val);
void            fstWriterEmitValueChange32(void *ctx, fstHandle handle,
                        uint32_t bits, uint32_t val);
void            fstWriterEmitValueChange64(void *ctx, fstHandle handle,
                        uint32_t bits, uint64_t val);
void            fstWriterEmitValueChangeVec32(void *ctx, fstHandle handle,
                        uint32_t bits, const uint32_t *val);
void            fstWriterEmitValueChangeVec64(void *ctx, fstHandle handle,
                        uint32_t bits, const uint64_t *val);
void            fstWriterEmitVariableLengthValueChange(void *ctx, fstHandle handle, const void *val, uint32_t len);
void            fstWriterEmitTimeChange(void *ctx, uint64_t tim);
void            fstWriterFlushContext(void *ctx);
int             fstWriterGetDumpSizeLimitReached(void *ctx);
int             fstWriterGetFseekFailed(void *ctx);
void            fstWriterSetAttrBegin(void *ctx, enum fstAttrType attrtype, int subtype,
                        const char *attrname, uint64_t arg);
void            fstWriterSetAttrEnd(void *ctx);
void            fstWriterSetComment(void *ctx, const char *comm);
void            fstWriterSetDate(void *ctx, const char *dat);
void            fstWriterSetDumpSizeLimit(void *ctx, uint64_t numbytes);
void            fstWriterSetEnvVar(void *ctx, const char *envvar);
void            fstWriterSetFileType(void *ctx, enum fstFileType filetype);
void            fstWriterSetPackType(void *ctx, enum fstWriterPackType typ);
void            fstWriterSetParallelMode(void *ctx, int enable);
void            fstWriterSetRepackOnClose(void *ctx, int enable);       /* type = 0 (none), 1 (libz) */
void            fstWriterSetScope(void *ctx, enum fstScopeType scopetype,
                        const char *scopename, const char *scopecomp);
void            fstWriterSetSourceInstantiationStem(void *ctx, const char *path, unsigned int line, unsigned int use_realpath);
void            fstWriterSetSourceStem(void *ctx, const char *path, unsigned int line, unsigned int use_realpath);
void            fstWriterSetTimescale(void *ctx, int ts);
void            fstWriterSetTimescaleFromString(void *ctx, const char *s);
void            fstWriterSetTimezero(void *ctx, int64_t tim);
void            fstWriterSetUpscope(void *ctx);
void		fstWriterSetValueList(void *ctx, const char *vl);
void            fstWriterSetVersion(void *ctx, const char *vers);


/*
 * reader functions
 */
void            fstReaderClose(void *ctx);
void            fstReaderClrFacProcessMask(void *ctx, fstHandle facidx);
void            fstReaderClrFacProcessMaskAll(void *ctx);
uint64_t        fstReaderGetAliasCount(void *ctx);
const char *    fstReaderGetCurrentFlatScope(void *ctx);
void *          fstReaderGetCurrentScopeUserInfo(void *ctx);
int             fstReaderGetCurrentScopeLen(void *ctx);
const char *    fstReaderGetDateString(void *ctx);
int             fstReaderGetDoubleEndianMatchState(void *ctx);
uint64_t        fstReaderGetDumpActivityChangeTime(void *ctx, uint32_t idx);
unsigned char   fstReaderGetDumpActivityChangeValue(void *ctx, uint32_t idx);
uint64_t        fstReaderGetEndTime(void *ctx);
int             fstReaderGetFacProcessMask(void *ctx, fstHandle facidx);
int             fstReaderGetFileType(void *ctx);
int             fstReaderGetFseekFailed(void *ctx);
fstHandle       fstReaderGetMaxHandle(void *ctx);
uint64_t        fstReaderGetMemoryUsedByWriter(void *ctx);
uint32_t        fstReaderGetNumberDumpActivityChanges(void *ctx);
uint64_t        fstReaderGetScopeCount(void *ctx);
uint64_t        fstReaderGetStartTime(void *ctx);
signed char     fstReaderGetTimescale(void *ctx);
int64_t         fstReaderGetTimezero(void *ctx);
uint64_t        fstReaderGetValueChangeSectionCount(void *ctx);
char *          fstReaderGetValueFromHandleAtTime(void *ctx, uint64_t tim, fstHandle facidx, char *buf);
uint64_t        fstReaderGetVarCount(void *ctx);
const char *    fstReaderGetVersionString(void *ctx);
struct fstHier *fstReaderIterateHier(void *ctx);
int             fstReaderIterateHierRewind(void *ctx);
int             fstReaderIterBlocks(void *ctx,
                        void (*value_change_callback)(void *user_callback_data_pointer, uint64_t time, fstHandle facidx, const unsigned char *value),
                        void *user_callback_data_pointer, FILE *vcdhandle);
int             fstReaderIterBlocks2(void *ctx,
                        void (*value_change_callback)(void *user_callback_data_pointer, uint64_t time, fstHandle facidx, const unsigned char *value),
                        void (*value_change_callback_varlen)(void *user_callback_data_pointer, uint64_t time, fstHandle facidx, const unsigned char *value, uint32_t len),
                        void *user_callback_data_pointer, FILE *vcdhandle);
void            fstReaderIterBlocksSetNativeDoublesOnCallback(void *ctx, int enable);
void *          fstReaderOpen(const char *nam);
void *          fstReaderOpenForUtilitiesOnly(void);
const char *    fstReaderPopScope(void *ctx);
int             fstReaderProcessHier(void *ctx, FILE *vcdhandle);
const char *    fstReaderPushScope(void *ctx, const char *nam, void *user_info);
void            fstReaderResetScope(void *ctx);
void            fstReaderSetFacProcessMask(void *ctx, fstHandle facidx);
void            fstReaderSetFacProcessMaskAll(void *ctx);
void            fstReaderSetLimitTimeRange(void *ctx, uint64_t start_time, uint64_t end_time);
void            fstReaderSetUnlimitedTimeRange(void *ctx);
void            fstReaderSetVcdExtensions(void *ctx, int enable);


/*
 * utility functions
 */
int             fstUtilityBinToEscConvertedLen(const unsigned char *s, int len); /* used for mallocs for fstUtilityBinToEsc() */
int             fstUtilityBinToEsc(unsigned char *d, const unsigned char *s, int len);
int             fstUtilityEscToBin(unsigned char *d, unsigned char *s, int len);
struct fstETab *fstUtilityExtractEnumTableFromString(const char *s);
void 		fstUtilityFreeEnumTable(struct fstETab *etab); /* must use to free fstETab properly */


#ifdef __cplusplus
}
#endif

#endif
