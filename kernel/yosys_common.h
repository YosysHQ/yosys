/* -*- c++ -*-
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#ifndef YOSYS_COMMON_H
#define YOSYS_COMMON_H

#include <map>
#include <set>
#include <tuple>
#include <vector>
#include <string>
#include <algorithm>
#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <initializer_list>
#include <variant>
#include <optional>
#include <stdexcept>
#include <memory>
#include <cmath>
#include <cstddef>

#include <sstream>
#include <fstream>
#include <istream>
#include <ostream>
#include <iostream>

#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include <limits.h>
#include <sys/stat.h>
#include <errno.h>

#ifdef WITH_PYTHON
#include <Python.h>
#endif

#ifndef _YOSYS_
#  error It looks like you are trying to build Yosys without the config defines set. \
         When building Yosys with a custom make system, make sure you set all the \
         defines the Yosys Makefile would set for your build configuration.
#endif

#define FRIEND_TEST(test_case_name, test_name) \
  friend class test_case_name##_##test_name##_Test

#ifdef YOSYS_ENABLE_TCL
#  include <tcl.h>
#  ifdef YOSYS_MXE_HACKS
extern Tcl_Command Tcl_CreateCommand(Tcl_Interp *interp, const char *cmdName, Tcl_CmdProc *proc, ClientData clientData, Tcl_CmdDeleteProc *deleteProc);
extern Tcl_Interp *Tcl_CreateInterp(void);
extern void Tcl_Preserve(ClientData data);
extern void Tcl_Release(ClientData clientData);
extern int Tcl_InterpDeleted(Tcl_Interp *interp);
extern void Tcl_DeleteInterp(Tcl_Interp *interp);
extern int Tcl_Eval(Tcl_Interp *interp, const char *script);
extern int Tcl_EvalFile(Tcl_Interp *interp, const char *fileName);
extern void Tcl_Finalize(void);
extern int Tcl_GetCommandInfo(Tcl_Interp *interp, const char *cmdName, Tcl_CmdInfo *infoPtr);
extern const char *Tcl_GetStringResult(Tcl_Interp *interp);
extern Tcl_Obj *Tcl_NewStringObj(const char *bytes, int length);
extern Tcl_Obj *Tcl_NewIntObj(int intValue);
extern Tcl_Obj *Tcl_NewListObj(int objc, Tcl_Obj *const objv[]);
extern Tcl_Obj *Tcl_ObjSetVar2(Tcl_Interp *interp, Tcl_Obj *part1Ptr, Tcl_Obj *part2Ptr, Tcl_Obj *newValuePtr, int flags);
#  endif
#  undef CONST
#  undef INLINE
#endif

#ifdef _WIN32
#  undef NOMINMAX
#  define NOMINMAX 1
#  undef YY_NO_UNISTD_H
#  define YY_NO_UNISTD_H 1

#  include <windows.h>
#  include <io.h>
#  include <direct.h>

#  define strtok_r strtok_s
#  define strdup _strdup
#  define snprintf _snprintf
#  define getcwd _getcwd
#  define mkdir _mkdir
#  define popen _popen
#  define pclose _pclose

#  ifndef __MINGW32__
#    define PATH_MAX MAX_PATH
#    define isatty _isatty
#    define fileno _fileno
#  endif

// The following defines conflict with our identifiers:
#  undef CONST
// `wingdi.h` defines a TRANSPARENT macro that conflicts with X(TRANSPARENT) entry in kernel/constids.inc
#  undef TRANSPARENT
#endif

#ifndef PATH_MAX
#  define PATH_MAX 4096
#endif


#define YOSYS_NAMESPACE          Yosys
#define PRIVATE_NAMESPACE_BEGIN  namespace {
#define PRIVATE_NAMESPACE_END    }
#define YOSYS_NAMESPACE_BEGIN    namespace Yosys {
#define YOSYS_NAMESPACE_END      }
#define YOSYS_NAMESPACE_PREFIX   Yosys::
#define USING_YOSYS_NAMESPACE    using namespace Yosys;

#if defined(__GNUC__) || defined(__clang__)
#  define YS_ATTRIBUTE(...) __attribute__((__VA_ARGS__))
#elif defined(_MSC_VER)
#  define YS_ATTRIBUTE(...)
#else
#  define YS_ATTRIBUTE(...)
#endif

#if defined(__GNUC__) || defined(__clang__)
#  define YS_MAYBE_UNUSED __attribute__((__unused__))
#else
#  define YS_MAYBE_UNUSED
#endif

#if __cplusplus >= 201703L
#  define YS_FALLTHROUGH [[fallthrough]];
#else
#  error "C++17 or later compatible compiler is required"
#endif


YOSYS_NAMESPACE_BEGIN

// Note: All headers included in hashlib.h must be included
// outside of YOSYS_NAMESPACE before this or bad things will happen.
#ifdef HASHLIB_H
#  undef HASHLIB_H
#  include "kernel/hashlib.h"
#else
#  include "kernel/hashlib.h"
#  undef HASHLIB_H
#endif


using std::vector;
using std::string;
using std::tuple;
using std::pair;

using std::make_tuple;
using std::make_pair;
using std::get;
using std::min;
using std::max;

// A primitive shared string implementation that does not
// move its .c_str() when the object is copied or moved.
struct shared_str {
	std::shared_ptr<string> content;
	shared_str() { }
	shared_str(string s) { content = std::shared_ptr<string>(new string(s)); }
	shared_str(const char *s) { content = std::shared_ptr<string>(new string(s)); }
	const char *c_str() const { return content->c_str(); }
	const string &str() const { return *content; }
	bool operator==(const shared_str &other) const { return *content == *other.content; }
	unsigned int hash() const { return hashlib::hash_ops<std::string>::hash(*content); }
};

using hashlib::mkhash;
using hashlib::mkhash_init;
using hashlib::mkhash_add;
using hashlib::mkhash_xorshift;
using hashlib::hash_ops;
using hashlib::hash_cstr_ops;
using hashlib::hash_ptr_ops;
using hashlib::hash_obj_ops;
using hashlib::dict;
using hashlib::idict;
using hashlib::pool;
using hashlib::mfp;

namespace RTLIL {
	struct IdString;
	struct Const;
	struct SigBit;
	struct SigSpec;
	struct Wire;
	struct Cell;
	struct Memory;
	struct Process;
	struct Module;
	struct Design;
	struct Monitor;
    struct Selection;
	struct SigChunk;
	enum State : unsigned char;

	typedef std::pair<SigSpec, SigSpec> SigSig;

    namespace ID {}
}

namespace AST {
	struct AstNode;
}

using RTLIL::IdString;
using RTLIL::Const;
using RTLIL::SigBit;
using RTLIL::SigSpec;
using RTLIL::Wire;
using RTLIL::Cell;
using RTLIL::Module;
using RTLIL::Design;

using RTLIL::State;
using RTLIL::SigChunk;
using RTLIL::SigSig;

namespace hashlib {
	template<> struct hash_ops<RTLIL::Wire*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Cell*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Memory*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Process*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Module*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Design*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Monitor*> : hash_obj_ops {};
	template<> struct hash_ops<AST::AstNode*> : hash_obj_ops {};

	template<> struct hash_ops<const RTLIL::Wire*> : hash_obj_ops {};
	template<> struct hash_ops<const RTLIL::Cell*> : hash_obj_ops {};
	template<> struct hash_ops<const RTLIL::Memory*> : hash_obj_ops {};
	template<> struct hash_ops<const RTLIL::Process*> : hash_obj_ops {};
	template<> struct hash_ops<const RTLIL::Module*> : hash_obj_ops {};
	template<> struct hash_ops<const RTLIL::Design*> : hash_obj_ops {};
	template<> struct hash_ops<const RTLIL::Monitor*> : hash_obj_ops {};
	template<> struct hash_ops<const AST::AstNode*> : hash_obj_ops {};
}

void memhasher_on();
void memhasher_off();
void memhasher_do();

extern bool memhasher_active;
inline void memhasher() { if (memhasher_active) memhasher_do(); }

void yosys_banner();
int ceil_log2(int x) YS_ATTRIBUTE(const);

inline std::string vstringf(const char *fmt, va_list ap)
{
        // For the common case of strings shorter than 128, save a heap
        // allocation by using a stack allocated buffer.
        const int kBufSize = 128;
        char buf[kBufSize];
        buf[0] = '\0';
        va_list apc;
        va_copy(apc, ap);
        int n = vsnprintf(buf, kBufSize, fmt, apc);
        va_end(apc);
        if (n < kBufSize)
          return std::string(buf);

        std::string string;
        char *str = NULL;
#if defined(_WIN32 )|| defined(__CYGWIN__)
        int sz = 2 * kBufSize, rc;
        while (1) {
		va_copy(apc, ap);
		str = (char*)realloc(str, sz);
		rc = vsnprintf(str, sz, fmt, apc);
		va_end(apc);
		if (rc >= 0 && rc < sz)
			break;
		sz *= 2;
	}
	if (str != NULL) {
		string = str;
		free(str);
	}
	return string;
#else
        if (vasprintf(&str, fmt, ap) < 0)
          str = NULL;
        if (str != NULL) {
          string = str;
          free(str);
        }
	return string;
#endif
}

std::string stringf(const char *fmt, ...) YS_ATTRIBUTE(format(printf, 1, 2));

inline std::string stringf(const char *fmt, ...)
{
	std::string string;
	va_list ap;

	va_start(ap, fmt);
	string = vstringf(fmt, ap);
	va_end(ap);

	return string;
}

int readsome(std::istream &f, char *s, int n);
std::string next_token(std::string &text, const char *sep = " \t\r\n", bool long_strings = false);
std::vector<std::string> split_tokens(const std::string &text, const char *sep = " \t\r\n");
bool patmatch(const char *pattern, const char *string);
#if !defined(YOSYS_DISABLE_SPAWN)
int run_command(const std::string &command, std::function<void(const std::string&)> process_line = std::function<void(const std::string&)>());
#endif
std::string get_base_tmpdir();
std::string make_temp_file(std::string template_str = get_base_tmpdir() + "/yosys_XXXXXX");
std::string make_temp_dir(std::string template_str = get_base_tmpdir() + "/yosys_XXXXXX");
bool check_file_exists(std::string filename, bool is_exec = false);
bool check_directory_exists(const std::string& dirname);
bool is_absolute_path(std::string filename);
void remove_directory(std::string dirname);
bool create_directory(const std::string& dirname);
std::string escape_filename_spaces(const std::string& filename);

template<typename T> int GetSize(const T &obj) { return obj.size(); }
inline int GetSize(RTLIL::Wire *wire);

extern int autoidx;
extern int yosys_xtrace;

RTLIL::IdString new_id(std::string file, int line, std::string func);
RTLIL::IdString new_id_suffix(std::string file, int line, std::string func, std::string suffix);

#define NEW_ID \
	YOSYS_NAMESPACE_PREFIX new_id(__FILE__, __LINE__, __FUNCTION__)
#define NEW_ID_SUFFIX(suffix) \
	YOSYS_NAMESPACE_PREFIX new_id_suffix(__FILE__, __LINE__, __FUNCTION__, suffix)

// Create a statically allocated IdString object, using for example ID::A or ID($add).
//
// Recipe for Converting old code that is using conversion of strings like ID::A and
// "$add" for creating IdStrings: Run below SED command on the .cc file and then use for
// example "meld foo.cc foo.cc.orig" to manually compile errors, if necessary.
//
//  sed -i.orig -r 's/"\\\\([a-zA-Z0-9_]+)"/ID(\1)/g; s/"(\$[a-zA-Z0-9_]+)"/ID(\1)/g;' <filename>
//
#define ID(_id) ([]() { const char *p = "\\" #_id, *q = p[1] == '$' ? p+1 : p; \
        static const YOSYS_NAMESPACE_PREFIX RTLIL::IdString id(q); return id; })()
namespace ID = RTLIL::ID;

namespace hashlib {
	template<> struct hash_ops<RTLIL::State> : hash_ops<int> {};
}


YOSYS_NAMESPACE_END

#endif
