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

#if defined(__has_cpp_attribute) && __has_cpp_attribute(gnu::cold)
#  define YS_COLD [[gnu::cold]]
#else
#  define YS_COLD
#endif

#include "kernel/io.h"

YOSYS_NAMESPACE_BEGIN

// Note: All headers included in hashlib.h must be included
// outside of YOSYS_NAMESPACE before this or bad things will happen.
#ifdef HASHLIB_H
#  error "You've probably included hashlib.h under two namespace paths. Bad idea."
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

using hashlib::Hasher;
using hashlib::run_hash;
using hashlib::hash_ops;
using hashlib::mkhash_xorshift;
using hashlib::dict;
using hashlib::idict;
using hashlib::pool;
using hashlib::mfp;

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
	[[nodiscard]] Hasher hash_into(Hasher h) const {
		h.eat(*content);
		return h;
	}
};

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

template<typename T> int GetSize(const T &obj) { return obj.size(); }
inline int GetSize(RTLIL::Wire *wire);

extern int autoidx;
extern int yosys_xtrace;
extern bool yosys_write_versions;

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


YOSYS_NAMESPACE_END

#endif
