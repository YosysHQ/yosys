/* -*- c++ -*-
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


// *** NOTE TO THE READER ***
//
// Maybe you have just opened this file in the hope to learn more about the
// Yosys API. Let me congratulate you on this great decision!  ;)
//
// If you want to know how the design is represented by Yosys in the memory,
// you should read "kernel/rtlil.h".
//
// If you want to know how to register a command with Yosys, you could read
// "kernel/register.h", but it would be easier to just look at a simple
// example instead. A simple one would be "passes/cmds/log.cc".
//
// This header is very boring. It just defines some general things that
// belong nowhere else and includes the interesting headers.
//
// Find more information in the "CodingReadme" file.


#ifndef YOSYS_H
#define YOSYS_H

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

#ifdef WITH_PYTHON
#include <Python.h>
#endif

#ifndef _YOSYS_
#  error It looks like you are trying to build Yosys without the config defines set. \
         When building Yosys with a custom make system, make sure you set all the \
         defines the Yosys Makefile would set for your build configuration.
#endif

#ifdef YOSYS_ENABLE_TCL
#  include <tcl.h>
#  ifdef YOSYS_MXE_HACKS
extern Tcl_Command Tcl_CreateCommand(Tcl_Interp *interp, const char *cmdName, Tcl_CmdProc *proc, ClientData clientData, Tcl_CmdDeleteProc *deleteProc);
extern Tcl_Interp *Tcl_CreateInterp(void);
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

#if __cplusplus >= 201103L
#  define YS_OVERRIDE override
#  define YS_FINAL final
#else
#  define YS_OVERRIDE
#  define YS_FINAL
#endif

#if defined(__GNUC__) || defined(__clang__)
#  define YS_ATTRIBUTE(...) __attribute__((__VA_ARGS__))
#  define YS_NORETURN
#elif defined(_MSC_VER)
#  define YS_ATTRIBUTE(...)
#  define YS_NORETURN __declspec(noreturn)
#else
#  define YS_ATTRIBUTE(...)
#  define YS_NORETURN
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
	struct Module;
	struct Design;
	struct Monitor;
	enum State : unsigned char;
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

namespace hashlib {
	template<> struct hash_ops<RTLIL::Wire*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Cell*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Module*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Design*> : hash_obj_ops {};
	template<> struct hash_ops<RTLIL::Monitor*> : hash_obj_ops {};
	template<> struct hash_ops<AST::AstNode*> : hash_obj_ops {};

	template<> struct hash_ops<const RTLIL::Wire*> : hash_obj_ops {};
	template<> struct hash_ops<const RTLIL::Cell*> : hash_obj_ops {};
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
std::string stringf(const char *fmt, ...) YS_ATTRIBUTE(format(printf, 1, 2));
std::string vstringf(const char *fmt, va_list ap);
int readsome(std::istream &f, char *s, int n);
std::string next_token(std::string &text, const char *sep = " \t\r\n", bool long_strings = false);
std::vector<std::string> split_tokens(const std::string &text, const char *sep = " \t\r\n");
bool patmatch(const char *pattern, const char *string);
int run_command(const std::string &command, std::function<void(const std::string&)> process_line = std::function<void(const std::string&)>());
std::string make_temp_file(std::string template_str = "/tmp/yosys_XXXXXX");
std::string make_temp_dir(std::string template_str = "/tmp/yosys_XXXXXX");
bool check_file_exists(std::string filename, bool is_exec = false);
bool is_absolute_path(std::string filename);
void remove_directory(std::string dirname);
std::string escape_filename_spaces(const std::string& filename);

template<typename T> int GetSize(const T &obj) { return obj.size(); }
int GetSize(RTLIL::Wire *wire);

extern int autoidx;
extern int yosys_xtrace;

YOSYS_NAMESPACE_END

#include "kernel/log.h"
#include "kernel/rtlil.h"
#include "kernel/register.h"

YOSYS_NAMESPACE_BEGIN

using RTLIL::State;
using RTLIL::SigChunk;
using RTLIL::SigSig;

namespace hashlib {
	template<> struct hash_ops<RTLIL::State> : hash_ops<int> {};
}

void yosys_setup();

#ifdef WITH_PYTHON
bool yosys_already_setup();
#endif

void yosys_shutdown();

#ifdef YOSYS_ENABLE_TCL
Tcl_Interp *yosys_get_tcl_interp();
#endif

extern RTLIL::Design *yosys_design;

RTLIL::IdString new_id(std::string file, int line, std::string func);

#define NEW_ID \
	YOSYS_NAMESPACE_PREFIX new_id(__FILE__, __LINE__, __FUNCTION__)

// Create a statically allocated IdString object, using for example ID(A) or ID($add).
//
// Recipe for Converting old code that is using conversion of strings like "\\A" and
// "$add" for creating IdStrings: Run below SED command on the .cc file and then use for
// example "meld foo.cc foo.cc.orig" to manually compile errors, if necessary.
//
//  sed -i.orig -r 's/"\\\\([a-zA-Z0-9_]+)"/ID(\1)/g; s/"(\$[a-zA-Z0-9_]+)"/ID(\1)/g;' <filename>
//
#define ID(_id) ([]() { const char *p = "\\" #_id, *q = p[1] == '$' ? p+1 : p; \
        static const YOSYS_NAMESPACE_PREFIX RTLIL::IdString id(q); return id; })()
namespace ID = RTLIL::ID;

RTLIL::Design *yosys_get_design();
std::string proc_self_dirname();
std::string proc_share_dirname();
const char *create_prompt(RTLIL::Design *design, int recursion_counter);
std::vector<std::string> glob_filename(const std::string &filename_pattern);
void rewrite_filename(std::string &filename);

void run_pass(std::string command, RTLIL::Design *design = nullptr);
void run_frontend(std::string filename, std::string command, std::string *backend_command, std::string *from_to_label = nullptr, RTLIL::Design *design = nullptr);
void run_frontend(std::string filename, std::string command, RTLIL::Design *design = nullptr);
void run_backend(std::string filename, std::string command, RTLIL::Design *design = nullptr);
void shell(RTLIL::Design *design);

// journal of all input and output files read (for "yosys -E")
extern std::set<std::string> yosys_input_files, yosys_output_files;

// from kernel/version_*.o (cc source generated from Makefile)
extern const char *yosys_version_str;

// from passes/cmds/design.cc
extern std::map<std::string, RTLIL::Design*> saved_designs;
extern std::vector<RTLIL::Design*> pushed_designs;

// from passes/cmds/pluginc.cc
extern std::map<std::string, void*> loaded_plugins;
#ifdef WITH_PYTHON
extern std::map<std::string, void*> loaded_python_plugins;
#endif
extern std::map<std::string, std::string> loaded_plugin_aliases;
void load_plugin(std::string filename, std::vector<std::string> aliases);

YOSYS_NAMESPACE_END

#endif
