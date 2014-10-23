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
#include <vector>
#include <string>
#include <algorithm>
#include <functional>
#include <initializer_list>

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

#ifndef _YOSYS_
#  error It looks like you are trying to build Yosys without the config defines set. \
         When building Yosys with a custom make system, make sure you set all the \
         defines the Yosys Makefile would set for your build configuration.
#endif

#ifdef YOSYS_ENABLE_TCL
#  include <tcl.h>
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
#  define PATH_MAX MAX_PATH

#  ifndef __MINGW32__
#    define isatty _isatty
#    define fileno _fileno
#  endif
#endif

#define PRIVATE_NAMESPACE_BEGIN  namespace {
#define PRIVATE_NAMESPACE_END    }
#define YOSYS_NAMESPACE_BEGIN    namespace Yosys {
#define YOSYS_NAMESPACE_END      }
#define YOSYS_NAMESPACE_PREFIX   Yosys::
#define USING_YOSYS_NAMESPACE    using namespace Yosys;

#if __cplusplus >= 201103L
#  define OVERRIDE override
#  define FINAL final
#else
#  define OVERRIDE
#  define FINAL
#endif

#if !defined(__GNUC__) && !defined(__clang__)
#  define __attribute__(...)
#  define _NORETURN_ __declspec(noreturn)
#else
#  define _NORETURN_
#endif

YOSYS_NAMESPACE_BEGIN

namespace RTLIL {
	struct IdString;
	struct SigSpec;
	struct Wire;
	struct Cell;
}

std::string stringf(const char *fmt, ...) __attribute__((format(printf, 1, 2)));
std::string vstringf(const char *fmt, va_list ap);
int readsome(std::istream &f, char *s, int n);
std::string next_token(std::string &text, const char *sep);
bool patmatch(const char *pattern, const char *string);
int run_command(const std::string &command, std::function<void(const std::string&)> process_line = std::function<void(const std::string&)>());
std::string make_temp_file(std::string template_str = "/tmp/yosys_XXXXXX");
std::string make_temp_dir(std::string template_str = "/tmp/yosys_XXXXXX");
bool check_file_exists(std::string filename, bool is_exec = false);
void remove_directory(std::string dirname);

template<typename T> int GetSize(const T &obj) { return obj.size(); }
int GetSize(RTLIL::Wire *wire);

YOSYS_NAMESPACE_END

#include "kernel/log.h"
#include "kernel/rtlil.h"
#include "kernel/register.h"

YOSYS_NAMESPACE_BEGIN

void yosys_setup();
void yosys_shutdown();

#ifdef YOSYS_ENABLE_TCL
Tcl_Interp *yosys_get_tcl_interp();
#endif

extern int autoidx;
extern RTLIL::Design *yosys_design;

RTLIL::IdString new_id(std::string file, int line, std::string func);

#define NEW_ID \
	YOSYS_NAMESPACE_PREFIX new_id(__FILE__, __LINE__, __FUNCTION__)

#define ID(_str) \
	([]() { static YOSYS_NAMESPACE_PREFIX RTLIL::IdString _id(_str); return _id; })()

RTLIL::Design *yosys_get_design();
std::string proc_self_dirname();
std::string proc_share_dirname();
const char *create_prompt(RTLIL::Design *design, int recursion_counter);

void run_frontend(std::string filename, std::string command, RTLIL::Design *design, std::string *backend_command, std::string *from_to_label);
void run_pass(std::string command, RTLIL::Design *design);
void run_backend(std::string filename, std::string command, RTLIL::Design *design);
void shell(RTLIL::Design *design);

// from kernel/version_*.o (cc source generated from Makefile)
extern const char *yosys_version_str;

// from passes/cmds/design.cc
extern std::map<std::string, RTLIL::Design*> saved_designs;
extern std::vector<RTLIL::Design*> pushed_designs;

// from passes/cmds/pluginc.cc
extern std::map<std::string, void*> loaded_plugins;
extern std::map<std::string, std::string> loaded_plugin_aliases;
void load_plugin(std::string filename, std::vector<std::string> aliases);

YOSYS_NAMESPACE_END

#endif
