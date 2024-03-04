/*
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

#include "kernel/yosys.h"
#include "kernel/celltypes.h"

#ifdef YOSYS_ENABLE_READLINE
#  include <readline/readline.h>
#  include <readline/history.h>
#endif

#ifdef YOSYS_ENABLE_EDITLINE
#  include <editline/readline.h>
#endif

#ifdef YOSYS_ENABLE_PLUGINS
#  include <dlfcn.h>
#endif

#if defined(_WIN32)
#  include <windows.h>
#  include <io.h>
#elif defined(__APPLE__)
#  include <mach-o/dyld.h>
#  include <unistd.h>
#  include <dirent.h>
#  include <sys/stat.h>
#else
#  include <unistd.h>
#  include <dirent.h>
#  include <sys/types.h>
#  include <sys/stat.h>
#  if !defined(YOSYS_DISABLE_SPAWN)
#    include <sys/wait.h>
#  endif
#endif

#if !defined(_WIN32) && defined(YOSYS_ENABLE_GLOB)
#  include <glob.h>
#endif

#if defined(__FreeBSD__) || defined(__NetBSD__)
#  include <sys/sysctl.h>
#endif

#ifdef WITH_PYTHON
#if PY_MAJOR_VERSION >= 3
#   define INIT_MODULE PyInit_libyosys
    extern "C" PyObject* INIT_MODULE();
#else
#   define INIT_MODULE initlibyosys
	extern "C" void INIT_MODULE();
#endif
#include <signal.h>
#endif

#include <limits.h>
#include <errno.h>

#include "libs/json11/json11.hpp"

YOSYS_NAMESPACE_BEGIN

int autoidx = 1;
int yosys_xtrace = 0;
RTLIL::Design *yosys_design = NULL;
CellTypes yosys_celltypes;

#ifdef YOSYS_ENABLE_TCL
Tcl_Interp *yosys_tcl_interp = NULL;
bool yosys_tcl_repl_active = false;
#endif

std::set<std::string> yosys_input_files, yosys_output_files;

bool memhasher_active = false;
uint32_t memhasher_rng = 123456;
std::vector<void*> memhasher_store;

std::string yosys_share_dirname;
std::string yosys_abc_executable;

void init_share_dirname();
void init_abc_executable_name();

void memhasher_on()
{
#if defined(__linux__) || defined(__FreeBSD__)
	memhasher_rng += time(NULL) << 16 ^ getpid();
#endif
	memhasher_store.resize(0x10000);
	memhasher_active = true;
}

void memhasher_off()
{
	for (auto p : memhasher_store)
		if (p) free(p);
	memhasher_store.clear();
	memhasher_active = false;
}

void memhasher_do()
{
	memhasher_rng ^= memhasher_rng << 13;
	memhasher_rng ^= memhasher_rng >> 17;
	memhasher_rng ^= memhasher_rng << 5;

	int size, index = (memhasher_rng >> 4) & 0xffff;
	switch (memhasher_rng & 7) {
		case 0: size =   16; break;
		case 1: size =  256; break;
		case 2: size = 1024; break;
		case 3: size = 4096; break;
		default: size = 0;
	}
	if (index < 16) size *= 16;
	memhasher_store[index] = realloc(memhasher_store[index], size);
}

void yosys_banner()
{
	log("\n");
	log(" /----------------------------------------------------------------------------\\\n");
	log(" |  yosys -- Yosys Open SYnthesis Suite                                       |\n");
	log(" |  Copyright (C) 2012 - 2024  Claire Xenia Wolf <claire@yosyshq.com>         |\n");
	log(" |  Distributed under an ISC-like license, type \"license\" to see terms        |\n");
	log(" \\----------------------------------------------------------------------------/\n");
	log(" %s\n", yosys_version_str);
}

int ceil_log2(int x)
{
#if defined(__GNUC__)
        return x > 1 ? (8*sizeof(int)) - __builtin_clz(x-1) : 0;
#else
	if (x <= 0)
		return 0;
	for (int i = 0; i < 32; i++)
		if (((x-1) >> i) == 0)
			return i;
	log_abort();
#endif
}

int readsome(std::istream &f, char *s, int n)
{
	int rc = int(f.readsome(s, n));

	// f.readsome() sometimes returns 0 on a non-empty stream..
	if (rc == 0) {
		int c = f.get();
		if (c != EOF) {
			*s = c;
			rc = 1;
		}
	}

	return rc;
}

std::string next_token(std::string &text, const char *sep, bool long_strings)
{
	size_t pos_begin = text.find_first_not_of(sep);

	if (pos_begin == std::string::npos)
		pos_begin = text.size();

	if (long_strings && pos_begin != text.size() && text[pos_begin] == '"') {
		string sep_string = sep;
		for (size_t i = pos_begin+1; i < text.size(); i++) {
			if (text[i] == '"' && (i+1 == text.size() || sep_string.find(text[i+1]) != std::string::npos)) {
				std::string token = text.substr(pos_begin, i-pos_begin+1);
				text = text.substr(i+1);
				return token;
			}
			if (i+1 < text.size() && text[i] == '"' && text[i+1] == ';' && (i+2 == text.size() || sep_string.find(text[i+2]) != std::string::npos)) {
				std::string token = text.substr(pos_begin, i-pos_begin+1);
				text = text.substr(i+2);
				return token + ";";
			}
		}
	}

	size_t pos_end = text.find_first_of(sep, pos_begin);

	if (pos_end == std::string::npos)
		pos_end = text.size();

	std::string token = text.substr(pos_begin, pos_end-pos_begin);
	text = text.substr(pos_end);
	return token;
}

std::vector<std::string> split_tokens(const std::string &text, const char *sep)
{
	std::vector<std::string> tokens;
	std::string current_token;
	for (char c : text) {
		if (strchr(sep, c)) {
			if (!current_token.empty()) {
				tokens.push_back(current_token);
				current_token.clear();
			}
		} else
			current_token += c;
	}
	if (!current_token.empty()) {
		tokens.push_back(current_token);
		current_token.clear();
	}
	return tokens;
}

// this is very similar to fnmatch(). the exact rules used by this
// function are:
//
//    ?        matches any character except
//    *        matches any sequence of characters
//    [...]    matches any of the characters in the list
//    [!..]    matches any of the characters not in the list
//
// a backslash may be used to escape the next characters in the
// pattern. each special character can also simply match itself.
//
bool patmatch(const char *pattern, const char *string)
{
	if (*pattern == 0)
		return *string == 0;

	if (*pattern == '\\') {
		if (pattern[1] == string[0] && patmatch(pattern+2, string+1))
			return true;
	}

	if (*pattern == '?') {
		if (*string == 0)
			return false;
		return patmatch(pattern+1, string+1);
	}

	if (*pattern == '*') {
		while (*string) {
			if (patmatch(pattern+1, string++))
				return true;
		}
		return pattern[1] == 0;
	}

	if (*pattern == '[') {
		bool found_match = false;
		bool inverted_list = pattern[1] == '!';
		const char *p = pattern + (inverted_list ? 1 : 0);

		while (*++p) {
			if (*p == ']') {
				if (found_match != inverted_list && patmatch(p+1, string+1))
					return true;
				break;
			}

			if (*p == '\\') {
				if (*++p == *string)
					found_match = true;
			} else
			if (*p == *string)
				found_match = true;
		}
	}

	if (*pattern == *string)
		return patmatch(pattern+1, string+1);

	return false;
}

#if !defined(YOSYS_DISABLE_SPAWN)
int run_command(const std::string &command, std::function<void(const std::string&)> process_line)
{
	if (!process_line)
		return system(command.c_str());

	FILE *f = popen(command.c_str(), "r");
	if (f == nullptr)
		return -1;

	std::string line;
	char logbuf[128];
	while (fgets(logbuf, 128, f) != NULL) {
		line += logbuf;
		if (!line.empty() && line.back() == '\n')
			process_line(line), line.clear();
	}
	if (!line.empty())
		process_line(line);

	int ret = pclose(f);
	if (ret < 0)
		return -1;
#ifdef _WIN32
	return ret;
#else
	return WEXITSTATUS(ret);
#endif
}
#endif

std::string get_base_tmpdir()
{
	static std::string tmpdir;

	if (!tmpdir.empty()) {
		return tmpdir;
	}

#if defined(_WIN32)
#  ifdef __MINGW32__
	char longpath[MAX_PATH + 1];
	char shortpath[MAX_PATH + 1];
#  else
	WCHAR longpath[MAX_PATH + 1];
	TCHAR shortpath[MAX_PATH + 1];
#  endif
	if (!GetTempPath(MAX_PATH+1, longpath))
		log_error("GetTempPath() failed.\n");
	if (!GetShortPathName(longpath, shortpath, MAX_PATH + 1))
		log_error("GetShortPathName() failed.\n");
	for (int i = 0; shortpath[i]; i++)
		tmpdir += char(shortpath[i]);
#else
	char * var = std::getenv("TMPDIR");
	if (var && strlen(var)!=0) {
		tmpdir.assign(var);
		// We return the directory name without the trailing '/'
		while (!tmpdir.empty() && (tmpdir.back() == '/')) {
			tmpdir.pop_back();
		}
	} else {
		tmpdir.assign("/tmp");
	}
#endif
	return tmpdir;
}

std::string make_temp_file(std::string template_str)
{
	size_t pos = template_str.rfind("XXXXXX");
	log_assert(pos != std::string::npos);
#if defined(__wasm)
	static size_t index = 0;
	template_str.replace(pos, 6, stringf("%06zu", index++));
#elif defined(_WIN32)
#ifndef YOSYS_WIN32_UNIX_DIR
	std::replace(template_str.begin(), template_str.end(), '/', '\\');
#endif
	while (1) {
		for (int i = 0; i < 6; i++) {
			static std::string y = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
			static uint32_t x = 314159265 ^ uint32_t(time(NULL));
			x ^= x << 13, x ^= x >> 17, x ^= x << 5;
			template_str[pos+i] = y[x % y.size()];
		}
		if (_access(template_str.c_str(), 0) != 0)
			break;
	}
#else
	int suffixlen = GetSize(template_str) - pos - 6;

	char *p = strdup(template_str.c_str());
	close(mkstemps(p, suffixlen));
	template_str = p;
	free(p);
#endif

	return template_str;
}

std::string make_temp_dir(std::string template_str)
{
#if defined(_WIN32)
	template_str = make_temp_file(template_str);
	mkdir(template_str.c_str());
	return template_str;
#elif defined(__wasm)
	template_str = make_temp_file(template_str);
	mkdir(template_str.c_str(), 0777);
	return template_str;
#else
#  ifndef NDEBUG
	size_t pos = template_str.rfind("XXXXXX");
	log_assert(pos != std::string::npos);

	int suffixlen = GetSize(template_str) - pos - 6;
	log_assert(suffixlen == 0);
#  endif

	char *p = strdup(template_str.c_str());
	char *res = mkdtemp(p);
	log_assert(res != NULL);
	template_str = p;
	free(p);

	return template_str;
#endif
}

bool check_directory_exists(const std::string& dirname)
{
#if defined(_WIN32)
	struct _stat info;
	if (_stat(dirname.c_str(), &info) != 0)
	{
		return false;
	}
	return (info.st_mode & _S_IFDIR) != 0;
#else
	struct stat info;
	if (stat(dirname.c_str(), &info) != 0)
	{
		return false;
	}
	return (info.st_mode & S_IFDIR) != 0;
#endif
}

#ifdef _WIN32
bool check_file_exists(std::string filename, bool)
{
	return _access(filename.c_str(), 0) == 0;
}
#else
bool check_file_exists(std::string filename, bool is_exec)
{
	return access(filename.c_str(), is_exec ? X_OK : F_OK) == 0;
}
#endif

bool is_absolute_path(std::string filename)
{
#ifdef _WIN32
	return filename[0] == '/' || filename[0] == '\\' || (filename[0] != 0 && filename[1] == ':');
#else
	return filename[0] == '/';
#endif
}

void remove_directory(std::string dirname)
{
#ifdef _WIN32
	run_command(stringf("rmdir /s /q \"%s\"", dirname.c_str()));
#else
	struct stat stbuf;
	struct dirent **namelist;
	int n = scandir(dirname.c_str(), &namelist, nullptr, alphasort);
	log_assert(n >= 0);
	for (int i = 0; i < n; i++) {
		if (strcmp(namelist[i]->d_name, ".") && strcmp(namelist[i]->d_name, "..")) {
			std::string buffer = stringf("%s/%s", dirname.c_str(), namelist[i]->d_name);
			if (!stat(buffer.c_str(), &stbuf) && S_ISREG(stbuf.st_mode)) {
				remove(buffer.c_str());
			} else
				remove_directory(buffer);
		}
		free(namelist[i]);
	}
	free(namelist);
	rmdir(dirname.c_str());
#endif
}

bool create_directory(const std::string& dirname)
{
#if defined(_WIN32)
	int ret = _mkdir(dirname.c_str());
#else
	mode_t mode = 0755;
	int ret = mkdir(dirname.c_str(), mode);
#endif
	if (ret == 0)
		return true;

	switch (errno)
	{
	case ENOENT:
		// parent didn't exist, try to create it
		{
			std::string::size_type pos = dirname.find_last_of('/');
			if (pos == std::string::npos)
#if defined(_WIN32)
				pos = dirname.find_last_of('\\');
			if (pos == std::string::npos)
#endif
				return false;
			if (!create_directory( dirname.substr(0, pos) ))
				return false;
		}
		// now, try to create again
#if defined(_WIN32)
		return 0 == _mkdir(dirname.c_str());
#else
		return 0 == mkdir(dirname.c_str(), mode);
#endif

	case EEXIST:
		// done!
		return check_directory_exists(dirname);

	default:
		return false;
	}
}

std::string escape_filename_spaces(const std::string& filename)
{
	std::string out;
	out.reserve(filename.size());
	for (auto c : filename)
	{
		if (c == ' ')
			out += "\\ ";
		else
			out.push_back(c);
	}
	return out;
}

bool already_setup = false;

void yosys_setup()
{
	if(already_setup)
		return;
	already_setup = true;
	init_share_dirname();
	init_abc_executable_name();

#define X(_id) RTLIL::ID::_id = "\\" # _id;
#include "kernel/constids.inc"
#undef X

	#ifdef WITH_PYTHON
		PyImport_AppendInittab((char*)"libyosys", INIT_MODULE);
		Py_Initialize();
		PyRun_SimpleString("import sys");
		signal(SIGINT, SIG_DFL);
	#endif

	Pass::init_register();
	yosys_design = new RTLIL::Design;
	yosys_celltypes.setup();
	log_push();
}

bool yosys_already_setup()
{
	return already_setup;
}

bool already_shutdown = false;

void yosys_shutdown()
{
	if(already_shutdown)
		return;
	already_shutdown = true;
	log_pop();

	Pass::done_register();

	delete yosys_design;
	yosys_design = NULL;

	for (auto f : log_files)
		if (f != stderr)
			fclose(f);
	log_errfile = NULL;
	log_files.clear();

	yosys_celltypes.clear();

#ifdef YOSYS_ENABLE_TCL
	if (yosys_tcl_interp != NULL) {
		if (!Tcl_InterpDeleted(yosys_tcl_interp)) {
			Tcl_DeleteInterp(yosys_tcl_interp);
		}
		Tcl_Finalize();
		yosys_tcl_interp = NULL;
	}
#endif

#ifdef YOSYS_ENABLE_PLUGINS
	for (auto &it : loaded_plugins)
		dlclose(it.second);

	loaded_plugins.clear();
#ifdef WITH_PYTHON
	loaded_python_plugins.clear();
#endif
	loaded_plugin_aliases.clear();
#endif

#ifdef WITH_PYTHON
	Py_Finalize();
#endif
}

RTLIL::IdString new_id(std::string file, int line, std::string func)
{
#ifdef _WIN32
	size_t pos = file.find_last_of("/\\");
#else
	size_t pos = file.find_last_of('/');
#endif
	if (pos != std::string::npos)
		file = file.substr(pos+1);

	pos = func.find_last_of(':');
	if (pos != std::string::npos)
		func = func.substr(pos+1);

	return stringf("$auto$%s:%d:%s$%d", file.c_str(), line, func.c_str(), autoidx++);
}

RTLIL::IdString new_id_suffix(std::string file, int line, std::string func, std::string suffix)
{
#ifdef _WIN32
	size_t pos = file.find_last_of("/\\");
#else
	size_t pos = file.find_last_of('/');
#endif
	if (pos != std::string::npos)
		file = file.substr(pos+1);

	pos = func.find_last_of(':');
	if (pos != std::string::npos)
		func = func.substr(pos+1);

	return stringf("$auto$%s:%d:%s$%s$%d", file.c_str(), line, func.c_str(), suffix.c_str(), autoidx++);
}

RTLIL::Design *yosys_get_design()
{
	return yosys_design;
}

const char *create_prompt(RTLIL::Design *design, int recursion_counter)
{
	static char buffer[100];
	std::string str = "\n";
	if (recursion_counter > 1)
		str += stringf("(%d) ", recursion_counter);
	str += "yosys";
	if (!design->selected_active_module.empty())
		str += stringf(" [%s]", RTLIL::unescape_id(design->selected_active_module).c_str());
	if (!design->selection_stack.empty() && !design->selection_stack.back().full_selection) {
		if (design->selected_active_module.empty())
			str += "*";
		else if (design->selection_stack.back().selected_modules.size() != 1 || design->selection_stack.back().selected_members.size() != 0 ||
				design->selection_stack.back().selected_modules.count(design->selected_active_module) == 0)
			str += "*";
	}
	snprintf(buffer, 100, "%s> ", str.c_str());
	return buffer;
}

std::vector<std::string> glob_filename(const std::string &filename_pattern)
{
	std::vector<std::string> results;

#if defined(_WIN32) || !defined(YOSYS_ENABLE_GLOB)
	results.push_back(filename_pattern);
#else
	glob_t globbuf;

	int err = glob(filename_pattern.c_str(), 0, NULL, &globbuf);

	if(err == 0) {
		for (size_t i = 0; i < globbuf.gl_pathc; i++)
			results.push_back(globbuf.gl_pathv[i]);
		globfree(&globbuf);
	} else {
		results.push_back(filename_pattern);
	}
#endif

	return results;
}

void rewrite_filename(std::string &filename)
{
	if (filename.compare(0, 1, "\"") == 0 && filename.compare(GetSize(filename)-1, std::string::npos, "\"") == 0)
		filename = filename.substr(1, GetSize(filename)-2);
	if (filename.compare(0, 2, "+/") == 0)
		filename = proc_share_dirname() + filename.substr(2);
#ifndef _WIN32
	if (filename.compare(0, 2, "~/") == 0)
		filename = filename.replace(0, 1, getenv("HOME"));
#endif
}

#ifdef YOSYS_ENABLE_TCL

static Tcl_Obj *json_to_tcl(Tcl_Interp *interp, const json11::Json &json)
{
	if (json.is_null())
		return Tcl_NewStringObj("null", 4);
	else if (json.is_string()) {
		auto string = json.string_value();
		return Tcl_NewStringObj(string.data(), string.size());
	} else if (json.is_number()) {
		double value = json.number_value();
		double round_val = std::nearbyint(value);
		if (std::isfinite(round_val) && value == round_val && value >= LONG_MIN && value < -double(LONG_MIN))
			return Tcl_NewLongObj((long)round_val);
		else
			return Tcl_NewDoubleObj(value);
	} else if (json.is_bool()) {
		return Tcl_NewBooleanObj(json.bool_value());
	} else if (json.is_array()) {
		auto list = json.array_items();
		Tcl_Obj *result = Tcl_NewListObj(list.size(), nullptr);
		for (auto &item : list)
			Tcl_ListObjAppendElement(interp, result, json_to_tcl(interp, item));
		return result;
	} else if (json.is_object()) {
		auto map = json.object_items();
		Tcl_Obj *result = Tcl_NewListObj(map.size() * 2, nullptr);
		for (auto &item : map) {
			Tcl_ListObjAppendElement(interp, result, Tcl_NewStringObj(item.first.data(), item.first.size()));
			Tcl_ListObjAppendElement(interp, result, json_to_tcl(interp, item.second));
		}
		return result;
	} else {
		log_abort();
	}
}

static int tcl_yosys_cmd(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	std::vector<std::string> args;
	for (int i = 1; i < argc; i++)
		args.push_back(argv[i]);

	if (args.size() >= 1 && args[0] == "-import") {
		for (auto &it : pass_register) {
			std::string tcl_command_name = it.first;
			if (tcl_command_name == "proc")
				tcl_command_name = "procs";
			else if (tcl_command_name == "rename")
				tcl_command_name = "renames";
			Tcl_CmdInfo info;
			if (Tcl_GetCommandInfo(interp, tcl_command_name.c_str(), &info) != 0) {
				log("[TCL: yosys -import] Command name collision: found pre-existing command `%s' -> skip.\n", it.first.c_str());
			} else {
				std::string tcl_script = stringf("proc %s args { yosys %s {*}$args }", tcl_command_name.c_str(), it.first.c_str());
				Tcl_Eval(interp, tcl_script.c_str());
			}
		}
		return TCL_OK;
	}

	yosys_get_design()->scratchpad_unset("result.json");
	yosys_get_design()->scratchpad_unset("result.string");

	bool in_repl = yosys_tcl_repl_active;
	bool restore_log_cmd_error_throw = log_cmd_error_throw;

	log_cmd_error_throw = true;

	try {
		if (args.size() == 1) {
			Pass::call(yosys_get_design(), args[0]);
		} else {
			Pass::call(yosys_get_design(), args);
		}
	} catch (log_cmd_error_exception) {
		if (in_repl) {
			auto design = yosys_get_design();
			while (design->selection_stack.size() > 1)
				design->selection_stack.pop_back();
			log_reset_stack();
		}
		Tcl_SetResult(interp, (char *)"Yosys command produced an error", TCL_STATIC);

		yosys_tcl_repl_active = in_repl;
		log_cmd_error_throw = restore_log_cmd_error_throw;
		return TCL_ERROR;
	} catch (...) {
		log_error("uncaught exception during Yosys command invoked from TCL\n");
	}

	yosys_tcl_repl_active = in_repl;
	log_cmd_error_throw = restore_log_cmd_error_throw;

	auto &scratchpad = yosys_get_design()->scratchpad;
	auto result = scratchpad.find("result.json");
	if (result != scratchpad.end()) {
		std::string err;
		auto json = json11::Json::parse(result->second, err);
		if (err.empty()) {
			Tcl_SetObjResult(interp, json_to_tcl(interp, json));
		} else
			log_warning("Ignoring result.json scratchpad value due to parse error: %s\n", err.c_str());
	} else if ((result = scratchpad.find("result.string")) != scratchpad.end()) {
		Tcl_SetObjResult(interp, Tcl_NewStringObj(result->second.data(), result->second.size()));
	}

	return TCL_OK;
}

int yosys_tcl_iterp_init(Tcl_Interp *interp)
{
	if (Tcl_Init(interp)!=TCL_OK)
		log_warning("Tcl_Init() call failed - %s\n",Tcl_ErrnoMsg(Tcl_GetErrno()));
	Tcl_CreateCommand(interp, "yosys", tcl_yosys_cmd, NULL, NULL);
	return TCL_OK ;
}

void yosys_tcl_activate_repl()
{
	yosys_tcl_repl_active = true;
}

extern Tcl_Interp *yosys_get_tcl_interp()
{
	if (yosys_tcl_interp == NULL) {
		yosys_tcl_interp = Tcl_CreateInterp();
		yosys_tcl_iterp_init(yosys_tcl_interp);
	}
	return yosys_tcl_interp;
}

struct TclPass : public Pass {
	TclPass() : Pass("tcl", "execute a TCL script file") { }
	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    tcl <filename> [args]\n");
		log("\n");
		log("This command executes the tcl commands in the specified file.\n");
		log("Use 'yosys cmd' to run the yosys command 'cmd' from tcl.\n");
		log("\n");
		log("The tcl command 'yosys -import' can be used to import all yosys\n");
		log("commands directly as tcl commands to the tcl shell. Yosys commands\n");
		log("'proc' and 'rename' are wrapped to tcl commands 'procs' and 'renames'\n");
		log("in order to avoid a name collision with the built in commands.\n");
		log("\n");
		log("If any arguments are specified, these arguments are provided to the script via\n");
		log("the standard $argc and $argv variables.\n");
		log("\n");
		log("Note, tcl will not recieve the output of any yosys command. If the output\n");
		log("of the tcl commands are needed, use the yosys command 'tee -s result.string'\n");
		log("to redirect yosys's output to the 'result.string' scratchpad value.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *) override {
		if (args.size() < 2)
			log_cmd_error("Missing script file.\n");

		std::vector<Tcl_Obj*> script_args;
		for (auto it = args.begin() + 2; it != args.end(); ++it)
			script_args.push_back(Tcl_NewStringObj((*it).c_str(), (*it).size()));

		Tcl_Interp *interp = yosys_get_tcl_interp();
		Tcl_Preserve(interp);
		Tcl_ObjSetVar2(interp, Tcl_NewStringObj("argc", 4), NULL, Tcl_NewIntObj(script_args.size()), 0);
		Tcl_ObjSetVar2(interp, Tcl_NewStringObj("argv", 4), NULL, Tcl_NewListObj(script_args.size(), script_args.data()), 0);
		Tcl_ObjSetVar2(interp, Tcl_NewStringObj("argv0", 5), NULL, Tcl_NewStringObj(args[1].c_str(), args[1].size()), 0);
		if (Tcl_EvalFile(interp, args[1].c_str()) != TCL_OK)
			log_cmd_error("TCL interpreter returned an error: %s\n", Tcl_GetStringResult(interp));
		Tcl_Release(interp);
	}
} TclPass;
#endif

#if defined(__linux__) || defined(__CYGWIN__)
std::string proc_self_dirname()
{
	char path[PATH_MAX];
	ssize_t buflen = readlink("/proc/self/exe", path, sizeof(path));
	if (buflen < 0) {
		log_error("readlink(\"/proc/self/exe\") failed: %s\n", strerror(errno));
	}
	while (buflen > 0 && path[buflen-1] != '/')
		buflen--;
	return std::string(path, buflen);
}
#elif defined(__FreeBSD__) || defined(__NetBSD__)
std::string proc_self_dirname()
{
#ifdef __NetBSD__
	int mib[4] = {CTL_KERN, KERN_PROC_ARGS, getpid(), KERN_PROC_PATHNAME};
#else
	int mib[4] = {CTL_KERN, KERN_PROC, KERN_PROC_PATHNAME, -1};
#endif
	size_t buflen;
	char *buffer;
	std::string path;
	if (sysctl(mib, 4, NULL, &buflen, NULL, 0) != 0)
		log_error("sysctl failed: %s\n", strerror(errno));
	buffer = (char*)malloc(buflen);
	if (buffer == NULL)
		log_error("malloc failed: %s\n", strerror(errno));
	if (sysctl(mib, 4, buffer, &buflen, NULL, 0) != 0)
		log_error("sysctl failed: %s\n", strerror(errno));
	while (buflen > 0 && buffer[buflen-1] != '/')
		buflen--;
	path.assign(buffer, buflen);
	free(buffer);
	return path;
}
#elif defined(__APPLE__)
std::string proc_self_dirname()
{
	char *path = NULL;
	uint32_t buflen = 0;
	while (_NSGetExecutablePath(path, &buflen) != 0)
		path = (char *) realloc((void *) path, buflen);
	while (buflen > 0 && path[buflen-1] != '/')
		buflen--;
	std::string str(path, buflen);
	free(path);
	return str;
}
#elif defined(_WIN32)
std::string proc_self_dirname()
{
	int i = 0;
#  ifdef __MINGW32__
	char longpath[MAX_PATH + 1];
	char shortpath[MAX_PATH + 1];
#  else
	WCHAR longpath[MAX_PATH + 1];
	TCHAR shortpath[MAX_PATH + 1];
#  endif
	if (!GetModuleFileName(0, longpath, MAX_PATH+1))
		log_error("GetModuleFileName() failed.\n");
	if (!GetShortPathName(longpath, shortpath, MAX_PATH+1))
		log_error("GetShortPathName() failed.\n");
	while (shortpath[i] != 0)
		i++;
	while (i > 0 && shortpath[i-1] != '/' && shortpath[i-1] != '\\')
		shortpath[--i] = 0;
	std::string path;
	for (i = 0; shortpath[i]; i++)
		path += char(shortpath[i]);
	return path;
}
#elif defined(EMSCRIPTEN) || defined(__wasm)
std::string proc_self_dirname()
{
	return "/";
}
#elif defined(__OpenBSD__)
char yosys_path[PATH_MAX];
char *yosys_argv0;

std::string proc_self_dirname(void)
{
	char buf[PATH_MAX + 1] = "", *path, *p;
	// if case argv[0] contains a valid path, return it
	if (strlen(yosys_path) > 0) {
		p = strrchr(yosys_path, '/');
		snprintf(buf, sizeof buf, "%*s/", (int)(yosys_path - p), yosys_path);
		return buf;
	}
	// if argv[0] does not, reconstruct the path out of $PATH
	path = strdup(getenv("PATH"));
	if (!path)
		log_error("getenv(\"PATH\") failed: %s\n",  strerror(errno));
	for (p = strtok(path, ":"); p; p = strtok(NULL, ":")) {
		snprintf(buf, sizeof buf, "%s/%s", p, yosys_argv0);
		if (access(buf, X_OK) == 0) {
			*(strrchr(buf, '/') + 1) = '\0';
			free(path);
			return buf;
		}
	}
	free(path);
	log_error("Can't determine yosys executable path\n.");
	return NULL;
}
#else
	#error "Don't know how to determine process executable base path!"
#endif

#if defined(EMSCRIPTEN) || defined(__wasm)
void init_share_dirname()
{
	yosys_share_dirname = "/share/";
}
#else
void init_share_dirname()
{
	std::string proc_self_path = proc_self_dirname();
#  if defined(_WIN32) && !defined(YOSYS_WIN32_UNIX_DIR)
	std::string proc_share_path = proc_self_path + "share\\";
	if (check_file_exists(proc_share_path, true)) {
		yosys_share_dirname = proc_share_path;
		return;
	}
	proc_share_path = proc_self_path + "..\\share\\";
	if (check_file_exists(proc_share_path, true)) {
		yosys_share_dirname = proc_share_path;
		return;
	}
#  else
	std::string proc_share_path = proc_self_path + "share/";
	if (check_file_exists(proc_share_path, true)) {
		yosys_share_dirname = proc_share_path;
		return;
	}
	proc_share_path = proc_self_path + "../share/" + proc_program_prefix()+ "yosys/";
	if (check_file_exists(proc_share_path, true)) {
		yosys_share_dirname = proc_share_path;
		return;
	}
#    ifdef YOSYS_DATDIR
	proc_share_path = YOSYS_DATDIR "/";
	if (check_file_exists(proc_share_path, true)) {
		yosys_share_dirname = proc_share_path;
		return;
	}
#    endif
#  endif
}
#endif

void init_abc_executable_name()
{
#ifdef ABCEXTERNAL
	std::string exe_file;
	if (std::getenv("ABC")) {
		yosys_abc_executable = std::getenv("ABC");
	} else {
		yosys_abc_executable = ABCEXTERNAL;
	}
#else
	yosys_abc_executable = proc_self_dirname() + proc_program_prefix()+ "yosys-abc";
#endif
#ifdef _WIN32
#ifndef ABCEXTERNAL
	if (!check_file_exists(yosys_abc_executable + ".exe") && check_file_exists(proc_self_dirname() + "..\\" + proc_program_prefix() + "yosys-abc.exe"))
		yosys_abc_executable = proc_self_dirname() + "..\\" + proc_program_prefix() + "yosys-abc";
#endif
#endif
}

std::string proc_share_dirname()
{
	if (yosys_share_dirname.empty())
		log_error("init_share_dirname: unable to determine share/ directory!\n");
	return yosys_share_dirname;
}

std::string proc_program_prefix()
{
	std::string program_prefix;
#ifdef YOSYS_PROGRAM_PREFIX
	program_prefix = YOSYS_PROGRAM_PREFIX;
#endif
	return program_prefix;
}

bool fgetline(FILE *f, std::string &buffer)
{
	buffer = "";
	char block[4096];
	while (1) {
		if (fgets(block, 4096, f) == NULL)
			return false;
		buffer += block;
		if (buffer.size() > 0 && (buffer[buffer.size()-1] == '\n' ||  buffer[buffer.size()-1] == '\r')) {
			while (buffer.size() > 0 && (buffer[buffer.size()-1] == '\n' ||  buffer[buffer.size()-1] == '\r'))
				buffer.resize(buffer.size()-1);
			return true;
		}
	}
}

static void handle_label(std::string &command, bool &from_to_active, const std::string &run_from, const std::string &run_to)
{
	int pos = 0;
	std::string label;

	while (pos < GetSize(command) && (command[pos] == ' ' || command[pos] == '\t'))
		pos++;

	if (pos < GetSize(command) && command[pos] == '#')
		return;

	while (pos < GetSize(command) && command[pos] != ' ' && command[pos] != '\t' && command[pos] != '\r' && command[pos] != '\n')
		label += command[pos++];

	if (GetSize(label) > 1 && label.back() == ':')
	{
		label = label.substr(0, GetSize(label)-1);
		command = command.substr(pos);

		if (label == run_from)
			from_to_active = true;
		else if (label == run_to || (run_from == run_to && !run_from.empty()))
			from_to_active = false;
	}
}

bool run_frontend(std::string filename, std::string command, RTLIL::Design *design, std::string *from_to_label)
{
	if (design == nullptr)
		design = yosys_design;

	if (command == "auto") {
		std::string filename_trim = filename;
		if (filename_trim.size() > 3 && filename_trim.compare(filename_trim.size()-3, std::string::npos, ".gz") == 0)
			filename_trim.erase(filename_trim.size()-3);
		if (filename_trim.size() > 2 && filename_trim.compare(filename_trim.size()-2, std::string::npos, ".v") == 0)
			command = " -vlog2k";
		else if (filename_trim.size() > 2 && filename_trim.compare(filename_trim.size()-3, std::string::npos, ".sv") == 0)
			command = " -sv";
		else if (filename_trim.size() > 3 && filename_trim.compare(filename_trim.size()-4, std::string::npos, ".vhd") == 0)
			command = " -vhdl";
		else if (filename_trim.size() > 4 && filename_trim.compare(filename_trim.size()-5, std::string::npos, ".blif") == 0)
			command = "blif";
		else if (filename_trim.size() > 5 && filename_trim.compare(filename_trim.size()-6, std::string::npos, ".eblif") == 0)
			command = "blif";
		else if (filename_trim.size() > 4 && filename_trim.compare(filename_trim.size()-5, std::string::npos, ".json") == 0)
			command = "json";
		else if (filename_trim.size() > 3 && filename_trim.compare(filename_trim.size()-3, std::string::npos, ".il") == 0)
			command = "rtlil";
		else if (filename_trim.size() > 3 && filename_trim.compare(filename_trim.size()-3, std::string::npos, ".ys") == 0)
			command = "script";
		else if (filename_trim.size() > 3 && filename_trim.compare(filename_trim.size()-4, std::string::npos, ".tcl") == 0)
			command = "tcl";
		else if (filename == "-")
			command = "script";
		else
			log_error("Can't guess frontend for input file `%s' (missing -f option)!\n", filename.c_str());
	}

	if (command == "script")
	{
		std::string run_from, run_to;
		bool from_to_active = true;

		if (from_to_label != NULL) {
			size_t pos = from_to_label->find(':');
			if (pos == std::string::npos) {
				run_from = *from_to_label;
				run_to = *from_to_label;
			} else {
				run_from = from_to_label->substr(0, pos);
				run_to = from_to_label->substr(pos+1);
			}
			from_to_active = run_from.empty();
		}

		log("\n-- Executing script file `%s' --\n", filename.c_str());

		FILE *f = stdin;

		if (filename != "-") {
			f = fopen(filename.c_str(), "r");
			yosys_input_files.insert(filename);
		}

		if (f == NULL)
			log_error("Can't open script file `%s' for reading: %s\n", filename.c_str(), strerror(errno));

		FILE *backup_script_file = Frontend::current_script_file;
		Frontend::current_script_file = f;

		try {
			std::string command;
			while (fgetline(f, command)) {
				while (!command.empty() && command[command.size()-1] == '\\') {
					std::string next_line;
					if (!fgetline(f, next_line))
						break;
					command.resize(command.size()-1);
					command += next_line;
				}
				handle_label(command, from_to_active, run_from, run_to);
				if (from_to_active) {
					Pass::call(design, command);
					design->check();
				}
			}

			if (!command.empty()) {
				handle_label(command, from_to_active, run_from, run_to);
				if (from_to_active) {
					Pass::call(design, command);
					design->check();
				}
			}
		}
		catch (...) {
			Frontend::current_script_file = backup_script_file;
			throw;
		}

		Frontend::current_script_file = backup_script_file;

		if (filename != "-")
			fclose(f);

		return true;
	}

	if (command == "tcl") {
		Pass::call(design, vector<string>({command, filename}));
		return true;
	}

	if (filename == "-") {
		log("\n-- Parsing stdin using frontend `%s' --\n", command.c_str());
	} else {
		log("\n-- Parsing `%s' using frontend `%s' --\n", filename.c_str(), command.c_str());
	}

	if (command[0] == ' ') {
		auto argv = split_tokens("read" + command);
		argv.push_back(filename);
		Pass::call(design, argv);
	} else
		Frontend::frontend_call(design, NULL, filename, command);

	design->check();
	return false;
}

void run_pass(std::string command, RTLIL::Design *design)
{
	if (design == nullptr)
		design = yosys_design;

	log("\n-- Running command `%s' --\n", command.c_str());

	Pass::call(design, command);
}

void run_backend(std::string filename, std::string command, RTLIL::Design *design)
{
	if (design == nullptr)
		design = yosys_design;

	if (command == "auto") {
		if (filename.size() > 2 && filename.compare(filename.size()-2, std::string::npos, ".v") == 0)
			command = "verilog";
		else if (filename.size() > 3 && filename.compare(filename.size()-3, std::string::npos, ".sv") == 0)
			command = "verilog -sv";
		else if (filename.size() > 3 && filename.compare(filename.size()-3, std::string::npos, ".il") == 0)
			command = "rtlil";
		else if (filename.size() > 3 && filename.compare(filename.size()-3, std::string::npos, ".cc") == 0)
			command = "cxxrtl";
		else if (filename.size() > 4 && filename.compare(filename.size()-4, std::string::npos, ".aig") == 0)
			command = "aiger";
		else if (filename.size() > 5 && filename.compare(filename.size()-5, std::string::npos, ".blif") == 0)
			command = "blif";
		else if (filename.size() > 5 && filename.compare(filename.size()-5, std::string::npos, ".edif") == 0)
			command = "edif";
		else if (filename.size() > 5 && filename.compare(filename.size()-5, std::string::npos, ".json") == 0)
			command = "json";
		else if (filename == "-")
			command = "rtlil";
		else if (filename.empty())
			return;
		else
			log_error("Can't guess backend for output file `%s' (missing -b option)!\n", filename.c_str());
	}

	if (filename.empty())
		filename = "-";

	if (filename == "-") {
		log("\n-- Writing to stdout using backend `%s' --\n", command.c_str());
	} else {
		log("\n-- Writing to `%s' using backend `%s' --\n", filename.c_str(), command.c_str());
	}

	Backend::backend_call(design, NULL, filename, command);
}

#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
static char *readline_cmd_generator(const char *text, int state)
{
	static std::map<std::string, Pass*>::iterator it;
	static int len;

	if (!state) {
		it = pass_register.begin();
		len = strlen(text);
	}

	for (; it != pass_register.end(); it++) {
		if (it->first.compare(0, len, text) == 0)
			return strdup((it++)->first.c_str());
	}
	return NULL;
}

static char *readline_obj_generator(const char *text, int state)
{
	static std::vector<char*> obj_names;
	static size_t idx;

	if (!state)
	{
		idx = 0;
		obj_names.clear();

		RTLIL::Design *design = yosys_get_design();
		int len = strlen(text);

		if (design->selected_active_module.empty())
		{
			for (auto mod : design->modules())
				if (RTLIL::unescape_id(mod->name).compare(0, len, text) == 0)
					obj_names.push_back(strdup(log_id(mod->name)));
		}
		else if (design->module(design->selected_active_module) != nullptr)
		{
			RTLIL::Module *module = design->module(design->selected_active_module);

			for (auto w : module->wires())
				if (RTLIL::unescape_id(w->name).compare(0, len, text) == 0)
					obj_names.push_back(strdup(log_id(w->name)));

			for (auto &it : module->memories)
				if (RTLIL::unescape_id(it.first).compare(0, len, text) == 0)
					obj_names.push_back(strdup(log_id(it.first)));

			for (auto cell : module->cells())
				if (RTLIL::unescape_id(cell->name).compare(0, len, text) == 0)
					obj_names.push_back(strdup(log_id(cell->name)));

			for (auto &it : module->processes)
				if (RTLIL::unescape_id(it.first).compare(0, len, text) == 0)
					obj_names.push_back(strdup(log_id(it.first)));
		}

		std::sort(obj_names.begin(), obj_names.end());
	}

	if (idx < obj_names.size())
		return strdup(obj_names[idx++]);

	idx = 0;
	obj_names.clear();
	return NULL;
}

static char **readline_completion(const char *text, int start, int)
{
	if (start == 0)
		return rl_completion_matches(text, readline_cmd_generator);
	if (strncmp(rl_line_buffer, "read_", 5) && strncmp(rl_line_buffer, "write_", 6))
		return rl_completion_matches(text, readline_obj_generator);
	return NULL;
}
#endif

void shell(RTLIL::Design *design)
{
	static int recursion_counter = 0;

	recursion_counter++;
	log_cmd_error_throw = true;

#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
	rl_readline_name = (char*)"yosys";
	rl_attempted_completion_function = readline_completion;
	rl_basic_word_break_characters = (char*)" \t\n";
#endif

	char *command = NULL;
#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
	while ((command = readline(create_prompt(design, recursion_counter))) != NULL)
	{
#else
	char command_buffer[4096];
	while (1)
	{
		fputs(create_prompt(design, recursion_counter), stdout);
		fflush(stdout);
		if ((command = fgets(command_buffer, 4096, stdin)) == NULL)
			break;
#endif
		if (command[strspn(command, " \t\r\n")] == 0) {
#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
			free(command);
#endif
			continue;
		}
#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
		add_history(command);
#endif

		char *p = command + strspn(command, " \t\r\n");
		if (!strncmp(p, "exit", 4)) {
			p += 4;
			p += strspn(p, " \t\r\n");
			if (*p == 0)
				break;
		}

		try {
			log_assert(design->selection_stack.size() == 1);
			Pass::call(design, command);
		} catch (log_cmd_error_exception) {
			while (design->selection_stack.size() > 1)
				design->selection_stack.pop_back();
			log_reset_stack();
		}
		design->check();
#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
		if (command)
			free(command);
#endif
	}
	if (command == NULL)
		printf("exit\n");
#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
	else
		free(command);
#endif
	recursion_counter--;
	log_cmd_error_throw = false;
}

struct ShellPass : public Pass {
	ShellPass() : Pass("shell", "enter interactive command mode") { }
	void help() override {
		log("\n");
		log("    shell\n");
		log("\n");
		log("This command enters the interactive command mode. This can be useful\n");
		log("in a script to interrupt the script at a certain point and allow for\n");
		log("interactive inspection or manual synthesis of the design at this point.\n");
		log("\n");
		log("The command prompt of the interactive shell indicates the current\n");
		log("selection (see 'help select'):\n");
		log("\n");
		log("    yosys>\n");
		log("        the entire design is selected\n");
		log("\n");
		log("    yosys*>\n");
		log("        only part of the design is selected\n");
		log("\n");
		log("    yosys [modname]>\n");
		log("        the entire module 'modname' is selected using 'select -module modname'\n");
		log("\n");
		log("    yosys [modname]*>\n");
		log("        only part of current module 'modname' is selected\n");
		log("\n");
		log("When in interactive shell, some errors (e.g. invalid command arguments)\n");
		log("do not terminate yosys but return to the command prompt.\n");
		log("\n");
		log("This command is the default action if nothing else has been specified\n");
		log("on the command line.\n");
		log("\n");
		log("Press Ctrl-D or type 'exit' to leave the interactive shell.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		extra_args(args, 1, design, false);
		shell(design);
	}
} ShellPass;

#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
struct HistoryPass : public Pass {
	HistoryPass() : Pass("history", "show last interactive commands") { }
	void help() override {
		log("\n");
		log("    history\n");
		log("\n");
		log("This command prints all commands in the shell history buffer. This are\n");
		log("all commands executed in an interactive session, but not the commands\n");
		log("from executed scripts.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		extra_args(args, 1, design, false);
#ifdef YOSYS_ENABLE_READLINE
		for(HIST_ENTRY **list = history_list(); *list != NULL; list++)
			log("%s\n", (*list)->line);
#else
		for (int i = where_history(); history_get(i); i++)
			log("%s\n", history_get(i)->line);
#endif
	}
} HistoryPass;
#endif

struct ScriptCmdPass : public Pass {
	ScriptCmdPass() : Pass("script", "execute commands from file or wire") { }
	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    script <filename> [<from_label>:<to_label>]\n");
		log("    script -scriptwire [selection]\n");
		log("\n");
		log("This command executes the yosys commands in the specified file (default\n");
		log("behaviour), or commands embedded in the constant text value connected to the\n");
		log("selected wires.\n");
		log("\n");
		log("In the default (file) case, the 2nd argument can be used to only execute the\n");
		log("section of the file between the specified labels. An empty from label is\n");
		log("synonymous with the beginning of the file and an empty to label is synonymous\n");
		log("with the end of the file.\n");
		log("\n");
		log("If only one label is specified (without ':') then only the block\n");
		log("marked with that label (until the next label) is executed.\n");
		log("\n");
		log("In \"-scriptwire\" mode, the commands on the selected wire(s) will be executed\n");
		log("in the scope of (and thus, relative to) the wires' owning module(s). This\n");
		log("'-module' mode can be exited by using the 'cd' command.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool scriptwire = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-scriptwire") {
				scriptwire = true;
				continue;
			}
			break;
		}
		if (scriptwire) {
			extra_args(args, argidx, design);

			for (auto mod : design->selected_modules())
				for (auto &c : mod->connections()) {
					if (!c.first.is_wire())
						continue;
					auto w = c.first.as_wire();
					if (!mod->selected(w))
						continue;
					if (!c.second.is_fully_const())
						log_error("RHS of selected wire %s.%s is not constant.\n", log_id(mod), log_id(w));
					auto v = c.second.as_const();
					Pass::call_on_module(design, mod, v.decode_string());
				}
		}
		else if (args.size() < 2)
			log_cmd_error("Missing script file.\n");
		else if (args.size() == 2)
			run_frontend(args[1], "script", design);
		else if (args.size() == 3)
			run_frontend(args[1], "script", design, &args[2]);
		else
			extra_args(args, 2, design, false);
	}
} ScriptCmdPass;

YOSYS_NAMESPACE_END
