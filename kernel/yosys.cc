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

#include "kernel/yosys.h"
#include "kernel/celltypes.h"

#ifdef YOSYS_ENABLE_READLINE
#  include <readline/readline.h>
#  include <readline/history.h>
#endif

#ifdef YOSYS_ENABLE_PLUGINS
#  include <dlfcn.h>
#endif

#ifdef _WIN32
#  include <windows.h>
#  include <io.h>
#elif defined(__APPLE__)
#  include <mach-o/dyld.h>
#  include <unistd.h>
#  include <dirent.h>
#  include <sys/stat.h>
#  include <glob.h>
#else
#  include <unistd.h>
#  include <dirent.h>
#  include <sys/types.h>
#  include <sys/stat.h>
#  include <glob.h>
#endif

#include <limits.h>
#include <errno.h>

YOSYS_NAMESPACE_BEGIN

int autoidx = 1;
int yosys_xtrace = 0;
RTLIL::Design *yosys_design = NULL;
CellTypes yosys_celltypes;

#ifdef YOSYS_ENABLE_TCL
Tcl_Interp *yosys_tcl_interp = NULL;
#endif

bool memhasher_active = false;
uint32_t memhasher_rng = 123456;
std::vector<void*> memhasher_store;

void memhasher_on()
{
#ifdef __linux__
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
	log(" |                                                                            |\n");
	log(" |  yosys -- Yosys Open SYnthesis Suite                                       |\n");
	log(" |                                                                            |\n");
	log(" |  Copyright (C) 2012 - 2016  Clifford Wolf <clifford@clifford.at>           |\n");
	log(" |                                                                            |\n");
	log(" |  Permission to use, copy, modify, and/or distribute this software for any  |\n");
	log(" |  purpose with or without fee is hereby granted, provided that the above    |\n");
	log(" |  copyright notice and this permission notice appear in all copies.         |\n");
	log(" |                                                                            |\n");
	log(" |  THE SOFTWARE IS PROVIDED \"AS IS\" AND THE AUTHOR DISCLAIMS ALL WARRANTIES  |\n");
	log(" |  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF          |\n");
	log(" |  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR   |\n");
	log(" |  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES    |\n");
	log(" |  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN     |\n");
	log(" |  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF   |\n");
	log(" |  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.            |\n");
	log(" |                                                                            |\n");
	log(" \\----------------------------------------------------------------------------/\n");
	log("\n");
	log(" %s\n", yosys_version_str);
	log("\n");
}

int ceil_log2(int x)
{
	if (x <= 0)
		return 0;

	for (int i = 0; i < 32; i++)
		if (((x-1) >> i) == 0)
			return i;

	log_abort();
}

std::string stringf(const char *fmt, ...)
{
	std::string string;
	va_list ap;

	va_start(ap, fmt);
	string = vstringf(fmt, ap);
	va_end(ap);

	return string;
}

std::string vstringf(const char *fmt, va_list ap)
{
	std::string string;
	char *str = NULL;

#ifdef _WIN32
	int sz = 64, rc;
	while (1) {
		va_list apc;
		va_copy(apc, ap);
		str = (char*)realloc(str, sz);
		rc = vsnprintf(str, sz, fmt, apc);
		va_end(apc);
		if (rc >= 0 && rc < sz)
			break;
		sz *= 2;
	}
#else
	if (vasprintf(&str, fmt, ap) < 0)
		str = NULL;
#endif

	if (str != NULL) {
		string = str;
		free(str);
	}

	return string;
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
		for (size_t i = pos_begin+1; i < text.size(); i++)
			if (text[i] == '"' && (i+1 == text.size() || sep_string.find(text[i+1]) != std::string::npos)) {
				std::string token = text.substr(pos_begin, i-pos_begin+1);
				text = text.substr(i+1);
				return token;
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

std::string make_temp_file(std::string template_str)
{
#ifdef _WIN32
	if (template_str.rfind("/tmp/", 0) == 0) {
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
		std::string path;
		for (int i = 0; shortpath[i]; i++)
			path += char(shortpath[i]);
		template_str = stringf("%s\\%s", path.c_str(), template_str.c_str() + 5);
	}

	size_t pos = template_str.rfind("XXXXXX");
	log_assert(pos != std::string::npos);

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
	size_t pos = template_str.rfind("XXXXXX");
	log_assert(pos != std::string::npos);

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
#ifdef _WIN32
	template_str = make_temp_file(template_str);
	mkdir(template_str.c_str());
	return template_str;
#else
#  ifndef NDEBUG
	size_t pos = template_str.rfind("XXXXXX");
	log_assert(pos != std::string::npos);

	int suffixlen = GetSize(template_str) - pos - 6;
	log_assert(suffixlen == 0);
#  endif

	char *p = strdup(template_str.c_str());
	p = mkdtemp(p);
	log_assert(p != NULL);
	template_str = p;
	free(p);

	return template_str;
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

int GetSize(RTLIL::Wire *wire)
{
	return wire->width;
}

void yosys_setup()
{
	// if there are already IdString objects then we have a global initialization order bug
	IdString empty_id;
	log_assert(empty_id.index_ == 0);
	IdString::get_reference(empty_id.index_);

	Pass::init_register();
	yosys_design = new RTLIL::Design;
	yosys_celltypes.setup();
	log_push();
}

void yosys_shutdown()
{
	log_pop();

	delete yosys_design;
	yosys_design = NULL;

	for (auto f : log_files)
		if (f != stderr)
			fclose(f);
	log_errfile = NULL;
	log_files.clear();

	Pass::done_register();
	yosys_celltypes.clear();

#ifdef YOSYS_ENABLE_TCL
	if (yosys_tcl_interp != NULL) {
		Tcl_DeleteInterp(yosys_tcl_interp);
		Tcl_Finalize();
		yosys_tcl_interp = NULL;
	}
#endif

#ifdef YOSYS_ENABLE_PLUGINS
	for (auto &it : loaded_plugins)
		dlclose(it.second);

	loaded_plugins.clear();
	loaded_plugin_aliases.clear();
#endif

	IdString empty_id;
	IdString::put_reference(empty_id.index_);
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

#ifdef _WIN32
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
	if (filename.substr(0, 1) == "\"" && filename.substr(GetSize(filename)-1) == "\"")
		filename = filename.substr(1, GetSize(filename)-2);
	if (filename.substr(0, 2) == "+/")
		filename = proc_share_dirname() + filename.substr(2);
}

#ifdef YOSYS_ENABLE_TCL
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

	if (args.size() == 1) {
		Pass::call(yosys_get_design(), args[0]);
		return TCL_OK;
	}

	Pass::call(yosys_get_design(), args);
	return TCL_OK;
}

extern Tcl_Interp *yosys_get_tcl_interp()
{
	if (yosys_tcl_interp == NULL) {
		yosys_tcl_interp = Tcl_CreateInterp();
		Tcl_CreateCommand(yosys_tcl_interp, "yosys", tcl_yosys_cmd, NULL, NULL);
	}
	return yosys_tcl_interp;
}

struct TclPass : public Pass {
	TclPass() : Pass("tcl", "execute a TCL script file") { }
	virtual void help() {
		log("\n");
		log("    tcl <filename>\n");
		log("\n");
		log("This command executes the tcl commands in the specified file.\n");
		log("Use 'yosys cmd' to run the yosys command 'cmd' from tcl.\n");
		log("\n");
		log("The tcl command 'yosys -import' can be used to import all yosys\n");
		log("commands directly as tcl commands to the tcl shell. The yosys\n");
		log("command 'proc' is wrapped using the tcl command 'procs' in order\n");
		log("to avoid a name collision with the tcl builtin command 'proc'.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) {
		if (args.size() < 2)
			log_cmd_error("Missing script file.\n");
		if (args.size() > 2)
			extra_args(args, 1, design, false);
		if (Tcl_EvalFile(yosys_get_tcl_interp(), args[1].c_str()) != TCL_OK)
			log_cmd_error("TCL interpreter returned an error: %s\n", Tcl_GetStringResult(yosys_get_tcl_interp()));
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
#elif defined(__APPLE__)
std::string proc_self_dirname()
{
	char *path = NULL;
	uint32_t buflen = 0;
	while (_NSGetExecutablePath(path, &buflen) != 0)
		path = (char *) realloc((void *) path, buflen);
	while (buflen > 0 && path[buflen-1] != '/')
		buflen--;
	return std::string(path, buflen);
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
#elif defined(EMSCRIPTEN)
std::string proc_self_dirname()
{
	return "/";
}
#else
	#error Dont know how to determine process executable base path!
#endif

#ifdef EMSCRIPTEN
std::string proc_share_dirname()
{
	return "/share";
}
#else
std::string proc_share_dirname()
{
	std::string proc_self_path = proc_self_dirname();
#  if defined(_WIN32) && !defined(YOSYS_WIN32_UNIX_DIR)
	std::string proc_share_path = proc_self_path + "share\\";
	if (check_file_exists(proc_share_path, true))
		return proc_share_path;
	proc_share_path = proc_self_path + "..\\share\\";
	if (check_file_exists(proc_share_path, true))
		return proc_share_path;
#  else
	std::string proc_share_path = proc_self_path + "share/";
	if (check_file_exists(proc_share_path, true))
		return proc_share_path;
	proc_share_path = proc_self_path + "../share/yosys/";
	if (check_file_exists(proc_share_path, true))
		return proc_share_path;
#    ifdef YOSYS_DATDIR
	proc_share_path = YOSYS_DATDIR "/";
	if (check_file_exists(proc_share_path, true))
		return proc_share_path;
#    endif
#  endif
	log_error("proc_share_dirname: unable to determine share/ directory!\n");
}
#endif

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

	if (label.back() == ':' && GetSize(label) > 1)
	{
		label = label.substr(0, GetSize(label)-1);
		command = command.substr(pos);

		if (label == run_from)
			from_to_active = true;
		else if (label == run_to || (run_from == run_to && !run_from.empty()))
			from_to_active = false;
	}
}

void run_frontend(std::string filename, std::string command, std::string *backend_command, std::string *from_to_label, RTLIL::Design *design)
{
	if (design == nullptr)
		design = yosys_design;

	if (command == "auto") {
		if (filename.size() > 2 && filename.substr(filename.size()-2) == ".v")
			command = "verilog";
		else if (filename.size() > 2 && filename.substr(filename.size()-3) == ".sv")
			command = "verilog -sv";
		else if (filename.size() > 2 && filename.substr(filename.size()-4) == ".vhd")
			command = "vhdl";
		else if (filename.size() > 4 && filename.substr(filename.size()-5) == ".blif")
			command = "blif";
		else if (filename.size() > 3 && filename.substr(filename.size()-3) == ".il")
			command = "ilang";
		else if (filename.size() > 3 && filename.substr(filename.size()-3) == ".ys")
			command = "script";
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

		if (filename != "-")
			f = fopen(filename.c_str(), "r");

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
				if (from_to_active)
					Pass::call(design, command);
			}

			if (!command.empty()) {
				handle_label(command, from_to_active, run_from, run_to);
				if (from_to_active)
					Pass::call(design, command);
			}
		}
		catch (...) {
			Frontend::current_script_file = backup_script_file;
			throw;
		}

		Frontend::current_script_file = backup_script_file;

		if (filename != "-")
			fclose(f);

		if (backend_command != NULL && *backend_command == "auto")
			*backend_command = "";

		return;
	}

	if (filename == "-") {
		log("\n-- Parsing stdin using frontend `%s' --\n", command.c_str());
	} else {
		log("\n-- Parsing `%s' using frontend `%s' --\n", filename.c_str(), command.c_str());
	}

	Frontend::frontend_call(design, NULL, filename, command);
}

void run_frontend(std::string filename, std::string command, RTLIL::Design *design)
{
	run_frontend(filename, command, nullptr, nullptr, design);
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
		if (filename.size() > 2 && filename.substr(filename.size()-2) == ".v")
			command = "verilog";
		else if (filename.size() > 3 && filename.substr(filename.size()-3) == ".il")
			command = "ilang";
		else if (filename.size() > 5 && filename.substr(filename.size()-5) == ".blif")
			command = "blif";
		else if (filename.size() > 5 && filename.substr(filename.size()-5) == ".edif")
			command = "edif";
		else if (filename.size() > 5 && filename.substr(filename.size()-5) == ".json")
			command = "json";
		else if (filename == "-")
			command = "ilang";
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

#ifdef YOSYS_ENABLE_READLINE
static char *readline_cmd_generator(const char *text, int state)
{
	static std::map<std::string, Pass*>::iterator it;
	static int len;

	if (!state) {
		it = pass_register.begin();
		len = strlen(text);
	}

	for (; it != pass_register.end(); it++) {
		if (it->first.substr(0, len) == text)
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
			for (auto &it : design->modules_)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first)));
		}
		else
		if (design->modules_.count(design->selected_active_module) > 0)
		{
			RTLIL::Module *module = design->modules_.at(design->selected_active_module);

			for (auto &it : module->wires_)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first)));

			for (auto &it : module->memories)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first)));

			for (auto &it : module->cells_)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first)));

			for (auto &it : module->processes)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first)));
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

#ifdef YOSYS_ENABLE_READLINE
	rl_readline_name = "yosys";
	rl_attempted_completion_function = readline_completion;
	rl_basic_word_break_characters = " \t\n";
#endif

	char *command = NULL;
#ifdef YOSYS_ENABLE_READLINE
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
		if (command[strspn(command, " \t\r\n")] == 0)
			continue;
#ifdef YOSYS_ENABLE_READLINE
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
	}
	if (command == NULL)
		printf("exit\n");

	recursion_counter--;
	log_cmd_error_throw = false;
}

struct ShellPass : public Pass {
	ShellPass() : Pass("shell", "enter interactive command mode") { }
	virtual void help() {
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
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) {
		extra_args(args, 1, design, false);
		shell(design);
	}
} ShellPass;

#ifdef YOSYS_ENABLE_READLINE
struct HistoryPass : public Pass {
	HistoryPass() : Pass("history", "show last interactive commands") { }
	virtual void help() {
		log("\n");
		log("    history\n");
		log("\n");
		log("This command prints all commands in the shell history buffer. This are\n");
		log("all commands executed in an interactive session, but not the commands\n");
		log("from executed scripts.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) {
		extra_args(args, 1, design, false);
		for(HIST_ENTRY **list = history_list(); *list != NULL; list++)
			log("%s\n", (*list)->line);
	}
} HistoryPass;
#endif

struct ScriptCmdPass : public Pass {
	ScriptCmdPass() : Pass("script", "execute commands from script file") { }
	virtual void help() {
		log("\n");
		log("    script <filename> [<from_label>:<to_label>]\n");
		log("\n");
		log("This command executes the yosys commands in the specified file.\n");
		log("\n");
		log("The 2nd argument can be used to only execute the section of the\n");
		log("file between the specified labels. An empty from label is synonymous\n");
		log("for the beginning of the file and an empty to label is synonymous\n");
		log("for the end of the file.\n");
		log("\n");
		log("If only one label is specified (without ':') then only the block\n");
		log("marked with that label (until the next label) is executed.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) {
		if (args.size() < 2)
			log_cmd_error("Missing script file.\n");
		else if (args.size() == 2)
			run_frontend(args[1], "script", design);
		else if (args.size() == 3)
			run_frontend(args[1], "script", NULL, &args[2], design);
		else
			extra_args(args, 2, design, false);
	}
} ScriptCmdPass;

YOSYS_NAMESPACE_END
