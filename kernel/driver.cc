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
#include "libs/sha1/sha1.h"
#include "libs/cxxopts/include/cxxopts.hpp"
#include <iostream>

#ifdef YOSYS_ENABLE_READLINE
#  include <readline/readline.h>
#  include <readline/history.h>
#endif

#ifdef YOSYS_ENABLE_EDITLINE
#  include <editline/readline.h>
#endif

#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <errno.h>
#ifndef __STDC_FORMAT_MACROS
#  define __STDC_FORMAT_MACROS
#endif
#include <inttypes.h>

#if defined (__linux__) || defined(__FreeBSD__)
#  include <sys/resource.h>
#  include <sys/types.h>
#  include <unistd.h>
#endif

#ifdef __FreeBSD__
#  include <sys/sysctl.h>
#  include <sys/user.h>
#endif

#if !defined(_WIN32) || defined(__MINGW32__)
#  include <unistd.h>
#endif

USING_YOSYS_NAMESPACE

#ifdef EMSCRIPTEN
#  include <sys/stat.h>
#  include <sys/types.h>
#  include <emscripten.h>

extern "C" int main(int, char**);
extern "C" void run(const char*);
extern "C" const char *errmsg();
extern "C" const char *prompt();

int main(int argc, char **argv)
{
	EM_ASM(
		if (ENVIRONMENT_IS_NODE)
		{
			FS.mkdir('/hostcwd');
			FS.mount(NODEFS, { root: '.' }, '/hostcwd');
			FS.mkdir('/hostfs');
			FS.mount(NODEFS, { root: '/' }, '/hostfs');
		}
	);

	mkdir("/work", 0777);
	chdir("/work");
	log_files.push_back(stdout);
	log_error_stderr = true;
	yosys_banner();
	yosys_setup();
#ifdef WITH_PYTHON
	PyRun_SimpleString(("sys.path.append(\""+proc_self_dirname()+"\")").c_str());
	PyRun_SimpleString(("sys.path.append(\""+proc_share_dirname()+"plugins\")").c_str());
#endif

	if (argc == 2)
	{
		// Run the first argument as a script file
		run_frontend(argv[1], "script");
	}
}

void run(const char *command)
{
	int selSize = GetSize(yosys_get_design()->selection_stack);
	try {
		log_last_error = "Internal error (see JavaScript console for details)";
		run_pass(command);
		log_last_error = "";
	} catch (...) {
		while (GetSize(yosys_get_design()->selection_stack) > selSize)
			yosys_get_design()->selection_stack.pop_back();
		throw;
	}
}

const char *errmsg()
{
	return log_last_error.c_str();
}

const char *prompt()
{
	const char *p = create_prompt(yosys_get_design(), 0);
	while (*p == '\n') p++;
	return p;
}

#else /* EMSCRIPTEN */

#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
int yosys_history_offset = 0;
std::string yosys_history_file;
#endif

#if defined(__wasm)
extern "C" {
	// FIXME: WASI does not currently support exceptions.
	void* __cxa_allocate_exception(size_t thrown_size) throw() {
		return malloc(thrown_size);
	}
	bool __cxa_uncaught_exception() throw();
	void __cxa_throw(void* thrown_exception, struct std::type_info * tinfo, void (*dest)(void*)) {
		std::terminate();
	}
}
#endif

void yosys_atexit()
{
#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
	if (!yosys_history_file.empty()) {
#if defined(YOSYS_ENABLE_READLINE)
		if (yosys_history_offset > 0) {
			history_truncate_file(yosys_history_file.c_str(), 100);
			append_history(where_history() - yosys_history_offset, yosys_history_file.c_str());
		} else
			write_history(yosys_history_file.c_str());
#else
		write_history(yosys_history_file.c_str());
#endif
	}

	clear_history();
#if defined(YOSYS_ENABLE_READLINE)
	HIST_ENTRY **hist_list = history_list();
	if (hist_list != NULL)
		free(hist_list);
#endif
#endif
}

#if defined(__OpenBSD__)
namespace Yosys {
extern char *yosys_argv0;
extern char yosys_path[PATH_MAX];
};
#endif
#ifdef YOSYS_ENABLE_TCL
namespace Yosys {
	extern int yosys_tcl_iterp_init(Tcl_Interp *interp);
	extern void yosys_tcl_activate_repl();
};
#endif

int main(int argc, char **argv)
{
	std::string frontend_command = "auto";
	std::string backend_command = "auto";
	std::vector<std::string> vlog_defines;
	std::vector<std::string> passes_commands;
	std::vector<std::string> frontend_files;
	std::vector<std::string> plugin_filenames;
	std::vector<std::string> special_args;
	std::string output_filename = "";
	std::string scriptfile = "";
	std::string depsfile = "";
	std::string topmodule = "";
	std::string perffile = "";
	bool scriptfile_tcl = false;
	bool scriptfile_python = false;
	bool print_banner = true;
	bool print_stats = true;
	bool call_abort = false;
	bool timing_details = false;
	bool run_shell = true;
	bool run_tcl_shell = false;
	bool mode_v = false;
	bool mode_q = false;

	cxxopts::Options options(argv[0], "Yosys Open SYnthesis Suite");
	options.set_width(SIZE_MAX);

	options.add_options("operation")
		("b,backend", "use <backend> for the output file specified on the command line",
			cxxopts::value<std::string>(), "<backend>")
		("f,frontend", "use <frontend> for the input files on the command line",
			cxxopts::value<std::string>(), "<frontend>")
		("s,scriptfile", "execute the commands in <scriptfile>",
			cxxopts::value<std::string>(), "<scriptfile>")
#ifdef YOSYS_ENABLE_TCL
		("c,tcl-scriptfile", "execute the commands in the TCL <tcl_scriptfile> (see 'help tcl' for details)",
			cxxopts::value<std::string>(),"<tcl_scriptfile>")
		("C,tcl-interactive", "enters TCL interactive shell mode")
#endif // YOSYS_ENABLE_TCL
#ifdef WITH_PYTHON
		("y,py-scriptfile", "execute the Python <script>",
			cxxopts::value<std::vector<std::string>>(), "<script>")
#endif // WITH_PYTHON
		("p,commands", "execute <commands> (to chain commands, separate them with semicolon + whitespace: 'cmd1; cmd2')",
			cxxopts::value<std::vector<std::string>>(), "<commands>")
		("r,top", "elaborate the specified HDL <top> module",
			cxxopts::value<std::string>(), "<top>")
		("m,plugin", "load the specified <plugin> module",
			cxxopts::value<std::vector<std::string>>(), "<plugin>")
		("D,define", "set the specified Verilog define to <value> if supplied via command \"read -define\"",
			cxxopts::value<std::vector<std::string>>(), "<define>[=<value>]")
		("S,synth", "shortcut for calling the \"synth\" command, a default script for transforming " \
					"the Verilog input to a gate-level netlist. For example: " \
					"yosys -o output.blif -S input.v " \
					"For more complex synthesis jobs it is recommended to use the read_* and write_* " \
					"commands in a script file instead of specifying input and output files on the " \
					"command line.")
		("H", "print the command list")
		("h,help", "print this help message. If given, print help for <command>.",
			cxxopts::value<std::string>(), "[<command>]")
		("V,version", "print version information and exit")
		("infile", "input files", cxxopts::value<std::vector<std::string>>())
	;
	options.add_options("logging")
		("Q", "suppress printing of banner (copyright, disclaimer, version)")
		("T", "suppress printing of footer (log hash, version, timing statistics)")
		("q,quiet", "quiet operation. Only write warnings and error messages to console. " \
					"Use this option twice to also quiet warning messages")
		("v,verbose", "print log headers up to <level> to the console. " \
                      "Implies -q for everything except the 'End of script.' message.",
			cxxopts::value<int>(), "<level>")
		("t,timestamp", "annotate all log messages with a time stamp")
		("d,detailed-timing", "print more detailed timing stats at exit")
		("l,logfile", "write log messages to <logfile>",
			cxxopts::value<std::vector<std::string>>(), "<logfile>")
		("L,line-buffered-logfile", "like -l but open <logfile> in line buffered mode",
			cxxopts::value<std::vector<std::string>>(), "<logfile>")
		("o,outfile", "write the design to <outfile> on exit",
			cxxopts::value<std::string>(), "<outfile>")
		("P,dump-design", "dump the design when printing the specified log header to a file. " \
						   "yosys_dump_<header_id>.il is used as filename if none is specified. " \
						   "Use 'ALL' as <header_id> to dump at every header.",
						   cxxopts::value<std::vector<std::string>>(), "<header_id>[:<filename>]")
		("W,warning-as-warning", "print a warning for all log messages matching <regex>",
			cxxopts::value<std::vector<std::string>>(), "<regex>")
		("w,warning-as-message", "if a warning message matches <regex>, it is printed as regular message instead",
			cxxopts::value<std::vector<std::string>>(), "<regex>")
		("e,warning-as-error", "if a warning message matches <regex>, it is printed as error message instead",
			cxxopts::value<std::vector<std::string>>(), "<regex>")
		("E,deps-file", "write a Makefile dependencies file <depsfile> with input and output file names",
			cxxopts::value<std::string>(), "<depsfile>")
	;
	options.add_options("developer")
		("X,trace", "enable tracing of core data structure changes. for debugging")
		("M,randomize-pointers", "will slightly randomize allocated pointer addresses. for debugging")
		("A,abort", "will call abort() at the end of the script. for debugging")
		("x,experimental", "do not print warnings for the experimental <feature>",
			cxxopts::value<std::vector<std::string>>(), "<feature>")
		("g,debug", "globally enable debug log messages")
		("perffile", "write a JSON performance log to <perffile>", cxxopts::value<std::string>(), "<perffile>")
	;

	options.parse_positional({"infile"});
	options.positional_help("[<infile> [..]]");

	// We can't have -h optionally require an argument
	// cxxopts does have an implit argument concept but that doesn't work for us
	// cxxopts is therefore instructed allowed to only handle the command help case
	if (argc == 2 && (!strcmp(argv[1], "-h") || !strcmp(argv[1], "-help") || !strcmp(argv[1], "--help"))) {
		std::cout << options.help() << std::endl;
		exit(0);
	}
	try {
		// Check for "--" in arguments
		auto it = std::find(argv, argv + argc, std::string("--"));
		if (it != argv + argc) {
			special_args.assign(it + 1, argv + argc);
			// Remove these arguments from cxxopts parsing
			argc = std::distance(argv, it);
		}

		auto result = options.parse(argc, argv);

		if (result.count("M")) memhasher_on();
		if (result.count("X")) yosys_xtrace++;
		if (result.count("A")) call_abort = true;
		if (result.count("Q")) print_banner = false;
		if (result.count("T")) print_stats = false;
		if (result.count("V")) {
			std::cout << yosys_version_str << std::endl;
			exit(0);
		}
		if (result.count("S")) {
			passes_commands.push_back("synth");
			run_shell = false;
		}
		if (result.count("C")) run_tcl_shell = true;
		if (result.count("g")) log_force_debug++;
		if (result.count("m")) plugin_filenames = result["m"].as<std::vector<std::string>>();
		if (result.count("f")) frontend_command = result["f"].as<std::string>();
		if (result.count("H")) {
			passes_commands.push_back("help");
			run_shell = false;
		}
		if (result.count("h")) {
			std::string res = result["h"].as<std::string>();
			passes_commands.push_back("help " + res);
			run_shell = false;
		}
		if (result.count("b")) {
			backend_command = result["b"].as<std::string>();
			run_shell = false;
		}
		if (result.count("p")) {
			auto cmds = result["p"].as<std::vector<std::string>>();
			passes_commands.insert(passes_commands.end(), cmds.begin(), cmds.end());
			run_shell = false;
		}
		if (result.count("o")) {
			output_filename = result["o"].as<std::string>();
			run_shell = false;
		}
		for (const auto& key : {"l", "L"}) {
			if (result.count(key)) {
				for (const auto& filename : result[key].as<std::vector<std::string>>()) {
					if (FILE* f = fopen(filename.c_str(), "wt")) {
						log_files.push_back(f);
						if (key[0] == 'L') setvbuf(f, NULL, _IOLBF, 0);
					} else {
						std::cerr << "Can't open log file `" << filename << "' for writing!\n";
						exit(1);
					}
				}
			}
		}
		if (result.count("q")) {
			mode_q = true;
			if (log_errfile == stderr) log_quiet_warnings = true;
			log_errfile = stderr;
		}
		if (result.count("v")) {
			mode_v = true;
			log_errfile = stderr;
			log_verbose_level = result["v"].as<int>();
		}
		if (result.count("t")) log_time = true;
		if (result.count("d")) timing_details = true;
		for (const auto& key : {"s", "c"}) {
			if (result.count(key)) {
				scriptfile = result[key].as<std::string>();
				scriptfile_tcl = std::string(key) == "c";
				run_shell = false;
			}
		}
		if (result.count("y")) {
			scriptfile = result["y"].as<std::string>();
			scriptfile_python = true;
			run_shell = false;
		}
		for (const auto& key : {"W", "w", "e"}) {
			if (result.count(key)) {
				auto regexes = result[key].as<std::vector<std::string>>();
				for (const auto& regex : regexes) {
					if (std::string(key) == "W")
						log_warn_regexes.push_back(std::regex(regex));
					if (std::string(key) == "w")
						log_nowarn_regexes.push_back(std::regex(regex));
					if (std::string(key) == "e")
						log_werror_regexes.push_back(std::regex(regex));
				}
			}
		}
		if (result.count("r")) topmodule = result["r"].as<std::string>();
		if (result.count("D")) vlog_defines = result["D"].as<std::vector<std::string>>();
		if (result.count("P")) {
			auto dump_args = result["P"].as<std::vector<std::string>>();
			for (const auto& arg : dump_args) {
				auto tokens = split_tokens(arg, ":");
				if (!tokens.empty() && tokens[0] == "ALL") {
					if (tokens.size() != 1) {
						std::cerr << "Invalid number of tokens in -P ALL." << std::endl;
						exit(1);
					}
					log_hdump_all = true;
				} else {
					if (!tokens.empty() && !tokens[0].empty() && tokens[0].back() == '.')
						tokens[0].pop_back();
					if (tokens.size() == 1)
						tokens.push_back("yosys_dump_" + tokens[0] + ".il");
					if (tokens.size() != 2) {
						std::cerr << "Invalid number of tokens in -P." << std::endl;
						exit(1);
					}
					log_hdump[tokens[0]].insert(tokens[1]);
				}
			}
		}
		if (result.count("E")) depsfile = result["E"].as<std::string>();
		if (result.count("x")) {
			auto ignores = result["x"].as<std::vector<std::string>>();
			log_experimentals_ignored.insert(ignores.begin(), ignores.end());
		}
		if (result.count("perffile")) perffile = result["perffile"].as<std::string>();
		if (result.count("infile")) {
			frontend_files = result["infile"].as<std::vector<std::string>>();
		}

		if (log_errfile == NULL) {
			log_files.push_back(stdout);
			log_error_stderr = true;
		}

		if (print_banner)
			yosys_banner();

	}
	catch (const cxxopts::exceptions::parsing& e) {
		std::cerr << "Error parsing options: " << e.what() << std::endl;
		std::cerr << "Run '" << argv[0] << " --help' for help." << std::endl;
		exit(1);
	}

#if defined(YOSYS_ENABLE_READLINE) || defined(YOSYS_ENABLE_EDITLINE)
	std::string state_dir;
	#if defined(_WIN32)
		if (getenv("HOMEDRIVE") != NULL && getenv("HOMEPATH") != NULL) {
			state_dir = stringf("%s%s/.local/state", getenv("HOMEDRIVE"), getenv("HOMEPATH"));
		} else {
			log_debug("$HOMEDRIVE and/or $HOMEPATH is empty. No history file will be created.\n");
		}
	#else
		if (getenv("XDG_STATE_HOME") == NULL || getenv("XDG_STATE_HOME")[0] == '\0') {
			if (getenv("HOME") != NULL) {
				state_dir = stringf("%s/.local/state", getenv("HOME"));
			} else {
				log_debug("$HOME is empty. No history file will be created.\n");
			}
		} else {
			state_dir = stringf("%s", getenv("XDG_STATE_HOME"));
		}
	#endif

	if (!state_dir.empty()) {
		std::string yosys_dir = state_dir + "/yosys";
		create_directory(yosys_dir);

		yosys_history_file = yosys_dir + "/history";
		read_history(yosys_history_file.c_str());
		yosys_history_offset = where_history();
	}
#endif

	if (print_stats)
		log_hasher = new SHA1;

#if defined(__OpenBSD__)
	// save the executable origin for proc_self_dirname()
	yosys_argv0 = argv[0];
	realpath(yosys_argv0, yosys_path);
#endif

#if defined(__linux__)
	// set stack size to >= 128 MB
	{
		struct rlimit rl;
		const rlim_t stack_size = 128L * 1024L * 1024L;
		if (getrlimit(RLIMIT_STACK, &rl) == 0 && rl.rlim_cur < stack_size) {
			rl.rlim_cur = stack_size;
			setrlimit(RLIMIT_STACK, &rl);
		}
	}
#endif

	yosys_setup();
#ifdef WITH_PYTHON
	PyRun_SimpleString(("sys.path.append(\""+proc_self_dirname()+"\")").c_str());
	PyRun_SimpleString(("sys.path.append(\""+proc_share_dirname()+"plugins\")").c_str());
#endif
	log_error_atexit = yosys_atexit;

	for (auto &fn : plugin_filenames)
		load_plugin(fn, {});

	log_suppressed();

	if (!vlog_defines.empty()) {
		std::string vdef_cmd = "read -define";
		for (auto vdef : vlog_defines)
			vdef_cmd += " " + vdef;
		run_pass(vdef_cmd);
	}

	if (scriptfile.empty() || (!scriptfile_tcl && !scriptfile_python)) {
		// Without a TCL or Python script, arguments following '--'
		// are also treated as frontend files
		for (auto special_arg : special_args)
			frontend_files.push_back(special_arg);
	}

	for (auto it = frontend_files.begin(); it != frontend_files.end(); ++it) {
		if (run_frontend((*it).c_str(), frontend_command))
			run_shell = false;
	}

	if (!topmodule.empty())
		run_pass("hierarchy -top " + topmodule);
	if (!scriptfile.empty()) {
		if (scriptfile_tcl) {
#ifdef YOSYS_ENABLE_TCL
			int tcl_argc = argc - optind;
			std::vector<Tcl_Obj*> script_args;
			Tcl_Interp *interp = yosys_get_tcl_interp();
			for (int i = optind; i < argc; ++i)
				script_args.push_back(Tcl_NewStringObj(argv[i], strlen(argv[i])));

			Tcl_ObjSetVar2(interp, Tcl_NewStringObj("argc", 4), NULL, Tcl_NewIntObj(tcl_argc), 0);
			Tcl_ObjSetVar2(interp, Tcl_NewStringObj("argv", 4), NULL, Tcl_NewListObj(tcl_argc, script_args.data()), 0);
			Tcl_ObjSetVar2(interp, Tcl_NewStringObj("argv0", 5), NULL, Tcl_NewStringObj(scriptfile.c_str(), scriptfile.length()), 0);

			if (Tcl_EvalFile(interp, scriptfile.c_str()) != TCL_OK)
				log_error("TCL interpreter returned an error: %s\n", Tcl_GetStringResult(yosys_get_tcl_interp()));
#else
			log_error("Can't execute TCL script: this version of yosys is not built with TCL support enabled.\n");
#endif
		} else if (scriptfile_python) {
#ifdef WITH_PYTHON
			PyObject *sys = PyImport_ImportModule("sys");
			PyObject *new_argv = PyList_New(argc - optind + 1);
			PyList_SetItem(new_argv, 0, PyUnicode_FromString(scriptfile.c_str()));
			for (int i = optind; i < argc; ++i)
				PyList_SetItem(new_argv, i - optind + 1, PyUnicode_FromString(argv[i]));

			PyObject *old_argv = PyObject_GetAttrString(sys, "argv");
			PyObject_SetAttrString(sys, "argv", new_argv);
			Py_DECREF(old_argv);

			PyObject *py_path = PyUnicode_FromString(scriptfile.c_str());
			PyObject_SetAttrString(sys, "_yosys_script_path", py_path);
			Py_DECREF(py_path);
			PyRun_SimpleString("import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(sys._yosys_script_path)))");

			FILE *scriptfp = fopen(scriptfile.c_str(), "r");
			if (scriptfp == nullptr) {
				log_error("Failed to open file '%s' for reading.\n", scriptfile.c_str());
			}
			if (PyRun_SimpleFile(scriptfp, scriptfile.c_str()) != 0) {
				log_flush();
				PyErr_Print();
				log_error("Python interpreter encountered an exception.");
			}
#else
			log_error("Can't execute Python script: this version of yosys is not built with Python support enabled.\n");
#endif
		} else
			run_frontend(scriptfile, "script");
	}

	for (auto it = passes_commands.begin(); it != passes_commands.end(); it++)
		run_pass(*it);

	if (run_tcl_shell) {
#ifdef YOSYS_ENABLE_TCL
		yosys_tcl_activate_repl();
		Tcl_Main(argc, argv, yosys_tcl_iterp_init);
#else
		log_error("Can't exectue TCL shell: this version of yosys is not built with TCL support enabled.\n");
#endif
	} else {
		if (run_shell)
			shell(yosys_design);
		else
			run_backend(output_filename, backend_command);
	}

	yosys_design->check();
	for (auto it : saved_designs)
		it.second->check();
	for (auto it : pushed_designs)
		it->check();

	if (!depsfile.empty())
	{
		FILE *f = fopen(depsfile.c_str(), "wt");
		if (f == nullptr)
			log_error("Can't open dependencies file for writing: %s\n", strerror(errno));
		bool first = true;
		for (auto fn : yosys_output_files) {
			fprintf(f, "%s%s", first ? "" : " ", escape_filename_spaces(fn).c_str());
			first = false;
		}
		fprintf(f, ":");
		for (auto fn : yosys_input_files) {
			if (yosys_output_files.count(fn) == 0)
				fprintf(f, " %s", escape_filename_spaces(fn).c_str());
		}
		fprintf(f, "\n");
	}

	if (log_expect_no_warnings && log_warnings_count_noexpect)
		log_error("Unexpected warnings found: %d unique messages, %d total, %d expected\n", GetSize(log_warnings),
					log_warnings_count, log_warnings_count - log_warnings_count_noexpect);

	if (print_stats)
	{
		std::string hash = log_hasher->final().substr(0, 10);
		delete log_hasher;
		log_hasher = nullptr;

		log_time = false;
		yosys_xtrace = 0;
		log_spacer();

		if (mode_v && !mode_q)
			log_files.push_back(stderr);

		if (log_warnings_count)
			log("Warnings: %d unique messages, %d total\n", GetSize(log_warnings), log_warnings_count);

		if (!log_experimentals.empty())
			log("Warnings: %d experimental features used (not excluded with -x).\n", GetSize(log_experimentals));

#ifdef _WIN32
		log("End of script. Logfile hash: %s\n", hash.c_str());
#else
		std::string meminfo;
		std::string stats_divider = ", ";

		struct rusage ru_buffer;
		getrusage(RUSAGE_SELF, &ru_buffer);
		if (yosys_design->scratchpad_get_bool("print_stats.include_children")) {
			struct rusage ru_buffer_children;
			getrusage(RUSAGE_CHILDREN, &ru_buffer_children);
			ru_buffer.ru_utime.tv_sec += ru_buffer_children.ru_utime.tv_sec;
			ru_buffer.ru_utime.tv_usec += ru_buffer_children.ru_utime.tv_usec;
			ru_buffer.ru_stime.tv_sec += ru_buffer_children.ru_stime.tv_sec;
			ru_buffer.ru_stime.tv_usec += ru_buffer_children.ru_stime.tv_usec;
#if defined(__linux__) || defined(__FreeBSD__) || defined(__APPLE__)
			ru_buffer.ru_maxrss = std::max(ru_buffer.ru_maxrss, ru_buffer_children.ru_maxrss);
#endif
		}
#if defined(__linux__) || defined(__FreeBSD__)
		meminfo = stringf(", MEM: %.2f MB peak",
				ru_buffer.ru_maxrss / 1024.0);
#elif defined(__APPLE__)
// https://stackoverflow.com/questions/59913657/strange-values-of-get-rusage-maxrss-on-macos-and-linux
		meminfo = stringf(", MEM: %.2f MB peak",
				ru_buffer.ru_maxrss / (1024.0 * 1024.0));
#endif
		log("End of script. Logfile hash: %s%sCPU: user %.2fs system %.2fs%s\n", hash.c_str(),
				stats_divider.c_str(), ru_buffer.ru_utime.tv_sec + 1e-6 * ru_buffer.ru_utime.tv_usec,
				ru_buffer.ru_stime.tv_sec + 1e-6 * ru_buffer.ru_stime.tv_usec, meminfo.c_str());
#endif
		log("%s\n", yosys_version_str);

		int64_t total_ns = 0;
		std::set<tuple<int64_t, int, std::string>> timedat;

		for (auto &it : pass_register)
			if (it.second->call_counter) {
				total_ns += it.second->runtime_ns + 1;
				timedat.insert(make_tuple(it.second->runtime_ns + 1, it.second->call_counter, it.first));
			}

		if (timing_details)
		{
			log("Time spent:\n");
			for (auto it = timedat.rbegin(); it != timedat.rend(); it++) {
				log("%5d%% %5d calls %8.3f sec %s\n", int(100*std::get<0>(*it) / total_ns),
						std::get<1>(*it), std::get<0>(*it) / 1000000000.0, std::get<2>(*it).c_str());
			}
		}
		else
		{
			int out_count = 0;
			log("Time spent:");
			for (auto it = timedat.rbegin(); it != timedat.rend() && out_count < 4; it++, out_count++) {
				if (out_count >= 2 && (std::get<0>(*it) < 1000000000 || int(100*std::get<0>(*it) / total_ns) < 20)) {
					log(", ...");
					break;
				}
				log("%s %d%% %dx %s (%d sec)", out_count ? "," : "", int(100*std::get<0>(*it) / total_ns),
						std::get<1>(*it), std::get<2>(*it).c_str(), int(std::get<0>(*it) / 1000000000));
			}
			log("%s\n", out_count ? "" : " no commands executed");
		}
		if(!perffile.empty())
		{
			FILE *f = fopen(perffile.c_str(), "wt");
			if (f == nullptr)
				log_error("Can't open performance log file for writing: %s\n", strerror(errno));

			fprintf(f, "{\n");
			fprintf(f, "  \"generator\": \"%s\",\n", yosys_version_str);
			fprintf(f, "  \"total_ns\": %" PRIu64 ",\n", total_ns);
			fprintf(f, "  \"passes\": {");

			bool first = true;
			for (auto it = timedat.rbegin(); it != timedat.rend(); it++) {
				if (!first)
					fprintf(f, ",");
				fprintf(f, "\n	\"%s\": {\n", std::get<2>(*it).c_str());
				fprintf(f, "	  \"runtime_ns\": %" PRIu64 ",\n", std::get<0>(*it));
				fprintf(f, "	  \"num_calls\": %u\n", std::get<1>(*it));
				fprintf(f, "	}");
				first = false;
			}
			fprintf(f, "\n  }\n}\n");
		}
	}

#if defined(YOSYS_ENABLE_COVER) && (defined(__linux__) || defined(__FreeBSD__))
	if (getenv("YOSYS_COVER_DIR") || getenv("YOSYS_COVER_FILE"))
	{
		string filename;
		FILE *f;

		if (getenv("YOSYS_COVER_DIR")) {
			filename = stringf("%s/yosys_cover_%d_XXXXXX.txt", getenv("YOSYS_COVER_DIR"), getpid());
			filename = make_temp_file(filename);
		} else {
			filename = getenv("YOSYS_COVER_FILE");
		}

		f = fopen(filename.c_str(), "a+");

		if (f == NULL)
			log_error("Can't create coverage file `%s'.\n", filename.c_str());

		log("<writing coverage file \"%s\">\n", filename.c_str());

		for (auto &it : get_coverage_data())
			fprintf(f, "%-60s %10d %s\n", it.second.first.c_str(), it.second.second, it.first.c_str());

		fclose(f);
	}
#endif

	log_check_expected();

	yosys_atexit();

	memhasher_off();
	if (call_abort)
		abort();

	log_flush();
#if defined(_MSC_VER)
	_exit(0);
#elif defined(_WIN32)
	_Exit(0);
#endif

	yosys_shutdown();

	return 0;
}

#endif /* EMSCRIPTEN */
