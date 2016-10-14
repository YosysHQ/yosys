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
#include "libs/sha1/sha1.h"

#ifdef YOSYS_ENABLE_READLINE
#  include <readline/readline.h>
#  include <readline/history.h>
#endif

#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <errno.h>

#ifdef __linux__
#  include <sys/types.h>
#  include <unistd.h>
#endif

#if !defined(_WIN32) || defined(__MINGW32__)
#  include <unistd.h>
#else
char *optarg;
int optind = 1, optcur = 1;
int getopt(int argc, char **argv, const char *optstring)
{
	if (optind >= argc || argv[optind][0] != '-')
		return -1;

	bool takes_arg = false;
	int opt = argv[optind][optcur];
	for (int i = 0; optstring[i]; i++)
		if (opt == optstring[i] && optstring[i + 1] == ':')
			takes_arg = true;

	if (!takes_arg) {
		if (argv[optind][++optcur] == 0)
			optind++, optcur = 1;
		return opt;
	}

	if (argv[optind][++optcur]) {
		optarg = argv[optind++] + optcur;
		optcur = 1;
		return opt;
	}

	optarg = argv[++optind];
	optind++, optcur = 1;
	return opt;
}
#endif


USING_YOSYS_NAMESPACE

#ifdef EMSCRIPTEN
#  include <sys/stat.h>
#  include <sys/types.h>

extern "C" int main(int, char**);
extern "C" void run(const char*);
extern "C" const char *errmsg();
extern "C" const char *prompt();

int main(int, char**)
{
	mkdir("/work", 0777);
	chdir("/work");
	log_files.push_back(stdout);
	log_error_stderr = true;
	yosys_banner();
	yosys_setup();
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

int main(int argc, char **argv)
{
	std::string frontend_command = "auto";
	std::string backend_command = "auto";
	std::vector<std::string> passes_commands;
	std::vector<std::string> plugin_filenames;
	std::string output_filename = "";
	std::string scriptfile = "";
	bool scriptfile_tcl = false;
	bool got_output_filename = false;
	bool print_banner = true;
	bool print_stats = true;
	bool call_abort = false;
	bool timing_details = false;
	bool mode_v = false;
	bool mode_q = false;

#ifdef YOSYS_ENABLE_READLINE
	int history_offset = 0;
	std::string history_file;
	if (getenv("HOME") != NULL) {
		history_file = stringf("%s/.yosys_history", getenv("HOME"));
		read_history(history_file.c_str());
		history_offset = where_history();
	}
#endif

	if (argc == 2 && (!strcmp(argv[1], "-h") || !strcmp(argv[1], "-help") || !strcmp(argv[1], "--help")))
	{
		printf("\n");
		printf("Usage: %s [options] [<infile> [..]]\n", argv[0]);
		printf("\n");
		printf("    -Q\n");
		printf("        suppress printing of banner (copyright, disclaimer, version)\n");
		printf("\n");
		printf("    -T\n");
		printf("        suppress printing of footer (log hash, version, timing statistics)\n");
		printf("\n");
		printf("    -q\n");
		printf("        quiet operation. only write warnings and error messages to console\n");
		printf("        use this option twice to also quiet warning messages\n");
		printf("\n");
		printf("    -v <level>\n");
		printf("        print log headers up to level <level> to the console. (this\n");
		printf("        implies -q for everything except the 'End of script.' message.)\n");
		printf("\n");
		printf("    -t\n");
		printf("        annotate all log messages with a time stamp\n");
		printf("\n");
		printf("    -d\n");
		printf("        print more detailed timing stats at exit\n");
		printf("\n");
		printf("    -l logfile\n");
		printf("        write log messages to the specified file\n");
		printf("\n");
		printf("    -L logfile\n");
		printf("        like -l but open log file in line buffered mode\n");
		printf("\n");
		printf("    -o outfile\n");
		printf("        write the design to the specified file on exit\n");
		printf("\n");
		printf("    -b backend\n");
		printf("        use this backend for the output file specified on the command line\n");
		printf("\n");
		printf("    -f frontend\n");
		printf("        use the specified frontend for the input files on the command line\n");
		printf("\n");
		printf("    -H\n");
		printf("        print the command list\n");
		printf("\n");
		printf("    -h command\n");
		printf("        print the help message for the specified command\n");
		printf("\n");
		printf("    -s scriptfile\n");
		printf("        execute the commands in the script file\n");
		printf("\n");
		printf("    -c tcl_scriptfile\n");
		printf("        execute the commands in the tcl script file (see 'help tcl' for details)\n");
		printf("\n");
		printf("    -p command\n");
		printf("        execute the commands\n");
		printf("\n");
		printf("    -m module_file\n");
		printf("        load the specified module (aka plugin)\n");
		printf("\n");
		printf("    -X\n");
		printf("        enable tracing of core data structure changes. for debugging\n");
		printf("\n");
		printf("    -M\n");
		printf("        will slightly randomize allocated pointer addresses. for debugging\n");
		printf("\n");
		printf("    -A\n");
		printf("        will call abort() at the end of the script. for debugging\n");
		printf("\n");
		printf("    -D <header_id>[:<filename>]\n");
		printf("        dump the design when printing the specified log header to a file.\n");
		printf("        yosys_dump_<header_id>.il is used as filename if none is specified.\n");
		printf("        Use 'ALL' as <header_id> to dump at every header.\n");
		printf("\n");
		printf("    -V\n");
		printf("        print version information and exit\n");
		printf("\n");
		printf("The option -S is an shortcut for calling the \"synth\" command, a default\n");
		printf("script for transforming the Verilog input to a gate-level netlist. For example:\n");
		printf("\n");
		printf("    yosys -o output.blif -S input.v\n");
		printf("\n");
		printf("For more complex synthesis jobs it is recommended to use the read_* and write_*\n");
		printf("commands in a script file instead of specifying input and output files on the\n");
		printf("command line.\n");
		printf("\n");
		printf("When no commands, script files or input files are specified on the command\n");
		printf("line, yosys automatically enters the interactive command mode. Use the 'help'\n");
		printf("command to get information on the individual commands.\n");
		printf("\n");
		exit(0);
	}

	int opt;
	while ((opt = getopt(argc, argv, "MXAQTVSm:f:Hh:b:o:p:l:L:qv:tds:c:D:")) != -1)
	{
		switch (opt)
		{
		case 'M':
			memhasher_on();
			break;
		case 'X':
			yosys_xtrace++;
			break;
		case 'A':
			call_abort = true;
			break;
		case 'Q':
			print_banner = false;
			break;
		case 'T':
			print_stats = false;
			break;
		case 'V':
			printf("%s\n", yosys_version_str);
			exit(0);
		case 'S':
			passes_commands.push_back("synth");
			break;
		case 'm':
			plugin_filenames.push_back(optarg);
			break;
		case 'f':
			frontend_command = optarg;
			break;
		case 'H':
			passes_commands.push_back("help");
			break;
		case 'h':
			passes_commands.push_back(stringf("help %s", optarg));
			break;
		case 'b':
			backend_command = optarg;
			break;
		case 'p':
			passes_commands.push_back(optarg);
			break;
		case 'o':
			output_filename = optarg;
			got_output_filename = true;
			break;
		case 'l':
		case 'L':
			log_files.push_back(fopen(optarg, "wt"));
			if (log_files.back() == NULL) {
				fprintf(stderr, "Can't open log file `%s' for writing!\n", optarg);
				exit(1);
			}
			if (opt == 'L')
				setvbuf(log_files.back(), NULL, _IOLBF, 0);
			break;
		case 'q':
			mode_q = true;
			if (log_errfile == stderr)
				log_quiet_warnings = true;
			log_errfile = stderr;
			break;
		case 'v':
			mode_v = true;
			log_errfile = stderr;
			log_verbose_level = atoi(optarg);
			break;
		case 't':
			log_time = true;
			break;
		case 'd':
			timing_details = true;
			break;
		case 's':
			scriptfile = optarg;
			scriptfile_tcl = false;
			break;
		case 'c':
			scriptfile = optarg;
			scriptfile_tcl = true;
			break;
		case 'D':
			{
				auto args = split_tokens(optarg, ":");
				if (!args.empty() && args[0] == "ALL") {
					if (GetSize(args) != 1) {
						fprintf(stderr, "Invalid number of tokens in -D ALL.\n");
						exit(1);
					}
					log_hdump_all = true;
				} else {
					if (!args.empty() && !args[0].empty() && args[0].back() == '.')
						args[0].pop_back();
					if (GetSize(args) == 1)
						args.push_back("yosys_dump_" + args[0] + ".il");
					if (GetSize(args) != 2) {
						fprintf(stderr, "Invalid number of tokens in -D.\n");
						exit(1);
					}
					log_hdump[args[0]].insert(args[1]);
				}
			}
			break;
		default:
			fprintf(stderr, "Run '%s -h' for help.\n", argv[0]);
			exit(1);
		}
	}

	if (log_errfile == NULL) {
		log_files.push_back(stdout);
		log_error_stderr = true;
	}

	if (print_banner)
		yosys_banner();

	if (print_stats)
		log_hasher = new SHA1;

	yosys_setup();

	for (auto &fn : plugin_filenames)
		load_plugin(fn, {});

	if (optind == argc && passes_commands.size() == 0 && scriptfile.empty()) {
		if (!got_output_filename)
			backend_command = "";
		shell(yosys_design);
	}

	while (optind < argc)
		run_frontend(argv[optind++], frontend_command, output_filename == "-" ? &backend_command : NULL);

	if (!scriptfile.empty()) {
		if (scriptfile_tcl) {
#ifdef YOSYS_ENABLE_TCL
			if (Tcl_EvalFile(yosys_get_tcl_interp(), scriptfile.c_str()) != TCL_OK)
				log_error("TCL interpreter returned an error: %s\n", Tcl_GetStringResult(yosys_get_tcl_interp()));
#else
			log_error("Can't exectue TCL script: this version of yosys is not built with TCL support enabled.\n");
#endif
		} else
			run_frontend(scriptfile, "script", output_filename == "-" ? &backend_command : NULL);
	}

	for (auto it = passes_commands.begin(); it != passes_commands.end(); it++)
		run_pass(*it);

	if (!backend_command.empty())
		run_backend(output_filename, backend_command);

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

#ifdef _WIN32
		log("End of script. Logfile hash: %s\n", hash.c_str());
#else
		std::string meminfo;
		std::string stats_divider = ", ";
#  ifdef __linux__
		std::ifstream statm;
		statm.open(stringf("/proc/%lld/statm", (long long)getpid()));
		if (statm.is_open()) {
			int sz_total, sz_resident;
			statm >> sz_total >> sz_resident;
			meminfo = stringf(", MEM: %.2f MB total, %.2f MB resident",
					sz_total * (getpagesize() / 1024.0 / 1024.0),
					sz_resident * (getpagesize() / 1024.0 / 1024.0));
			stats_divider = "\n";
		}
#  endif

		struct rusage ru_buffer;
		getrusage(RUSAGE_SELF, &ru_buffer);
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
	}

#if defined(YOSYS_ENABLE_COVER) && defined(__linux__)
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

	memhasher_off();
	if (call_abort)
		abort();

#ifdef YOSYS_ENABLE_READLINE
	if (!history_file.empty()) {
		if (history_offset > 0) {
			history_truncate_file(history_file.c_str(), 100);
			append_history(where_history() - history_offset, history_file.c_str());
		} else
			write_history(history_file.c_str());
	}

	clear_history();
	HIST_ENTRY **hist_list = history_list();
	if (hist_list != NULL)
		free(hist_list);
#endif

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

