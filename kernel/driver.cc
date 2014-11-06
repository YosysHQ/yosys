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

#ifdef YOSYS_ENABLE_READLINE
	int history_offset = 0;
	std::string history_file;
	if (getenv("HOME") != NULL) {
		history_file = stringf("%s/.yosys_history", getenv("HOME"));
		read_history(history_file.c_str());
		history_offset = where_history();
	}
#endif

	int opt;
	while ((opt = getopt(argc, argv, "AQTVSm:f:Hh:b:o:p:l:qv:ts:c:")) != -1)
	{
		switch (opt)
		{
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
			log_files.push_back(fopen(optarg, "wt"));
			if (log_files.back() == NULL) {
				fprintf(stderr, "Can't open log file `%s' for writing!\n", optarg);
				exit(1);
			}
			break;
		case 'q':
			log_errfile = stderr;
			break;
		case 'v':
			log_errfile = stderr;
			log_verbose_level = atoi(optarg);
			break;
		case 't':
			log_time = true;
			break;
		case 's':
			scriptfile = optarg;
			scriptfile_tcl = false;
			break;
		case 'c':
			scriptfile = optarg;
			scriptfile_tcl = true;
			break;
		default:
			fprintf(stderr, "\n");
			fprintf(stderr, "Usage: %s [-V -S -Q -T -q] [-v <level>[-t] [-l <logfile>] [-o <outfile>] [-f <frontend>] [-h cmd] \\\n", argv[0]);
			fprintf(stderr, "       %*s[{-s|-c} <scriptfile>] [-p <pass> [-p ..]] [-b <backend>] [-m <module_file>] [<infile> [..]]\n", int(strlen(argv[0])+1), "");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -Q\n");
			fprintf(stderr, "        suppress printing of banner (copyright, disclaimer, version)\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -T\n");
			fprintf(stderr, "        suppress printing of footer (log hash, version, timing statistics)\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -q\n");
			fprintf(stderr, "        quiet operation. only write error messages to console\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -v <level>\n");
			fprintf(stderr, "        print log headers up to level <level> to the console. (implies -q)\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -t\n");
			fprintf(stderr, "        annotate all log messages with a time stamp\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -l logfile\n");
			fprintf(stderr, "        write log messages to the specified file\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -o outfile\n");
			fprintf(stderr, "        write the design to the specified file on exit\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -b backend\n");
			fprintf(stderr, "        use this backend for the output file specified on the command line\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -f backend\n");
			fprintf(stderr, "        use the specified front for the input files on the command line\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -H\n");
			fprintf(stderr, "        print the command list\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -h command\n");
			fprintf(stderr, "        print the help message for the specified command\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -s scriptfile\n");
			fprintf(stderr, "        execute the commands in the script file\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -c tcl_scriptfile\n");
			fprintf(stderr, "        execute the commands in the tcl script file (see 'help tcl' for details)\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -p command\n");
			fprintf(stderr, "        execute the commands\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -m module_file\n");
			fprintf(stderr, "        load the specified module (aka plugin)\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -A\n");
			fprintf(stderr, "        will call abort() at the end of the script. useful for debugging\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -V\n");
			fprintf(stderr, "        print version information and exit\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "The option -S is an shortcut for calling the \"synth\" command, a default\n");
			fprintf(stderr, "script for transforming the verilog input to a gate-level netlist. For example:\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    yosys -o output.blif -S input.v\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "For more complex synthesis jobs it is recommended to use the read_* and write_*\n");
			fprintf(stderr, "commands in a script file instead of specifying input and output files on the\n");
			fprintf(stderr, "command line.\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "When no commands, script files or input files are specified on the command\n");
			fprintf(stderr, "line, yosys automatically enters the interactive command mode. Use the 'help'\n");
			fprintf(stderr, "command to get information on the individual commands.\n");
			fprintf(stderr, "\n");
			exit(1);
		}
	}

	if (log_errfile == NULL)
		log_files.push_back(stderr);

	if (print_banner) {
		log("\n");
		log(" /----------------------------------------------------------------------------\\\n");
		log(" |                                                                            |\n");
		log(" |  yosys -- Yosys Open SYnthesis Suite                                       |\n");
		log(" |                                                                            |\n");
		log(" |  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>                  |\n");
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
		run_frontend(argv[optind++], frontend_command, yosys_design, output_filename == "-" ? &backend_command : NULL, NULL);

	if (!scriptfile.empty()) {
		if (scriptfile_tcl) {
#ifdef YOSYS_ENABLE_TCL
			if (Tcl_EvalFile(yosys_get_tcl_interp(), scriptfile.c_str()) != TCL_OK)
				log_error("TCL interpreter returned an error: %s\n", Tcl_GetStringResult(yosys_get_tcl_interp()));
#else
			log_error("Can't exectue TCL script: this version of yosys is not built with TCL support enabled.\n");
#endif
		} else
			run_frontend(scriptfile, "script", yosys_design, output_filename == "-" ? &backend_command : NULL, NULL);
	}

	for (auto it = passes_commands.begin(); it != passes_commands.end(); it++)
		run_pass(*it, yosys_design);

	if (!backend_command.empty())
		run_backend(output_filename, backend_command, yosys_design);

	if (print_stats)
	{
		std::string hash = log_hasher->final().substr(0, 10);
		delete log_hasher;
		log_hasher = nullptr;

		log_spacer();
#ifdef _WIN32
		log("End of script. Logfile hash: %s\n", hash.c_str());
#else
		struct rusage ru_buffer;
		getrusage(RUSAGE_SELF, &ru_buffer);
		log("End of script. Logfile hash: %s, CPU: user %.2fs system %.2fs\n", hash.c_str(),
				ru_buffer.ru_utime.tv_sec + 1e-6 * ru_buffer.ru_utime.tv_usec,
				ru_buffer.ru_stime.tv_sec + 1e-6 * ru_buffer.ru_stime.tv_usec);
#endif
		log("%s\n", yosys_version_str);

		int64_t total_ns = 0;
		std::set<std::tuple<int64_t, int, std::string>> timedat;

		for (auto &it : pass_register)
			if (it.second->call_counter) {
				total_ns += it.second->runtime_ns + 1;
				timedat.insert(make_tuple(it.second->runtime_ns + 1, it.second->call_counter, it.first));
			}

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

#ifdef YOSYS_ENABLE_COVER
	if (getenv("YOSYS_COVER_DIR") || getenv("YOSYS_COVER_FILE"))
	{
		char filename_buffer[4096];
		FILE *f;

		if (getenv("YOSYS_COVER_DIR")) {
			snprintf(filename_buffer, 4096, "%s/yosys_cover_%d_XXXXXX.txt", getenv("YOSYS_COVER_DIR"), getpid());
			f = fdopen(mkstemps(filename_buffer, 4), "w");
		} else {
			snprintf(filename_buffer, 4096, "%s", getenv("YOSYS_COVER_FILE"));
			f = fopen(filename_buffer, "a+");
		}

		if (f == NULL)
			log_error("Can't create coverage file `%s'.\n", filename_buffer);

		log("<writing coverage file \"%s\">\n", filename_buffer);

		for (auto &it : get_coverage_data())
			fprintf(f, "%-60s %10d %s\n", it.second.first.c_str(), it.second.second, it.first.c_str());

		fclose(f);
	}
#endif

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

	yosys_shutdown();

	return 0;
}

