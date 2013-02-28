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

#include <stdio.h>
#include <readline/readline.h>
#include <readline/history.h>

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/log.h"
#include <string.h>
#include <unistd.h>

static void run_frontend(std::string filename, std::string command, RTLIL::Design *design, std::string *backend_command)
{
	if (command == "auto") {
		if (filename.size() > 2 && filename.substr(filename.size()-2) == ".v")
			command = "verilog";
		else if (filename.size() > 3 && filename.substr(filename.size()-3) == ".il")
			command = "ilang";
		else if (filename.size() > 3 && filename.substr(filename.size()-3) == ".ys")
			command = "script";
		else if (filename == "-")
			command = "script";
		else
			log_error("Can't guess frontend for input file `%s' (missing -f option)!\n", filename.c_str());
	}

	if (command == "script") {
		log("\n-- Executing script file `%s' --\n", filename.c_str());
		FILE *f = stdin;
		if (filename != "-")
			f = fopen(filename.c_str(), "r");
		if (f == NULL)
			log_error("Can't open script file `%s' for reading: %s\n", filename.c_str(), strerror(errno));
		char buffer[4096];
		while (fgets(buffer, 4096, f) != NULL) {
			Pass::call(design, buffer);
			design->check();
		}
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
	design->check();
}

static void run_pass(std::string command, RTLIL::Design *design)
{
	log("\n-- Running pass `%s' --\n", command.c_str());

	Pass::call(design, command);
	design->check();
}

static void run_backend(std::string filename, std::string command, RTLIL::Design *design)
{
	if (command == "auto") {
		if (filename.size() > 2 && filename.substr(filename.size()-2) == ".v")
			command = "verilog";
		else if (filename.size() > 3 && filename.substr(filename.size()-3) == ".il")
			command = "ilang";
		else if (filename == "-")
			command = "ilang";
		else
			log_error("Can't guess frontend for input file `%s' (missing -f option)!\n", filename.c_str());
	}

	if (filename == "-") {
		log("\n-- Writing to stdout using backend `%s' --\n", command.c_str());
	} else {
		log("\n-- Writing to `%s' using backend `%s' --\n", filename.c_str(), command.c_str());
	}

	Backend::backend_call(design, NULL, filename, command);
	design->check();
}

static char *readline_cmd_generator(const char *text, int state)
{
	static std::map<std::string, Pass*>::iterator it;
	static int len;

	if (!state) {
		it = REGISTER_INTERN::pass_register.begin();
		len = strlen(text);
	}

	for (; it != REGISTER_INTERN::pass_register.end(); it++) {
		if (it->first.substr(0, len) == text)
			return strdup((it++)->first.c_str());
	}
	return NULL;
}

static char **readline_completion(const char *text, int start, int)
{
	if (start == 0)
		return rl_completion_matches(text, readline_cmd_generator);
	return NULL;
}

static const char *create_prompt(RTLIL::Design *design)
{
	static char buffer[100];
	std::string str = "\nyosys";
	if (!design->selected_active_module.empty())
		str += stringf(" [%s]", design->selected_active_module.c_str());
	if (!design->selection_stack.back().full_selection) {
		if (design->selected_active_module.empty())
			str += "*";
		else if (design->selection_stack.back().selected_modules.size() != 1 || design->selection_stack.back().selected_members.size() != 0 ||
				design->selection_stack.back().selected_modules.count(design->selected_active_module) == 0)
			str += "*";
	}
	snprintf(buffer, 100, "%s> ", str.c_str());
	return buffer;
}

static void shell(RTLIL::Design *design)
{
	static bool recursion_detect = false;

	if (recursion_detect) {
		log("Already in interactive shell.\n");
		return;
	}

	recursion_detect = true;
	log_cmd_error_throw = true;

	rl_readline_name = "yosys";
	rl_attempted_completion_function = readline_completion;

	char *command = NULL;
	while ((command = readline(create_prompt(design))) != NULL)
	{
		if (command[strspn(command, " \t\r\n")] == 0)
			continue;
		add_history(command);

		try {
			assert(design->selection_stack.size() == 1);
			Pass::call(design, command);
		} catch (int) {
			while (design->selection_stack.size() > 1)
				design->selection_stack.pop_back();
			log_reset_stack();
		}
	}

	recursion_detect = false;
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
		log("When in interavtive shell, some errors (e.g. invalid command arguments)\n");
		log("do not terminate yosys but return to the command prompt.\n");
		log("\n");
		log("This command is the default action if nothing else has been specified\n");
		log("on the command line.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string>, RTLIL::Design *design) {
		shell(design);
	}
} ShellPass;

int main(int argc, char **argv)
{
	std::string frontend_command = "auto";
	std::string backend_command = "auto";
	std::vector<std::string> passes_commands;
	std::string output_filename = "-";
	std::string scriptfile = "";
	bool got_output_filename = false;

	Pass::init_register();

	RTLIL::Design *design = new RTLIL::Design;
	design->selection_stack.push_back(RTLIL::Selection());
	log_push();

	int opt;
	while ((opt = getopt(argc, argv, "f:b:o:p:l:qts:")) != -1)
	{
		switch (opt)
		{
		case 'f':
			frontend_command = optarg;
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
		case 't':
			log_time = true;
			break;
		case 's':
			scriptfile = optarg;
			break;
		default:
			fprintf(stderr, "\n");
			fprintf(stderr, "Usage: %s [-q] [-t] [-l logfile] [-o <outfile>] [-f <frontend>] [-s <scriptfile>]\n", argv[0]);
			fprintf(stderr, "       %*s[-p <pass> [-p ..]] [-b <backend>] [<infile> [..]]\n", int(strlen(argv[0])+1), "");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -q\n");
			fprintf(stderr, "        quiet operation. only write error messages to console\n");
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
			fprintf(stderr, "    -s scriptfile\n");
			fprintf(stderr, "        execute the commands in the script file\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -p command\n");
			fprintf(stderr, "        execute the commands\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "For more complex synthesis jobs it is recommended to use the read_* and write_*\n");
			fprintf(stderr, "commands in a script file instead of specifying input and output files on the\n");
			fprintf(stderr, "command line.\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "When no commands, script files and input files are specified on the command\n");
			fprintf(stderr, "line, yosys automatically enters the interactive command mode. Use the 'help'\n");
			fprintf(stderr, "command to get information on the individual commands.\n");
			fprintf(stderr, "\n");
			exit(1);
		}
	}

	if (log_errfile == NULL)
		log_files.push_back(stderr);

	log("\n");
	log(" /-----------------------------------------------------------------------------\\\n");
	log(" |                                                                             |\n");
	log(" |  yosys -- Yosys Open SYnthesis Suite                                        |\n");
	log(" |                                                                             |\n");
	log(" |  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>                   |\n");
	log(" |                                                                             |\n");
	log(" |  Permission to use, copy, modify, and/or distribute this software for any   |\n");
	log(" |  purpose with or without fee is hereby granted, provided that the above     |\n");
	log(" |  copyright notice and this permission notice appear in all copies.          |\n");
	log(" |                                                                             |\n");
	log(" |  THE SOFTWARE IS PROVIDED \"AS IS\" AND THE AUTHOR DISCLAIMS ALL WARRANTIES   |\n");
	log(" |  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF           |\n");
	log(" |  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR    |\n");
	log(" |  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES     |\n");
	log(" |  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN      |\n");
	log(" |  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF    |\n");
	log(" |  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.             |\n");
	log(" |                                                                             |\n");
	log(" \\-----------------------------------------------------------------------------/\n");
	log("\n");

	if (optind == argc && passes_commands.size() == 0 && scriptfile.empty()) {
		if (!got_output_filename)
			backend_command = "";
		shell(design);
	}

	while (optind < argc)
		run_frontend(argv[optind++], frontend_command, design, output_filename == "-" ? &backend_command : NULL);

	if (!scriptfile.empty())
		run_frontend(scriptfile, "script", design, output_filename == "-" ? &backend_command : NULL);

	for (auto it = passes_commands.begin(); it != passes_commands.end(); it++)
		run_pass(*it, design);

	if (!backend_command.empty())
		run_backend(output_filename, backend_command, design);

	delete design;

	log("\nREADY.\n");
	log_pop();

	for (auto f : log_files)
		if (f != stderr)
			fclose(f);
	log_errfile = NULL;
	log_files.clear();

	Pass::done_register();

	return 0;
}

