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
			command = "ilang";
		else
			log_error("Can't guess frontend for input file `%s' (missing -f option)!\n", filename.c_str());
	}

	if (command == "script") {
		log("\n-- Executing script file `%s' --\n", filename.c_str());
		FILE *f = fopen(filename.c_str(), "r");
		if (f == NULL)
			log_error("Can;t open script file `%s' for reading: %s\n", filename.c_str(), strerror(errno));
		char buffer[4096];
		while (fgets(buffer, 4096, f) != NULL) {
			Pass::call(design, buffer);
			design->check();
		}
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

int main(int argc, char **argv)
{
	std::string frontend_command = "auto";
	std::string backend_command = "auto";
	std::vector<std::string> passes_commands;
	std::string output_filename = "-";
	std::string scriptfile = "";
	bool got_output_filename = false;

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
			fprintf(stderr, "Usage: %s [-q] [-t] [-l logfile] [-o <outfile>] [-f <frontend>] [-s <scriptfile>] [-p <pass> [-p ..]] [-b <backend>] [<infile> [..]]\n", argv[0]);
			exit(1);
		}
	}

	if (log_errfile == NULL)
		log_files.push_back(stderr);

	if (optind == argc && passes_commands.size() == 0 && scriptfile.empty())
	{
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

		if (!got_output_filename)
			backend_command = "";
		log_cmd_error_throw = false;
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

	return 0;
}

