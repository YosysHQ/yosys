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

#include "register.h"
#include "log.h"
#include <assert.h>
#include <string.h>

using namespace REGISTER_INTERN;
#define MAX_REG_COUNT 1000

namespace REGISTER_INTERN
{
	int raw_register_count = 0;
	bool raw_register_done = false;
	Pass *raw_register_array[MAX_REG_COUNT];

	std::map<std::string, Frontend*> frontend_register;
	std::map<std::string, Pass*> pass_register;
	std::map<std::string, Backend*> backend_register;
}

std::vector<std::string> Frontend::next_args;

Pass::Pass(std::string name) : pass_name(name)
{
	assert(!raw_register_done);
	assert(raw_register_count < MAX_REG_COUNT);
	raw_register_array[raw_register_count++] = this;
}

void Pass::run_register()
{
	assert(pass_register.count(pass_name) == 0);
	pass_register[pass_name] = this;
}

void Pass::init_register()
{
	if (raw_register_done)
		done_register();
	while (raw_register_count > 0)
		raw_register_array[--raw_register_count]->run_register();
	raw_register_done = true;
}

void Pass::done_register()
{
	frontend_register.clear();
	pass_register.clear();
	backend_register.clear();
	raw_register_done = false;
}

Pass::~Pass()
{
}

void Pass::help()
{
	log("No help message for this command.\n");
}

void Pass::cmd_log_args(const std::vector<std::string> &args)
{
	if (args.size() <= 1)
		return;
	log("Full command line:");
	for (size_t i = 0; i < args.size(); i++)
		log(" %s", args[i].c_str());
	log("\n");
}

void Pass::cmd_error(const std::vector<std::string> &args, size_t argidx, std::string msg)
{
	std::string command_text;
	int error_pos = 0;

	for (size_t i = 0; i < args.size(); i++) {
		if (i < argidx)
			error_pos += args[i].size() + 1;
		command_text = command_text + (command_text.empty() ? "" : " ") + args[i];
	}

	log("\nSyntax error in command `%s':\n", command_text.c_str());
	help();

	log_cmd_error("Command syntax error: %s\n> %s\n> %*s^\n",
			msg.c_str(), command_text.c_str(), error_pos, "");
}

void Pass::extra_args(std::vector<std::string> args, size_t argidx, RTLIL::Design *)
{
	for (; argidx < args.size(); argidx++)
	{
		std::string arg = args[argidx];

		if (arg.substr(0, 1) == "-")
			cmd_error(args, argidx, "Unkown option or option in arguments.");
		cmd_error(args, argidx, "Extra argument.");
	}
	cmd_log_args(args);
}

void Pass::call(RTLIL::Design *design, std::string command)
{
	std::vector<std::string> args;
	char *s = strdup(command.c_str()), *saveptr;
	for (char *p = strtok_r(s, " \t\r\n", &saveptr); p; p = strtok_r(NULL, " \t\r\n", &saveptr)) {
		std::string str = p;
		int strsz = str.size();
		if (strsz > 0 && str[strsz-1] == ';') {
			while (strsz > 0 && str[strsz-1] == ';')
				strsz--;
			if (strsz > 0)
				args.push_back(str.substr(0, strsz));
			call(design, args);
			args.clear();
		} else
			args.push_back(str);
	}
	free(s);
	call(design, args);
}

void Pass::call(RTLIL::Design *design, std::vector<std::string> args)
{
	if (args.size() == 0 || args[0][0] == '#')
		return;
	if (pass_register.count(args[0]) == 0)
		log_cmd_error("No such command: %s\n", args[0].c_str());

	size_t orig_sel_stack_pos = design->selection_stack.size();
	pass_register[args[0]]->execute(args, design);
	while (design->selection_stack.size() > orig_sel_stack_pos)
		design->selection_stack.pop_back();
}

Frontend::Frontend(std::string name) : Pass("read_"+name), frontend_name(name)
{
}

void Frontend::run_register()
{
	assert(pass_register.count(pass_name) == 0);
	pass_register[pass_name] = this;

	assert(frontend_register.count(frontend_name) == 0);
	frontend_register[frontend_name] = this;
}

Frontend::~Frontend()
{
}

void Frontend::execute(std::vector<std::string> args, RTLIL::Design *design)
{
	assert(next_args.empty());
	do {
		FILE *f = NULL;
		next_args.clear();
		execute(f, std::string(), args, design);
		args = next_args;
		fclose(f);
	} while (!args.empty());
}

void Frontend::extra_args(FILE *&f, std::string &filename, std::vector<std::string> args, size_t argidx)
{
	bool called_with_fp = f != NULL;

	next_args.clear();
	for (; argidx < args.size(); argidx++)
	{
		std::string arg = args[argidx];

		if (arg.substr(0, 1) == "-")
			cmd_error(args, argidx, "Unkown option or option in arguments.");
		if (f != NULL)
			cmd_error(args, argidx, "Extra filename argument in direct file mode.");

		filename = arg;
		f = fopen(filename.c_str(), "r");
		if (f == NULL)
			log_cmd_error("Can't open input file `%s' for reading: %s\n", filename.c_str(), strerror(errno));

		if (argidx+1 < args.size()) {
			next_args.insert(next_args.begin(), args.begin(), args.begin()+argidx);
			next_args.insert(next_args.begin()+argidx, args.begin()+argidx+1, args.end());
			args.erase(args.begin()+argidx+1, args.end());
		}
		break;
	}
	if (f == NULL)
		cmd_error(args, argidx, "No filename given.");

	if (called_with_fp)
		args.push_back(filename);
	args[0] = pass_name;
	cmd_log_args(args);
}

void Frontend::frontend_call(RTLIL::Design *design, FILE *f, std::string filename, std::string command)
{
	std::vector<std::string> args;
	char *s = strdup(command.c_str());
	for (char *p = strtok(s, " \t\r\n"); p; p = strtok(NULL, " \t\r\n"))
		args.push_back(p);
	free(s);
	frontend_call(design, f, filename, args);
}

void Frontend::frontend_call(RTLIL::Design *design, FILE *f, std::string filename, std::vector<std::string> args)
{
	if (args.size() == 0)
		return;
	if (frontend_register.count(args[0]) == 0)
		log_cmd_error("No such frontend: %s\n", args[0].c_str());

	if (f != NULL) {
		frontend_register[args[0]]->execute(f, filename, args, design);
	} else if (filename == "-") {
		frontend_register[args[0]]->execute(stdin, "<stdin>", args, design);
	} else {
		if (!filename.empty())
			args.push_back(filename);
		frontend_register[args[0]]->execute(args, design);
	}
}

Backend::Backend(std::string name) : Pass("write_"+name), backend_name(name)
{
}

void Backend::run_register()
{
	assert(pass_register.count(pass_name) == 0);
	pass_register[pass_name] = this;

	assert(backend_register.count(backend_name) == 0);
	backend_register[backend_name] = this;
}

Backend::~Backend()
{
}

void Backend::execute(std::vector<std::string> args, RTLIL::Design *design)
{
	FILE *f = NULL;
	execute(f, std::string(), args, design);
	if (f != stdout)
		fclose(f);
}

void Backend::extra_args(FILE *&f, std::string &filename, std::vector<std::string> args, size_t argidx)
{
	bool called_with_fp = f != NULL;

	for (; argidx < args.size(); argidx++)
	{
		std::string arg = args[argidx];

		if (arg.substr(0, 1) == "-" && arg != "-")
			cmd_error(args, argidx, "Unkown option or option in arguments.");
		if (f != NULL)
			cmd_error(args, argidx, "Extra filename argument in direct file mode.");

		if (arg == "-") {
			filename = "<stdout>";
			f = stdout;
			continue;
		}

		filename = arg;
		f = fopen(filename.c_str(), "w");
		if (f == NULL)
			log_cmd_error("Can't open output file `%s' for writing: %s\n", filename.c_str(), strerror(errno));
	}

	if (called_with_fp)
		args.push_back(filename);
	args[0] = pass_name;
	cmd_log_args(args);

	if (f == NULL) {
		filename = "<stdout>";
		f = stdout;
	}
}

void Backend::backend_call(RTLIL::Design *design, FILE *f, std::string filename, std::string command)
{
	std::vector<std::string> args;
	char *s = strdup(command.c_str());
	for (char *p = strtok(s, " \t\r\n"); p; p = strtok(NULL, " \t\r\n"))
		args.push_back(p);
	free(s);
	backend_call(design, f, filename, args);
}

void Backend::backend_call(RTLIL::Design *design, FILE *f, std::string filename, std::vector<std::string> args)
{
	if (args.size() == 0)
		return;
	if (backend_register.count(args[0]) == 0)
		log_cmd_error("No such backend: %s\n", args[0].c_str());

	size_t orig_sel_stack_pos = design->selection_stack.size();

	if (f != NULL) {
		backend_register[args[0]]->execute(f, filename, args, design);
	} else if (filename == "-") {
		backend_register[args[0]]->execute(stdout, "<stdout>", args, design);
	} else {
		if (!filename.empty())
			args.push_back(filename);
		backend_register[args[0]]->execute(args, design);
	}

	while (design->selection_stack.size() > orig_sel_stack_pos)
		design->selection_stack.pop_back();
}

