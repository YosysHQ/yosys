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
#include <string.h>
#include <unistd.h>
#include <libgen.h>
#include <dlfcn.h>
#include <limits.h>
#include <errno.h>

#include <algorithm>

#include "kernel/rtlil.h"
#include "kernel/register.h"
#include "kernel/log.h"

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

	while (pos < SIZE(command) && (command[pos] == ' ' || command[pos] == '\t'))
		pos++;

	while (pos < SIZE(command) && command[pos] != ' ' && command[pos] != '\t' && command[pos] != '\r' && command[pos] != '\n')
		label += command[pos++];

	if (label.back() == ':' && SIZE(label) > 1)
	{
		label = label.substr(0, SIZE(label)-1);
		command = command.substr(pos);

		if (label == run_from)
			from_to_active = true;
		else if (label == run_to || (run_from == run_to && !run_from.empty()))
			from_to_active = false;
	}
}

static void run_frontend(std::string filename, std::string command, RTLIL::Design *design, std::string *backend_command, std::string *from_to_label)
{
	if (command == "auto") {
		if (filename.size() > 2 && filename.substr(filename.size()-2) == ".v")
			command = "verilog";
		else if (filename.size() > 2 && filename.substr(filename.size()-3) == ".sv")
			command = "verilog -sv";
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

static void run_pass(std::string command, RTLIL::Design *design)
{
	log("\n-- Running pass `%s' --\n", command.c_str());

	Pass::call(design, command);
}

static void run_backend(std::string filename, std::string command, RTLIL::Design *design)
{
	if (command == "auto") {
		if (filename.size() > 2 && filename.substr(filename.size()-2) == ".v")
			command = "verilog";
		else if (filename.size() > 3 && filename.substr(filename.size()-3) == ".il")
			command = "ilang";
		else if (filename.size() > 5 && filename.substr(filename.size()-5) == ".blif")
			command = "blif";
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
			for (auto &it : design->modules)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first.c_str())));
		}
		else
		if (design->modules.count(design->selected_active_module) > 0)
		{
			RTLIL::Module *module = design->modules.at(design->selected_active_module);

			for (auto &it : module->wires)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first.c_str())));

			for (auto &it : module->memories)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first.c_str())));

			for (auto &it : module->cells)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first.c_str())));

			for (auto &it : module->processes)
				if (RTLIL::unescape_id(it.first).substr(0, len) == text)
					obj_names.push_back(strdup(RTLIL::id2cstr(it.first.c_str())));
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

const char *create_prompt(RTLIL::Design *design, int recursion_counter)
{
	static char buffer[100];
	std::string str = "\n";
	if (recursion_counter > 1)
		str += stringf("(%d) ", recursion_counter);
	str += "yosys";
	if (!design->selected_active_module.empty())
		str += stringf(" [%s]", RTLIL::id2cstr(design->selected_active_module));
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
	static int recursion_counter = 0;

	recursion_counter++;
	log_cmd_error_throw = true;

	rl_readline_name = "yosys";
	rl_attempted_completion_function = readline_completion;
	rl_basic_word_break_characters = " \t\n";

	char *command = NULL;
	while ((command = readline(create_prompt(design, recursion_counter))) != NULL)
	{
		if (command[strspn(command, " \t\r\n")] == 0)
			continue;
		add_history(command);

		char *p = command + strspn(command, " \t\r\n");
		if (!strncmp(p, "exit", 4)) {
			p += 4;
			p += strspn(p, " \t\r\n");
			if (*p == 0)
				break;
		}

		try {
			assert(design->selection_stack.size() == 1);
			Pass::call(design, command);
		} catch (int) {
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

struct ScriptPass : public Pass {
	ScriptPass() : Pass("script", "execute commands from script file") { }
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
			run_frontend(args[1], "script", design, NULL, NULL);
		else if (args.size() == 3)
			run_frontend(args[1], "script", design, NULL, &args[2]);
		else
			extra_args(args, 2, design, false);
	}
} ScriptPass;

#ifdef YOSYS_ENABLE_TCL
static Tcl_Interp *yosys_tcl_interp = NULL;

static int tcl_yosys_cmd(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	std::vector<std::string> args;
	for (int i = 1; i < argc; i++)
		args.push_back(argv[i]);

	if (args.size() >= 1 && args[0] == "-import") {
		for (auto &it : REGISTER_INTERN::pass_register) {
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
		log("to avoid a name collision with the tcl builting command 'proc'.\n");
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

static RTLIL::Design *yosys_design = NULL;

extern RTLIL::Design *yosys_get_design()
{
	return yosys_design;
}

#if defined(__linux__)
std::string proc_self_dirname ()
{
	char path [PATH_MAX];
	ssize_t buflen = readlink("/proc/self/exe", path, sizeof(path));
	if (buflen < 0) {
		log_cmd_error("readlink(\"/proc/self/exe\") failed: %s", strerror(errno));
		log_abort();
	}
	while (buflen > 0 && path[buflen-1] != '/')
		buflen--;
	return std::string(path, buflen);
}
#elif defined(__APPLE__)
#include <mach-o/dyld.h>
std::string proc_self_dirname ()
{
	char * path = NULL;
	uint32_t buflen = 0;
	while (_NSGetExecutablePath(path, &buflen) != 0)
		path = (char *) realloc((void *) path, buflen);
	while (buflen > 0 && path[buflen-1] != '/')
		buflen--;
	return std::string(path, buflen);
}
#else
	#error Dont know how to determine process executable base path!
#endif

std::string proc_share_dirname ()
{
	std::string proc_self_path = proc_self_dirname();
	std::string proc_share_path = proc_self_path + "share/";
	if (access(proc_share_path.c_str(), X_OK) == 0)
		return proc_share_path;
	proc_share_path = proc_self_path + "../share/yosys/";
	if (access(proc_share_path.c_str(), X_OK) == 0)
		return proc_share_path;
	log_cmd_error("proc_share_dirname: unable to determine share/ directory!");
	log_abort();
}

int main(int argc, char **argv)
{
	std::string frontend_command = "auto";
	std::string backend_command = "auto";
	std::vector<std::string> passes_commands;
	std::vector<void*> loaded_modules;
	std::string output_filename = "";
	std::string scriptfile = "";
	bool scriptfile_tcl = false;
	bool got_output_filename = false;

	int history_offset = 0;
	std::string history_file;
	if (getenv("HOME") != NULL) {
		history_file = stringf("%s/.yosys_history", getenv("HOME"));
		read_history(history_file.c_str());
		history_offset = where_history();
	}

	int opt;
	while ((opt = getopt(argc, argv, "VSm:f:Hh:b:o:p:l:qv:ts:c:")) != -1)
	{
		switch (opt)
		{
		case 'V':
			printf("%s\n", yosys_version_str);
			exit(0);
		case 'S':
			passes_commands.push_back("hierarchy");
			passes_commands.push_back("proc");
			passes_commands.push_back("opt");
			passes_commands.push_back("memory");
			passes_commands.push_back("opt");
			passes_commands.push_back("techmap");
			passes_commands.push_back("opt");
			break;
		case 'm':
			loaded_modules.push_back(dlopen(optarg, RTLD_LAZY|RTLD_GLOBAL));
			if (loaded_modules.back() == NULL) {
				fprintf(stderr, "Can't load module `%s': %s\n", optarg, dlerror());
				exit(1);
			}
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
			fprintf(stderr, "Usage: %s [-V] [-S] [-q] [-v <level>[-t] [-l <logfile>] [-o <outfile>] [-f <frontend>] [-h cmd] \\\n", argv[0]);
			fprintf(stderr, "       %*s[{-s|-c} <scriptfile>] [-p <pass> [-p ..]] [-b <backend>] [-m <module_file>] [<infile> [..]]\n", int(strlen(argv[0])+1), "");
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
			fprintf(stderr, "    -V\n");
			fprintf(stderr, "        print version information and exit\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "The option -S is an alias for the following options that perform a simple\n");
			fprintf(stderr, "transformation of the input to a gate-level netlist.\n");
			fprintf(stderr, "\n");
			fprintf(stderr, "    -p hierarchy -p proc -p opt -p memory -p opt -p techmap -p opt\n");
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
	log(" %s\n", yosys_version_str);
	log("\n");

	Pass::init_register();

	yosys_design = new RTLIL::Design;
	yosys_design->selection_stack.push_back(RTLIL::Selection());
	log_push();

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

	delete yosys_design;
	yosys_design = NULL;

#ifndef NDEBUG
	if (getenv("YOSYS_COVER_DIR") || getenv("YOSYS_COVER_FILE"))
	{
		char filename_buffer[4096];
		FILE *f;

		if (getenv("YOSYS_COVER_DIR")) {
			snprintf(filename_buffer, 4096, "%s/yosys_cover_%d_XXXXXX.txt", getenv("YOSYS_COVER_DIR"), getpid());
			f = fdopen(mkstemps(filename_buffer, 4), "w");
		} else {
			snprintf(filename_buffer, 4096, "%s", getenv("YOSYS_COVER_FILE"));
			f = fopen(filename_buffer, "w");
		}

		if (f == NULL)
			log_error("Can't create coverage file `%s'.\n", filename_buffer);

		log("<writing coverage file \"%s\">\n", filename_buffer);

		std::map<std::string, std::pair<std::string, int>> coverage_data;
		for (CoverAgent *p = CoverAgent::first_cover_agent; p; p = p->next_cover_agent) {
			if (coverage_data.count(p->id))
				log("WARNING: found duplicate coverage id \"%s\".\n", p->id);
			coverage_data[p->id].first = stringf("%s:%d:%s", p->file, p->line, p->func);
			coverage_data[p->id].second += p->ticks;
		}

		for (auto &it : coverage_data)
			fprintf(f, "%-40s %10d %s\n", it.second.first.c_str(), it.second.second, it.first.c_str());
		fclose(f);
	}
#endif

	log("\nREADY.\n");
	log_pop();

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

	for (auto f : log_files)
		if (f != stderr)
			fclose(f);
	log_errfile = NULL;
	log_files.clear();

	Pass::done_register();

	for (auto mod : loaded_modules)
		dlclose(mod);

#ifdef YOSYS_ENABLE_TCL
	if (yosys_tcl_interp != NULL) {
		Tcl_DeleteInterp(yosys_tcl_interp);
		Tcl_Finalize();
		yosys_tcl_interp = NULL;
	}
#endif

	return 0;
}

