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

#include "kernel/register.h"
#include "kernel/log.h"
#include <cstdio>
#include <sys/wait.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ExecPass : public Pass {
	ExecPass() : Pass("exec", "execute commands in the operating system shell") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    exec [options] -- [command]\n");
		log("\n");
		log("Execute a command in the operating system shell.  All supplied arguments are\n");
		log("concatenated and passed as a command to popen(3).  Whitespace is not guaranteed\n");
		log("to be preserved, even if quoted.  stdin is not connected, while stdout is\n");
		log("logged and stderr is logged as a warning.\n");
		log("\n");
		log("\n");
		log("    -q\n");
		log("        suppress stdout and stderr from subprocess\n");
		log("\n");
		log("    -expected-return <int>\n");
		log("        generates an error if popen() does not return specified value.\n");
		log("\n");
		log("    -expected-stdout <regex>\n");
		log("        generates an error if specified regex does not match any line\n");
		log("        in subprocess stdout.\n");
		log("\n");
		log("\n");
		log("    Example: exec -q -expected-return 0 -- echo \"bananapie\" | grep \"nana\"\n");
		log("\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		if(args.size() == 0)
			log_cmd_error("No command provided.\n");

		std::string cmd = "";
		char buf[4096] = {};
		std::string linebuf = "";
		bool flag_cmd = false;
		bool flag_quiet = false;
		bool flag_expected_return = false;
		bool flag_expected_stdout = false;
		int expected_return_value = 0;
		YS_REGEX_TYPE expected_stdout_re;
		std::string expected_stdout_re_str;
		bool expected_stdout_re_matched = false;

		for(size_t argidx = 1; argidx < args.size(); ++argidx) {
			if (flag_cmd) {
				cmd += args[argidx] + (argidx != (args.size() - 1)? " " : "");
			} else {
				if (args[argidx] == "--")
					flag_cmd = true;
				else if (args[argidx] == "-q")
					flag_quiet = true;
				else if (args[argidx] == "-expected-return") {
					flag_expected_return = true;
					++argidx;
					if (argidx >= args.size())
						log_cmd_error("No expected return value specified.\n");

					expected_return_value = atoi(args[argidx].c_str());
				} else if (args[argidx] == "-expected-stdout") {
					flag_expected_stdout = true;
					++argidx;
					if (argidx >= args.size())
						log_cmd_error("No expected regular expression to find in stdout specified.\n");

					try{
						expected_stdout_re_str = args[argidx];
						expected_stdout_re = YS_REGEX_COMPILE(args[argidx]);
					} catch (const YS_REGEX_NS::regex_error& e) {
						log_cmd_error("Error in regex expression '%s' !\n", expected_stdout_re_str.c_str());
					}

				} else
					log_cmd_error("Unknown option \"%s\" or \"--\" doesn\'t precede command.", args[argidx].c_str());
			}
		}

		log_header(design, "Executing command \"%s\".\n", cmd.c_str());
		log_push();

		fflush(stdout);
		bool keep_reading = true;
		auto *f = popen(cmd.c_str(), "r");
		if (f == nullptr)
			log_cmd_error("errno %d after popen() returned NULL.\n", errno);
		while (keep_reading) {
			keep_reading = (fgets(buf, sizeof(buf), f) != nullptr);
			linebuf += buf;
			memset(buf, 0, sizeof(buf));

			auto pos = linebuf.find('\n');
			while (pos != std::string::npos) {
				std::string line = linebuf.substr(0, pos);
				linebuf.erase(0, pos + 1);
				if (!flag_quiet)
					log("%s\n", line.c_str());

				if(YS_REGEX_NS::regex_search(line, expected_stdout_re))
					expected_stdout_re_matched = true;

				pos = linebuf.find('\n');
			}
		}
		int status = pclose(f);
		int retval = -1;

		if(WIFEXITED(status)) {
		    retval = WEXITSTATUS(status);
		}
		else if(WIFSIGNALED(status)) {
		    retval = WTERMSIG(status);
		}
		else if(WIFSTOPPED(status)) {
		    retval = WSTOPSIG(status);
		}

		if (flag_expected_return && retval != expected_return_value)
			log_cmd_error("Return value %d did not match expected return value %d.\n", retval, expected_return_value);

		if (flag_expected_stdout && !expected_stdout_re_matched)
			log_cmd_error("Command stdout did not have a line matching given regex \"%s\".\n", expected_stdout_re_str.c_str());

		log_pop();
	}
} ExecPass;

PRIVATE_NAMESPACE_END
