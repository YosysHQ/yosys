/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012 - 2020  Claire Xenia Wolf <claire@yosyshq.com>
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

#if defined(_WIN32)
#  include <csignal>
#  define WIFEXITED(x) 1
#  define WIFSIGNALED(x) 0
#  define WIFSTOPPED(x) 0
#  define WEXITSTATUS(x) ((x) & 0xff)
#  define WTERMSIG(x) SIGTERM
#  define WSTOPSIG(x) 0
#else
#  include <sys/wait.h>
#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ExecPass : public Pass {
	ExecPass() : Pass("exec", "execute commands in the operating system shell") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    exec [options] -- [command]\n");
		log("\n");
		log("Execute a command in the operating system shell.  All supplied arguments are\n");
		log("concatenated and passed as a command to popen(3).  Whitespace is not guaranteed\n");
		log("to be preserved, even if quoted.  stdin and stderr are not connected, while\n");
		log("stdout is logged unless the \"-q\" option is specified.\n");
		log("\n");
		log("\n");
		log("    -q\n");
		log("        Suppress stdout and stderr from subprocess\n");
		log("\n");
		log("    -expect-return <int>\n");
		log("        Generate an error if popen() does not return specified value.\n");
		log("        May only be specified once; the final specified value is controlling\n");
		log("        if specified multiple times.\n");
		log("\n");
		log("    -expect-stdout <regex>\n");
		log("        Generate an error if the specified regex does not match any line\n");
		log("        in subprocess's stdout.  May be specified multiple times.\n");
		log("\n");
		log("    -not-expect-stdout <regex>\n");
		log("        Generate an error if the specified regex matches any line\n");
		log("        in subprocess's stdout.  May be specified multiple times.\n");
		log("\n");
		log("\n");
		log("    Example: exec -q -expect-return 0 -- echo \"bananapie\" | grep \"nana\"\n");
		log("\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string cmd = "";
		char buf[1024] = {};
		std::string linebuf = "";
		bool flag_cmd = false;
		bool flag_quiet = false;
		bool flag_expect_return = false;
		int expect_return_value = 0;
		bool flag_expect_stdout = false;
		struct expect_stdout_elem {
			bool matched;
			bool polarity;	//true: this regex must match at least one line
					//false: this regex must not match any line
			std::string str;
			std::regex re;

			expect_stdout_elem() : matched(false), polarity(true), str(), re(){};
		};
		std::vector<expect_stdout_elem> expect_stdout;

		if(args.size() == 0)
			log_cmd_error("No command provided.\n");

		for(size_t argidx = 1; argidx < args.size(); ++argidx) {
			if (flag_cmd) {
				cmd += args[argidx] + (argidx != (args.size() - 1)? " " : "");
			} else {
				if (args[argidx] == "--")
					flag_cmd = true;
				else if (args[argidx] == "-q")
					flag_quiet = true;
				else if (args[argidx] == "-expect-return") {
					flag_expect_return = true;
					++argidx;
					if (argidx >= args.size())
						log_cmd_error("No expected return value specified.\n");

					expect_return_value = atoi(args[argidx].c_str());
				} else if (args[argidx] == "-expect-stdout") {
					flag_expect_stdout = true;
					++argidx;
					if (argidx >= args.size())
						log_cmd_error("No expected regular expression specified.\n");

					try{
						expect_stdout_elem x;
						x.str = args[argidx];
						x.re = YS_REGEX_COMPILE(args[argidx]);
						expect_stdout.push_back(x);
					} catch (const std::regex_error& e) {
						log_cmd_error("Error in regex expression '%s' !\n", args[argidx].c_str());
					}
				} else if (args[argidx] == "-not-expect-stdout") {
					flag_expect_stdout = true;
					++argidx;
					if (argidx >= args.size())
						log_cmd_error("No expected regular expression specified.\n");

					try{
						expect_stdout_elem x;
						x.str = args[argidx];
						x.re = YS_REGEX_COMPILE(args[argidx]);
						x.polarity = false;
						expect_stdout.push_back(x);
					} catch (const std::regex_error& e) {
						log_cmd_error("Error in regex expression '%s' !\n", args[argidx].c_str());
					}

				} else
					log_cmd_error("Unknown option \"%s\" or \"--\" doesn\'t precede command.\n", args[argidx].c_str());
			}
		}

		log_header(design, "Executing command \"%s\".\n", cmd.c_str());
		log_push();

		fflush(stdout);
		bool keep_reading = true;
		int status = 0;
		int retval = 0;

#ifndef EMSCRIPTEN
		FILE *f = popen(cmd.c_str(), "r");
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

				if (flag_expect_stdout)
					for(auto &x : expect_stdout)
						if (std::regex_search(line, x.re))
							x.matched = true;

				pos = linebuf.find('\n');
			}
		}
		status = pclose(f);
#endif

		if(WIFEXITED(status)) {
		    retval = WEXITSTATUS(status);
		}
		else if(WIFSIGNALED(status)) {
		    retval = WTERMSIG(status);
		}
		else if(WIFSTOPPED(status)) {
		    retval = WSTOPSIG(status);
		}

		if (flag_expect_return && retval != expect_return_value)
			log_cmd_error("Return value %d did not match expected return value %d.\n", retval, expect_return_value);

		if (flag_expect_stdout)
			for (auto &x : expect_stdout)
				if (x.polarity ^ x.matched)
					log_cmd_error("Command stdout did%s have a line matching given regex \"%s\".\n", (x.polarity? " not" : ""), x.str.c_str());

		log_pop();
	}
} ExecPass;

PRIVATE_NAMESPACE_END
