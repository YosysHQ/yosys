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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <dirent.h>
#include <errno.h>
#include <limits.h>

YOSYS_NAMESPACE_BEGIN

struct Vhdl2verilogPass : public Pass {
	Vhdl2verilogPass() : Pass("vhdl2verilog", "importing VHDL designs using vhdl2verilog") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    vhdl2verilog [options] <vhdl-file>..\n");
		log("\n");
		log("This command reads VHDL source files using the 'vhdl2verilog' tool and the\n");
		log("Yosys Verilog frontend.\n");
		log("\n");
		log("    -out <out_file>\n");
		log("        do not import the vhdl2verilog output. instead write it to the\n");
		log("        specified file.\n");
		log("\n");
		log("    -vhdl2verilog_dir <directory>\n");
		log("        do use the specified vhdl2verilog installation. this is the directory\n");
		log("        that contains the setup_env.sh file. when this option is not present,\n");
		log("        it is assumed that vhdl2verilog is in the PATH environment variable.\n");
		log("\n");
		log("    -top <top-entity-name>\n");
		log("        The name of the top entity. This option is mandatory.\n");
		log("\n");
		log("The following options are passed as-is to vhdl2verilog:\n");
		log("\n");
		log("    -arch <architecture_name>\n");
		log("    -unroll_generate\n");
		log("    -nogenericeval\n");
		log("    -nouniquify\n");
		log("    -oldparser\n");
		log("    -suppress <list>\n");
		log("    -quiet\n");
		log("    -nobanner\n");
		log("    -mapfile <file>\n");
		log("\n");
		log("vhdl2verilog can be obtained from:\n");
		log("http://www.edautils.com/vhdl2verilog.html\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing VHDL2VERILOG (importing VHDL designs using vhdl2verilog).\n");
		log_push();

		std::string out_file, top_entity;
		std::string vhdl2verilog_dir;
		std::string extra_opts;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-out" && argidx+1 < args.size()) {
				out_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_entity = args[++argidx];
				continue;
			}
			if (args[argidx] == "-vhdl2verilog_dir" && argidx+1 < args.size()) {
				vhdl2verilog_dir = args[++argidx];
				continue;
			}
			if ((args[argidx] == "-arch" || args[argidx] == "-suppress" || args[argidx] == "-mapfile") && argidx+1 < args.size()) {
				if (args[argidx] == "-mapfile" && !args[argidx+1].empty() && args[argidx+1][0] != '/') {
					char pwd[PATH_MAX];
					if (!getcwd(pwd, sizeof(pwd))) {
						log_cmd_error("getcwd failed: %s", strerror(errno));
						log_abort();
					}
					args[argidx+1] = pwd + ("/" + args[argidx+1]);
				}
				extra_opts += std::string(" ") + args[argidx];
				extra_opts += std::string(" '") + args[++argidx] + std::string("'");
				continue;
			}
			if (args[argidx] == "-unroll_generate" || args[argidx] == "-nogenericeval" || args[argidx] == "-nouniquify" ||
					args[argidx] == "-oldparser" || args[argidx] == "-quiet" || args[argidx] == "-nobanner") {
				extra_opts += std::string(" ") + args[argidx];
				continue;
			}
			break;
		}

		if (argidx == args.size())
			cmd_error(args, argidx, "Missing filenames.");
		if (args[argidx].substr(0, 1) == "-")
			cmd_error(args, argidx, "Unknown option.");
		if (top_entity.empty())
			log_cmd_error("Missing -top option.\n");

		char tempdir_name[] = "/tmp/yosys-vhdl2verilog-XXXXXX";
		char *p = mkdtemp(tempdir_name);
		log("Using temp directory %s.\n", tempdir_name);
		if (p == NULL)
			log_error("For some reason mkdtemp() failed!\n");

		if (!out_file.empty() && out_file[0] != '/') {
			char pwd[PATH_MAX];
			if (!getcwd(pwd, sizeof(pwd))) {
				log_cmd_error("getcwd failed: %s", strerror(errno));
				log_abort();
			}
			out_file = pwd + ("/" + out_file);
		}

		FILE *f = fopen(stringf("%s/files.list", tempdir_name).c_str(), "wt");
		while (argidx < args.size()) {
			std::string file = args[argidx++];
			if (file.empty())
				continue;
			if (file[0] != '/') {
				char pwd[PATH_MAX];
				if (!getcwd(pwd, sizeof(pwd))) {
					log_cmd_error("getcwd failed: %s", strerror(errno));
					log_abort();
				}
				file = pwd + ("/" + file);
			}
			fprintf(f, "%s\n", file.c_str());
			log("Adding '%s' to the file list.\n", file.c_str());
		}
		fclose(f);

		std::string command = "exec 2>&1; ";
		if (!vhdl2verilog_dir.empty())
			command += stringf("cd '%s'; . ./setup_env.sh; ", vhdl2verilog_dir.c_str());
		command += stringf("cd '%s'; vhdl2verilog -out '%s' -filelist files.list -top '%s'%s", tempdir_name,
				out_file.empty() ? "vhdl2verilog_output.v" : out_file.c_str(), top_entity.c_str(), extra_opts.c_str());

		log("Running '%s'..\n", command.c_str());

                errno = ENOMEM;  // popen does not set errno if memory allocation fails, therefore set it by hand
		f = popen(command.c_str(), "r");
		if (f == NULL)
			log_error("Opening pipe to `%s' for reading failed: %s\n", command.c_str(), strerror(errno));

		char logbuf[1024];
		while (fgets(logbuf, 1024, f) != NULL)
			log("%s", logbuf);

		int ret = pclose(f);
		if (ret < 0)
			log_error("Closing pipe to `%s' failed: %s\n", command.c_str(), strerror(errno));
		if (WEXITSTATUS(ret) != 0)
			log_error("Execution of command \"%s\" failed: the shell returned %d\n", command.c_str(), WEXITSTATUS(ret));

		if (out_file.empty()) {
			std::ifstream ff;
			ff.open(stringf("%s/vhdl2verilog_output.v", tempdir_name).c_str());
			if (ff.fail())
				log_error("Can't open vhdl2verilog output file `vhdl2verilog_output.v'.\n");
			Frontend::frontend_call(design, &ff, stringf("%s/vhdl2verilog_output.v", tempdir_name), "verilog");
		}

		log_header("Removing temp directory `%s':\n", tempdir_name);
		if (system(stringf("rm -rf '%s'", tempdir_name).c_str()) != 0)
			log_error("Execution of \"rm -rf '%s'\" failed!\n", tempdir_name);

		log_pop();
	}
} Vhdl2verilogPass;
 
YOSYS_NAMESPACE_END

