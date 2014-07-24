/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Clifford Wolf <clifford@clifford.at>
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
#include "kernel/rtlil.h"
#include "kernel/log.h"

struct CoverPass : public Pass {
	CoverPass() : Pass("cover", "print code coverage counters") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    cover [-q] [-o logfile|-a logfile]\n");
		log("\n");
		log("Print the code coverage counters collected using the cover() macro in the Yosys\n");
		log("C++ code. This is useful to figure out what parts of Yosys are utilized by a\n");
		log("test bench.\n");
		log("\n");
		log("    -q\n");
		log("        Do not print output to the normal destination (console and/or log file)\n");
		log("\n");
		log("    -o logfile\n");
		log("        Write output to this file, truncate if exists.\n");
		log("\n");
		log("    -a logfile\n");
		log("        Write output to this file, append if exists.\n");
		log("\n");
		log("\n");
		log("It is also possible to instruct Yosys to print the coverage counters to a file\n");
		log("using environment variables.\n");
		log("\n");
		log("    YOSYS_COVER_DIR=\"{dir-name}\" yosys {args}n");
		log("\n");
		log("        This will create a file (with an auto-generated name) in this\n");
		log("        directory and wire the coverage counters to it.\n");
		log("\n");
		log("    YOSYS_COVER_FILE=\"{file-name}\" yosys {args}n");
		log("\n");
		log("        This will append the coverage counters to the specified file.\n");
		log("\n");
		log("\n");
		log("Hint: Use the following AWK command to consolidate Yosys coverage files:\n");
		log("\n");
		log("    gawk '{ p[$3] = $1; c[$3] += $2; } END { for (i in p)\n");
		log("      printf \"%%-60s %%10d %%s\\n\", p[i], c[i], i; }' {files} | sort -k3\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::vector<FILE*> out_files;
		bool do_log = true;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-q") {
				do_log = false;
				continue;
			}
			if ((args[argidx] == "-o" || args[argidx] == "-a") && argidx+1 < args.size()) {
				const char *open_mode = args[argidx] == "-o" ? "w" : "a+";
				FILE *f = fopen(args[++argidx].c_str(), open_mode);
				if (f == NULL) {
					for (auto f : out_files)
						fclose(f);
					log_cmd_error("Can't create file %s.\n", args[argidx].c_str());
				}
				out_files.push_back(f);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (do_log) {
			log_header("Printing code coverage counters.\n");
			log("\n");
		}

#ifndef NDEBUG
		for (auto &it : get_coverage_data()) {
			for (auto f : out_files)
				fprintf(f, "%-60s %10d %s\n", it.second.first.c_str(), it.second.second, it.first.c_str());
			if (do_log)
				log("%-60s %10d %s\n", it.second.first.c_str(), it.second.second, it.first.c_str());
		}
#else
		for (auto f : out_files)
			fclose(f);

		log_cmd_error("Coverage counters are only available in debug builds of Yosys.");
#endif

		for (auto f : out_files)
			fclose(f);
	}
} CoverPass;

