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

#include "kernel/yosys.h"
#include <sys/types.h>

#ifndef _WIN32
#  include <unistd.h>
#else
#  include <io.h>
#endif

#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct CoverPass : public Pass {
	CoverPass() : Pass("cover", "print code coverage counters") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    cover [options] [pattern]\n");
		log("\n");
		log("Print the code coverage counters collected using the cover() macro in the Yosys\n");
		log("C++ code. This is useful to figure out what parts of Yosys are utilized by a\n");
		log("test bench.\n");
		log("\n");
		log("    -q\n");
		log("        Do not print output to the normal destination (console and/or log file)\n");
		log("\n");
		log("    -o file\n");
		log("        Write output to this file, truncate if exists.\n");
		log("\n");
		log("    -a file\n");
		log("        Write output to this file, append if exists.\n");
		log("\n");
		log("    -d dir\n");
		log("        Write output to a newly created file in the specified directory.\n");
		log("\n");
		log("When one or more pattern (shell wildcards) are specified, then only counters\n");
		log("matching at least one pattern are printed.\n");
		log("\n");
		log("\n");
		log("It is also possible to instruct Yosys to print the coverage counters on program\n");
		log("exit to a file using environment variables:\n");
		log("\n");
		log("    YOSYS_COVER_DIR=\"{dir-name}\" yosys {args}\n");
		log("\n");
		log("        This will create a file (with an auto-generated name) in this\n");
		log("        directory and write the coverage counters to it.\n");
		log("\n");
		log("    YOSYS_COVER_FILE=\"{file-name}\" yosys {args}\n");
		log("\n");
		log("        This will append the coverage counters to the specified file.\n");
		log("\n");
		log("\n");
		log("Hint: Use the following AWK command to consolidate Yosys coverage files:\n");
		log("\n");
		log("    gawk '{ p[$3] = $1; c[$3] += $2; } END { for (i in p)\n");
		log("      printf \"%%-60s %%10d %%s\\n\", p[i], c[i], i; }' {files} | sort -k3\n");
		log("\n");
		log("\n");
		log("Coverage counters are only available in Yosys for Linux.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::vector<FILE*> out_files;
		std::vector<std::string> patterns;
		bool do_log = true;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-q") {
				do_log = false;
				continue;
			}
			if ((args[argidx] == "-o" || args[argidx] == "-a" || args[argidx] == "-d") && argidx+1 < args.size()) {
				const char *open_mode = args[argidx] == "-a" ? "a+" : "w";
				const std::string &filename = args[++argidx];
				FILE *f = nullptr;
				if (args[argidx-1] == "-d") {
			#ifdef _WIN32
					log_cmd_error("The 'cover -d' option is not supported on win32.\n");
			#else
					char filename_buffer[4096];
					snprintf(filename_buffer, 4096, "%s/yosys_cover_%d_XXXXXX.txt", filename.c_str(), getpid());
					f = fdopen(mkstemps(filename_buffer, 4), "w");
			#endif
				} else {
					f = fopen(filename.c_str(), open_mode);
				}
				if (f == NULL) {
					for (auto f : out_files)
						fclose(f);
					log_cmd_error("Can't create file %s%s.\n", args[argidx-1] == "-d" ? "in directory " : "", args[argidx].c_str());
				}
				out_files.push_back(f);
				continue;
			}
			break;
		}
		while (argidx < args.size() && args[argidx].compare(0, 1, "-") != 0)
			patterns.push_back(args[argidx++]);
		extra_args(args, argidx, design);

		if (do_log) {
			log_header(design, "Printing code coverage counters.\n");
			log("\n");
		}

#if defined(YOSYS_ENABLE_COVER) && (defined(__linux__) || defined(__FreeBSD__))
		for (auto &it : get_coverage_data()) {
			if (!patterns.empty()) {
				for (auto &p : patterns)
					if (patmatch(p.c_str(), it.first.c_str()))
						goto pattern_match;
				continue;
			}
		pattern_match:
			for (auto f : out_files)
				fprintf(f, "%-60s %10d %s\n", it.second.first.c_str(), it.second.second, it.first.c_str());
			if (do_log)
				log("%-60s %10d %s\n", it.second.first.c_str(), it.second.second, it.first.c_str());
		}
#else
		for (auto f : out_files)
			fclose(f);

		log_cmd_error("This version of Yosys was not built with support for code coverage counters.\n");
#endif

		for (auto f : out_files)
			fclose(f);
	}
} CoverPass;

PRIVATE_NAMESPACE_END
