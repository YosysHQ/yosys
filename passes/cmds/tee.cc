/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2014  Johann Glaser <Johann.Glaser@gmx.at>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TeePass : public Pass {
	TeePass() : Pass("tee", "redirect command output to file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    tee [-q] [-o logfile|-a logfile] cmd\n");
		log("\n");
		log("Execute the specified command, optionally writing the commands output to the\n");
		log("specified logfile(s).\n");
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
		log("    +INT, -INT\n");
		log("        Add/subract INT from the -v setting for this command.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::vector<FILE*> backup_log_files, files_to_close;
		int backup_log_verbose_level = log_verbose_level;
		backup_log_files = log_files;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-q" && files_to_close.empty()) {
				log_files.clear();
				continue;
			}
			if ((args[argidx] == "-o" || args[argidx] == "-a") && argidx+1 < args.size()) {
				const char *open_mode = args[argidx] == "-o" ? "w" : "a+";
				FILE *f = fopen(args[++argidx].c_str(), open_mode);
				if (f == NULL) {
					for (auto cf : files_to_close)
						fclose(cf);
					log_cmd_error("Can't create file %s.\n", args[argidx].c_str());
				}
				log_files.push_back(f);
				files_to_close.push_back(f);
				continue;
			}
			if (GetSize(args[argidx]) >= 2 && (args[argidx][0] == '-' || args[argidx][0] == '+') && args[argidx][1] >= '0' && args[argidx][1] <= '9') {
				log_verbose_level += atoi(args[argidx].c_str());
				continue;
			}
			break;
		}

		try {
			std::vector<std::string> new_args(args.begin() + argidx, args.end());
			Pass::call(design, new_args);
		} catch (...) {
			for (auto cf : files_to_close)
				fclose(cf);
			log_files = backup_log_files;
			throw;
		}

		for (auto cf : files_to_close)
			fclose(cf);

		log_verbose_level = backup_log_verbose_level;
		log_files = backup_log_files;
	}
} TeePass;

PRIVATE_NAMESPACE_END
