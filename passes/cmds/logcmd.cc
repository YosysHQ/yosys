/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

struct LogPass : public Pass {
	LogPass() : Pass("log", "print text and log files") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    log string\n");
		log("\n");
		log("Print the given string to the screen and/or the log file. This is useful for TCL\n");
		log("scripts, because the TCL command \"puts\" only goes to stdout but not to\n");
		log("logfiles.\n");
		log("\n");
		log("    -stdout\n");
		log("        Print the output to stdout too. This is useful when all Yosys is executed\n");
		log("        with a script and the -q (quiet operation) argument to notify the user.\n");
		log("\n");
		log("    -stderr\n");
		log("        Print the output to stderr too.\n");
		log("\n");
		log("    -nolog\n");
		log("        Don't use the internal log() command. Use either -stdout or -stderr,\n");
		log("        otherwise no output will be generated at all.\n");
		log("\n");
		log("    -n\n");
		log("        do not append a newline\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design*)
	{
		size_t argidx;
		bool to_stdout = false;
		bool to_stderr = false;
		bool to_log    = true;
		bool newline   = true;
		std::string text;

		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if      (args[argidx] == "-stdout") to_stdout = true;
			else if (args[argidx] == "-stderr") to_stderr = true;
			else if (args[argidx] == "-nolog")  to_log    = false;
			else if (args[argidx] == "-n")      newline   = false;
			else break;
		}
		for (; argidx < args.size(); argidx++)
			text += args[argidx] + ' ';
		if (!text.empty()) text.resize(text.size()-1);

		if (to_stdout) fprintf(stdout, (newline ? "%s\n" : "%s"), text.c_str());
		if (to_stderr) fprintf(stderr, (newline ? "%s\n" : "%s"), text.c_str());
		if (to_log)    log    (        (newline ? "%s\n" : "%s"), text.c_str());
	}
} LogPass;

PRIVATE_NAMESPACE_END
