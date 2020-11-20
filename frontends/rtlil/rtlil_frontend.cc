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
 *  ---
 *
 *  A very simple and straightforward frontend for the RTLIL text
 *  representation.
 *
 */

#include "rtlil_frontend.h"
#include "kernel/register.h"
#include "kernel/log.h"

void rtlil_frontend_yyerror(char const *s)
{
	YOSYS_NAMESPACE_PREFIX log_error("Parser error in line %d: %s\n", rtlil_frontend_yyget_lineno(), s);
}

YOSYS_NAMESPACE_BEGIN

struct RTLILFrontend : public Frontend {
	RTLILFrontend() : Frontend("rtlil", "read modules from RTLIL file") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read_rtlil [filename]\n");
		log("\n");
		log("Load modules from an RTLIL file to the current design. (RTLIL is a text\n");
		log("representation of a design in yosys's internal format.)\n");
		log("\n");
		log("    -nooverwrite\n");
		log("        ignore re-definitions of modules. (the default behavior is to\n");
		log("        create an error message if the existing module is not a blackbox\n");
		log("        module, and overwrite the existing module if it is a blackbox module.)\n");
		log("\n");
		log("    -overwrite\n");
		log("        overwrite existing modules with the same name\n");
		log("\n");
		log("    -lib\n");
		log("        only create empty blackbox modules\n");
		log("\n");
	}
	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		RTLIL_FRONTEND::flag_nooverwrite = false;
		RTLIL_FRONTEND::flag_overwrite = false;
		RTLIL_FRONTEND::flag_lib = false;

		log_header(design, "Executing RTLIL frontend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-nooverwrite") {
				RTLIL_FRONTEND::flag_nooverwrite = true;
				RTLIL_FRONTEND::flag_overwrite = false;
				continue;
			}
			if (arg == "-overwrite") {
				RTLIL_FRONTEND::flag_nooverwrite = false;
				RTLIL_FRONTEND::flag_overwrite = true;
				continue;
			}
			if (arg == "-lib") {
				RTLIL_FRONTEND::flag_lib = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		log("Input filename: %s\n", filename.c_str());

		RTLIL_FRONTEND::lexin = f;
		RTLIL_FRONTEND::current_design = design;
		rtlil_frontend_yydebug = false;
		rtlil_frontend_yyrestart(NULL);
		rtlil_frontend_yyparse();
		rtlil_frontend_yylex_destroy();
	}
} RTLILFrontend;

struct IlangFrontend : public Frontend {
	IlangFrontend() : Frontend("ilang", "(deprecated) alias of read_rtlil") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("See `help read_rtlil`.\n");
		log("\n");
	}
	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		RTLILFrontend.execute(f, filename, args, design);
	}
} IlangFrontend;

YOSYS_NAMESPACE_END

