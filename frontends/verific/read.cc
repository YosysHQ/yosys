/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "frontends/verific/verific.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ReadPass : public Pass {
	ReadPass() : Pass("read", "load HDL designs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read {-vlog95|-vlog2k|-sv2005|-sv2009|-sv2012|\n");
		log("          -sv2017|-sv2023|-sv|-formal} <verilog-file>..\n");
		log("\n");
		log("Load the specified Verilog/SystemVerilog files. (Full SystemVerilog support\n");
		log("is only available via Verific.)\n");
		log("\n");
		log("Additional -D<macro>[=<value>] options may be added after the option indicating\n");
		log("the language version (and before file names) to set additional verilog defines.\n");
		log("\n");
		log("\n");
#ifdef VERIFIC_VHDL_SUPPORT
		log("    read {-vhdl87|-vhdl93|-vhdl2k|-vhdl2008|-vhdl2019|-vhdl} <vhdl-file>..\n");
		log("\n");
		log("Load the specified VHDL files. (Requires Verific.)\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_EDIF_SUPPORT
		log("    read {-edif} <edif-file>..\n");
		log("\n");
		log("Load the specified EDIF files. (Requires Verific.)\n");
		log("\n");
		log("\n");
#endif
		log("    read {-liberty} <liberty-file>..\n");
		log("\n");
		log("Load the specified Liberty files.\n");
		log("\n");
		log("    -lib\n");
		log("        only create empty blackbox modules\n");
		log("\n");
		log("\n");
		log("    read {-f|-F} <command-file>\n");
		log("\n");
		log("Load and execute the specified command file.\n");
		log("Check verific command for more information about supported commands in file.\n");
		log("\n");
		log("\n");
		log("    read -define <macro>[=<value>]..\n");
		log("\n");
		log("Set global Verilog/SystemVerilog defines.\n");
		log("\n");
		log("\n");
		log("    read -undef <macro>..\n");
		log("\n");
		log("Unset global Verilog/SystemVerilog defines.\n");
		log("\n");
		log("\n");
		log("    read -incdir <directory>\n");
		log("\n");
		log("Add directory to global Verilog/SystemVerilog include directories.\n");
		log("\n");
		log("\n");
		log("    read -verific\n");
		log("    read -noverific\n");
		log("\n");
		log("Subsequent calls to 'read' will either use or not use Verific. Calling 'read'\n");
		log("with -verific will result in an error on Yosys binaries that are built without\n");
		log("Verific support. The default is to use Verific if it is available.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
#ifdef YOSYS_ENABLE_VERIFIC
		static bool verific_available = !check_noverific_env();
#else
		static bool verific_available = false;
#endif
		static bool use_verific = verific_available;

		if (args.size() < 2 || args[1][0] != '-')
			cmd_error(args, 1, "Missing mode parameter.\n");

		if (args[1] == "-verific" || args[1] == "-noverific") {
			if (args.size() != 2)
				cmd_error(args, 1, "Additional arguments to -verific/-noverific.\n");
			if (args[1] == "-verific") {
				if (!verific_available)
					cmd_error(args, 1, "This version of Yosys is built without Verific support.\n");
				use_verific = true;
			} else {
				use_verific = false;
			}
			return;
		}

		if (args.size() < 3)
			cmd_error(args, 3, "Missing file name parameter.\n");

		if (args[1] == "-vlog95" || args[1] == "-vlog2k") {
			if (use_verific) {
				args[0] = "verific";
			} else {
				args[0] = "read_verilog";
				args[1] = "-defer";
			}
			Pass::call(design, args);
			return;
		}

		if (args[1] == "-sv2005" || args[1] == "-sv2009" || args[1] == "-sv2012" ||
			args[1] == "-sv2017" || args[1] == "-sv2023" || args[1] == "-sv" || args[1] == "-formal") {
			if (use_verific) {
				args[0] = "verific";
			} else {
				args[0] = "read_verilog";
				if (args[1] == "-formal")
					args.insert(args.begin()+1, std::string());
				args[1] = "-sv";
				args.insert(args.begin()+1, "-defer");
			}
			Pass::call(design, args);
			return;
		}

#ifdef VERIFIC_VHDL_SUPPORT
		if (args[1] == "-vhdl87" || args[1] == "-vhdl93" || args[1] == "-vhdl2k" || args[1] == "-vhdl2008" || args[1] == "-vhdl2019" || args[1] == "-vhdl") {
			if (use_verific) {
				args[0] = "verific";
				Pass::call(design, args);
			} else {
				cmd_error(args, 1, "This version of Yosys is built without Verific support.\n");
			}
			return;
		}
#endif
#ifdef VERIFIC_EDIF_SUPPORT
		if (args[1] == "-edif") {
			if (use_verific) {
				args[0] = "verific";
				Pass::call(design, args);
			} else {
				cmd_error(args, 1, "This version of Yosys is built without Verific support.\n");
			}
			return;
		}
#endif
		if (args[1] == "-liberty") {
			if (use_verific) {
				args[0] = "verific";
			} else {
				args[0] = "read_liberty";
			}
			Pass::call(design, args);
			return;
		}
		if (args[1] == "-f" || args[1] == "-F") {
			if (use_verific) {
				args[0] = "verific";
			} else {
				args[0] = "read_verilog_file_list";
			}
			Pass::call(design, args);
			return;
		}

		if (args[1] == "-define") {
			if (use_verific) {
				args[0] = "verific";
				args[1] = "-vlog-define";
				Pass::call(design, args);
			}
			args[0] = "verilog_defines";
			args.erase(args.begin()+1, args.begin()+2);
			for (int i = 1; i < GetSize(args); i++)
				args[i] = "-D" + args[i];
			Pass::call(design, args);
			return;
		}

		if (args[1] == "-undef") {
			if (use_verific) {
				args[0] = "verific";
				args[1] = "-vlog-undef";
				Pass::call(design, args);
			}
			args[0] = "verilog_defines";
			args.erase(args.begin()+1, args.begin()+2);
			for (int i = 1; i < GetSize(args); i++)
				args[i] = "-U" + args[i];
			Pass::call(design, args);
			return;
		}

		if (args[1] == "-incdir") {
			if (use_verific) {
				args[0] = "verific";
				args[1] = "-vlog-incdir";
				Pass::call(design, args);
			}
			args[0] = "verilog_defaults";
			args[1] = "-add";
			for (int i = 2; i < GetSize(args); i++)
				args[i] = "-I" + args[i];
			Pass::call(design, args);
			return;
		}

		cmd_error(args, 1, "Missing or unsupported mode parameter.\n");
	}
} ReadPass;

PRIVATE_NAMESPACE_END
