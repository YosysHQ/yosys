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
#include "frontends/verific/verific_command.h"

#ifdef YOSYS_ENABLE_VERIFIC

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Woverloaded-virtual"
#endif

#include "Message.h"

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
#include "VerificExtensions.h"
#endif

#ifdef __clang__
#pragma clang diagnostic pop
#endif

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct VerificPass : public Pass {
	VerificPass() : Pass("verific", "load Verilog and VHDL designs using Verific") { }

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
	void on_register() override	{ VerificExtensions::Reset(); }
#endif

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		log("    verific {-vlog95|-vlog2k|-sv2005|-sv2009|-sv2012|\n");
		log("             -sv2017|-sv2023|-sv} <verilog-file>..\n");
		log("\n");
		log("Load the specified Verilog/SystemVerilog files into Verific.\n");
		log("Note that -sv option will use latest supported SystemVerilog standard.\n");
		log("\n");
		log("All files specified in one call to this command are one compilation unit.\n");
		log("Files passed to different calls to this command are treated as belonging to\n");
		log("different compilation units.\n");
		log("\n");
		log("Additional -D<macro>[=<value>] options may be added after the option indicating\n");
		log("the language version (and before file names) to set additional verilog defines.\n");
		log("The macros YOSYS, SYNTHESIS, and VERIFIC are defined implicitly.\n");
		log("\n");
		log("\n");
		log("    verific -formal <verilog-file>..\n");
		log("\n");
		log("Like -sv, but define FORMAL instead of SYNTHESIS.\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_VHDL_SUPPORT
		log("    verific {-vhdl87|-vhdl93|-vhdl2k|-vhdl2008|-vhdl2019|-vhdl} <vhdl-file>..\n");
		log("\n");
		log("Load the specified VHDL files into Verific.\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_EDIF_SUPPORT
		log("    verific {-edif} <edif-file>..\n");
		log("\n");
		log("Load the specified EDIF files into Verific.\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_LIBERTY_SUPPORT
		log("    verific {-liberty} <liberty-file>..\n");
		log("\n");
		log("Load the specified Liberty files into Verific.\n");
		log("Default library when -work is not present is one specified in liberty file.\n");
		log("To use from SystemVerilog or VHDL use -L to specify liberty library.\n");
		log("\n");
		log("    -lib\n");
		log("        only create empty blackbox modules\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		log("    verific {-f|-F} [-vlog95|-vlog2k|-sv2005|-sv2009|\n");
#ifdef VERIFIC_VHDL_SUPPORT
		log("                     -vhdl87|-vhdl93|-vhdl2k|-vhdl2008|-vhdl2019|-vhdl|\n");
#endif
		log("                     -sv2012|-sv2017|-sv2023|-sv|-formal] <command-file>\n");
		log("\n");
		log("Load and execute the specified command file.\n");
		log("Override verilog parsing mode can be set.\n");
		log("The macros YOSYS, SYNTHESIS/FORMAL, and VERIFIC are defined implicitly.\n");
		log("\n");
		log("Command file parser supports following commands in file:\n");
		log("    +define+<MACRO>=<VALUE> - defines macro\n");
		log("    -u                      - upper case all identifier (makes Verilog parser\n");
		log("                              case insensitive)\n");
		log("    -v <filepath>           - register library name (file)\n");
		log("    -y <filepath>           - register library name (directory)\n");
		log("    +incdir+<filepath>      - specify include dir\n");
		log("    +libext+<filepath>      - specify library extension\n");
		log("    +liborder+<id>          - add library in ordered list\n");
		log("    +librescan              - unresolved modules will be always searched\n");
		log("                              starting with the first library specified\n");
		log("                              by -y/-v options.\n");
		log("    -f/-file <filepath>     - nested -f option\n");
		log("    -F <filepath>           - nested -F option (relative path)\n");
		log("    parse files:\n");
		log("        <filepath>\n");
		log("        +systemverilogext+<filepath>\n");
		log("        +verilog1995ext+<filepath>\n");
		log("        +verilog2001ext+<filepath>\n");
		log("\n");
		log("    analysis mode:\n");
		log("        -ams\n");
		log("        +v2k\n");
		log("        -sverilog\n");
		log("\n");
		log("\n");
#endif
		log("    verific [-work <libname>] {-sv|-vhdl|...} <hdl-file>\n");
		log("\n");
		log("Load the specified Verilog/SystemVerilog/VHDL file into the specified library.\n");
		log("(default library when -work is not present: \"work\")\n");
		log("\n");
		log("\n");
		log("    verific [-L <libname>] {-sv|-vhdl|...} <hdl-file>\n");
		log("\n");
		log("Look up external definitions in the specified library.\n");
		log("(-L may be used more than once)\n");
		log("\n");
		log("\n");
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		log("    verific -vlog-incdir <directory>..\n");
		log("\n");
		log("Add Verilog include directories.\n");
		log("\n");
		log("\n");
		log("    verific -vlog-libdir <directory>..\n");
		log("\n");
		log("Add Verilog library directories. Verific will search in this directories to\n");
		log("find undefined modules.\n");
		log("\n");
		log("\n");
		log("    verific -vlog-libext <extension>..\n");
		log("\n");
		log("Add Verilog library extensions, used when searching in library directories.\n");
		log("\n");
		log("\n");
		log("    verific -vlog-define <macro>[=<value>]..\n");
		log("\n");
		log("Add Verilog defines.\n");
		log("\n");
		log("\n");
		log("    verific -vlog-undef <macro>..\n");
		log("\n");
		log("Remove Verilog defines previously set with -vlog-define.\n");
		log("\n");
		log("\n");
#endif
		log("    verific -set-error <msg_id>..\n");
		log("    verific -set-warning <msg_id>..\n");
		log("    verific -set-info <msg_id>..\n");
		log("    verific -set-ignore <msg_id>..\n");
		log("\n");
		log("Set message severity. <msg_id> is the string in square brackets when a message\n");
		log("is printed, such as VERI-1209.\n");
		log("Also errors, warnings, infos and comments could be used to set new severity for\n");
		log("all messages of certain type.\n");
		log("\n");
		log("\n");
		log("    verific -cleanup\n");
		log("\n");
		log("Discard all files read so far without importing them and reset the internal\n");
		log("state of Verific.\n");
		log("\n");
		log("\n");
		log("    verific -import [options] <top>..\n");
		log("\n");
		log("Elaborate the design for the specified top modules or configurations, import to\n");
		log("Yosys and reset the internal state of Verific.\n");
		log("\n");
		log("Import options:\n");
		log("\n");
		log("  -all\n");
		log("    Elaborate all modules, not just the hierarchy below the given top\n");
		log("    modules. With this option the list of modules to import is optional.\n");
		log("\n");
		log("  -gates\n");
		log("    Create a gate-level netlist.\n");
		log("\n");
		log("  -flatten\n");
		log("    Flatten the design in Verific before importing.\n");
		log("\n");
		log("  -extnets\n");
		log("    Resolve references to external nets by adding module ports as needed.\n");
		log("\n");
		log("  -no-split-complex-ports\n");
		log("    Complex ports (structs or arrays) are not split and remain packed as a single port.\n");
		log("\n");
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		log("  -autocover\n");
		log("    Generate automatic cover statements for all asserts\n");
		log("\n");
#endif
		log("  -fullinit\n");
		log("    Keep all register initializations, even those for non-FF registers.\n");
		log("\n");
		log("  -cells\n");
		log("    Import all cell definitions from Verific loaded libraries even if they are\n");
		log("    unused in design. Useful with \"-edif\" and \"-liberty\" option.\n");
		log("\n");
		log("  -chparam name value \n");
		log("    Elaborate the specified top modules (all modules when -all given) using\n");
		log("    this parameter value. Modules on which this parameter does not exist will\n");
		log("    cause Verific to produce a VERI-1928 or VHDL-1676 message. This option\n");
		log("    can be specified multiple times to override multiple parameters.\n");
		log("    String values must be passed in double quotes (\").\n");
		log("\n");
		log("  -v, -vv\n");
		log("    Verbose log messages. (-vv is even more verbose than -v.)\n");
		log("\n");
		log("  -pp <filename>\n");
		log("    Pretty print design after elaboration to specified file.\n");
		log("\n");
		log("The following additional import options are useful for debugging the Verific\n");
		log("bindings (for Yosys and/or Verific developers):\n");
		log("\n");
		log("  -k\n");
		log("    Keep going after an unsupported verific primitive is found. The\n");
		log("    unsupported primitive is added as blackbox module to the design.\n");
		log("    This will also add all SVA related cells to the design parallel to\n");
		log("    the checker logic inferred by it.\n");
		log("\n");
		log("  -V\n");
		log("    Import Verific netlist as-is without translating to Yosys cell types. \n");
		log("\n");
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		log("  -nosva\n");
		log("    Ignore SVA properties, do not infer checker logic.\n");
		log("\n");
		log("  -sva-continue-on-err\n");
		log("    Turns unsupported SVA from an error into a warning. Properties are imported\n");
		log("    with their trigger condition replaced with 'x and with an `unsupported_sva'\n");
		log("    attribute to produce a later error in SBY if they remain in the design.\n");
		log("\n");
		log("  -L <int>\n");
		log("    Maximum number of ctrl bits for SVA checker FSMs (default=16).\n");
		log("\n");
#endif
		log("  -n\n");
		log("    Keep all Verific names on instances and nets. By default only\n");
		log("    user-declared names are preserved.\n");
		log("\n");
		log("  -d <dump_file>\n");
		log("    Dump the Verific netlist as a verilog file.\n");
		log("\n");
		log("\n");
		log("    verific [-work <libname>] -pp [options] <filename> [<module>]..\n");
		log("\n");
		log("Pretty print design (or just module) to the specified file from the\n");
		log("specified library. (default library when -work is not present: \"work\")\n");
		log("\n");
		log("Pretty print options:\n");
		log("\n");
		log("  -verilog\n");
		log("    Save output for Verilog/SystemVerilog design modules (default).\n");
		log("\n");
		log("  -vhdl\n");
		log("    Save output for VHDL design units.\n");
		log("\n");
		log("\n");
		log("    verific -cfg [<name> [<value>]]\n");
		log("\n");
		log("Get/set Verific runtime flags.\n");
		log("\n");
		log("\n");
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		log("    verific -target <target> [-family <family>]]\n");
		log("\n");
		log("Loads required cell definitions for specified <target> and <family>.\n");
		log("\n");
		log("\n");
#endif
#if defined(YOSYS_ENABLE_VERIFIC) and defined(YOSYSHQ_VERIFIC_EXTENSIONS)
		VerificExtensions::Help();
#endif
		log("Use YosysHQ Tabby CAD Suite if you need Yosys+Verific.\n");
		log("https://www.yosyshq.com/\n");
		log("\n");
		log("Contact office@yosyshq.com for free evaluation\n");
		log("binaries of YosysHQ Tabby CAD Suite.\n");
		log("\n");
	}
#ifdef YOSYS_ENABLE_VERIFIC
	void log_release()
	{
		const char *release_str = Message::ReleaseString();
		time_t release_time = Message::ReleaseDate();
		char *release_tmstr = ctime(&release_time);

		if (release_str == nullptr)
			release_str = "(no release string)";

		for (char *p = release_tmstr; *p; p++)
			if (*p == '\n') *p = 0;

		log("Built with Verific %s, released at %s.\n", release_str, release_tmstr);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		if (check_noverific_env())
			log_cmd_error("This version of Yosys is built without Verific support.\n"
					"\n"
					"Use YosysHQ Tabby CAD Suite if you need Yosys+Verific.\n"
					"https://www.yosyshq.com/\n"
					"\n"
					"Contact office@yosyshq.com for free evaluation\n"
					"binaries of YosysHQ Tabby CAD Suite.\n");

		log_header(design, "Executing VERIFIC (loading SystemVerilog and VHDL designs using Verific).\n");

		std::unique_ptr<VerificSession> ending_session = {};
		{
			VerificCommand command(*this, args, design);

			if (command.mode == "-cleanup") {
				(void)VerificSession::deferred_end(design);
				return;
			}

			if (command.mode == "-import") {
				ending_session = VerificSession::deferred_end(design);
				if (!ending_session)
					log_cmd_error("Nothing was read into Verific for this design.\n");
			} else {
				VerificSession::begin(design);
			}

			verific_setup();
			verific_verbose = 0;
			verific_sva_fsm_limit = 16;
			log_release();
			command.run();
		}

		if (!verific_error_msg.empty())
			log_error("%s\n", verific_error_msg);
	}
#else /* YOSYS_ENABLE_VERIFIC */
	void execute(std::vector<std::string>, RTLIL::Design *) override {
		log_cmd_error("This version of Yosys is built without Verific support.\n"
				"\n"
				"Use YosysHQ Tabby CAD Suite if you need Yosys+Verific.\n"
				"https://www.yosyshq.com/\n"
				"\n"
				"Contact office@yosyshq.com for free evaluation\n"
				"binaries of YosysHQ Tabby CAD Suite.\n");
	}
#endif
} VerificPass;

PRIVATE_NAMESPACE_END
