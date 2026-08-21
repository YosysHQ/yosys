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

#include "slang/util/CommandLine.h"

#include <fmt/color.h>
#include <fmt/format.h>

YOSYS_NAMESPACE_BEGIN

using namespace slang;

bool is_verbose = false;
bool show_build_status = false;

class ColorLogSink : public LogSink
{
public:
	bool should_log(const LogMessage &msg) const override;
	void log(const LogMessage &msg) override;
};

bool ColorLogSink::should_log(const LogMessage &msg) const
{
	if (is_verbose)
		return true;
	else 
		return (msg.severity == LogSeverity::LOG_WARNING || msg.severity == LogSeverity::LOG_ERROR);
}
void ColorLogSink::log(const LogMessage &msg)
{
	FILE *f = stderr;
	switch (msg.severity) {
		case LOG_WARNING:
			fmt::print(f, fg(fmt::terminal_color::bright_yellow), "{}", msg.prefix);
			fmt::print(f, fg(fmt::terminal_color::blue) | fmt::emphasis::bold, "{}", msg.message);
			break;

		case LOG_ERROR:
			fmt::print(f, fg(fmt::terminal_color::bright_red), "{}", msg.prefix);
			fmt::print(f, fg(fmt::terminal_color::blue) | fmt::emphasis::bold, "{}", msg.message);
			break;

		case LOG_HEADER:
			fmt::print(f, fg(fmt::terminal_color::cyan) | fmt::emphasis::bold, "{}", msg.prefix);
			fmt::print(f, fg(fmt::terminal_color::white) | fmt::emphasis::bold, "{}", msg.message);
			break;

		case LOG_COMMENT:
		case LOG_DEBUG:
			fmt::print(f, fg(fmt::terminal_color::bright_black), "{}{}", msg.prefix, msg.message);
			break;

		case LOG_INFO:
		default:
			fmt::print(f, "{}{}", msg.prefix, msg.message);
			break;
	}
}

void yc_error_atexit()
{
	if (!show_build_status)
		return;
	int num_errors = logger().get_errors_total();
	int num_warnings = logger().get_warnings_total();
	bool succeeded = num_errors == 0;
	if (succeeded)
		fmt::print(fg(fmt::terminal_color::bright_green), "Build succeeded: ");
	else
		fmt::print(fg(fmt::terminal_color::bright_red), "Build failed: ");

	fmt::print("{} error{}, {} warning{}\n", num_errors,
							num_errors == 1 ? "" : "s",
							num_warnings,
							num_warnings == 1 ? "" : "s");
} 

class YosysDriver {
public:
	CommandLine cmdLine;

	struct Options {
		std::optional<bool> showHelp;
		std::optional<bool> showVerbose;
		std::optional<bool> showVersion;
		std::optional<bool> printTargets;
		std::optional<bool> printLanguages;
		std::optional<bool> printStandards;

		std::vector<std::string> defines;
		std::vector<std::string> undefines;
		std::optional<std::string> topModule;
		std::optional<std::string> outputFile;
		std::optional<std::string> target;
	} options;

	std::vector<std::string> sourceFiles;

	std::string language;
	std::string standard;

	void addStandardArgs();
	int run(int argc, char **argv);
	void printError(const std::string& message);
};

void YosysDriver::printError(const std::string& message) {
	log_error("%s\n", message);
}

int YosysDriver::run(int argc, char **argv) {
	log_error_atexit = &yc_error_atexit;
	logger().add_sink<ColorLogSink>();

	cmdLine.add("-h,--help", options.showHelp, "Display available options");
	cmdLine.add("--version", options.showVersion, "Display version information and exit");
	cmdLine.add("-x",
				[this](std::string_view value) {
					language = value;
					return "";
				},
				"Treat subsequent input files as having type <language>", "<language>");
	cmdLine.add("--std",
				[this](std::string_view value) {
					standard = value;
					return "";
				},
				"Language standard to compile for", "<value>");
	cmdLine.add("-o,--out", options.outputFile, "Write the design netlist to <outfile>", "<file>");
	cmdLine.add("--top", options.topModule,
				"Top-level module to instantiate"
				"<name>");
	
	cmdLine.add("--target", options.target,
				"Generate netlist for the given target",
				"<value>");
	cmdLine.add("-D", options.defines,
				"Define preprocessor symbol <macro> to <value> (empty if <value> ommitted)",
				"<macro>[=<value>]",
				CommandLineFlags::CommaList);
	cmdLine.add("-U", options.undefines,
				"Undefine preprocessor symbol <macro>",
				"<macro>",
				CommandLineFlags::CommaList);
	cmdLine.add("--print-languages", options.printLanguages, "Print available languages");
	cmdLine.add("--print-standards", options.printStandards, "Print available standards for language");
	cmdLine.add("--print-targets", options.printTargets, "Print available targets");
	cmdLine.add("-v,--verbose", options.showVerbose, "Verbose output");
	cmdLine.setPositional(
		[this](std::string_view value) {
			sourceFiles.push_back(std::string(value));
			return "";
		},
		"files");

	log_suppressed();

	if (!cmdLine.parse(argc, argv, {})) {
		for (auto& err : cmdLine.getErrors()) {
			//auto loc = err.location;
			printError(err.message.c_str());
		}
		return 1;
	}

	if (options.showVerbose) {
		is_verbose = true;
	}

	if (options.showHelp) {
		printf("%s\n", cmdLine.getHelpText("Yosys compiler").c_str());
		return 0;
	}

	if (options.showVersion) {
		printf("%s\n", yosys_version_str);
		return 0;
	}
	if (options.printLanguages) {
		printf("Registered Languages:\n");
		printf("    verilog   - Verilog (default)\n");
		printf("    sv        - SystemVerilog\n");
		printf("    vhdl      - VHDL\n");
		return 0;
	}
	if (options.printStandards) {
		printf("Registered Standards for '%s':\n", "verilog");
		printf("    1995      - Verilog 1364-1995\n");
		printf("    2001      - Verilog 1364-2001\n");
		printf("    2005      - Verilog 1364-2005\n");
		//printf("    2005      - SystemVerilog 1800-2005\n");
		//printf("    2009      - SystemVerilog 1800-2009\n");
		//printf("    2012      - SystemVerilog 1800-2012\n");
		//printf("    2017      - SystemVerilog 1800-2017\n");
		//printf("    2023      - SystemVerilog 1800-2023\n");
	}

	if (options.printTargets) {
		printf("Registered Targets:\n");
		printf("    ice40     - Lattice iCE 40\n");
		printf("    ecp5      - Lattice ECP5\n");
		return 0;
	}

	if (!options.target) {
		printError("Target is not specified.");
		return 1;
	}
	if (!sourceFiles.size()) {
		printError("no input files");
		return 2;
	}
	if (!options.outputFile) {
		printError("no output file");
		return 2;
	}
	if (!options.topModule) {
		printError("no top module specified");
		return 2;
	}
	
	show_build_status = true;
	run_pass("read -noverific");
	if (!options.defines.empty()) {
		for (auto vdef : options.defines)
			run_pass("read -define " + vdef);
	}
	if (!options.undefines.empty()) {
		for (auto vdef : options.undefines)
			run_pass("read -undef " + vdef);
	}

	for (auto fn : sourceFiles)
		run_frontend(fn.c_str(), "auto");

	run_pass(stringf("hierarchy -top %s", options.topModule.value()));

	run_pass(stringf("synth_%s", options.target.value()));

	run_backend(options.outputFile.value(), "auto");

	yosys_design->check();
	for (auto it : saved_designs)
		it.second->check();
	for (auto it : pushed_designs)
		it->check();

	yc_error_atexit();
	log_flush();
	return 0;
}

YOSYS_NAMESPACE_END


USING_YOSYS_NAMESPACE

int main(int argc, char **argv)
{
	yosys_setup();
	YosysDriver driver;
	int ret = driver.run(argc, argv);
	yosys_shutdown();
	return ret;
}
