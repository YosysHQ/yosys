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

YOSYS_NAMESPACE_BEGIN
extern void (*log_warning_callback)(std::string);

using namespace slang;

void yosys_atexit() {
	printf("error: %s\n", log_last_error.c_str());
}

void yosys_warning(std::string msg) {
	printf("warning: %s\n", msg.c_str());
}

class YosysDriver {
public:
	CommandLine cmdLine;

	struct Options {
		std::optional<bool> showHelp;
		std::optional<bool> showVerbose;
		std::optional<bool> showVersion;
		std::optional<bool> printTargets;
		std::optional<bool> printDevices;
		std::optional<bool> printLanguages;
		std::optional<bool> printStandards;

		std::vector<std::string> defines;
		std::vector<std::string> undefines;
		std::optional<std::string> topModule;
		std::optional<std::string> outputFile;
		std::optional<std::string> target;
		std::optional<std::string> device;
	} options;

	std::vector<std::string> sourceFiles;

	std::string language;
	std::string standard;

	void addStandardArgs();
	int run(int argc, char **argv);
	void printError(const std::string& message);
};

void YosysDriver::printError(const std::string& message) {
	printf("error: %s\n", message.c_str());
}

void YosysDriver::addStandardArgs() {
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
	cmdLine.add("-o", options.outputFile, "Write the design netlist to <outfile>", "<file>");
	cmdLine.add("--top", options.topModule,
				"Top-level module to instantiate "
				"(instead of figuring it out automatically)",
				"<name>");
	
	cmdLine.add("--target", options.target,
				"Generate netlist for the given target",
				"<value>");
	cmdLine.add("--mdevice", options.device,
				"For a list of available devices use '--print-supported-devices'",
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
	cmdLine.add("--print-supported-devices", options.printDevices, "Print supported devices per target");
	cmdLine.add("-v,--verbose", options.showVerbose, "Verbose output");
	cmdLine.setPositional(
		[this](std::string_view value) {
			sourceFiles.push_back(std::string(value));
			return "";
		},
		"files");
}

int YosysDriver::run(int argc, char **argv) {
	addStandardArgs();

	log_suppressed();

	if (!cmdLine.parse(argc, argv, {})) {
		for (auto& err : cmdLine.getErrors()) {
			//auto loc = err.location;
			printError(err.message.c_str());
		}
		return 1;
	}

	if (options.showVerbose) {
		log_files.push_back(stdout);
		log_error_stderr = true;
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
	if (options.printDevices) {
		printf("Available devices for this target:\n");
		//printf("    ice40     - Lattice iCE 40\n");
		return 0;
	}

	log_error_atexit = yosys_atexit;
	log_warning_callback = yosys_warning;
	if (!sourceFiles.size()) {
		printError("no input files");
		return 2;
	}
	if (!options.outputFile) {
		printError("no output file");
		return 2;
	}

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

	if (options.topModule)
		run_pass(stringf("hierarchy -top %s", options.topModule.value()));

	run_pass(stringf("synth_%s", options.target.value()));

	run_backend(options.outputFile.value(), "auto");

	yosys_design->check();
	for (auto it : saved_designs)
		it.second->check();
	for (auto it : pushed_designs)
		it->check();

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
