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
		return (msg.severity == LogSeverity::Warning || msg.severity == LogSeverity::Error);
}
void ColorLogSink::log(const LogMessage &msg)
{
	FILE *f = stderr;
	switch (msg.severity) {
		case LogSeverity::Warning:
			fmt::print(f, fg(fmt::terminal_color::bright_yellow), "{}", msg.prefix);
			fmt::print(f, fg(fmt::terminal_color::blue) | fmt::emphasis::bold, "{}", msg.message);
			break;

		case LogSeverity::Error:
			fmt::print(f, fg(fmt::terminal_color::bright_red), "{}", msg.prefix);
			fmt::print(f, fg(fmt::terminal_color::blue) | fmt::emphasis::bold, "{}", msg.message);
			break;

		case LogSeverity::Header:
			fmt::print(f, fg(fmt::terminal_color::cyan) | fmt::emphasis::bold, "{}", msg.prefix);
			fmt::print(f, fg(fmt::terminal_color::white) | fmt::emphasis::bold, "{}", msg.message);
			break;

		case LogSeverity::Comment:
		case LogSeverity::Debug:
			fmt::print(f, fg(fmt::terminal_color::bright_black), "{}{}", msg.prefix, msg.message);
			break;

		case LogSeverity::Info:
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

enum class Language
{
    Auto,
    Verilog,
    SystemVerilog,
    Vhdl
};

enum class SystemVerilogFrontend
{
    Legacy,
    Slang,
    Verific
};

enum class VhdlFrontend
{
    GHDL,
    Verific
};

enum class VerilogStandard
{
    V1995,
    V2001,
    V2005,
	Latest = V2005
};

enum class SystemVerilogStandard
{
    V2005,
    V2009,
    V2012,
    V2017,
    V2023,
	Latest = V2023
};

enum class VhdlStandard
{
    V1987,
    V1993,
    V2000,
    V2008,
    V2019,
	Latest = V2019
};

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

	struct Target
	{
		std::string name;
		std::string description;
		std::vector<std::string> passes;
	};
	using SourceStandard = std::variant<
		VerilogStandard,
		SystemVerilogStandard,
		VhdlStandard
	>;

	struct SourceFile
	{
		std::string filename;
		Language language;
		SourceStandard standard;
	};

	std::vector<SourceFile> sourceFiles;
	std::vector<Target> targets;

	Language language = Language::Auto;
	VerilogStandard verilog_standard = VerilogStandard::Latest;
	SystemVerilogStandard system_verilog_standard = SystemVerilogStandard::Latest;
	VhdlStandard vhdl_standard = VhdlStandard::Latest;
	SystemVerilogFrontend system_verilog_frontend;
	VhdlFrontend vhdl_frontend;

	void addStandardArgs();
	int run(int argc, char **argv);
	void printError(const std::string& message);
	void printHeader(const std::string& message);
	void printOption(const std::string& name, const std::string& desc);
	void registerTarget(std::string name,
						std::string description,
						std::vector<std::string> passes)
	{
		targets.push_back({
			std::move(name),
			std::move(description),
			std::move(passes)
		});
	}
};

void YosysDriver::printError(const std::string& message) {
	fmt::print(stderr, fg(fmt::terminal_color::bright_red), "{}", "ERROR: ");
	fmt::print(stderr, fg(fmt::terminal_color::blue) | fmt::emphasis::bold, "{}", message);
	fmt::print(stderr, "\n");
}

void YosysDriver::printHeader(const std::string& message) {
	fmt::print(stderr, fg(fmt::terminal_color::white) | fmt::emphasis::bold, "{}", message);
	fmt::print(stderr, "\n");
}
void YosysDriver::printOption(const std::string& name, const std::string& desc) {
	fmt::print(stderr, fg(fmt::terminal_color::bright_blue) | fmt::emphasis::bold, "    {:<12}", name);
	fmt::print(stderr, "- {}", desc);
	fmt::print(stderr, "\n");
}

static Language languageFromExtension(std::string_view filename)
{
    auto pos = filename.rfind('.');
    if (pos == std::string_view::npos)
        return Language::Auto;

    auto extension = filename.substr(pos);

    if (extension == ".v")
        return Language::Verilog;

    if (extension == ".sv")
        return Language::SystemVerilog;

    if (extension == ".vhd" || extension == ".vhdl")
        return Language::Vhdl;

    return Language::Auto;
}

int YosysDriver::run(int argc, char **argv) {
	log_error_atexit = &yc_error_atexit;
	logger().add_sink<ColorLogSink>();

	cmdLine.add("-h,--help", options.showHelp, "Display available options");
	cmdLine.add("--version", options.showVersion, "Display version information and exit");
	cmdLine.add("-x",
		[this](std::string_view value) {
			if (value == "auto")
				language = Language::Auto;
			else if (value == "verilog")
			{
				language = Language::Verilog;
				verilog_standard = VerilogStandard::Latest;
			}
			else if (value == "sv")
			{
				language = Language::SystemVerilog;
				system_verilog_standard = SystemVerilogStandard::Latest;
			}
			else if (value == "vhdl")
			{
				language = Language::Vhdl;
				vhdl_standard = VhdlStandard::Latest;
			}
			else
				return fmt::format(
					"Invalid language '{}'; expected auto, verilog, sv or vhdl",
					value);

			return std::string{};
		},
		"Treat subsequent input files as having type <language>",
		"<language>");
	cmdLine.add("--std",
		[this](std::string_view value) {
			switch (language)
			{
			case Language::Verilog:
				if (value == "1995")
					verilog_standard = VerilogStandard::V1995;
				else if (value == "2001")
					verilog_standard = VerilogStandard::V2001;
				else if (value == "2005")
					verilog_standard = VerilogStandard::V2005;
				else
					return fmt::format(
						"Invalid Verilog standard '{}'; expected 1995, 2001 or 2005",
						value);
				break;

			case Language::SystemVerilog:
				if (value == "2005")
					system_verilog_standard = SystemVerilogStandard::V2005;
				else if (value == "2009")
					system_verilog_standard = SystemVerilogStandard::V2009;
				else if (value == "2012")
					system_verilog_standard = SystemVerilogStandard::V2012;
				else if (value == "2017")
					system_verilog_standard = SystemVerilogStandard::V2017;
				else if (value == "2023")
					system_verilog_standard = SystemVerilogStandard::V2023;
				else
					return fmt::format(
						"Invalid SystemVerilog standard '{}'; expected 2005, 2009, 2012, 2017 or 2023",
						value);
				break;

			case Language::Vhdl:
				if (value == "1987")
					vhdl_standard = VhdlStandard::V1987;
				else if (value == "1993")
					vhdl_standard = VhdlStandard::V1993;
				else if (value == "2000")
					vhdl_standard = VhdlStandard::V2000;
				else if (value == "2008")
					vhdl_standard = VhdlStandard::V2008;
				else if (value == "2019")
					vhdl_standard = VhdlStandard::V2019;
				else
					return fmt::format(
						"Invalid VHDL standard '{}'; expected 1987, 1993, 2000, 2008 or 2019",
						value);
				break;

			case Language::Auto:
				return std::string("Cannot specify --std when language is auto");
			}

			return std::string{};
		},
		"Language standard to compile for",
		"<value>");

	cmdLine.add("-svf,--system-verilog-frontend",
		[this](std::string_view value) {
			if (value == "legacy")
				system_verilog_frontend = SystemVerilogFrontend::Legacy;
			else if (value == "slang")
				system_verilog_frontend = SystemVerilogFrontend::Slang;
			else if (value == "verific")
				system_verilog_frontend = SystemVerilogFrontend::Verific;
			else
				return fmt::format(
					"Invalid SystemVerilog frontend '{}'; expected legacy, slang or verific", value);

			return std::string{};
		},
		"SystemVerilog frontend to use (legacy, slang or verific)", "<frontend>");

	cmdLine.add("-vhf,--vhdl-frontend",
		[this](std::string_view value) {
			if (value == "ghdl")
				vhdl_frontend = VhdlFrontend::GHDL;
			else if (value == "verific")
				vhdl_frontend = VhdlFrontend::Verific;
			else
				return fmt::format(
					"Invalid VHDL frontend '{}'; expected ghdl or verific", value);

			return std::string{};
		},
		"VHDL frontend to use (ghdl or verific)", "<frontend>");

	cmdLine.add("-o,--out", options.outputFile, "Write the design netlist to <outfile>", "<file>");
	cmdLine.add("--top", options.topModule,
				"Top-level module to instantiate"
				"<name>");

	cmdLine.add("--target",
		[this](std::string_view value) {
			auto it = std::find_if(targets.begin(), targets.end(),
				[value](const auto &target) {
					return target.name == value;
				});

			if (it == targets.end())
				return fmt::format("Invalid target '{}'", value);

			options.target = value;
			return std::string{};
		},
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
			Language fileLanguage = language;

			if (fileLanguage == Language::Auto)
				fileLanguage = languageFromExtension(value);

			if (fileLanguage == Language::Auto)
				return fmt::format(
					"Cannot determine language for '{}'; use -x <language>",
					value);

			SourceStandard fileStandard;

			switch (fileLanguage)
			{
			case Language::Verilog:
				fileStandard = verilog_standard;
				break;

			case Language::SystemVerilog:
				fileStandard = system_verilog_standard;
				break;

			case Language::Vhdl:
				fileStandard = vhdl_standard;
				break;

			case Language::Auto:
				// Handled above.
				return std::string{};
			}
			return std::string{};
		},
		"files");

	log_suppressed();

	if (!cmdLine.parse(argc, argv, {})) {
		for (auto& err : cmdLine.getErrors()) {
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
		printHeader("Registered Languages:");
		printOption("verilog", "Verilog");
		printOption("sv", "SystemVerilog");
		printOption("vhdl", "VHDL");
		return 0;
	}

	if (options.printStandards) {
		switch (language) {
		case Language::Verilog:
			printHeader("Registered Standards for verilog:");
			printOption("1995", "Verilog 1364-1995");
			printOption("2001", "Verilog 1364-2001");
			printOption("2005", "Verilog 1364-2005");
			break;

		case Language::SystemVerilog:
			printHeader("Registered Standards for sv:");
			printOption("2005", "SystemVerilog 1800-2005");
			printOption("2009", "SystemVerilog 1800-2009");
			printOption("2012", "SystemVerilog 1800-2012");
			printOption("2017", "SystemVerilog 1800-2017");
			printOption("2023", "SystemVerilog 1800-2023");
			break;

		case Language::Vhdl:
			printHeader("Registered Standards for vhdl:");
			printOption("1987", "VHDL 1987");
			printOption("1993", "VHDL 1993");
			printOption("2000", "VHDL 2000");
			printOption("2008", "VHDL 2008");
			printOption("2019", "VHDL 2019");
			break;

		case Language::Auto:
			printHeader("Registered Standards:");
			printOption("verilog", "Use -x verilog to list Verilog standards");
			printOption("sv", "Use -x sv to list SystemVerilog standards");
			printOption("vhdl", "Use -x vhdl to list VHDL standards");
			break;
		}

		return 0;
	}

	if (options.printTargets) {
		printHeader("Registered Targets:");

		for (const auto &target : targets)
			printOption(target.name, target.description);

		return 0;
	}

	if (!options.target) {
		printError("target is not specified.");
		return 1;
	}
	if (!sourceFiles.size()) {
		printError("no input files");
		return 1;
	}
	if (!options.outputFile) {
		printError("no output file");
		return 1;
	}
	if (!options.topModule) {
		printError("no top module specified");
		return 1;
	}

	show_build_status = true;
	std::vector<std::string> passes;

	passes.push_back("read -noverific");
	if (!options.defines.empty()) {
		for (auto vdef : options.defines)
			passes.push_back("read -define " + vdef);
	}
	if (!options.undefines.empty()) {
		for (auto vdef : options.undefines)
			passes.push_back("read -undef " + vdef);
	}

	//for (auto fn : sourceFiles)
		//passes.push_back(stringf("read_verilog -sv %s", fn));
		//run_frontend(fn.c_str(), "auto");


	for (const auto &file : sourceFiles)
	{
		switch (file.language)
		{
		case Language::Verilog:
			passes.push_back(stringf("read_verilog %s", file.filename));
			break;

		case Language::SystemVerilog:
			switch (system_verilog_frontend)
			{
			case SystemVerilogFrontend::Legacy:
				passes.push_back(stringf("read_verilog -sv %s", file.filename));
				break;

			case SystemVerilogFrontend::Slang:
				passes.push_back(stringf("read_slang %s", file.filename));
				break;

			case SystemVerilogFrontend::Verific:
				passes.push_back(stringf("read_verific -sv %s", file.filename));
				break;
			}
			break;

		case Language::Vhdl:
			switch (vhdl_frontend)
			{
			case VhdlFrontend::GHDL:
				passes.push_back(stringf("ghdl %s", file.filename));
				break;

			case VhdlFrontend::Verific:
				passes.push_back(stringf("read_verific -vhdl %s", file.filename));
				break;
			}
			break;

		case Language::Auto:
			// Should never occur; resolved when SourceFile was created.
			break;
		}
	}
	passes.push_back(stringf("hierarchy -top %s", options.topModule.value()));

	//passes.push_back(stringf("synth_%s", options.target.value()));
	auto it = std::find_if(targets.begin(), targets.end(),
		[this](const auto &target) {
			return target.name == options.target;
		});

	for (const auto &pass : it->passes) {
		// run pass
		passes.push_back(pass);
	}

	//run_backend(options.outputFile.value(), "auto");
	passes.push_back(stringf("write_verilog %s", options.outputFile.value()));

	for(auto &p : passes) {
		run_pass(p);
	}
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
