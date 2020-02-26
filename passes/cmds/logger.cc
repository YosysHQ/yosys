/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Miodrag Milanovic <clifford@clifford.at>
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
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct LoggerPass : public Pass {
	LoggerPass() : Pass("logger", "set logger properties") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    logger [options]\n");
		log("\n");
		log("This command sets global logger properties, also available using command line\n");
		log("options.\n");
		log("\n");
		log("    -[no]time\n");
		log("        enable/disable display of timestamp in log output.\n");
		log("\n");
		log("    -[no]stderr\n");
		log("        enable/disable logging errors to stderr.\n");
		log("\n");
		log("    -warn regex\n");
		log("        print a warning for all log messages matching the regex.\n");
		log("\n");
		log("    -nowarn regex\n");
		log("        if a warning message matches the regex, it is printed as regular\n");
		log("        message instead.\n");
		log("\n");
		log("    -werror regex\n");
		log("        if a warning message matches the regex, it is printed as error\n");
		log("        message instead and the tool terminates with a nonzero return code.\n");
		log("\n");
		log("    -[no]debug\n");
		log("        globally enable/disable debug log messages.\n");
		log("\n");
		log("    -experimental <feature>\n");
		log("        do not print warnings for the specified experimental feature\n");
		log("\n");
		log("    -expect <type> <regex> <expected_count>\n");
		log("        expect log,warning or error to appear. In case of error return code is 0.\n");
		log("\n");
		log("    -expect-no-warnings\n");
		log("        gives error in case there is at least one warning that is not expected.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design * design) YS_OVERRIDE
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{

			if (args[argidx] == "-time") {
				log_time = true;
				log("Enabled timestamp in logs.\n");
				continue;
			}
			if (args[argidx] == "-notime") {
				log_time = false;
				log("Disabled timestamp in logs.\n");
				continue;
			}
			if (args[argidx] == "-stderr") {
				log_error_stderr = true;
				log("Enabled loggint errors to stderr.\n");
				continue;
			}
			if (args[argidx] == "-nostderr") {
				log_error_stderr = false;
				log("Disabled loggint errors to stderr.\n");
				continue;
			}
			if (args[argidx] == "-warn" && argidx+1 < args.size()) {
				std::string pattern = args[++argidx];
				if (pattern.front() == '\"' && pattern.back() == '\"') pattern = pattern.substr(1, pattern.size() - 2);		
				try {
					log("Added regex '%s' for warnings to warn list.\n", pattern.c_str());
					log_warn_regexes.push_back(std::regex(pattern,
						std::regex_constants::nosubs |
						std::regex_constants::optimize |
						std::regex_constants::egrep));
				}
				catch (const std::regex_error& e) {
					log_cmd_error("Error in regex expression '%s' !\n", pattern.c_str());
				}
				continue;
			}
			if (args[argidx] == "-nowarn" && argidx+1 < args.size()) {
				std::string pattern = args[++argidx];
				if (pattern.front() == '\"' && pattern.back() == '\"') pattern = pattern.substr(1, pattern.size() - 2);	
				try {
					log("Added regex '%s' for warnings to nowarn list.\n", pattern.c_str());
					log_nowarn_regexes.push_back(std::regex(pattern,
						std::regex_constants::nosubs |
						std::regex_constants::optimize |
						std::regex_constants::egrep));
				}
				catch (const std::regex_error& e) {
					log_cmd_error("Error in regex expression '%s' !\n", pattern.c_str());
				}
				continue;
			}
			if (args[argidx] == "-werror" && argidx+1 < args.size()) {
				std::string pattern = args[++argidx];
				if (pattern.front() == '\"' && pattern.back() == '\"') pattern = pattern.substr(1, pattern.size() - 2);	
				try {
					log("Added regex '%s' for warnings to werror list.\n", pattern.c_str());
					log_werror_regexes.push_back(std::regex(pattern,
						std::regex_constants::nosubs |
						std::regex_constants::optimize |
						std::regex_constants::egrep));
				}
				catch (const std::regex_error& e) {
					log_cmd_error("Error in regex expression '%s' !\n", pattern.c_str());
				}
				continue;
			}
			if (args[argidx] == "-debug") {
				log_force_debug = 1;
				log("Enabled debug log messages.\n");
				continue;
			}
			if (args[argidx] == "-nodebug") {
				log_force_debug = 0;
				log("Disabled debug log messages.\n");
				continue;
			}
			if (args[argidx] == "-experimental" && argidx+1 < args.size()) {
				std::string value = args[++argidx];
				log("Added '%s' experimental ignore list.\n", value.c_str());
				log_experimentals_ignored.insert(value);
				continue;
			}
			if (args[argidx] == "-expect" && argidx+3 < args.size()) {
				std::string type = args[++argidx];
				if (type!="error" && type!="warning" && type!="log")
					log_cmd_error("Expect command require type to be 'log', 'warning' or 'error' !\n");
				if (type=="error" && log_expect_error.size()>0)
					log_cmd_error("Only single error message can be expected !\n");
				std::string pattern = args[++argidx];
				if (pattern.front() == '\"' && pattern.back() == '\"') pattern = pattern.substr(1, pattern.size() - 2);					
				int count = atoi(args[++argidx].c_str());
				if (count<=0)
					log_cmd_error("Number of expected messages must be higher then 0 !\n");
				if (type=="error" && count!=1)
					log_cmd_error("Expected error message occurrences must be 1 !\n");
				log("Added regex '%s' for warnings to expected %s list.\n", pattern.c_str(), type.c_str());
				try {
					if (type=="error")
						log_expect_error.push_back(std::make_pair(std::regex(pattern,
							std::regex_constants::nosubs |
							std::regex_constants::optimize |
							std::regex_constants::egrep), LogExpectedItem(pattern, count)));
					else if (type=="warning")
						log_expect_warning.push_back(std::make_pair(std::regex(pattern,
							std::regex_constants::nosubs |
							std::regex_constants::optimize |
							std::regex_constants::egrep), LogExpectedItem(pattern, count)));
					else
						log_expect_log.push_back(std::make_pair(std::regex(pattern,
							std::regex_constants::nosubs |
							std::regex_constants::optimize |
							std::regex_constants::egrep), LogExpectedItem(pattern, count)));
				}
				catch (const std::regex_error& e) {
					log_cmd_error("Error in regex expression '%s' !\n", pattern.c_str());
				}
				continue;
			}
			if (args[argidx] == "-expect-no-warnings") {
				log_expect_no_warnings = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);
	}
} LoggerPass;

PRIVATE_NAMESPACE_END
