/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Nina Engelhardt <nak@symbioticeda.com>
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

struct ScratchpadPass : public Pass {
	ScratchpadPass() : Pass("scratchpad", "get/set values in the scratchpad") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    scratchpad [options]\n");
		log("\n");
		log("This pass allows to read and modify values from the scratchpad of the current\n");
		log("design. Options:\n");
		log("\n");
		log("    -get <identifier>\n");
		log("        print the value saved in the scratchpad under the given identifier.\n");
		log("\n");
		log("    -set <identifier> <value>\n");
		log("        save the given value in the scratchpad under the given identifier.\n");
		log("\n");
		log("    -unset <identifier>\n");
		log("        remove the entry for the given identifier from the scratchpad.\n");
		log("\n");
		log("    -copy <identifier_from> <identifier_to>\n");
		log("        copy the value of the first identifier to the second identifier.\n");
		log("\n");
		log("    -assert <identifier> <value>\n");
		log("        assert that the entry for the given identifier is set to the given value.\n");
		log("\n");
		log("    -assert-set <identifier>\n");
		log("        assert that the entry for the given identifier exists.\n");
		log("\n");
		log("    -assert-unset <identifier>\n");
		log("        assert that the entry for the given identifier does not exist.\n");
		log("\n");
		log("The identifier may not contain whitespace. By convention, it is usually prefixed\n");
		log("by the name of the pass that uses it, e.g. 'opt.did_something'. If the value\n");
		log("contains whitespace, it must be enclosed in double quotes.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-get" && argidx+1 < args.size()) {
				string identifier = args[++argidx];
				if (design->scratchpad.count(identifier)) {
					log("%s\n", design->scratchpad_get_string(identifier).c_str());
				} else if (RTLIL::constpad.count(identifier)) {
					log("%s\n", RTLIL::constpad.at(identifier).c_str());
				} else {
					log("\"%s\" not set\n", identifier.c_str());
				}
				continue;
			}
			if (args[argidx] == "-set" && argidx+2 < args.size()) {
				string identifier = args[++argidx];
				if (RTLIL::constpad.count(identifier))
					log_error("scratchpad entry \"%s\" is a global constant\n", identifier.c_str());
				string value = args[++argidx];
				if (value.front() == '\"' && value.back() == '\"') value = value.substr(1, value.size() - 2);
				design->scratchpad_set_string(identifier, value);
				continue;
			}
			if (args[argidx] == "-unset" && argidx+1 < args.size()) {
				string identifier = args[++argidx];
				design->scratchpad_unset(identifier);
				continue;
			}
			if (args[argidx] == "-copy" && argidx+2 < args.size()) {
				string identifier_from = args[++argidx];
				string identifier_to = args[++argidx];
				string value;
				if (design->scratchpad.count(identifier_from))
					value = design->scratchpad_get_string(identifier_from);
				else if (RTLIL::constpad.count(identifier_from))
					value = RTLIL::constpad.at(identifier_from);
				else
					log_error("\"%s\" not set\n", identifier_from.c_str());
				if (RTLIL::constpad.count(identifier_to))
					log_error("scratchpad entry \"%s\" is a global constant\n", identifier_to.c_str());
				design->scratchpad_set_string(identifier_to, value);
				continue;
			}
			if (args[argidx] == "-assert" && argidx+2 < args.size()) {
				string identifier = args[++argidx];
				string expected = args[++argidx];
				if (expected.front() == '\"' && expected.back() == '\"') expected = expected.substr(1, expected.size() - 2);
				if (design->scratchpad.count(identifier) == 0)
					log_error("scratchpad entry '%s' is not defined\n", identifier.c_str());
				string value = design->scratchpad_get_string(identifier);
				if (value != expected) {
					log_error("scratchpad entry '%s' is set to '%s' instead of the asserted '%s'\n",
					           identifier.c_str(), value.c_str(), expected.c_str());
				}
				continue;
			}
			if (args[argidx] == "-assert-set" && argidx+1 < args.size()) {
				string identifier = args[++argidx];
				if (design->scratchpad.count(identifier) == 0)
					log_error("scratchpad entry '%s' is not defined\n", identifier.c_str());
				continue;
			}
			if (args[argidx] == "-assert-unset" && argidx+1 < args.size()) {
				string identifier = args[++argidx];
				if (design->scratchpad.count(identifier) > 0)
					log_error("scratchpad entry '%s' is defined\n", identifier.c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);
	}
} ScratchpadPass;
PRIVATE_NAMESPACE_END
