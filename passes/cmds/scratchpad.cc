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
		log("    scratchpad [ -get id | -set id val | -unset id | -copy id1 id2 ]\n");
		log("\n");
		log("This pass allows to read and modify values from the scratchpad of the current\n");
		log("design. Options:\n");
		log("    -get <identifier>\n");
		log("    -set <identifier> <value>\n");
		log("    -unset <identifier>\n");
		log("    -copy <identifier_from> <identifier_to>\n");
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
				if (design->scratchpad.count(identifier)){
					log("%s\n", design->scratchpad_get_string(identifier).c_str());
				} else {
					log("\"%s\" not set\n", identifier.c_str());
				}
				continue;
			}
			if (args[argidx] == "-set" && argidx+2 < args.size()) {
				string identifier = args[++argidx];
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
				if (design->scratchpad.count(identifier_from) == 0) log_error("\"%s\" not set\n", identifier_from.c_str());
				string value = design->scratchpad_get_string(identifier_from);
				design->scratchpad_set_string(identifier_to, value);
				continue;
			}
			log("Unrecognized argument: %s\n", args[argidx].c_str());
			break;
		}
	}
} ScratchpadPass;
PRIVATE_NAMESPACE_END
