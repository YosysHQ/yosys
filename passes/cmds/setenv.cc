/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024 N. Engelhardt <nak@yosyshq.com>
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
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN
struct SetenvPass : public Pass {
	SetenvPass() : Pass("setenv", "set an environment variable") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    setenv name value\n");
		log("\n");
		log("Set the given environment variable on the current process. Values containing\n");
		log("whitespace must be passed in double quotes (\").\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, [[maybe_unused]] RTLIL::Design *design) override
	{
		if(args.size() != 3)
			log_cmd_error("Wrong number of arguments given.\n");

		std::string name = args[1];
		std::string value = args[2];
		if (value.front() == '\"' && value.back() == '\"') value = value.substr(1, value.size() - 2);
		
#if defined(_WIN32)
		_putenv_s(name.c_str(), value.c_str());
#else
		if (setenv(name.c_str(), value.c_str(), 1))
			log_cmd_error("Invalid name \"%s\".\n", name.c_str());
#endif
		
	}
} SetenvPass;

PRIVATE_NAMESPACE_END
