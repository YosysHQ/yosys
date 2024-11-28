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
		log("Set the given environment variable on the current process. String values must be\n");
		log("passed in double quotes (\").\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, [[maybe_unused]] RTLIL::Design *design) override
	{
		if(args.size() != 3)
			log_cmd_error("Wrong number of arguments given.\n");
		
#if defined(_WIN32)
		_putenv_s(args[1].c_str(), args[2].c_str());
#else
		setenv(args[1].c_str(), args[2].c_str(), 1);
#endif

	}
} SetenvPass;

PRIVATE_NAMESPACE_END
