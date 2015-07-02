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

struct CopyPass : public Pass {
	CopyPass() : Pass("copy", "copy modules in the design") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    copy old_name new_name\n");
		log("\n");
		log("Copy the specified module. Note that selection patterns are not supported\n");
		log("by this command.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		if (args.size() != 3)
			log_cmd_error("Invalid number of arguments!\n");

		std::string src_name = RTLIL::escape_id(args[1]);
		std::string trg_name = RTLIL::escape_id(args[2]);

		if (design->modules_.count(src_name) == 0)
			log_cmd_error("Can't find source module %s.\n", src_name.c_str());

		if (design->modules_.count(trg_name) != 0)
			log_cmd_error("Target module name %s already exists.\n", trg_name.c_str());

		RTLIL::Module *new_mod = design->module(src_name)->clone();
		new_mod->name = trg_name;
		design->add(new_mod);
	}
} CopyPass;

PRIVATE_NAMESPACE_END
