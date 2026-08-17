/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Simon Tupy <simontupy64@gmail.com>
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

YOSYS_NAMESPACE_BEGIN
// Read by convert_liberty_files_to_merged_scl() in liberty_cache.h
bool scl_cache_enabled = true;
YOSYS_NAMESPACE_END

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SclCachePass : public Pass {
	SclCachePass() : Pass("scl_cache", "control caching of merged SCL files generated for ABC") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    scl_cache {-enable|-disable|-list}\n");
		log("\n");
		log("Controls the on-disk cache of merged SCL files that the abc and abc9 passes\n");
		log("generate from liberty files.\n");
		log("\n");
		log("    -enable    Enable caching (default).\n");
		log("    -disable   Disable caching, ABC reads the liberty files directly.\n");
		log("    -list      Display the current cache setting.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *) override
	{
		bool enable = false;
		bool disable = false;
		bool list = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-enable") {
				enable = true;
				continue;
			}
			if (args[argidx] == "-disable") {
				disable = true;
				continue;
			}
			if (args[argidx] == "-list") {
				list = true;
				continue;
			}
			break;
		}
		if (argidx != args.size())
			log_cmd_error("Unexpected argument `%s'.\n", args[argidx].c_str());

		int modes = enable + disable + list;
		if (modes != 1)
			log_cmd_error("Exactly one of -enable, -disable, or -list is required.\n");

		if (list)
			log("SCL caching is %s.\n", scl_cache_enabled ? "enabled" : "disabled");
		else
			scl_cache_enabled = enable;
	}
} SclCachePass;

PRIVATE_NAMESPACE_END
