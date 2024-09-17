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

#include <iterator>
#include <optional>
#include <stdint.h>

#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "passes/techmap/libparse.h"
#include "kernel/cost.h"
#include "frontends/ast/ast.h"
#include "libs/json11/json11.hpp"

#if defined(__APPLE__) && defined(__MACH__)
#include <mach/task.h>
#include <mach/mach_init.h>
#endif

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

std::optional<uint64_t> current_mem_bytes() {

#if defined(__APPLE__)
    task_basic_info_64_data_t basicInfo;
    mach_msg_type_number_t count = TASK_BASIC_INFO_64_COUNT;
    kern_return_t error = task_info(mach_task_self(), TASK_BASIC_INFO_64, (task_info_t)&basicInfo, &count);
    if (error != KERN_SUCCESS) {
        return {}; // Error getting task information
    }
    return basicInfo.resident_size; // Return RSS in KB

#elif defined(__linux__)
	// Not all linux distributions have to have this file
    std::ifstream statusFile("/proc/self/status");
    std::string line;
    while (std::getline(statusFile, line)) {
        if (line.find("VmRSS:") == 0) {
            std::istringstream iss(line);
            std::string token;
			// Skip prefix
            iss >> token;
            uint64_t rss;
            iss >> rss;
            return rss * 1024;
        }
    }
	// Error reading /proc/self/status
    return {};

#else
	return {};
#endif
}

struct InternalStatsPass : public Pass {
	InternalStatsPass() : Pass("internal_stats", "print internal statistics") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("Print internal statistics for developers (experimental)\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool json_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-json") {
				json_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if(!json_mode)
			log_header(design, "Printing internal statistics.\n");

		log_experimental("internal_stats");

		if (json_mode) {
			log("{\n");
			log("   \"creator\": %s,\n", json11::Json(yosys_version_str).dump().c_str());
			std::stringstream invocation;
			std::copy(args.begin(), args.end(), std::ostream_iterator<std::string>(invocation, " "));
			log("   \"invocation\": %s,\n", json11::Json(invocation.str()).dump().c_str());
			if (auto mem = current_mem_bytes()) {
				log("   \"memory_now\": %s,\n", std::to_string(*mem).c_str());
			}
			auto ast_bytes = AST::astnode_count() * (unsigned long long) sizeof(AST::AstNode);
			log("   \"memory_ast\": %s,\n", std::to_string(ast_bytes).c_str());
		}

		// stats go here

		if (json_mode) {
			log("\n");
			log("}\n");
		}

	}
} InternalStatsPass;

PRIVATE_NAMESPACE_END
