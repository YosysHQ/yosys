/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2025  Jannis Harder <jix@yosyshq.com> <me@jix.one>
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
 #include "passes/techmap/libparse.h"

 USING_YOSYS_NAMESPACE
 PRIVATE_NAMESPACE_BEGIN

 struct LibcachePass : public Pass {
	LibcachePass() : Pass("libcache", "control caching of technology library data parsed from liberty files") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    libcache {-enable|-disable|-purge} { -all | [path]... }\n");
		log("\n");
		log("Controls the default and per path caching of liberty file data.\n");
		log("\n");
		log("    -enable    Enable caching.\n");
		log("    -disable   Disable caching.\n");
		log("    -purge     Reset cache setting and forget cached data.\n");
		log("\n");
		log("This mode takes a list of paths as argument. If no paths are provided, this\n");
		log("command does nothing. The -all option can be used to change the default cache\n");
		log("setting for -enable/-disable or to reset and forget about all paths.\n");
		log("\n");
		log("By default caching is disabled.\n");
		log("\n");
		log("    libcache -list\n");
		log("\n");
		log("Displays the current cache settings and cached paths.\n");
		log("\n");
		log("    libcache {-verbose|-quiet}\n");
		log("\n");
		log("Controls cache use logging.\n");
		log("\n");
		log("    -verbose   Enable printing info when cache is used\n");
		log("    -quiet     Disable printing info when cache is used (default)\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *) override
	{
		bool enable = false;
		bool disable = false;
		bool purge = false;
		bool all = false;
		bool list = false;
		bool verbose = false;
		bool quiet = false;
		std::vector<std::string> paths;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-enable") {
				enable = true;
				continue;
			}
			if (args[argidx] == "-disable") {
				enable = true;
				continue;
			}
			if (args[argidx] == "-purge") {
				purge = true;
				continue;
			}
			if (args[argidx] == "-all") {
				all = true;
				continue;
			}
			if (args[argidx] == "-list") {
				list = true;
				continue;
			}
			if (args[argidx] == "-verbose") {
				verbose = true;
				continue;
			}
			if (args[argidx] == "-quiet") {
				quiet = true;
				continue;
			}
			std::string fname = args[argidx];
			rewrite_filename(fname);
			paths.push_back(fname);
			break;
		}
		int modes = enable + disable + purge + list + verbose + quiet;
		if (modes == 0)
			log_cmd_error("At least one of -enable, -disable, -purge, -list,\n-verbose, or -quiet is required.\n");
		if (modes > 1)
			log_cmd_error("Only one of -enable, -disable, -purge, -list,\n-verbose, or -quiet may be present.\n");

		if (all && !paths.empty())
			log_cmd_error("The -all option cannot be combined with a list of paths.\n");
		if (list && (all || !paths.empty()))
			log_cmd_error("The -list mode takes no further options.\n");
		if (!list && !all && paths.empty())
			log("No paths specified, use -all to %s\n", purge ? "purge all paths" : "change the default setting");

		if (list) {
			log("Caching is %s by default.\n", LibertyAstCache::instance.cache_by_default ? "enabled" : "disabled");
			for (auto const &entry : LibertyAstCache::instance.cache_path)
				log("Caching is %s for `%s'.\n", entry.second ? "enabled" : "disabled", entry.first.c_str());
			for (auto const &entry : LibertyAstCache::instance.cached)
				log("Data for `%s' is currently cached.\n", entry.first.c_str());
		} else if (enable || disable) {
			if (all) {
				LibertyAstCache::instance.cache_by_default = enable;
			} else {
				for (auto const &path : paths) {
					LibertyAstCache::instance.cache_path[path] = enable;
				}
			}
		} else if (purge) {
			if (all) {
				LibertyAstCache::instance.cached.clear();
				LibertyAstCache::instance.cache_path.clear();
			} else {
				for (auto const &path : paths) {
					LibertyAstCache::instance.cached.erase(path);
					LibertyAstCache::instance.cache_path.erase(path);
				}
			}
		} else if (verbose) {
			LibertyAstCache::instance.verbose = true;
		} else if (quiet) {
			LibertyAstCache::instance.verbose = false;
		} else {
			log_assert(false);
		}
	}
} LibcachePass;

PRIVATE_NAMESPACE_END
