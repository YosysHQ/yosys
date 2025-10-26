/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Claire Xenia Wolf <claire@yosyshq.com>
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
#include "kernel/log_help.h"

#ifdef YOSYS_ENABLE_PLUGINS
#  include <dlfcn.h>
#  include <filesystem>
namespace fs = std::filesystem;
#endif

#ifdef YOSYS_ENABLE_PYTHON
#  include <Python.h>
#  include <pybind11/pybind11.h>
namespace py = pybind11;
#endif

YOSYS_NAMESPACE_BEGIN

std::map<std::string, void*> loaded_plugins;
#ifdef YOSYS_ENABLE_PYTHON
std::map<std::string, void*> loaded_python_plugins;
#endif
std::map<std::string, std::string> loaded_plugin_aliases;

#ifdef YOSYS_ENABLE_PLUGINS

static constexpr const char *path_delimiters = fs::path::preferred_separator == '\\' ? ";" : ":" ;

inline const std::vector<fs::path> get_plugin_search_paths() {
	std::vector<fs::path> result;
	const char *yosys_plugin_path = std::getenv("YOSYS_PLUGIN_PATH");
	if (yosys_plugin_path != nullptr && strlen(yosys_plugin_path)) {
		// make mutable. std::string also manages allocation as a bonus
		// guaranteed contiguous in c++>=11
		std::string copy{yosys_plugin_path};
		char *token = nullptr;
		char *rest = &copy[0];
		while ((token = strtok_r(rest, path_delimiters, &rest))) {
			result.push_back(fs::path(token));
		}
	}
	result.push_back(fs::path(proc_share_dirname()) / "plugins"); // lowest priority
	return result;
}

void load_plugin(std::string filename, std::vector<std::string> aliases)
{
	std::string orig_filename = filename;
	rewrite_filename(filename);

	// Would something like this better be put in `rewrite_filename`?
	if (filename.find("/") == std::string::npos)
		filename = "./" + filename;


	#ifdef YOSYS_ENABLE_PYTHON
	const bool is_loaded = loaded_plugins.count(orig_filename) && loaded_python_plugins.count(orig_filename);
	#else
	const bool is_loaded = loaded_plugins.count(orig_filename);
	#endif

	fs::path full_path = fs::absolute(filename);

	if (!is_loaded) {
		// Check if we're loading a python script
		if (full_path.extension() == ".py") {
			#ifdef YOSYS_ENABLE_PYTHON
				fs::path plugin_python_path = full_path.parent_path();
				fs::path basename = full_path.stem();

				py::object sys = py::module_::import("sys");
				sys.attr("path").attr("insert")(0, py::str(plugin_python_path.c_str()));

				try {
					auto module_container = py::module_::import(basename.c_str());
					loaded_python_plugins[orig_filename] = module_container.ptr();
				} catch (py::error_already_set &e) {
					log_cmd_error("Can't load python module `%s': %s\n", basename, e.what());
					return;
				}
				Pass::init_register();
			#else
				log_error(
					"\n  This version of Yosys cannot load python plugins.\n"
					"  Ensure Yosys is built with Python support to do so.\n"
				);
			#endif
		} else {
			// Otherwise we assume it's a native plugin
			void *hdl = dlopen(filename.c_str(), RTLD_LAZY|RTLD_LOCAL);

			// We were unable to open the file, try to do so from plugin search
			// paths
			if (hdl == nullptr && orig_filename.find('/') == std::string::npos) {
				const std::vector<fs::path> search_paths = get_plugin_search_paths();
				for (const auto &search_path: search_paths) {
					fs::path potential_path = search_path / orig_filename;
					if (potential_path.extension() != ".so") {
						potential_path = search_path / (orig_filename + ".so");
					}
					hdl = dlopen(potential_path.string().c_str(), RTLD_LAZY | RTLD_LOCAL);
					if (hdl != nullptr) {
						break;
					}
				}
			}

			if (hdl == nullptr)
				log_cmd_error("Can't load module `%s': %s\n", filename, dlerror());

			loaded_plugins[orig_filename] = hdl;
			Pass::init_register();
		}
	}

	for (auto &alias : aliases)
		loaded_plugin_aliases[alias] = orig_filename;
}
#else
void load_plugin(std::string, std::vector<std::string>)
{
	log_error(
		"\n  This version of Yosys cannot load plugins at runtime.\n"
		"  Some plugins may have been included at build time.\n"
		"  Use `yosys -H' to see the available built-in and plugin commands.\n"
	);
}
#endif

struct PluginPass : public Pass {
	PluginPass() : Pass("plugin", "load and list loaded plugins") { }
	bool formatted_help() override {
		auto *help = PrettyHelp::get_current();
		help->set_group("passes/status");
		return false;
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    plugin [options]\n");
		log("\n");
		log("Load and list loaded plugins.\n");
		log("\n");
		log("    -i <plugin_filename>\n");
		log("        Load (install) the specified plugin.\n");
		log("\n");
		log("    -a <alias_name>\n");
		log("        Register the specified alias name for the loaded plugin\n");
		log("\n");
		log("    -l\n");
		log("        List loaded plugins\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string plugin_filename;
		std::vector<std::string> plugin_aliases;
		bool list_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if ((args[argidx] == "-i") && argidx+1 < args.size() && plugin_filename.empty()) {
				plugin_filename = args[++argidx];
				continue;
			}
			if ((args[argidx] == "-a") && argidx+1 < args.size()) {
				plugin_aliases.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-l") {
				list_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);

		if (!plugin_filename.empty())
			load_plugin(plugin_filename, plugin_aliases);

		if (list_mode)
		{
			log("\n");
#ifdef YOSYS_ENABLE_PYTHON
			if (loaded_plugins.empty() and loaded_python_plugins.empty())
#else
			if (loaded_plugins.empty())
#endif
				log("No plugins loaded.\n");
			else
				log("Loaded plugins:\n");

			for (auto &it : loaded_plugins)
				log("  %s\n", it.first);

#ifdef YOSYS_ENABLE_PYTHON
			for (auto &it : loaded_python_plugins)
				log("  %s\n", it.first);
#endif

			if (!loaded_plugin_aliases.empty()) {
				log("\n");
				int max_alias_len = 1;
				for (auto &it : loaded_plugin_aliases)
					max_alias_len = max(max_alias_len, GetSize(it.first));
				for (auto &it : loaded_plugin_aliases)
					log("Alias: %-*s %s\n", max_alias_len, it.first, it.second);
			}
		}
	}
} PluginPass;

YOSYS_NAMESPACE_END
