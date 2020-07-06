/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2014  Clifford Wolf <clifford@clifford.at>
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

#ifdef YOSYS_ENABLE_PLUGINS
#  include <dlfcn.h>
#endif

#ifdef WITH_PYTHON
#  include <boost/algorithm/string/predicate.hpp>
#  include <Python.h>
#  include <boost/filesystem.hpp>
#endif

YOSYS_NAMESPACE_BEGIN

std::map<std::string, void*> loaded_plugins;
#ifdef WITH_PYTHON
std::map<std::string, void*> loaded_python_plugins;
#endif
std::map<std::string, std::string> loaded_plugin_aliases;

#ifdef YOSYS_ENABLE_PLUGINS
void load_plugin(std::string filename, std::vector<std::string> aliases)
{
	std::string orig_filename = filename;

	if (filename.find('/') == std::string::npos)
		filename = "./" + filename;

	#ifdef WITH_PYTHON
	if (!loaded_plugins.count(filename) && !loaded_python_plugins.count(filename)) {
	#else
	if (!loaded_plugins.count(filename)) {
	#endif

		#ifdef WITH_PYTHON

		boost::filesystem::path full_path(filename);

		if(strcmp(full_path.extension().c_str(), ".py") == 0)
		{
			std::string path(full_path.parent_path().c_str());
			filename = full_path.filename().c_str();
			filename = filename.substr(0,filename.size()-3);
			PyRun_SimpleString(("sys.path.insert(0,\""+path+"\")").c_str());
			PyErr_Print();
			PyObject *module_p = PyImport_ImportModule(filename.c_str());
			if(module_p == NULL)
			{
				PyErr_Print();
				log_cmd_error("Can't load python module `%s'\n", full_path.filename().c_str());
				return;
			}
			loaded_python_plugins[orig_filename] = module_p;
			Pass::init_register();
		} else {
		#endif

		void *hdl = dlopen(filename.c_str(), RTLD_LAZY|RTLD_LOCAL);
		if (hdl == NULL && orig_filename.find('/') == std::string::npos)
			hdl = dlopen((proc_share_dirname() + "plugins/" + orig_filename + ".so").c_str(), RTLD_LAZY|RTLD_LOCAL);
		if (hdl == NULL)
			log_cmd_error("Can't load module `%s': %s\n", filename.c_str(), dlerror());
		loaded_plugins[orig_filename] = hdl;
		Pass::init_register();

		#ifdef WITH_PYTHON
		}
		#endif
	}

	for (auto &alias : aliases)
		loaded_plugin_aliases[alias] = orig_filename;
}
#else
void load_plugin(std::string, std::vector<std::string>)
{
	log_error("This version of yosys is built without plugin support.\n");
}
#endif

struct PluginPass : public Pass {
	PluginPass() : Pass("plugin", "load and list loaded plugins") { }
	void help() YS_OVERRIDE
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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
#ifdef WITH_PYTHON
			if (loaded_plugins.empty() and loaded_python_plugins.empty())
#else
			if (loaded_plugins.empty())
#endif
				log("No plugins loaded.\n");
			else
				log("Loaded plugins:\n");

			for (auto &it : loaded_plugins)
				log("  %s\n", it.first.c_str());

#ifdef WITH_PYTHON
			for (auto &it : loaded_python_plugins)
				log("  %s\n", it.first.c_str());
#endif

			if (!loaded_plugin_aliases.empty()) {
				log("\n");
				int max_alias_len = 1;
				for (auto &it : loaded_plugin_aliases)
					max_alias_len = max(max_alias_len, GetSize(it.first));
				for (auto &it : loaded_plugin_aliases)
					log("Alias: %-*s %s\n", max_alias_len, it.first.c_str(), it.second.c_str());
			}
		}
	}
} PluginPass;

YOSYS_NAMESPACE_END

