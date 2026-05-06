/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2018  Ruben Undheim <ruben.undheim@gmail.com>
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
#include "passes/hierarchy/util/interfaces.h"
#include "passes/hierarchy/util/misc.h"
#include "passes/hierarchy/util/clean.h"
#include "passes/hierarchy/util/top.h"
#include "passes/hierarchy/util/positionals.h"
#include "passes/hierarchy/util/verilog.h"
#include "passes/hierarchy/util/generate.h"
#include "passes/hierarchy/util/ports.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

#ifndef _WIN32
#  include <unistd.h>
#endif


USING_YOSYS_NAMESPACE
using namespace Hierarchy;

PRIVATE_NAMESPACE_BEGIN

struct HierarchyPass : public Pass {
	HierarchyPass() : Pass("hierarchy", "check, expand and clean up design hierarchy") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    hierarchy [-check] [-top <module>]\n");
		log("    hierarchy -generate <cell-types> <port-decls>\n");
		log("\n");
		log("In parametric designs, a module might exists in several variations with\n");
		log("different parameter values. This pass looks at all modules in the current\n");
		log("design and re-runs the language frontends for the parametric modules as\n");
		log("needed. It also resolves assignments to wired logic data types (wand/wor),\n");
		log("resolves positional module parameters, unrolls array instances, and more.\n");
		log("\n");
		log("    -check\n");
		log("        also check the design hierarchy. this generates an error when\n");
		log("        an unknown module is used as cell type.\n");
		log("\n");
		log("    -simcheck\n");
		log("        like -check, but also throw an error if blackbox modules are\n");
		log("        instantiated, and throw an error if the design has no top module.\n");
		log("\n");
		log("    -smtcheck\n");
		log("        like -simcheck, but allow smtlib2_module modules.\n");
		log("\n");
		log("    -purge_lib\n");
		log("        by default the hierarchy command will not remove library (blackbox)\n");
		log("        modules. use this option to also remove unused blackbox modules.\n");
		log("\n");
		log("    -libdir <directory>\n");
		log("        search for files named <module_name>.v in the specified directory\n");
		log("        for unknown modules and automatically run read_verilog for each\n");
		log("        unknown module.\n");
		log("\n");
		log("    -keep_positionals\n");
		log("        per default this pass also converts positional arguments in cells\n");
		log("        to arguments using port names. This option disables this behavior.\n");
		log("\n");
		log("    -keep_portwidths\n");
		log("        per default this pass adjusts the port width on cells that are\n");
		log("        module instances when the width does not match the module port. This\n");
		log("        option disables this behavior.\n");
		log("\n");
		log("    -nodefaults\n");
		log("        do not resolve input port default values\n");
		log("\n");
		log("    -nokeep_prints\n");
		log("        per default this pass sets the \"keep\" attribute on all modules\n");
		log("        that directly or indirectly display text on the terminal.\n");
		log("        This option disables this behavior.\n");
		log("\n");
		log("    -nokeep_asserts\n");
		log("        per default this pass sets the \"keep\" attribute on all modules\n");
		log("        that directly or indirectly contain one or more formal properties.\n");
		log("        This option disables this behavior.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified top module to build the design hierarchy. Modules\n");
		log("        outside this tree (unused modules) are removed.\n");
		log("\n");
		log("        when the -top option is used, the 'top' attribute will be set on the\n");
		log("        specified top module. otherwise a module with the 'top' attribute set\n");
		log("        will implicitly be used as top module, if such a module exists.\n");
		log("\n");
		log("    -auto-top\n");
		log("        automatically determine the top of the design hierarchy and mark it.\n");
		log("\n");
		log("    -chparam name value \n");
		log("       elaborate the top module using this parameter value. Modules on which\n");
		log("       this parameter does not exist may cause a warning message to be output.\n");
		log("       This option can be specified multiple times to override multiple\n");
		log("       parameters. String values must be passed in double quotes (\").\n");
		log("\n");
		log("In -generate mode this pass generates blackbox modules for the given cell\n");
		log("types (wildcards supported). For this the design is searched for cells that\n");
		log("match the given types and then the given port declarations are used to\n");
		log("determine the direction of the ports. The syntax for a port declaration is:\n");
		log("\n");
		log("    {i|o|io}[@<num>]:<portname>\n");
		log("\n");
		log("Input ports are specified with the 'i' prefix, output ports with the 'o'\n");
		log("prefix and inout ports with the 'io' prefix. The optional <num> specifies\n");
		log("the position of the port in the parameter list (needed when instantiated\n");
		log("using positional arguments). When <num> is not specified, the <portname> can\n");
		log("also contain wildcard characters.\n");
		log("\n");
		log("This pass ignores the current selection and always operates on all modules\n");
		log("in the current design.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing HIERARCHY pass (managing design hierarchy).\n");

		bool flag_check = false;
		bool flag_simcheck = false;
		bool flag_smtcheck = false;
		bool purge_lib = false;
		std::string top_mod_name_to_load = "";
		std::vector<std::string> libdirs;

		bool auto_top_mode = false;
		bool generate_mode = false;
		bool keep_positionals = false;
		bool keep_portwidths = false;
		bool nodefaults = false;
		bool nokeep_prints = false;
		bool nokeep_asserts = false;
		Generator generator;

		std::map<std::string, std::string> parameters;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-generate" && !flag_check && !flag_simcheck && !flag_smtcheck) {
				generate_mode = true;
				log("Entering generate mode.\n");
				while (++argidx < args.size()) {
					generator.parse_arg(args[argidx].c_str());
				}
				continue;
			}
			if (args[argidx] == "-check") {
				flag_check = true;
				continue;
			}
			if (args[argidx] == "-simcheck") {
				flag_simcheck = true;
				continue;
			}
			if (args[argidx] == "-smtcheck") {
				flag_smtcheck = true;
				continue;
			}
			if (args[argidx] == "-purge_lib") {
				purge_lib = true;
				continue;
			}
			if (args[argidx] == "-keep_positionals") {
				keep_positionals = true;
				continue;
			}
			if (args[argidx] == "-keep_portwidths") {
				keep_portwidths = true;
				continue;
			}
			if (args[argidx] == "-nodefaults") {
				nodefaults = true;
				continue;
			}
			if (args[argidx] == "-nokeep_prints") {
				nokeep_prints = true;
				continue;
			}
			if (args[argidx] == "-nokeep_asserts") {
				nokeep_asserts = true;
				continue;
			}
			if (args[argidx] == "-libdir" && argidx+1 < args.size()) {
				libdirs.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-top") {
				if (++argidx >= args.size())
					log_cmd_error("Option -top requires an additional argument!\n");
				top_mod_name_to_load = args[argidx];
				continue;
			}
			if (args[argidx] == "-auto-top") {
				auto_top_mode = true;
				continue;
			}
			if (args[argidx] == "-chparam"  && argidx+2 < args.size()) {
				const std::string &key = args[++argidx];
				const std::string &value = args[++argidx];
				auto r = parameters.emplace(key, value);
				if (!r.second) {
					log_warning("-chparam %s already specified: overwriting.\n", key);
					r.first->second = value;
				}
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);

		if (generate_mode)
			return generator.generate(design);

		log_push();

		TopModulePrepare top {design, parameters};
		Module* top_mod = top.load_top(top_mod_name_to_load, auto_top_mode);

		if ((flag_simcheck || flag_smtcheck) && top_mod == nullptr)
				log_error("Design has no top module.\n");

		expand_all_interfaces(design, top_mod, flag_check, flag_simcheck, flag_smtcheck, libdirs);

		log_header(design, "Resolving $connect directionality..\n");
		for (auto module : design->modules())
			resolve_connect_directionality(module);

		if (top_mod != NULL) {
			log_header(design, "Analyzing design hierarchy..\n");
			clean(design, top_mod, purge_lib);
		}

		if (top_mod != NULL)
			ensure_unique_top_attribute(top_mod, design);

		set_keeps(design, !nokeep_prints, !nokeep_asserts);

		if (flag_simcheck || flag_smtcheck) {
			check_supported_formal(design);
		}

		resolve_verilog(design, nodefaults, keep_positionals, keep_portwidths, top.is_from_verific);

		log_pop();
	}
} HierarchyPass;

PRIVATE_NAMESPACE_END
