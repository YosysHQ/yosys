/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Martin Povišer <povik@cutebit.org>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct AbcNewPass : public ScriptPass {
	AbcNewPass() : ScriptPass("abc_new", "(experimental) use ABC for SC technology mapping (new)")
	{
		experimental();
	}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc_new [options] [selection]\n");
		log("\n");
		log("This command uses the ABC tool [1] to optimize the current design and map it to\n");
		log("the target standard cell library.\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -exe <command>\n");
		log("    -script <file>\n");
		log("    -D <picoseconds>\n");
		log("    -constr <file>\n");
		log("    -dont_use <cell_name>\n");
		log("    -liberty <file>\n");
		log("        these options are passed on to the 'abc9_exe' command which invokes\n");
		log("        the ABC tool on individual modules of the design. please see\n");
		log("        'help abc9_exe' for more details\n");
		log("\n");
		log("[1] http://www.eecs.berkeley.edu/~alanmi/abc/\n");
		log("\n");
		help_script();
		log("\n");
	}

	bool cleanup;
	std::string abc_exe_options;

	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		std::string run_from, run_to;
		cleanup = true;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-exe" || args[argidx] == "-script" ||
					args[argidx] == "-D" ||
					args[argidx] == "-constr" || args[argidx] == "-dont_use" ||
					args[argidx] == "-liberty") {
				abc_exe_options += " " + args[argidx] + " " + args[argidx + 1];
				argidx++;
			} else if (args[argidx] == "-run" && argidx + 1 < args.size()) {
				size_t pos = args[++argidx].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[argidx].substr(0, pos);
				run_to = args[argidx].substr(pos + 1);
			} else if (args[argidx] == "-nocleanup") {
				cleanup = false;
			} else {
				break;
			}
		}
		extra_args(args, argidx, d);

		log_header(d, "Executing ABC_NEW pass.\n");
		log_push();
		run_script(d, run_from, run_to);
		log_pop();
	}

	void script() override
	{
		if (check_label("check")) {
			run("abc9_ops -check");	
		}

		if (check_label("prep_boxes")) {
			run("box_derive");
			run("abc9_ops -prep_box");
		}

		if (check_label("map")) {
			std::vector<Module *> selected_modules;

			if (!help_mode) {
				selected_modules = active_design->selected_whole_modules_warn();
				active_design->selection_stack.emplace_back(false);
			} else {
				selected_modules = {nullptr};
				run("foreach module in selection");
			}

			for (auto mod : selected_modules) {
				std::string tmpdir = "<abc-temp-dir>";
				std::string modname = "<module>";
				std::string exe_options = "[options]";
				if (!help_mode) {
					tmpdir = cleanup ? (get_base_tmpdir() + "/") : "_tmp_";
					tmpdir += proc_program_prefix() + "yosys-abc-XXXXXX";
					tmpdir = make_temp_dir(tmpdir);
					modname = mod->name.str();
					exe_options = abc_exe_options;
					log_header(active_design, "Mapping module '%s'.\n", log_id(mod));
					log_push();
					active_design->selection().select(mod);
				}

				run(stringf("  abc9_ops -write_box %s/input.box", tmpdir.c_str()));
				run(stringf("  write_xaiger2 -mapping_prep -map2 %s/input.map2 %s/input.xaig", tmpdir.c_str(), tmpdir.c_str()));
				run(stringf("  abc9_exe %s -cwd %s -box %s/input.box", exe_options.c_str(), tmpdir.c_str(), tmpdir.c_str()));
				run(stringf("  read_xaiger2 -sc_mapping -module_name %s -map2 %s/input.map2 %s/output.aig",
							modname.c_str(), tmpdir.c_str(), tmpdir.c_str()));

				if (!help_mode) {
					active_design->selection().selected_modules.clear();
					log_pop();
				}
			}

			if (!help_mode) {
				active_design->selection_stack.pop_back();
			}
		}
	}
} AbcNewPass;

PRIVATE_NAMESPACE_END
