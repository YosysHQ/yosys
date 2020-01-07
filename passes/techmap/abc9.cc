/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *            (C) 2019  Eddie Hung    <eddie@fpgeh.com>
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
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#define XC7_WIRE_DELAY 300 // Number with which ABC will map a 6-input gate
                           // to one LUT6 (instead of a LUT5 + LUT2)

struct Abc9Pass : public ScriptPass
{
	Abc9Pass() : ScriptPass("abc9", "use ABC9 for technology mapping") { }

	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc9 [options] [selection]\n");
		log("\n");
		log("This pass uses the ABC tool [1] for technology mapping of yosys's internal gate\n");
		log("library to a target architecture. Only fully-selected modules are supported.\n");
		log("\n");
		log("    -exe <command>\n");
#ifdef ABCEXTERNAL
		log("        use the specified command instead of \"" ABCEXTERNAL "\" to execute ABC.\n");
#else
		log("        use the specified command instead of \"<yosys-bindir>/yosys-abc\" to execute ABC.\n");
#endif
		log("        This can e.g. be used to call a specific version of ABC or a wrapper.\n");
		log("\n");
		log("    -script <file>\n");
		log("        use the specified ABC script file instead of the default script.\n");
		log("\n");
		log("        if <file> starts with a plus sign (+), then the rest of the filename\n");
		log("        string is interpreted as the command string to be passed to ABC. The\n");
		log("        leading plus sign is removed and all commas (,) in the string are\n");
		log("        replaced with blanks before the string is passed to ABC.\n");
		log("\n");
		log("        if no -script parameter is given, the following scripts are used:\n");
		log("\n");
		log("        for -lut/-luts (only one LUT size):\n");
		// FIXME
		//log("%s\n", fold_abc9_cmd(ABC_COMMAND_LUT /*"; lutpack {S}"*/).c_str());
		log("\n");
		log("        for -lut/-luts (different LUT sizes):\n");
		// FIXME
		//log("%s\n", fold_abc9_cmd(ABC_COMMAND_LUT).c_str());
		log("\n");
		log("    -fast\n");
		log("        use different default scripts that are slightly faster (at the cost\n");
		log("        of output quality):\n");
		log("\n");
		log("        for -lut/-luts:\n");
		// FIXME
		//log("%s\n", fold_abc9_cmd(ABC_FAST_COMMAND_LUT).c_str());
		log("\n");
		log("    -D <picoseconds>\n");
		log("        set delay target. the string {D} in the default scripts above is\n");
		log("        replaced by this option when used, and an empty string otherwise\n");
		log("        (indicating best possible delay).\n");
		log("\n");
//		log("    -S <num>\n");
//		log("        maximum number of LUT inputs shared.\n");
//		log("        (replaces {S} in the default scripts above, default: -S 1)\n");
//		log("\n");
		log("    -lut <width>\n");
		log("        generate netlist using luts of (max) the specified width.\n");
		log("\n");
		log("    -lut <w1>:<w2>\n");
		log("        generate netlist using luts of (max) the specified width <w2>. All\n");
		log("        luts with width <= <w1> have constant cost. for luts larger than <w1>\n");
		log("        the area cost doubles with each additional input bit. the delay cost\n");
		log("        is still constant for all lut widths.\n");
		log("\n");
		log("    -lut <file>\n");
		log("        pass this file with lut library to ABC.\n");
		log("\n");
		log("    -luts <cost1>,<cost2>,<cost3>,<sizeN>:<cost4-N>,..\n");
		log("        generate netlist using luts. Use the specified costs for luts with 1,\n");
		log("        2, 3, .. inputs.\n");
		log("\n");
		log("    -dff\n");
		log("        also pass $_ABC9_FF_ cells through to ABC. modules with many clock\n");
		log("        domains are marked as such and automatically partitioned by ABC.\n");
		log("\n");
		log("    -nocleanup\n");
		log("        when this option is used, the temporary files created by this pass\n");
		log("        are not removed. this is useful for debugging.\n");
		log("\n");
		log("    -showtmp\n");
		log("        print the temp dir name in log. usually this is suppressed so that the\n");
		log("        command output is identical across runs.\n");
		log("\n");
		log("    -box <file>\n");
		log("        pass this file with box library to ABC. Use with -lut.\n");
		log("\n");
		log("Note that this is a logic optimization pass within Yosys that is calling ABC\n");
		log("internally. This is not going to \"run ABC on your design\". It will instead run\n");
		log("ABC on logic snippets extracted from your design. You will not get any useful\n");
		log("output when passing an ABC script that writes a file. Instead write your full\n");
		log("design as an XAIGER file with `write_xaiger' and then load that into ABC\n");
		log("externally if you want to use ABC to convert your design into another format.\n");
		log("\n");
		log("[1] http://www.eecs.berkeley.edu/~alanmi/abc/\n");
		log("\n");
		help_script();
		log("\n");
	}

	std::stringstream exe_cmd;
	bool dff_mode, cleanup;

	void clear_flags() YS_OVERRIDE
	{
		exe_cmd.str("");
		exe_cmd << "abc9_exe";
		dff_mode = false;
		cleanup = true;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string run_from, run_to;
		clear_flags();

		// get arguments from scratchpad first, then override by command arguments
		dff_mode = design->scratchpad_get_bool("abc9.dff", dff_mode);
		cleanup = !design->scratchpad_get_bool("abc9.nocleanup", !cleanup);

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if ((arg == "-exe" || arg == "-script" || arg == "-D" ||
						/* arg == "-S" || */ arg == "-lut" || arg == "-luts" ||
						arg == "-box" || arg == "-W") &&
					argidx+1 < args.size()) {
				exe_cmd << " " << arg << " " << args[++argidx];
				continue;
			}
			if (arg == "-fast" || /* arg == "-dff" || */
					/* arg == "-nocleanup" || */ arg == "-showtmp" ||
					arg == "-nomfs") {
				exe_cmd << " " << arg;
				continue;
			}
			if (arg == "-dff") {
				dff_mode = true;
				continue;
			}
			if (arg == "-nocleanup") {
				cleanup = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		log_header(design, "Executing ABC9 pass.\n");

		run_script(design, run_from, run_to);
	}

	void script() YS_OVERRIDE
	{
		run("scc -set_attr abc9_scc_id {}");
		if (help_mode)
			run("abc9_ops -break_scc -prep_holes [-dff]", "(option for -dff)");
		else
			run("abc9_ops -break_scc -prep_holes" + std::string(dff_mode ? " -dff" : ""), "(option for -dff)");
		run("select -set abc9_holes A:abc9_holes");
		run("flatten -wb @abc9_holes");
		run("techmap @abc9_holes");
		run("aigmap");
		if (dff_mode)
			run("abc9_ops -prep_dff");
		run("opt -purge @abc9_holes");
		run("wbflip @abc9_holes");

		auto selected_modules = active_design->selected_modules();
		active_design->selection_stack.emplace_back(false);

		for (auto mod : selected_modules) {
			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", log_id(mod));
				continue;
			}
			log_assert(!mod->attributes.count(ID(abc9_box_id)));

			active_design->selection().select(mod);

			if (!active_design->selected_whole_module(mod))
				log_error("Can't handle partially selected module %s!\n", log_id(mod));

			std::string tempdir_name = "/tmp/yosys-abc-XXXXXX";
			if (!cleanup)
				tempdir_name[0] = tempdir_name[4] = '_';
			tempdir_name = make_temp_dir(tempdir_name);

			run(stringf("write_xaiger -map %s/input.sym %s/input.xaig", tempdir_name.c_str(), tempdir_name.c_str()),
					"write_xaiger -map <abc-temp-dir>/input.sym <abc-temp-dir>/input.xaig");

			int num_outputs = active_design->scratchpad_get_int("write_xaiger.num_outputs");
			log("Extracted %d AND gates and %d wires to a netlist network with %d inputs and %d outputs.\n",
					active_design->scratchpad_get_int("write_xaiger.num_ands"),
					active_design->scratchpad_get_int("write_xaiger.num_wires"),
					active_design->scratchpad_get_int("write_xaiger.num_inputs"),
					num_outputs);
			if (num_outputs) {
				run(stringf("%s -cwd %s", exe_cmd.str().c_str(), tempdir_name.c_str()),
						"abc9_exe [options] -cwd <abc-temp-dir>");
				run(stringf("read_aiger -xaiger -wideports -module_name %s$abc9 -map %s/input.sym %s/output.aig", log_id(mod->name), tempdir_name.c_str(), tempdir_name.c_str()),
						"read_aiger -xaiger -wideports -module_name <module-name>$abc9 -map <abc-temp-dir>/input.sym <abc-temp-dir>/output.aig");
				run("abc9_ops -reintegrate");
			}
			else
				log("Don't call ABC as there is nothing to map.\n");

			if (cleanup) {
				log("Removing temp directory.\n");
				remove_directory(tempdir_name);
			}

			active_design->selection().selected_modules.clear();
		}

		active_design->selection_stack.pop_back();

		run("abc9_ops -unbreak_scc");
	}
} Abc9Pass;

PRIVATE_NAMESPACE_END
