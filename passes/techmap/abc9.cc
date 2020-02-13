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

// [[CITE]] ABC
// Berkeley Logic Synthesis and Verification Group, ABC: A System for Sequential Synthesis and Verification
// http://www.eecs.berkeley.edu/~alanmi/abc/

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

// abc9_exe.cc
std::string fold_abc9_cmd(std::string str);

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Abc9Pass : public ScriptPass
{
	Abc9Pass() : ScriptPass("abc9", "use ABC9 for technology mapping") { }
	void on_register() YS_OVERRIDE
	{
		RTLIL::constpad["abc9.script.default"] = "+&scorr; &sweep; &dc2; &dch -f; &ps; &if {C} {W} {D} {R} -v; &mfs";
		RTLIL::constpad["abc9.script.default.area"] = "+&scorr; &sweep; &dc2; &dch -f; &ps; &if {C} {W} {D} {R} -a -v; &mfs";
		RTLIL::constpad["abc9.script.default.fast"] = "+&if {C} {W} {D} {R} -v";
		// Based on ABC's &flow
		RTLIL::constpad["abc9.script.flow"] = "+&scorr; &sweep;" \
			"&dch -C 500;" \
			/* Round 1 */ \
			/* Map 1 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &dsdb;" \
			/* Map 2 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &syn2 -m -R 10; &dsdb;" \
			"&blut -a -K 6;" \
			/* Map 3 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			/* Round 2 */ \
			"&st; &sopb;" \
			/* Map 1 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &dsdb;" \
			/* Map 2 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &syn2 -m -R 10; &dsdb;" \
			"&blut -a -K 6;" \
			/* Map 3 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			/* Round 3 */ \
			/* Map 1 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &dsdb;" \
			/* Map 2 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;" \
			"&st; &syn2 -m -R 10; &dsdb;" \
			"&blut -a -K 6;" \
			/* Map 3 */ "&unmap; &if {C} {W} {D} {R} -v; &save; &load; &mfs;";
		// Based on ABC's &flow2
		RTLIL::constpad["abc9.script.flow2"] = "+&scorr; &sweep;" \
			/* Comm1 */ "&synch2 -K 6 -C 500; &if -m {C} {W} {D} {R} -v; &mfs "/*"-W 4 -M 500 -C 7000"*/"; &save;"\
			/* Comm2 */ "&dch -C 500; &if -m {C} {W} {D} {R} -v; &mfs "/*"-W 4 -M 500 -C 7000"*/"; &save;"\
			"&load; &st; &sopb -R 10 -C 4; " \
			/* Comm3 */ "&synch2 -K 6 -C 500; &if -m "/*"-E 5"*/" {C} {W} {D} {R} -v; &mfs "/*"-W 4 -M 500 -C 7000"*/"; &save;"\
			/* Comm2 */ "&dch -C 500; &if -m {C} {W} {D} {R} -v; &mfs "/*"-W 4 -M 500 -C 7000"*/"; &save; "\
			"&load";
		// Based on ABC's &flow3
		RTLIL::constpad["abc9.script.flow3"] = "+&scorr; &sweep;" \
			"&if {C} {W} {D}; &save; &st; &syn2; &if {C} {W} {D} {R} -v; &save; &load;"\
			"&st; &if {C} -g -K 6; &dch -f; &if {C} {W} {D} {R} -v; &save; &load;"\
			"&st; &if {C} -g -K 6; &synch2; &if {C} {W} {D} {R} -v; &save; &load;"\
			"&mfs";
	}
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc9 [options] [selection]\n");
		log("\n");
		log("This script pass performs a sequence of commands to facilitate the use of the ABC\n");
		log("tool [1] for technology mapping of the current design to a target FPGA\n");
		log("architecture. Only fully-selected modules are supported.\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
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
		log("%s\n", fold_abc9_cmd(RTLIL::constpad.at("abc9.script.default").substr(1,std::string::npos)).c_str());
		log("\n");
		log("    -fast\n");
		log("        use different default scripts that are slightly faster (at the cost\n");
		log("        of output quality):\n");
		log("%s\n", fold_abc9_cmd(RTLIL::constpad.at("abc9.script.default.fast").substr(1,std::string::npos)).c_str());
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
		log("    -maxlut <width>\n");
		log("        when auto-generating the lut library, discard all luts equal to or\n");
		log("        greater than this size (applicable when neither -lut nor -luts is\n");
		log("        specified).\n");
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
		log("        pass this file with box library to ABC.\n");
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
	bool lut_mode;
	int maxlut;
	std::string box_file;

	void clear_flags() YS_OVERRIDE
	{
		exe_cmd.str("");
		exe_cmd << "abc9_exe";
		dff_mode = false;
		cleanup = true;
		lut_mode = false;
		maxlut = 0;
		box_file = "";
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string run_from, run_to;
		clear_flags();

		// get arguments from scratchpad first, then override by command arguments
		dff_mode = design->scratchpad_get_bool("abc9.dff", dff_mode);
		cleanup = !design->scratchpad_get_bool("abc9.nocleanup", !cleanup);

		if (design->scratchpad_get_bool("abc9.debug")) {
			cleanup = false;
			exe_cmd << " -showtmp";
		}

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if ((arg == "-exe" || arg == "-script" || arg == "-D" ||
						/*arg == "-S" ||*/ arg == "-lut" || arg == "-luts" ||
						/*arg == "-box" ||*/ arg == "-W") &&
					argidx+1 < args.size()) {
				if (arg == "-lut" || arg == "-luts")
					lut_mode = true;
				exe_cmd << " " << arg << " " << args[++argidx];
				continue;
			}
			if (arg == "-fast" || /* arg == "-dff" || */
					/* arg == "-nocleanup" || */ arg == "-showtmp") {
				exe_cmd << " " << arg;
				continue;
			}
			if (arg == "-dff") {
				dff_mode = true;
				exe_cmd << " " << arg;
				continue;
			}
			if (arg == "-nocleanup") {
				cleanup = false;
				continue;
			}
			if (arg == "-box" && argidx+1 < args.size()) {
				box_file = args[++argidx];
				continue;
			}
			if (arg == "-maxlut" && argidx+1 < args.size()) {
				maxlut = atoi(args[++argidx].c_str());
				continue;
			}
			if (arg == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[++argidx].substr(0, pos);
				run_to = args[argidx].substr(pos+1);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (maxlut && lut_mode)
			log_cmd_error("abc9 '-maxlut' option only applicable without '-lut' nor '-luts'.\n");

		log_assert(design);
		if (design->selected_modules().empty()) {
			log_warning("No modules selected for ABC9 techmapping.\n");
			return;
		}

		log_header(design, "Executing ABC9 pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() YS_OVERRIDE
	{
		if (check_label("pre")) {
			run("abc9_ops -check");
			run("scc -set_attr abc9_scc_id {}");
			if (help_mode)
				run("abc9_ops -mark_scc -prep_delays -prep_xaiger [-dff]", "(option for -dff)");
			else
				run("abc9_ops -mark_scc -prep_delays -prep_xaiger" + std::string(dff_mode ? " -dff" : ""), "(option for -dff)");
			if (help_mode)
				run("abc9_ops -prep_lut <maxlut>", "(skip if -lut or -luts)");
			else if (!lut_mode)
				run(stringf("abc9_ops -prep_lut %d", maxlut));
			if (help_mode)
				run("abc9_ops -prep_box [-dff]", "(skip if -box)");
			else if (box_file.empty())
				run(stringf("abc9_ops -prep_box %s", dff_mode ? "-dff" : ""));
			run("select -set abc9_holes A:abc9_holes");
			run("flatten -wb @abc9_holes");
			run("techmap @abc9_holes");
			if (dff_mode || help_mode)
				run("abc9_ops -prep_dff", "(only if -dff)");
			run("opt -purge @abc9_holes");
			run("aigmap");
			run("wbflip @abc9_holes");
		}

		if (check_label("map")) {
			if (help_mode) {
				run("foreach module in selection");
				run("    abc9_ops -write_lut <abc-temp-dir>/input.lut", "(skip if '-lut' or '-luts')");
				run("    abc9_ops -write_box <abc-temp-dir>/input.box");
				run("    write_xaiger -map <abc-temp-dir>/input.sym <abc-temp-dir>/input.xaig");
				run("    abc9_exe [options] -cwd <abc-temp-dir> [-lut <abc-temp-dir>/input.lut] -box <abc-temp-dir>/input.box");
				run("    read_aiger -xaiger -wideports -module_name <module-name>$abc9 -map <abc-temp-dir>/input.sym <abc-temp-dir>/output.aig");
				run("    abc9_ops -reintegrate");
			}
			else {
				auto selected_modules = active_design->selected_modules();
				active_design->selection_stack.emplace_back(false);

				for (auto mod : selected_modules) {
					if (mod->processes.size() > 0) {
						log("Skipping module %s as it contains processes.\n", log_id(mod));
						continue;
					}
					log_assert(!mod->attributes.count(ID(abc9_box_id)));

					log_push();
					active_design->selection().select(mod);

					if (!active_design->selected_whole_module(mod))
						log_error("Can't handle partially selected module %s!\n", log_id(mod));

					std::string tempdir_name = "/tmp/yosys-abc-XXXXXX";
					if (!cleanup)
						tempdir_name[0] = tempdir_name[4] = '_';
					tempdir_name = make_temp_dir(tempdir_name);

					if (!lut_mode)
						run(stringf("abc9_ops -write_lut %s/input.lut", tempdir_name.c_str()));
					run(stringf("abc9_ops -write_box %s/input.box", tempdir_name.c_str()));
					run(stringf("write_xaiger -map %s/input.sym %s/input.xaig", tempdir_name.c_str(), tempdir_name.c_str()));

					int num_outputs = active_design->scratchpad_get_int("write_xaiger.num_outputs");

					log("Extracted %d AND gates and %d wires from module `%s' to a netlist network with %d inputs and %d outputs.\n",
							active_design->scratchpad_get_int("write_xaiger.num_ands"),
							active_design->scratchpad_get_int("write_xaiger.num_wires"),
							log_id(mod),
							active_design->scratchpad_get_int("write_xaiger.num_inputs"),
							num_outputs);
					if (num_outputs) {
						std::string abc9_exe_cmd;
						abc9_exe_cmd += stringf("%s -cwd %s", exe_cmd.str().c_str(), tempdir_name.c_str());
						if (!lut_mode)
							abc9_exe_cmd += stringf(" -lut %s/input.lut", tempdir_name.c_str());
						abc9_exe_cmd += stringf(" -box %s/input.box", tempdir_name.c_str());
						run(abc9_exe_cmd);
						run(stringf("read_aiger -xaiger -wideports -module_name %s$abc9 -map %s/input.sym %s/output.aig", log_id(mod), tempdir_name.c_str(), tempdir_name.c_str()));
						run("abc9_ops -reintegrate");
					}
					else
						log("Don't call ABC as there is nothing to map.\n");

					if (cleanup) {
						log("Removing temp directory.\n");
						remove_directory(tempdir_name);
					}

					active_design->selection().selected_modules.clear();
					log_pop();
				}

				active_design->selection_stack.pop_back();
			}
		}
	}
} Abc9Pass;

PRIVATE_NAMESPACE_END
