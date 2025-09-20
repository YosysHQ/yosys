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

#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SynthPass : public ScriptPass {
	SynthPass() : ScriptPass("synth", "generic synthesis script") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth [options]\n");
		log("\n");
		log("This command runs the default synthesis script. This command does not operate\n");
		log("on partly selected designs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -auto-top\n");
		log("        automatically determine the top of the design hierarchy\n");
		log("\n");
		log("    -flatten\n");
		log("        flatten the design before synthesis. this will pass '-auto-top' to\n");
		log("        'hierarchy' if no top module is specified.\n");
		log("\n");
		log("    -hieropt\n");
		log("        enable hierarchical optimization. this option is useful when `-flatten'\n");
		log("        is not used, or when selected modules are marked with 'keep_hierarchy'\n.");
		log("        to prevent their dissolution.\n");
		log("\n");
		log("    -encfile <file>\n");
		log("        passed to 'fsm_recode' via 'fsm'\n");
		log("\n");
		log("    -lut <k>\n");
		log("        perform synthesis for a k-LUT architecture.\n");
		log("\n");
		log("    -nofsm\n");
		log("        do not run FSM optimization\n");
		log("\n");
		log("    -noabc\n");
		log("        do not run abc (as if yosys was compiled without ABC support)\n");
		log("\n");
		log("    -booth\n");
		log("        run the booth pass to map $mul to Booth encoded multipliers\n");
		log("\n");
		log("    -noalumacc\n");
		log("        do not run 'alumacc' pass. i.e. keep arithmetic operators in\n");
		log("        their direct form ($add, $sub, etc.).\n");
		log("\n");
		log("    -nordff\n");
		log("        passed to 'memory'. prohibits merging of FFs into memory read ports\n");
		log("\n");
		log("    -noshare\n");
		log("        do not run SAT-based resource sharing\n");
		log("\n");
		log("    -run <from_label>[:<to_label>]\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -abc9\n");
		log("        use new ABC9 flow (EXPERIMENTAL)\n");
		log("\n");
		log("    -flowmap\n");
		log("        use FlowMap LUT techmapping instead of ABC\n");
		log("\n");
		log("    -no-rw-check\n");
		log("        marks all recognized read ports as \"return don't-care value on\n");
		log("        read/write collision\" (same result as setting the no_rw_check\n");
		log("        attribute on all memories).\n");
		log("\n");
		log("    -extra-map filename\n");
		log("        source extra rules from the given file to complement the default\n");
		log("        mapping library in the `techmap` step. this option can be\n");
		log("        repeated.\n");
		log("\n");
		log("    -relativeshare\n");
		log("        use paths relative to share directory for source locations\n");
		log("        where possible (experimental).\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_module, fsm_opts, memory_opts, abc;
	bool autotop, flatten, noalumacc, nofsm, noabc, noshare, flowmap, booth, hieropt, relative_share;
	int lut;
	std::vector<std::string> techmap_maps;

	void clear_flags() override
	{
		top_module.clear();
		fsm_opts.clear();
		memory_opts.clear();

		autotop = false;
		flatten = false;
		lut = 0;
		noalumacc = false;
		nofsm = false;
		noabc = false;
		noshare = false;
		flowmap = false;
		booth = false;
		hieropt = false;
		relative_share = false;
		abc = "abc";
		techmap_maps.clear();
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-top" && argidx + 1 < args.size()) {
				top_module = args[++argidx];
				continue;
			}
			if (args[argidx] == "-encfile" && argidx + 1 < args.size()) {
				fsm_opts = " -encfile " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx + 1 < args.size()) {
				size_t pos = args[argidx + 1].find(':');
				if (pos == std::string::npos) {
					run_from = args[++argidx];
					run_to = args[argidx];
				} else {
					run_from = args[++argidx].substr(0, pos);
					run_to = args[argidx].substr(pos + 1);
				}
				continue;
			}
			if (args[argidx] == "-auto-top") {
				autotop = true;
				continue;
			}
			if (args[argidx] == "-flatten") {
				flatten = true;
				continue;
			}
			if (args[argidx] == "-lut" && argidx + 1 < args.size()) {
				lut = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-nofsm") {
				nofsm = true;
				continue;
			}
			if (args[argidx] == "-noabc") {
				noabc = true;
				continue;
			}
			if (args[argidx] == "-noalumacc") {
				noalumacc = true;
				continue;
			}
			if (args[argidx] == "-booth") {
				booth = true;
				continue;
			}

			if (args[argidx] == "-nordff") {
				memory_opts += " -nordff";
				continue;
			}
			if (args[argidx] == "-noshare") {
				noshare = true;
				continue;
			}
			if (args[argidx] == "-abc9") {
				abc = "abc9";
				continue;
			}
			if (args[argidx] == "-flowmap") {
				flowmap = true;
				continue;
			}
			if (args[argidx] == "-no-rw-check") {
				memory_opts += " -no-rw-check";
				continue;
			}
			if (args[argidx] == "-extra-map" && argidx + 1 < args.size()) {
				techmap_maps.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-hieropt") {
				hieropt = true;
				continue;
			}
			if (args[argidx] == "-relativeshare") {
				relative_share = true;
				log_experimental("synth -relativeshare");
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (abc == "abc9" && !lut)
			log_cmd_error("ABC9 flow only supported for FPGA synthesis (using '-lut' option)\n");
		if (flowmap && !lut)
			log_cmd_error("FlowMap is only supported for FPGA synthesis (using '-lut' option)\n");

		log_header(design, "Executing SYNTH pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		std::string hieropt_flag;
		if (help_mode)
			hieropt_flag = " [-hier]";
		else
			hieropt_flag = hieropt ? " -hier" : "";

		std::string techmap_cmd = "techmap";
		if (relative_share)
			techmap_cmd += " -relativeshare";

		if (check_label("begin")) {
			if (help_mode) {
				run("hierarchy -check [-top <top> | -auto-top]");
			} else {
				if (top_module.empty()) {
					if (flatten || autotop)
						run("hierarchy -check -auto-top");
					else
						run("hierarchy -check");
				} else
					run(stringf("hierarchy -check -top %s", top_module));
			}
		}

		if (check_label("coarse")) {
			run("proc");
			if (flatten || help_mode)
				run("flatten", "  (if -flatten)");
			run("opt_expr");
			run("opt_clean");
			run("check");
			run("opt -nodffe -nosdff");
			if (!nofsm || help_mode)
				run("fsm" + fsm_opts, "      (unless -nofsm)");
			run("opt" + hieropt_flag);
			run("wreduce");
			run("peepopt");
			run("opt_clean");
			if (help_mode)
				run(techmap_cmd + " -map +/cmp2lut.v -map +/cmp2lcu.v", " (if -lut)");
			else if (lut)
				run(stringf("%s -map +/cmp2lut.v -map +/cmp2lcu.v -D LUT_WIDTH=%d", techmap_cmd, lut));
			if (booth || help_mode)
				run("booth", "    (if -booth)");
			if (!noalumacc)
				run("alumacc", "  (unless -noalumacc)");
			if (!noshare)
				run("share", "    (unless -noshare)");
			run("opt" + hieropt_flag);
			run("memory -nomap" + memory_opts);
			run("opt_clean");
		}

		if (check_label("fine")) {
			run("opt -fast -full" + hieropt_flag);
			run("memory_map");
			run("opt -full");
			if (help_mode) {
				run(techmap_cmd, "                  (unless -extra-map)");	
				run(techmap_cmd + " -map +/techmap.v -map <inject>", "  (if -extra-map)");
			} else {
				std::string techmap_opts;
				if (!techmap_maps.empty())
					techmap_opts += " -map +/techmap.v";
				for (auto fn : techmap_maps)
					techmap_opts += stringf(" -map %s", fn);
				run(techmap_cmd + techmap_opts);
			}
			if (help_mode) {
				run(techmap_cmd + " -map +/gate2lut.v", "(if -noabc and -lut)");
				run("clean; opt_lut", "           (if -noabc and -lut)");
				run("flowmap -maxlut K", "        (if -flowmap and -lut)");
			} else if (noabc && lut) {
				run(stringf("%s -map +/gate2lut.v -D LUT_WIDTH=%d", techmap_cmd, lut));
				run("clean; opt_lut");
			} else if (flowmap) {
				run(stringf("flowmap -maxlut %d", lut));
			}
			run("opt -fast" + hieropt_flag);

			if ((!noabc && !flowmap) || help_mode) {
#ifdef YOSYS_ENABLE_ABC
				if (help_mode) {
					run(abc + " -fast", "       (unless -noabc, unless -lut)");
					run(abc + " -fast -lut k", "(unless -noabc, if -lut)");
				} else {
					if (lut)
						run(stringf("%s -fast -lut %d", abc, lut));
					else
						run(abc + " -fast");
				}
				run("opt -fast", "       (unless -noabc)");
#endif
			}
		}

		if (check_label("check")) {
			run("hierarchy -check");
			run("stat");
			run("check");
		}
	}
} SynthPass;

PRIVATE_NAMESPACE_END
