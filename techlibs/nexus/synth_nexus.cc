/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020 gatecat <gatecat@ds0.me>
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

struct SynthNexusPass : public ScriptPass
{
	SynthNexusPass() : ScriptPass("synth_nexus", "synthesis for Lattice Nexus FPGAs") { }

	void on_register() override
	{
		RTLIL::constpad["synth_nexus.abc9.W"] = "300";
	}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_nexus [options]\n");
		log("\n");
		log("This command runs synthesis for Lattice Nexus FPGAs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -family <device>\n");
		log("        run synthesis for the specified Nexus device\n");
		log("        supported values: lifcl, lfd2nx\n");
		log("\n");
		log("    -json <file>\n");
		log("        write the design to the specified JSON file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -vm <file>\n");
		log("        write the design to the specified structural Verilog file. writing of\n");
		log("        an output file is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis\n");
		log("\n");
		log("    -dff\n");
		log("        run 'abc'/'abc9' with -dff option\n");
		log("\n");
		log("    -retime\n");
		log("        run 'abc' with '-dff -D 1' options\n");
		log("\n");
		log("    -noccu2\n");
		log("        do not use CCU2 cells in output netlist\n");
		log("\n");
		log("    -nodffe\n");
		log("        do not use flipflops with CE in output netlist\n");
		log("\n");
		log("    -nolram\n");
		log("        do not use large RAM cells in output netlist\n");
		log("        note that large RAM must be explicitly requested with a (* lram *)\n");
		log("        attribute on the memory.\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use block RAM cells in output netlist\n");
		log("\n");
		log("    -nolutram\n");
		log("        do not use LUT RAM cells in output netlist\n");
		log("\n");
		log("    -nowidelut\n");
		log("        do not use PFU muxes to implement LUTs larger than LUT4s\n");
		log("\n");
		log("    -noiopad\n");
		log("        do not insert IO buffers\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not infer DSP multipliers\n");
		log("\n");
		log("    -abc9\n");
		log("        use new ABC9 flow (EXPERIMENTAL)\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, json_file, vm_file, family;
	bool noccu2, nodffe, nolram, nobram, nolutram, nowidelut, noiopad, nodsp, flatten, dff, retime, abc9;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		family = "lifcl";
		json_file = "";
		vm_file = "";
		noccu2 = false;
		nodffe = false;
		nolram = false;
		nobram = false;
		nolutram = false;
		nowidelut = false;
		noiopad = false;
		nodsp = false;
		flatten = true;
		dff = false;
		retime = false;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_opt = "-top " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-json" && argidx+1 < args.size()) {
				json_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-vm" && argidx+1 < args.size()) {
				vm_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[++argidx].substr(0, pos);
				run_to = args[argidx].substr(pos+1);
				continue;
			}
			if ((args[argidx] == "-family") && argidx+1 < args.size()) {
				family = args[++argidx];
				continue;
			}
			if (args[argidx] == "-flatten") {
				flatten = true;
				continue;
			}
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			if (args[argidx] == "-dff") {
				dff = true;
				continue;
			}
			if (args[argidx] == "-nodsp") {
				nodsp = true;
				continue;
			}
			if (args[argidx] == "-retime") {
				retime = true;
				continue;
			}
			if (args[argidx] == "-noccu2") {
				noccu2 = true;
				continue;
			}
			if (args[argidx] == "-nodffe") {
				nodffe = true;
				continue;
			}
			if (args[argidx] == "-nolram") {
				nolram = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-nolutram") {
				nolutram = true;
				continue;
			}
			if (args[argidx] == "-nowidelut") {
				nowidelut = true;
				continue;
			}
			if (args[argidx] == "-noiopad") {
				noiopad = true;
				continue;
			}
			if (args[argidx] == "-abc9") {
				abc9 = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (abc9 && retime)
				log_cmd_error("-retime option not currently compatible with -abc9!\n");

		log_header(design, "Executing SYNTH_NEXUS pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	struct DSPRule {
		int a_maxwidth;
		int b_maxwidth;
		int a_minwidth;
		int b_minwidth;
		std::string prim;
	};

	const std::vector<DSPRule> dsp_rules = {
		{36, 36, 22, 22, "$__NX_MUL36X36"},
		{36, 18, 22, 10, "$__NX_MUL36X18"},
		{18, 18, 10,  4, "$__NX_MUL18X18"},
		{18, 18,  4, 10, "$__NX_MUL18X18"},
		{ 9,  9,  4,  4, "$__NX_MUL9X9"},
	};

	void script() override
	{

		if (family != "lifcl" && family != "lfd2nx")
			log_cmd_error("Invalid Nexus -family setting: '%s'.\n", family.c_str());

		if (check_label("begin"))
		{
			run("read_verilog -lib -specify +/nexus/cells_sim.v +/nexus/cells_xtra.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (check_label("coarse"))
		{
			run("proc");
			if (flatten || help_mode)
				run("flatten");
			run("tribuf -logic");
			run("deminout");
			run("opt_expr");
			run("opt_clean");
			run("check");
			run("opt -nodffe -nosdff");
			run("fsm");
			run("opt");
			run("wreduce");
			run("peepopt");
			run("opt_clean");
			run("share");
			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=4");
			run("opt_expr");
			run("opt_clean");

			if (help_mode) {
				run("techmap -map +/mul2dsp.v [...]", "(unless -nodsp)");
				run("techmap -map +/nexus/dsp_map.v", "(unless -nodsp)");
			} else if (!nodsp) {
				for (const auto &rule : dsp_rules) {
					run(stringf("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=%d -D DSP_B_MAXWIDTH=%d -D DSP_A_MINWIDTH=%d -D DSP_B_MINWIDTH=%d -D DSP_NAME=%s",
						rule.a_maxwidth, rule.b_maxwidth, rule.a_minwidth, rule.b_minwidth, rule.prim.c_str()));
					run("chtype -set $mul t:$__soft_mul");
				}
				run("techmap -map +/nexus/dsp_map.v");
			}

			run("alumacc");
			run("opt");
			run("memory -nomap");
			run("opt_clean");
		}

		if (check_label("map_ram"))
		{
			std::string args = "";
			args += " -no-auto-huge";
			if (help_mode)
				args += " [-no-auto-block] [-no-auto-distributed]";
			else {
				if (nobram)
					args += " -no-auto-block";
				if (nolutram)
					args += " -no-auto-distributed";
			}
			run("memory_libmap -lib +/nexus/lutrams.txt -lib +/nexus/brams.txt -lib +/nexus/lrams.txt" + args, "(-no-auto-block if -nobram, -no-auto-distributed if -nolutram)");
			run("techmap -map +/nexus/lutrams_map.v -map +/nexus/brams_map.v -map +/nexus/lrams_map.v");
		}

		if (check_label("map_ffram"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates"))
		{
			if (noccu2)
				run("techmap");
			else
				run("techmap -map +/techmap.v -map +/nexus/arith_map.v");
			if (help_mode || !noiopad)
				run("iopadmap -bits -outpad OB I:O -inpad IB O:I -toutpad OBZ ~T:I:O -tinoutpad BB ~T:O:I:B A:top", "(skip if '-noiopad')");
			run("opt -fast");
			if (retime || help_mode)
				run("abc -dff -D 1", "(only if -retime)");
		}

		if (check_label("map_ffs"))
		{
			run("opt_clean");
			std::string dfflegalize_args = " -cell $_DFF_P_ 01 -cell $_DFF_PP?_ r -cell $_SDFF_PP?_ r -cell $_DLATCH_?_ x";
			if (help_mode) {
				dfflegalize_args += " [-cell $_DFFE_PP_ 01 -cell $_DFFE_PP?P_ r -cell $_SDFFE_PP?P_ r]";
			} else if (!nodffe) {
				dfflegalize_args += " -cell $_DFFE_PP_ 01 -cell $_DFFE_PP?P_ r -cell $_SDFFE_PP?P_ r";
			}
			run("dfflegalize" + dfflegalize_args, "($_*DFFE_* only if not -nodffe)");
			if ((abc9 && dff) || help_mode)
				run("zinit -all w:* t:$_DFF_?_ t:$_DFFE_??_ t:$_SDFF*", "(only if -abc9 and -dff");
			run("techmap -D NO_LUT -map +/nexus/cells_map.v");
			run("opt_expr -undriven -mux_undef");
			run("simplemap");
			run("attrmvcp -copy -attr syn_useioff");
			run("opt_clean");
		}

		if (check_label("map_luts"))
		{
			run("techmap -map +/nexus/latches_map.v");

			if (abc9) {
				std::string abc9_opts;
				if (nowidelut)
					abc9_opts += " -maxlut 4";
				std::string k = "synth_nexus.abc9.W";
				if (active_design && active_design->scratchpad.count(k))
					abc9_opts += stringf(" -W %s", active_design->scratchpad_get_string(k).c_str());
				else
					abc9_opts += stringf(" -W %s", RTLIL::constpad.at(k).c_str());
				if (nowidelut)
					abc9_opts += " -maxlut 4";
				if (dff)
					abc9_opts += " -dff";
				run("abc9" + abc9_opts);
			} else {
				std::string abc_args = " -dress";
				if (nowidelut)
					abc_args += " -lut 4";
				else
					abc_args += " -lut 4:5";
				if (dff)
					abc_args += " -dff";
				run("abc" + abc_args);
			}
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("techmap -map +/nexus/cells_map.v");

			// This is needed for Radiant, but perhaps not optimal for nextpnr...
			run("setundef -zero");

			run("hilomap -singleton -hicell VHI Z -locell VLO Z");
			run("clean");
		}

		if (check_label("check"))
		{
			run("autoname");
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
			run("blackbox =A:whitebox");
		}

		if (check_label("json"))
		{
			if (!json_file.empty() || help_mode)
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file.c_str()));
		}

		if (check_label("vm"))
		{
			if (!vm_file.empty() || help_mode)
				run(stringf("write_verilog %s", help_mode ? "<file-name>" : vm_file.c_str()));
		}
	}
} SynthNexusPass;

PRIVATE_NAMESPACE_END
