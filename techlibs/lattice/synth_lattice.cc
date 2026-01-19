/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012 Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2018 gatecat <gatecat@ds0.me>
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

struct SynthLatticePass : public ScriptPass
{
	SynthLatticePass() : ScriptPass("synth_lattice", "synthesis for Lattice FPGAs") { }

	void on_register() override
	{
		RTLIL::constpad["synth_lattice.abc9.W"] = "300";
	}

	struct DSPRule {
		int a_maxwidth;
		int b_maxwidth;
		int a_minwidth;
		int b_minwidth;
		std::string prim;
	};

	const std::vector<DSPRule> dsp_rules_nexus = {
		{36, 36, 22, 22, "$__NX_MUL36X36"},
		{36, 18, 22, 10, "$__NX_MUL36X18"},
		{18, 18, 10,  4, "$__NX_MUL18X18"},
		{18, 18,  4, 10, "$__NX_MUL18X18"},
		{ 9,  9,  4,  4, "$__NX_MUL9X9"},
	};
	const std::vector<DSPRule> dsp_rules_ecp5 = {
		{18, 18,  2,  2, "$__MUL18X18"},
	};

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_lattice [options]\n");
		log("\n");
		log("This command runs synthesis for Lattice FPGAs (excluding iCE40).\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -family <family>\n");
		log("        run synthesis for the specified Lattice architecture\n");
		log("        generate the synthesis netlist for the specified family.\n");
		log("        supported values:\n");
		log("        - ecp5: ECP5\n");
		log("        - xo2: MachXO2\n");
		log("        - xo3: MachXO3L/LF\n");
		log("        - xo3d: MachXO3D\n");
		log("        - lifcl: CrossLink-NX\n");
		log("        - lfd2nx: Certus-NX\n");
		//log("        - xo: MachXO (EXPERIMENTAL)\n");
		//log("        - pm: Platform Manager (EXPERIMENTAL)\n");
		//log("        - pm2: Platform Manager 2 (EXPERIMENTAL)\n");
		//log("        - xp: LatticeXP (EXPERIMENTAL)\n");
		//log("        - xp2: LatticeXP2 (EXPERIMENTAL)\n");
		//log("        - ecp: LatticeECP/EC (EXPERIMENTAL)\n");
		//log("        - sm: LatticeSC/M (EXPERIMENTAL)\n");
		//log("        - ecp2: LatticeECP2/M (EXPERIMENTAL)\n");
		//log("        - ecp3: LatticeECP3 (EXPERIMENTAL)\n");
		//log("        - lifmd: LIFMD (EXPERIMENTAL)\n");
		//log("        - lifmdf: LIFMDF (EXPERIMENTAL)\n");
		log("\n");
		log("    -edif <file>\n");
		log("        write the design to the specified EDIF file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -json <file>\n");
		log("        write the design to the specified JSON file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
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
		log("    -nobram\n");
		log("        do not use block RAM cells in output netlist\n");
		log("\n");
		log("    -nolutram\n");
		log("        do not use LUT RAM cells in output netlist\n");
		log("\n");
		log("    -nowidelut\n");
		log("        do not use PFU muxes to implement LUTs larger than LUT4s\n");
		log("        (by default enabled on MachXO2/XO3/XO3D)\n");
		log("\n");
		log("    -widelut\n");
		log("        force use of PFU muxes to implement LUTs larger than LUT4s\n");
		log("\n");
		log("    -asyncprld\n");
		log("        use async PRLD mode to implement ALDFF (EXPERIMENTAL)\n");
		log("\n");
		log("    -abc2\n");
		log("        run two passes of 'abc' for slightly improved logic density\n");
		log("\n");
		log("    -noabc9\n");
		log("        disable use of new ABC9 flow\n");
		log("\n");
		log("    -iopad\n");
		log("        insert IO buffers\n");
		log("        (by default enabled on Nexus FPGAs)\n");
		log("\n");
		log("    -noiopad\n");
		log("        do not insert IO buffers\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not infer DSP multipliers\n");
		log("\n");
		log("    -no-rw-check\n");
		log("        marks all recognized read ports as \"return don't-care value on\n");
		log("        read/write collision\" (same result as setting the no_rw_check\n");
		log("        attribute on all memories).\n");
		log("\n");
		log("    -cmp2softlogic\n");
		log("        implement constant comparisons in soft logic, do not involve\n");
		log("        hard carry chains\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, edif_file, json_file, family;
	bool noccu2, nodffe, nobram, nolutram, nowidelut, asyncprld, flatten, dff, retime, abc2, abc9, iopad, nodsp, no_rw_check, have_dsp;
	bool cmp2softlogic;
	string postfix, arith_map, brams_map, dsp_map, cells_map, map_ram_default, widelut_abc;
	bool is_nexus;
	std::vector<DSPRule> dsp_rules;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		edif_file = "";
		json_file = "";
		family = "";
		noccu2 = false;
		nodffe = false;
		nobram = false;
		nolutram = false;
		nowidelut = false;
		asyncprld = false;
		flatten = true;
		dff = false;
		retime = false;
		abc2 = false;
		abc9 = true;
		iopad = false;
		nodsp = false;
		no_rw_check = false;
		postfix = "";
		arith_map = "";
		brams_map = "";
		dsp_map = "";
		have_dsp = false;
		cmp2softlogic = false;
		is_nexus = false;
		map_ram_default = "";
		cells_map = "";
		widelut_abc = "4:7";
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		bool force_abc9 = false;
		bool force_widelut = false;
		bool force_iopad = false;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_opt = "-top " + args[++argidx];
				continue;
			}
			if ((args[argidx] == "-family" || args[argidx] == "-arch") && argidx+1 < args.size()) {
				family = args[++argidx];
				continue;
			}
			if (args[argidx] == "-edif" && argidx+1 < args.size()) {
				edif_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-json" && argidx+1 < args.size()) {
				json_file = args[++argidx];
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
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-asyncprld") {
				asyncprld = true;
				continue;
			}
			if (args[argidx] == "-nolutram" || /*deprecated alias*/ args[argidx] == "-nodram") {
				nolutram = true;
				continue;
			}
			if (args[argidx] == "-nowidelut" || /*deprecated alias*/ args[argidx] == "-nomux") {
				nowidelut = true;
				force_widelut = true;
				continue;
			}
			if (args[argidx] == "-widelut") {
				nowidelut = false;
				force_widelut = true;
				continue;
			}
			if (args[argidx] == "-abc2") {
				abc2 = true;
				continue;
			}
			if (args[argidx] == "-abc9") {
				// removed, ABC9 is on by default.
				force_abc9 = true;
				continue;
			}
			if (args[argidx] == "-noabc9") {
				force_abc9 = true;
				abc9 = false;
				continue;
			}
			if (args[argidx] == "-iopad") {
				iopad = true;
				force_iopad = true;
				continue;
			}
			if (args[argidx] == "-noiopad") {
				iopad = false;
				force_iopad = true;
				continue;
			}
			if (args[argidx] == "-nodsp") {
				nodsp = true;
				continue;
			}
			if (args[argidx] == "-no-rw-check") {
				no_rw_check = true;
				continue;
			}
			if (args[argidx] == "-cmp2softlogic") {
				cmp2softlogic = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (family.empty())
			log_cmd_error("Lattice family parameter must be set.\n");

		if (family == "ecp5") {
			postfix = "_ecp5";
			arith_map = "_ccu2c";
			brams_map = "_16kd";
			dsp_map = "_18x18";
			dsp_rules = dsp_rules_ecp5;
			have_dsp = true;
			cells_map = "_trellis";
		} else if (family == "xo2" ||
				family == "xo3" ||
				family == "xo3d" /* ||
				family == "pm2"*/) {
			postfix = "_" + family;
			arith_map = "_ccu2d";
			brams_map = "_8kc";
			cells_map = "_trellis";
			have_dsp = false;
			if (!force_widelut) nowidelut = true;
			if (!force_abc9) abc9 = false;
		} else if (family == "lifcl" ||
			family == "lfd2nx") {
			is_nexus = true;
			postfix = "_nexus";
			arith_map = "_nexus";
			brams_map = "_nexus";
			dsp_map = "_nexus";
			dsp_rules = dsp_rules_nexus;
			have_dsp = true;
			map_ram_default = " -no-auto-huge";
			cells_map = "_nexus";
			widelut_abc = "4:5";
			if (!force_iopad) iopad = true;
			if (!force_abc9) abc9 = false;
/*		} else if (family == "xo" ||
				family == "pm") {
		} else if (family == "xp" ||
				family == "xp2" ||
				family == "ecp" ||
				family == "sm" ||
				family == "ecp2" ||
				family == "ecp3" ||
				family == "lifmd" ||
				family == "lifmdf") {*/
		} else
			log_cmd_error("Invalid Lattice -family setting: '%s'.\n", family);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (abc9 && retime)
				log_cmd_error("-retime option not currently compatible with -abc9!\n");

		log_header(design, "Executing SYNTH_LATTICE pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		std::string no_rw_check_opt = "";
		if (no_rw_check)
			no_rw_check_opt = " -no-rw-check";
		if (help_mode)
			no_rw_check_opt = " [-no-rw-check]";

		if (check_label("begin"))
		{
			run("read_verilog -lib -specify +/lattice/cells_sim" + postfix + ".v +/lattice/cells_bb" + postfix + ".v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt));
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
			if (cmp2softlogic)
				run("techmap -map +/cmp2softlogic.v");
			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=4");
			run("opt_expr");
			run("opt_clean");

			if (help_mode) {
				run("techmap -map +/mul2dsp.v [...]", "(unless -nodsp)");
				run("techmap -map +/lattice/dsp_map" + dsp_map + ".v", "(unless -nodsp)");
			} else if (have_dsp && !nodsp) {
				for (const auto &rule : dsp_rules) {
					run(stringf("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=%d -D DSP_B_MAXWIDTH=%d -D DSP_A_MINWIDTH=%d -D DSP_B_MINWIDTH=%d -D DSP_NAME=%s",
						rule.a_maxwidth, rule.b_maxwidth, rule.a_minwidth, rule.b_minwidth, rule.prim));
					run("chtype -set $mul t:$__soft_mul");
				}
				run("techmap -map +/lattice/dsp_map" + dsp_map + ".v");
			}
			if (family == "xo3" || help_mode)
				run("booth", "(only if '-family xo3')");
			run("alumacc");
			run("opt");
			run("memory -nomap" + no_rw_check_opt);
			run("opt_clean");
		}

		if (check_label("map_ram"))
		{
			std::string args = map_ram_default;
			if (help_mode)
				args += " [-no-auto-block] [-no-auto-distributed]";
			else {
				if (nobram)
					args += " -no-auto-block";
				if (nolutram)
					args += " -no-auto-distributed";
			}
			if (!is_nexus) {
				run("memory_libmap -lib +/lattice/lutrams" + cells_map + ".txt -lib +/lattice/brams" + brams_map + ".txt" + args, "(-no-auto-block if -nobram, -no-auto-distributed if -nolutram)");
				run("techmap -map +/lattice/lutrams_map" + cells_map + ".v -map +/lattice/brams_map" + brams_map + ".v");
			} else {
				run("memory_libmap -lib +/lattice/lutrams" + cells_map + ".txt -lib +/lattice/brams" + brams_map + ".txt -lib +/lattice/lrams_nexus.txt" + args, "(-no-auto-block if -nobram, -no-auto-distributed if -nolutram)");
				run("techmap -map +/lattice/lutrams_map" + cells_map + ".v -map +/lattice/brams_map" + brams_map + ".v -map +/lattice/lrams_map_nexus.v");
			}
		}

		if (check_label("map_ffram"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine -mux_undef");
		}

		if (check_label("map_gates"))
		{
			if (noccu2)
				run("techmap");
			else
				run("techmap -map +/techmap.v -map +/lattice/arith_map" + arith_map + ".v");
			if (help_mode || iopad) {
				run("iopadmap -bits -outpad OB I:O -inpad IB O:I -toutpad OBZ ~T:I:O -tinoutpad BB ~T:O:I:B A:top", "(only if '-iopad')");
				run("attrmvcp -attr src -attr LOC t:OB %x:+[O] t:OBZ %x:+[O] t:BB %x:+[B]");
				run("attrmvcp -attr src -attr LOC -driven t:IB %x:+[I]");
			}
			run("opt -fast");
			if (retime || help_mode)
				run("abc -dff -D 1", "(only if -retime)");
		}

		if (check_label("map_ffs"))
		{
			run("opt_clean");
			if (!is_nexus) {
				std::string dfflegalize_args = " -cell $_DFF_?_ 01 -cell $_DFF_?P?_ r -cell $_SDFF_?P?_ r";
				if (help_mode) {
					dfflegalize_args += " [-cell $_DFFE_??_ 01 -cell $_DFFE_?P??_ r -cell $_SDFFE_?P??_ r]";
				} else if (!nodffe) {
					dfflegalize_args += " -cell $_DFFE_??_ 01 -cell $_DFFE_?P??_ r -cell $_SDFFE_?P??_ r";
				}
				if (help_mode) {
					dfflegalize_args += " [-cell $_ALDFF_?P_ x -cell $_ALDFFE_?P?_ x] [-cell $_DLATCH_?_ x]";
				} else if (asyncprld) {
					dfflegalize_args += " -cell $_ALDFF_?P_ x -cell $_ALDFFE_?P?_ x";
				} else {
					dfflegalize_args += " -cell $_DLATCH_?_ x";
				}
				run("dfflegalize" + dfflegalize_args, "($_ALDFF_*_ only if -asyncprld, $_DLATCH_* only if not -asyncprld, $_*DFFE_* only if not -nodffe)");
			} else {
				std::string dfflegalize_args = " -cell $_DFF_P_ 01 -cell $_DFF_PP?_ r -cell $_SDFF_PP?_ r -cell $_DLATCH_?_ x";
				if (help_mode) {
					dfflegalize_args += " [-cell $_DFFE_PP_ 01 -cell $_DFFE_PP?P_ r -cell $_SDFFE_PP?P_ r]";
				} else if (!nodffe) {
					dfflegalize_args += " -cell $_DFFE_PP_ 01 -cell $_DFFE_PP?P_ r -cell $_SDFFE_PP?P_ r";
				}
				run("dfflegalize" + dfflegalize_args, "($_*DFFE_* only if not -nodffe)");
			}
			run("opt_merge");
			if ((abc9 && dff) || help_mode)
				run("zinit -all w:* t:$_DFF_?_ t:$_DFFE_??_ t:$_SDFF*", "(only if -abc9 and -dff)");
			run("techmap -D NO_LUT -map +/lattice/cells_map" + cells_map + ".v");
			run("opt_expr -undriven -mux_undef");
			run("simplemap");
			if (!is_nexus) run("lattice_gsr");
			run("attrmvcp -copy -attr syn_useioff");
			run("opt_clean");
		}

		if (check_label("map_luts"))
		{
			if (abc2 || help_mode)
				run("abc", "      (only if -abc2)");
			if (!asyncprld || help_mode)
				run("techmap -map +/lattice/latches_map.v", "(skip if -asyncprld)");

			if (abc9) {
				std::string abc9_opts;
				if (nowidelut)
					abc9_opts += " -maxlut 4";
				std::string k = "synth_lattice.abc9.W";
				if (active_design && active_design->scratchpad.count(k))
					abc9_opts += stringf(" -W %s", active_design->scratchpad_get_string(k));
				else
					abc9_opts += stringf(" -W %s", RTLIL::constpad.at(k));
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
					abc_args += " -lut " + widelut_abc;
				if (dff)
					abc_args += " -dff";
				run("abc" + abc_args);
			}
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("techmap -map +/lattice/cells_map" + cells_map + ".v");
			if (is_nexus) {
				// This is needed for Radiant, but perhaps not optimal for nextpnr...
				run("setundef -zero");
				run("hilomap -singleton -hicell VHI Z -locell VLO Z");
			} else {
				run("opt_lut_ins -tech lattice");
			}
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

		if (check_label("edif"))
		{
			if (!edif_file.empty() || help_mode)
				run(stringf("write_edif %s", help_mode ? "<file-name>" : edif_file));
		}

		if (check_label("json"))
		{
			if (!json_file.empty() || help_mode)
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file));
		}
	}
} SynthLatticePass;

struct SynthNexusPass : public Pass
{
	SynthNexusPass() : Pass("synth_nexus", "synthesis for Nexus FPGAs") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_nexus [options]\n");
		log("\n");
		log("This command runs synthesis for Nexus FPGAs.\n");
		log("\n");
		log("This is a wrapper pass, for details take a look at help message for synth_lattice.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		args[0] = "synth_lattice";
		args.insert(args.begin()+1, std::string());
		args.insert(args.begin()+1, std::string());
		args[1] = "-family";
		args[2] = "lifcl";
		Pass::call(design, args);
	}
} SynthNexusPass;

struct SynthEcp5Pass : public Pass
{
	SynthEcp5Pass() : Pass("synth_ecp5", "synthesis for ECP5 FPGAs") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_ecp5 [options]\n");
		log("\n");
		log("This command runs synthesis for ECP5 FPGAs.\n");
		log("\n");
		log("This is a wrapper pass, for details take a look at help message for synth_lattice.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		args[0] = "synth_lattice";
		args.insert(args.begin()+1, std::string());
		args.insert(args.begin()+1, std::string());
		args[1] = "-family";
		args[2] = "ecp5";
		Pass::call(design, args);
	}
} SynthEcp5Pass;

PRIVATE_NAMESPACE_END
