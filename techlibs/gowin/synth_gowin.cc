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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SynthGowinPass : public ScriptPass
{
	SynthGowinPass() : ScriptPass("synth_gowin", "synthesis for Gowin FPGAs") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_gowin [options]\n");
		log("\n");
		log("This command runs synthesis for Gowin FPGAs. This work is experimental.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -vout <file>\n");
		log("        write the design to the specified Verilog netlist file. writing of an\n");
		log("        output file is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -json <file>\n");
		log("        write the design to the specified JSON netlist file. writing of an\n");
		log("        output file is omitted if this parameter is not specified.\n");
		log("        This disables features not yet supported by nexpnr-gowin.\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -nodffe\n");
		log("        do not use flipflops with CE in output netlist\n");
		log("\n");
		log("    -strict-gw5a-dffs\n");
		log("        use only DFFSE/DFFRE/DFFPE/DFFCE flipflops for the GW5A family\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use BRAM cells in output netlist\n");
		log("\n");
		log("    -nolutram\n");
		log("        do not use distributed RAM cells in output netlist\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis\n");
		log("\n");
		log("    -retime\n");
		log("        run 'abc' with '-dff -D 1' options\n");
		log("\n");
		log("    -nowidelut\n");
		log("        do not use muxes to implement LUTs larger than LUT4s\n");
		log("\n");
		log("    -noiopads\n");
		log("        do not emit IOB at top level ports\n");
		log("\n");
		log("    -noalu\n");
		log("        do not use ALU cells\n");
		log("\n");
		log("    -noabc9\n");
		log("        disable use of new ABC9 flow\n");
		log("\n");
		log("    -no-rw-check\n");
		log("        marks all recognized read ports as \"return don't-care value on\n");
		log("        read/write collision\" (same result as setting the no_rw_check\n");
		log("        attribute on all memories).\n");
		log("\n");
		log("    -family <family>\n");
		log("        sets the gowin family to the specified value. The default is 'gw1n'.\n");
		log("		  The following families are supported:\n");
		log("        'gw1n', 'gw2a', 'gw5a'.\n");
		log("\n");
		log("    -setundef\n");
		log("        set undriven wires and parameters to zero\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, vout_file, json_file, family;
	bool retime, nobram, nolutram, flatten, nodffe, strict_gw5a_dffs, nowidelut, abc9, noiopads, noalu, no_rw_check, setundef;

	void clear_flags() override
	{
		family = "gw1n";
		top_opt = "-auto-top";
		vout_file = "";
		json_file = "";
		retime = false;
		flatten = true;
		nobram = false;
		nodffe = false;
		strict_gw5a_dffs = false;
		nolutram = false;
		nowidelut = false;
		abc9 = true;
		noiopads = false;
		noalu = false;
		no_rw_check = false;
		setundef = false;
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
			if (args[argidx] == "-vout" && argidx+1 < args.size()) {
				vout_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-json" && argidx+1 < args.size()) {
				json_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-family" && argidx+1 < args.size()) {
				family = args[++argidx];
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
			if (args[argidx] == "-retime") {
				retime = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-nolutram" || /*deprecated*/args[argidx] == "-nodram") {
				nolutram = true;
				continue;
			}
			if (args[argidx] == "-nodffe") {
				nodffe = true;
				continue;
			}
			if (args[argidx] == "-strict-gw5a-dffs") {
				strict_gw5a_dffs = true;
				continue;
			}
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			if (args[argidx] == "-nowidelut") {
				nowidelut = true;
				continue;
			}
			if (args[argidx] == "-noalu") {
				noalu = true;
				continue;
			}
			if (args[argidx] == "-abc9") {
				// removed, ABC9 is on by default.
				continue;
			}
			if (args[argidx] == "-noabc9") {
				abc9 = false;
				continue;
			}
			if (args[argidx] == "-noiopads") {
				noiopads = true;
				continue;
			}
			if (args[argidx] == "-no-rw-check") {
				no_rw_check = true;
				continue;
			}
			if (args[argidx] == "-setundef") {
				setundef = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing SYNTH_GOWIN pass.\n");
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
			run("read_verilog -specify -lib +/gowin/cells_sim.v");
			run(stringf("read_verilog -specify -lib +/gowin/cells_xtra_%s.v", help_mode ? "<family>" : family));
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt));
		}

		if (flatten && check_label("flatten", "(unless -noflatten)"))
		{
			run("proc");
			run("flatten");
			run("tribuf -logic");
			run("deminout");
		}

		if (check_label("coarse"))
		{
			run("synth -run coarse" + no_rw_check_opt);
		}

		if (check_label("map_ram"))
		{
			std::string args = "";
			if (help_mode)
				args += " [-no-auto-block] [-no-auto-distributed]";
			else {
				if (nobram)
					args += " -no-auto-block";
				if (nolutram)
					args += " -no-auto-distributed";
			}
			run(stringf("memory_libmap -lib +/gowin/lutrams.txt -lib +/gowin/brams.txt -D %s", family) + args, "(-no-auto-block if -nobram, -no-auto-distributed if -nolutram)");
			run(stringf("techmap -map +/gowin/lutrams_map.v -map +/gowin/brams_map%s.v", family == "gw5a" ? "_gw5a" : ""));
		}

		if (check_label("map_ffram"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates"))
		{
			if (noalu) {
				run("techmap -map +/techmap.v");
			} else {
				run("techmap -map +/techmap.v -map +/gowin/arith_map.v");
			}
			run("opt -fast");
			if (retime || help_mode)
				run("abc -dff -D 1", "(only if -retime)");
			if (!noiopads || help_mode)
				run("iopadmap -bits -inpad IBUF O:I -outpad OBUF I:O "
					"-toutpad TBUF ~OEN:I:O -tinoutpad IOBUF ~OEN:O:I:IO", "(unless -noiopads)");
		}

		if (check_label("map_ffs"))
		{
			run("opt_clean");
			if (family == "gw5a") {
				if (strict_gw5a_dffs) {
					run("dfflegalize -cell $_SDFFE_PP?P_ r -cell $_DFFE_PP?P_ r");
				} else {
					run("dfflegalize -cell $_DFF_?_ 0 -cell $_SDFFE_PP?P_ r -cell $_DFFE_PP?P_ r");
				}
			} else {
				if (nodffe)
					run("dfflegalize -cell $_DFF_?_ 0 -cell $_SDFF_?P?_ r -cell $_DFF_?P?_ r");
				else
					run("dfflegalize -cell $_DFF_?_ 0 -cell $_DFFE_?P_ 0 -cell $_SDFF_?P?_ r -cell $_SDFFE_?P?P_ r -cell $_DFF_?P?_ r -cell $_DFFE_?P?P_ r");
			}
			run("techmap -map +/gowin/cells_map.v");
			run("opt_expr -mux_undef");
			run("simplemap");
		}

		if (check_label("map_luts"))
		{
			if (nowidelut && abc9) {
				run("read_verilog -icells -lib -specify +/abc9_model.v");
				run("abc9 -maxlut 4 -W 500");
			} else if (nowidelut && !abc9) {
				run("abc -lut 4");
			} else if (!nowidelut && abc9) {
				run("read_verilog -icells -lib -specify +/abc9_model.v");
				run("abc9 -maxlut 8 -W 500");
			} else if (!nowidelut && !abc9) {
				run("abc -lut 4:8");
			}
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("techmap -map +/gowin/cells_map.v");
			run("opt_lut_ins -tech gowin");
			if (setundef || help_mode)
				run("setundef -undriven -params -zero", "(only if -setundef)");
			run("hilomap -singleton -hicell VCC V -locell GND G");
			if (!vout_file.empty() || help_mode) // vendor output requires 1-bit wires
				run("splitnets -ports", "(only if -vout)");
			run("clean");
			run("autoname");
		}

		if (check_label("check"))
		{
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
			run("blackbox =A:whitebox");
		}

		if (check_label("vout"))
		{
			if (!vout_file.empty() || help_mode)
				 run(stringf("write_verilog -simple-lhs -decimal -attr2comment -defparam -renameprefix gen %s",
						help_mode ? "<file-name>" : vout_file.c_str()));
			if (!json_file.empty() || help_mode)
				 run(stringf("write_json %s",
						help_mode ? "<file-name>" : json_file.c_str()));
		}
	}
} SynthGowinPass;

PRIVATE_NAMESPACE_END
