/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

	void help() YS_OVERRIDE
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
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -nodffe\n");
		log("        do not use flipflops with CE in output netlist\n");
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
		//log("\n");
		//log("    -abc9\n");
		//log("        use new ABC9 flow (EXPERIMENTAL)\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, vout_file;
	bool retime, nobram, nolutram, flatten, nodffe, nowidelut, abc9, noiopads;

	void clear_flags() YS_OVERRIDE
	{
		top_opt = "-auto-top";
		vout_file = "";
		retime = false;
		flatten = true;
		nobram = false;
		nodffe = false;
		nolutram = false;
		nowidelut = false;
		abc9 = false;
		noiopads = false;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			if (args[argidx] == "-nowidelut") {
				nowidelut = true;
				continue;
			}
			//if (args[argidx] == "-abc9") {
			//	abc9 = true;
			//	continue;
			//}
			if (args[argidx] == "-noiopads") {
				noiopads = true;
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

	void script() YS_OVERRIDE
	{
		if (check_label("begin"))
		{
			run("read_verilog -lib +/gowin/cells_sim.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
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
			run("synth -run coarse");
		}

		if (!nobram && check_label("map_bram", "(skip if -nobram)"))
		{
			run("memory_bram -rules +/gowin/brams.txt");
			run("techmap -map +/gowin/brams_map.v");
		}

		if (!nolutram && check_label("map_lutram", "(skip if -nolutram)"))
		{
			run("memory_bram -rules +/gowin/lutrams.txt");
			run("techmap -map +/gowin/lutrams_map.v");
			run("determine_init");
		}

		if (check_label("map_ffram"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates"))
		{
			run("techmap -map +/techmap.v -map +/gowin/arith_map.v");
			run("opt -fast");
			if (retime || help_mode)
				run("abc -dff -D 1", "(only if -retime)");
			run("splitnets");
		}

		if (check_label("map_ffs"))
		{
			run("dffsr2dff");
			run("dff2dffs -match-init");
			run("opt_clean");
			if (!nodffe)
				run("dff2dffe -direct-match $_DFF_* -direct-match $__DFFS_*");
			run("techmap -map +/gowin/cells_map.v");
			run("opt_expr -mux_undef");
			run("simplemap");
		}

		if (check_label("map_luts"))
		{
			/*if (nowidelut && abc9) {
				run("abc9 -lut 4");
			} else*/ if (nowidelut && !abc9) {
				run("abc -lut 4");
			} else /*if (!nowidelut && abc9) {
				run("abc9 -lut 4:8");
			} else*/ if (!nowidelut && !abc9) {
				run("abc -lut 4:8");
			}
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("techmap -map +/gowin/cells_map.v");
			run("opt_lut_ins -tech gowin");
			run("setundef -undriven -params -zero");
			run("hilomap -singleton -hicell VCC V -locell GND G");
			if (!noiopads || help_mode)
				run("iopadmap -bits -inpad IBUF O:I -outpad OBUF I:O "
					"-toutpad TBUF OEN:I:O -tinoutpad IOBUF OEN:O:I:IO", "(unless -noiopads)");
			run("clean");
		}

		if (check_label("check"))
		{
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
		}

		if (check_label("vout"))
		{
			if (!vout_file.empty() || help_mode)
				 run(stringf("write_verilog -decimal -attr2comment -defparam -renameprefix gen %s",
						help_mode ? "<file-name>" : vout_file.c_str()));
		}
	}
} SynthGowinPass;

PRIVATE_NAMESPACE_END
