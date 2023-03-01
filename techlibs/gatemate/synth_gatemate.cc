/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Cologne Chip AG <support@colognechip.com>
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

struct SynthGateMatePass : public ScriptPass
{
	SynthGateMatePass() : ScriptPass("synth_gatemate", "synthesis for Cologne Chip GateMate FPGAs") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_gatemate [options]\n");
		log("\n");
		log("This command runs synthesis for Cologne Chip AG GateMate FPGAs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module.\n");
		log("\n");
		log("    -vlog <file>\n");
		log("        write the design to the specified verilog file. Writing of an output\n");
		log("        file is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -json <file>\n");
		log("        write the design to the specified JSON file. Writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). An empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis.\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use CC_BRAM_20K or CC_BRAM_40K cells in output netlist.\n");
		log("\n");
		log("    -noaddf\n");
		log("        do not use CC_ADDF full adder cells in output netlist.\n");
		log("\n");
		log("    -nomult\n");
		log("        do not use CC_MULT multiplier cells in output netlist.\n");
		log("\n");
		log("    -nomx8, -nomx4\n");
		log("        do not use CC_MX{8,4} multiplexer cells in output netlist.\n");
		log("\n");
		log("    -luttree\n");
		log("        use new LUT tree mapping approach (EXPERIMENTAL).\n");
		log("\n");
		log("    -dff\n");
		log("        run 'abc' with -dff option\n");
		log("\n");
		log("    -retime\n");
		log("        run 'abc' with '-dff -D 1' options\n");
		log("\n");
		log("    -noiopad\n");
		log("        disable I/O buffer insertion (useful for hierarchical or \n");
		log("        out-of-context flows).\n");
		log("\n");
		log("    -noclkbuf\n");
		log("        disable automatic clock buffer insertion.\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, vlog_file, json_file;
	bool noflatten, nobram, noaddf, nomult, nomx4, nomx8, luttree, dff, retime, noiopad, noclkbuf;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		vlog_file = "";
		json_file = "";
		noflatten = false;
		nobram = false;
		noaddf = false;
		nomult = false;
		nomx4 = false;
		nomx8 = false;
		luttree = false;
		dff = false;
		retime = false;
		noiopad = false;
		noclkbuf = false;
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
			if (args[argidx] == "-vlog" && argidx+1 < args.size()) {
				vlog_file = args[++argidx];
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
			if (args[argidx] == "-noflatten") {
				noflatten = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-noaddf") {
				noaddf = true;
				continue;
			}
			if (args[argidx] == "-nomult") {
				nomult = true;
				continue;
			}
			if (args[argidx] == "-nomx4") {
				nomx4 = true;
				continue;
			}
			if (args[argidx] == "-nomx8") {
				nomx8 = true;
				continue;
			}
			if (args[argidx] == "-luttree") {
				luttree = true;
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
			if (args[argidx] == "-noiopad") {
				noiopad = true;
				continue;
			}
			if (args[argidx] == "-noclkbuf") {
				noclkbuf = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection()) {
			log_cmd_error("This command only operates on fully selected designs!\n");
		}

		log_header(design, "Executing SYNTH_GATEMATE pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (check_label("begin"))
		{
			run("read_verilog -lib -specify +/gatemate/cells_sim.v +/gatemate/cells_bb.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (check_label("prepare"))
		{
			run("proc");
			if (!noflatten) {
				run("flatten");
			}
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
			run("muxpack");
			run("share");
			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=4");
			run("opt_expr");
			run("opt_clean");
		}

		if (check_label("map_mult", "(skip if '-nomult')") && !nomult)
		{
			run("techmap -map +/gatemate/mul_map.v");
		}

		if (check_label("coarse"))
		{
			run("alumacc");
			run("opt");
			run("memory -nomap");
			run("opt_clean");
		}

		if (check_label("map_bram", "(skip if '-nobram')") && !nobram)
		{
			run("memory_libmap -lib +/gatemate/brams.txt");
			run("techmap -map +/gatemate/brams_map.v");
		}

		if (check_label("map_ffram"))
		{
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates"))
		{
			std::string techmap_args = "";
			if (!noaddf) {
				techmap_args += " -map +/gatemate/arith_map.v";
			}
			run("techmap -map +/techmap.v " + techmap_args);
			run("opt -fast");
			if (retime) {
				run("abc -dff -D 1", "(only if -retime)");
			}
		}

		if (check_label("map_io", "(skip if '-noiopad')") && !noiopad)
		{
			run("iopadmap -bits "
				"-inpad CC_IBUF Y:I "
				"-outpad CC_OBUF A:O "
				"-toutpad CC_TOBUF ~T:A:O "
				"-tinoutpad CC_IOBUF ~T:Y:A:IO"
			);
			run("clean");
		}

		if (check_label("map_regs"))
		{
			run("opt_clean");
			run("dfflegalize -cell $_DFFE_????_ 01 -cell $_DLATCH_???_ 01");
			run("techmap -map +/gatemate/reg_map.v");
			run("opt_expr -mux_undef");
			run("simplemap");
			run("opt_clean");
		}

		if (check_label("map_muxs"))
		{
			std::string muxcover_args;
			if (!nomx4) {
				muxcover_args += stringf(" -mux4");
			}
			if (!nomx8) {
				muxcover_args += stringf(" -mux8");
			}
			run("muxcover " + muxcover_args);
			run("opt -full");
			run("techmap -map +/gatemate/mux_map.v");
		}

		if (check_label("map_luts"))
		{
			if (luttree || help_mode) {
				std::string abc_args = " -genlib +/gatemate/lut_tree_cells.genlib";
				if (dff) {
					abc_args += " -dff";
				}
				run("abc " + abc_args, "(with -luttree)");
				run("techmap -map +/gatemate/lut_tree_map.v", "(with -luttree)");
				run("gatemate_foldinv", "(with -luttree)");
				run("techmap -map +/gatemate/inv_map.v", "(with -luttree)");
			}
			if (!luttree || help_mode) {
				std::string abc_args = " -dress -lut 4";
				if (dff) {
					abc_args += " -dff";
				}
				run("abc " + abc_args, "(without -luttree)");
			}
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("techmap -map +/gatemate/lut_map.v");
			run("clean");
		}

		if (check_label("map_bufg", "(skip if '-noclkbuf')") && !noclkbuf)
		{
			run("clkbufmap -buf CC_BUFG O:I");
			run("clean");
		}

		if (check_label("check"))
		{
			run("hierarchy -check");
			run("stat -width");
			run("check -noinit");
			run("blackbox =A:whitebox");
		}

		if (check_label("vlog"))
		{
			run("opt_clean -purge");
			if (!vlog_file.empty() || help_mode) {
				run(stringf("write_verilog -noattr %s", help_mode ? "<file-name>" : vlog_file.c_str()));
			}
		}

		if (check_label("json"))
		{
			if (!json_file.empty() || help_mode) {
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file.c_str()));
			}
		}
	}
} SynthGateMatePass;

PRIVATE_NAMESPACE_END
