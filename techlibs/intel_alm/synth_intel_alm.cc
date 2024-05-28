/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2019  Hannah Ravensloft <dan.ravensloft@gmail.com>
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

struct SynthIntelALMPass : public ScriptPass {
	SynthIntelALMPass() : ScriptPass("synth_intel_alm", "synthesis for ALM-based Intel (Altera) FPGAs.") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_intel_alm [options]\n");
		log("\n");
		log("This command runs synthesis for ALM-based Intel FPGAs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -family <family>\n");
		log("        target one of:\n");
		log("        \"cyclonev\"    - Cyclone V (default)\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis; useful for per-module area\n");
		log("        statistics\n");
		log("\n");
		log("    -dff\n");
		log("        pass DFFs to ABC to perform sequential logic optimisations\n");
		log("        (EXPERIMENTAL)\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -nolutram\n");
		log("        do not use LUT RAM cells in output netlist\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use block RAM cells in output netlist\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not map multipliers to MISTRAL_MUL cells\n");
		log("\n");
		log("    -noiopad\n");
		log("        do not instantiate IO buffers\n");
		log("\n");
		log("    -noclkbuf\n");
		log("        do not insert global clock buffers\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, family_opt, bram_type;
	bool flatten, nolutram, nobram, dff, nodsp, noiopad, noclkbuf;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		family_opt = "cyclonev";
		bram_type = "m10k";
		flatten = true;
		nolutram = false;
		nobram = false;
		dff = false;
		nodsp = false;
		noiopad = false;
		noclkbuf = false;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-family" && argidx + 1 < args.size()) {
				family_opt = args[++argidx];
				continue;
			}
			if (args[argidx] == "-top" && argidx + 1 < args.size()) {
				top_opt = "-top " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx + 1 < args.size()) {
				size_t pos = args[argidx + 1].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[++argidx].substr(0, pos);
				run_to = args[argidx].substr(pos + 1);
				continue;
			}
			if (args[argidx] == "-nolutram") {
				nolutram = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-nodsp") {
				nodsp = true;
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

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing SYNTH_INTEL_ALM pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (help_mode) {
			family_opt = "<family>";
			bram_type = "<bram_type>";
		}

		if (check_label("begin")) {
			if (family_opt == "cyclonev")
				run(stringf("read_verilog -sv -lib +/intel_alm/%s/cells_sim.v", family_opt.c_str()));
			run(stringf("read_verilog -specify -lib -D %s +/intel_alm/common/alm_sim.v", family_opt.c_str()));
			run(stringf("read_verilog -specify -lib -D %s +/intel_alm/common/dff_sim.v", family_opt.c_str()));
			run(stringf("read_verilog -specify -lib -D %s +/intel_alm/common/dsp_sim.v", family_opt.c_str()));
			run(stringf("read_verilog -specify -lib -D %s +/intel_alm/common/mem_sim.v", family_opt.c_str()));
			run(stringf("read_verilog -specify -lib -D %s +/intel_alm/common/misc_sim.v", family_opt.c_str()));
			run(stringf("read_verilog -specify -lib -D %s -icells +/intel_alm/common/abc9_model.v", family_opt.c_str()));
			// Misc and common cells
			run("read_verilog -lib +/intel/common/altpll_bb.v");
			run("read_verilog -lib +/intel_alm/common/megafunction_bb.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		}

		if (check_label("coarse")) {
			run("proc");
			if (flatten || help_mode)
				run("flatten", "(skip if -noflatten)");
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
			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=6");
			run("opt_expr");
			run("opt_clean");
			if (help_mode) {
				run("techmap -map +/mul2dsp.v [...]", "(unless -nodsp)");
			} else if (!nodsp) {
				run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=27 -D DSP_B_MAXWIDTH=27  -D DSP_A_MINWIDTH=19 -D DSP_B_MINWIDTH=4 -D DSP_NAME=__MUL27X27");
				run("chtype -set $mul t:$__soft_mul");
				run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=27 -D DSP_B_MAXWIDTH=27  -D DSP_A_MINWIDTH=4 -D DSP_B_MINWIDTH=19 -D DSP_NAME=__MUL27X27");
				run("chtype -set $mul t:$__soft_mul");
				run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18  -D DSP_A_MINWIDTH=10 -D DSP_B_MINWIDTH=4 -D DSP_NAME=__MUL18X18");
				run("chtype -set $mul t:$__soft_mul");
				run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=18 -D DSP_B_MAXWIDTH=18  -D DSP_A_MINWIDTH=4 -D DSP_B_MINWIDTH=10 -D DSP_NAME=__MUL18X18");
				run("chtype -set $mul t:$__soft_mul");
				run("techmap -map +/mul2dsp.v -D DSP_A_MAXWIDTH=9 -D DSP_B_MAXWIDTH=9  -D DSP_A_MINWIDTH=4 -D DSP_B_MINWIDTH=4 -D DSP_NAME=__MUL9X9");
				run("chtype -set $mul t:$__soft_mul");
			}
			run("alumacc");
			if (!noiopad)
				run("iopadmap -bits -outpad MISTRAL_OB I:PAD -inpad MISTRAL_IB O:PAD -toutpad MISTRAL_IO OE:O:PAD -tinoutpad MISTRAL_IO OE:O:I:PAD A:top", "(unless -noiopad)");
			run("techmap -map +/intel_alm/common/arith_alm_map.v -map +/intel_alm/common/dsp_map.v");
			run("opt");
			run("memory -nomap");
			run("opt_clean");
		}

		if (!nobram && check_label("map_bram", "(skip if -nobram)")) {
			run(stringf("memory_bram -rules +/intel_alm/common/bram_%s.txt", bram_type.c_str()));
			run(stringf("techmap -map +/intel_alm/common/bram_%s_map.v", bram_type.c_str()));
		}

		if (!nolutram && check_label("map_lutram", "(skip if -nolutram)")) {
			run("memory_bram -rules +/intel_alm/common/lutram_mlab.txt", "(for Cyclone V)");
		}

		if (check_label("map_ffram")) {
			run("memory_map");
			run("opt -full");
		}

		if (check_label("map_ffs")) {
			run("techmap");
			run("dfflegalize -cell $_DFFE_PN0P_ 0 -cell $_SDFFCE_PP0P_ 0");
			run("techmap -map +/intel_alm/common/dff_map.v");
			run("opt -full -undriven -mux_undef");
			run("clean -purge");
			if (!noclkbuf)
				run("clkbufmap -buf MISTRAL_CLKBUF Q:A", "(unless -noclkbuf)");
		}

		if (check_label("map_luts")) {
			run("techmap -map +/intel_alm/common/abc9_map.v");
			run(stringf("abc9 %s -maxlut 6 -W 600", help_mode ? "[-dff]" : dff ? "-dff" : ""));
			run("techmap -map +/intel_alm/common/abc9_unmap.v");
			run("techmap -map +/intel_alm/common/alm_map.v");
			run("opt -fast");
			run("autoname");
			run("clean");
		}

		if (check_label("check")) {
			run("hierarchy -check");
			run("stat");
			run("check");
			run("blackbox =A:whitebox");
		}
	}
} SynthIntelALMPass;

PRIVATE_NAMESPACE_END
