/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Wolf <claire@symbioticeda.com>
 *  Copyright (C) 2019  Dan Ravensloft <dan.ravensloft@gmail.com>
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

struct SynthIntelLEPass : public ScriptPass {
	SynthIntelLEPass() : ScriptPass("synth_intel_le", "synthesis for LE-based Intel (Altera) FPGAs.") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_intel_le [options]\n");
		log("\n");
		log("This command runs synthesis for LE-based Intel FPGAs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -family <family>\n");
		log("        target one of:\n");
		log("        \"cycloneiv\"    - Cyclone IV (default)\n");
		log("        \"cycloneive\"    - Cyclone IV E \n");
		log("\n");
		log("    -vqm <file>\n");
		log("        write the design to the specified Verilog Quartus Mapping File. Writing of an\n");
		log("        output file is omitted if this parameter is not specified. Implies -quartus.\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design before synthesis; useful for per-module area statistics\n");
		log("\n");
		log("    -quartus\n");
		log("        output a netlist using Quartus cells instead of MISTRAL_* cells\n");
		log("\n");
		log("    -dff\n");
		log("        pass DFFs to ABC to perform sequential logic optimisations (EXPERIMENTAL)\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -nobram\n");
		log("        do not use block RAM cells in output netlist\n");
		log("\n");
		log("    -nodsp\n");
		log("        do not map multipliers to MISTRAL_MUL cells\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, family_opt, bram_type, vout_file;
	bool flatten, quartus, nobram, dff, nodsp;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		family_opt = "cycloneiv";
		bram_type = "m9k";
		vout_file = "";
		flatten = true;
		quartus = false;
		nobram = false;
		dff = false;
		nodsp = false;
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
			if (args[argidx] == "-vqm" && argidx + 1 < args.size()) {
				quartus = true;
				vout_file = args[++argidx];
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
			if (args[argidx] == "-quartus") {
				quartus = true;
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
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		if (family_opt == "cycloneiv" or family_opt == "cycloneive") {
			bram_type = "m9k";
		} else {
			log_cmd_error("Invalid family specified: '%s'\n", family_opt.c_str());
		}

		log_header(design, "Executing SYNTH_intel_le pass.\n");
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
			if (family_opt == "cycloneiv" or family_opt == "cycloneive")
				run(stringf("read_verilog -sv -lib +/intel_le/cycloneiv/cells_sim.v"));
			run(stringf("read_verilog -specify -lib -D %s +/intel_le/common/le_sim.v", family_opt.c_str()));
			run(stringf("read_verilog -specify -lib -D %s +/intel_le/common/dff_sim.v", family_opt.c_str()));
			run(stringf("read_verilog -specify -lib -D %s +/intel_le/common/mem_sim.v", family_opt.c_str()));
			run(stringf("read_verilog -specify -lib -D %s -icells +/intel_le/common/abc9_model.v", family_opt.c_str()));

			// Misc and common cells
			run("read_verilog -lib +/intel/common/altpll_bb.v");
			run("read_verilog -lib +/intel_le/common/megafunction_bb.v");
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
			run("techmap -map +/cmp2lut.v -D LUT_WIDTH=4");
			run("opt_expr");
			run("opt_clean");
			run("alumacc");
			run("techmap -map +/intel_le/common/arith_le_map.v");
			run("opt");
			run("memory -nomap");
			run("opt_clean");
		}

		if (!nobram && check_label("map_bram", "(skip if -nobram)")) {
			run(stringf("memory_bram -rules +/intel_le/common/bram_%s.txt", bram_type.c_str()));
			if (help_mode || bram_type != "m9k")
				run(stringf("techmap -map +/intel_le/common/bram_%s_map.v", bram_type.c_str()));
		}

		if (check_label("map_ffram")) {
			run("memory_map");
			run("opt -full");
		}

		if (check_label("map_ffs")) {
			run("techmap");
			run("dfflegalize -cell $_DFFE_PN0P_ 0 -cell $_SDFFCE_PP0P_ 0");
			run("techmap -map +/intel_le/common/dff_map.v");
			run("opt -full -undriven -mux_undef");
			run("clean -purge");
		}

		if (check_label("map_luts")) {
			run("techmap -map +/intel_le/common/abc9_map.v");
			run(stringf("abc9 %s -maxlut 4 -W 400", help_mode ? "[-dff]" : dff ? "-dff" : ""));
			run("techmap -map +/intel_le/common/abc9_unmap.v");
			run("techmap -map +/intel_le/common/le_map.v");
			run("opt -fast");
			run("autoname");
			run("clean");
		}

		if (check_label("check")) {
			run("hierarchy -check");
			run("stat");
			run("check");
		}

		if (check_label("quartus")) {
			if (quartus || help_mode) {
				// Quartus ICEs if you have a wire which has `[]` in its name,
				// which Yosys produces when building memories out of flops.
				run("rename -hide w:*[* w:*]*");
				// VQM mode does not support 'x, so replace those with zero.
				run("setundef -zero");
				// VQM mode does not support multi-bit constant assignments
				// (e.g. 2'b00 is an error), so as a workaround use references
				// to constant driver cells, which Quartus accepts.
				run("hilomap -singleton -hicell __MISTRAL_VCC Q -locell __MISTRAL_GND Q");
				// Rename from Yosys-internal MISTRAL_* cells to Quartus cells.
				run(stringf("techmap -D %s -map +/intel_le/common/quartus_rename.v", family_opt.c_str()));
			}
		}

		if (check_label("vqm")) {
			if (!vout_file.empty() || help_mode) {
				run(stringf("write_verilog -attr2comment -defparam -nohex -decimal %s", help_mode ? "<file-name>" : vout_file.c_str()));
			}
		}
	}
} SynthIntelLEPass;

PRIVATE_NAMESPACE_END
