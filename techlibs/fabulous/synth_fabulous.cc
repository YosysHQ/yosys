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

struct SynthPass : public ScriptPass
{
	SynthPass() : ScriptPass("synth_fabulous", "FABulous synthesis script") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_fabulous [options]\n");
		log("\n");
		log("This command runs synthesis for FPGA fabrics generated with FABulous. This command does not operate\n");
		log("on partly selected designs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -auto-top\n");
		log("        automatically determine the top of the design hierarchy\n");
		log("\n");
		log("    -blif <file>\n");
		log("        write the design to the specified BLIF file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -edif <file>\n");
		log("        write the design to the specified EDIF file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -json <file>\n");
		log("        write the design to the specified JSON file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -lut <k>\n");
		log("        perform synthesis for a k-LUT architecture (default 4).\n");
		log("\n");
		log("    -vpr\n");
		log("        perform synthesis for the FABulous VPR flow (using slightly different techmapping).\n");
		log("\n");
		log("    -plib <primitive_library.v>\n");
		log("        use the specified Verilog file as a primitive library.\n");
		log("\n");
		log("    -extra-plib <primitive_library.v>\n");
		log("        use the specified Verilog file for extra primitives (can be specified multiple\n");
		log("        times).\n");
		log("\n");
		log("    -extra-map <techamp.v>\n");
		log("        use the specified Verilog file for extra techmap rules (can be specified multiple\n");
		log("        times).\n");
		log("\n");
		log("    -encfile <file>\n");
		log("        passed to 'fsm_recode' via 'fsm'\n");
		log("\n");
		log("    -nofsm\n");
		log("        do not run FSM optimization\n");
		log("\n");
		log("    -noalumacc\n");
		log("        do not run 'alumacc' pass. i.e. keep arithmetic operators in\n");
		log("        their direct form ($add, $sub, etc.).\n");
		log("\n");
		log("    -carry <none|ha>\n");
		log("        carry mapping style (none, half-adders, ...) default=none\n");
		log("\n");
		log("    -noregfile\n");
		log("        do not map register files\n");
		log("\n");
		log("    -iopad\n");
		log("        enable automatic insertion of IO buffers (otherwise a wrapper\n");
		log("        with manually inserted and constrained IO should be used.)\n");
		log("\n");
		log("    -complex-dff\n");
		log("        enable support for FFs with enable and synchronous SR (must also be\n");
		log("        supported by the target fabric.)\n");
		log("\n");
		log("    -noflatten\n");
		log("        do not flatten design after elaboration\n");
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
		log("    -no-rw-check\n");
		log("        marks all recognized read ports as \"return don't-care value on\n");
		log("        read/write collision\" (same result as setting the no_rw_check\n");
		log("        attribute on all memories).\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_module, json_file, blif_file, plib, fsm_opts, memory_opts, carry_mode;
	std::vector<string> extra_plib, extra_map;

	bool autotop, forvpr, noalumacc, nofsm, noshare, noregfile, iopad, complexdff, flatten;
	int lut;

	void clear_flags() override
	{
		top_module.clear();
		plib.clear();
		autotop = false;
		lut = 4;
		forvpr = false;
		noalumacc = false;
		nofsm = false;
		noshare = false;
		iopad = false;
		complexdff = false;
		carry_mode = "none";
		flatten = true;
		json_file = "";
		blif_file = "";
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module = args[++argidx];
				continue;
			}
			if (args[argidx] == "-json" && argidx+1 < args.size()) {
				json_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-blif" && argidx+1 < args.size()) {
				blif_file = args[++argidx];
				continue;
			}
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos) {
					run_from = args[++argidx];
					run_to = args[argidx];
				} else {
					run_from = args[++argidx].substr(0, pos);
					run_to = args[argidx].substr(pos+1);
				}
				continue;
			}
			if (args[argidx] == "-vpr") {
				forvpr = true;
				continue;
			}
			if (args[argidx] == "-auto-top") {
				autotop = true;
				continue;
			}
			if (args[argidx] == "-lut") {
				lut = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-plib" && argidx+1 < args.size()) {
				plib = args[++argidx];
				continue;
			}
			if (args[argidx] == "-extra-plib" && argidx+1 < args.size()) {
				extra_plib.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-extra-map" && argidx+1 < args.size()) {
				extra_map.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-nofsm") {
				nofsm = true;
				continue;
			}
			if (args[argidx] == "-noalumacc") {
				noalumacc = true;
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
			if (args[argidx] == "-no-rw-check") {
				memory_opts += " -no-rw-check";
				continue;
			}
			if (args[argidx] == "-noregfile") {
				noregfile = true;
				continue;
			}
			if (args[argidx] == "-iopad") {
				iopad = true;
				continue;
			}
			if (args[argidx] == "-complex-dff") {
				complexdff = true;
				continue;
			}
			if (args[argidx] == "-carry") {
				carry_mode = args[++argidx];
				if (carry_mode != "none" && carry_mode != "ha")
					log_cmd_error("Unsupported carry style: %s\n", carry_mode.c_str());
				continue;
			}
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing SYNTH_FABULOUS pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (plib.empty())
			run(stringf("read_verilog %s -lib +/fabulous/prims.v", complexdff ? "-DCOMPLEX_DFF" : ""));
		else
			run("read_verilog -lib " + plib);

		if (help_mode) {
			run("read_verilog -lib <extra_plib.v>", "(for each -extra-plib)");
		} else for (auto lib : extra_plib) {
			run("read_verilog -lib " + lib);
		}

		if (check_label("begin")) {
			if (top_module.empty()) {
				if (autotop)
					run("hierarchy -check -auto-top");
				else
					run("hierarchy -check");
			} else
				run(stringf("hierarchy -check -top %s", top_module.c_str()));
			run("proc");
		}


		if (check_label("flatten", "(unless -noflatten)"))
		{
			if (flatten) {
				run("flatten");
				run("tribuf -logic");
				run("deminout");
			}
		}

		if (check_label("coarse")) {
	 		run("tribuf -logic");
			run("deminout");

			// synth pass
			run("opt_expr");
			run("opt_clean");
			run("check");
			run("opt -nodffe -nosdff");
			if (!nofsm)
				run("fsm" + fsm_opts, "      (unless -nofsm)");
			run("opt");
			run("wreduce");
			run("peepopt");
			run("opt_clean");
			if (help_mode)
				run("techmap -map +/cmp2lut.v -map +/cmp2lcu.v", " (if -lut)");
			else if (lut)
				run(stringf("techmap -map +/cmp2lut.v -map +/cmp2lcu.v -D LUT_WIDTH=%d", lut));
			if (!noalumacc)
				run("alumacc", "  (unless -noalumacc)");
			if (!noshare)
				run("share", "    (unless -noshare)");
			run("opt");
			run("memory -nomap" + memory_opts);
			run("opt_clean");
		}

		if (check_label("map_ram", "(unless -noregfile)")) {
			// RegFile extraction
			if (!noregfile) {
				run("memory_libmap -lib +/fabulous/ram_regfile.txt");
				run("techmap -map +/fabulous/regfile_map.v");
			}
		}

		if (check_label("map_ffram")) {
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_gates")) {
			run("opt -full");
			run(stringf("techmap -map +/techmap.v -map +/fabulous/arith_map.v -D ARITH_%s",
				help_mode ? "<carry>" : carry_mode.c_str()));
			run("opt -fast");
		}

		if (check_label("map_iopad", "(if -iopad)")) {
			if (iopad || help_mode) {
				run("opt -full");
				run("iopadmap -bits -outpad $__FABULOUS_OBUF I:PAD -inpad $__FABULOUS_IBUF O:PAD "
					"-toutpad IO_1_bidirectional_frame_config_pass ~T:I:PAD "
					"-tinoutpad IO_1_bidirectional_frame_config_pass ~T:O:I:PAD A:top", "(skip if '-noiopad')");
				run("techmap -map +/fabulous/io_map.v");
			}
		}


		if (check_label("map_ffs")) {
			if (complexdff) {
				run("dfflegalize -cell $_DFF_P_ 0 -cell $_SDFF_PP?_ 0 -cell $_SDFFCE_PP?P_ 0 -cell $_DLATCH_?_ x", "with -complex-dff");
			} else {
				run("dfflegalize -cell $_DFF_P_ 0 -cell $_DLATCH_?_ x", "without -complex-dff");
			}
			run("techmap -map +/fabulous/latches_map.v");
			run("techmap -map +/fabulous/ff_map.v");
			if (help_mode) {
				run("techmap -map <extra_map.v>...", "(for each -extra-map)");
			} else if (!extra_map.empty()) {
				std::string map_str = "techmap";
				for (auto map : extra_map)
					map_str += stringf(" -map %s", map.c_str());
				run(map_str);
			}
			run("clean");
		}

		if (check_label("map_luts")) {
			run(stringf("abc -lut %d -dress", lut));
			run("clean");
		}

		if (check_label("map_cells")) {
			if (!forvpr)
				run(stringf("techmap -D LUT_K=%d -map +/fabulous/cells_map.v", lut));
			run("clean");
		}
		if (check_label("check")) {
			run("hierarchy -check");
			run("stat");
		}

		if (check_label("blif"))
		{
			if (!blif_file.empty() || help_mode)
			{
				run("opt_clean -purge");
				run(stringf("write_blif -attr -cname -conn -param %s",
						help_mode ? "<file-name>" : blif_file.c_str()));
			}
		}

		if (check_label("json"))
		{
			if (!json_file.empty() || help_mode)
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file.c_str()));
		}
	}
} SynthPass;

PRIVATE_NAMESPACE_END
