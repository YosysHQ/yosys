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
	SynthPass() : ScriptPass("synth_fabulous", "FABulous synthesis script") {}

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
		log("    -json <file>\n");
		log("        write the design to the specified JSON file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -lut <k>\n");
		log("        perform synthesis for a k-LUT architecture (default 4).\n");
		log("\n");
		log("    -ff <cell_type_pattern> <init_values>\n");
		log("        convert FFs to cell types via dfflegalize (can be specified multiple times).\n");
		log("\n");
		log("    -cells-map <cells_map>\n");
		log("        map luts to corresponding cells.\n");
		log("\n");
		log("    -arith-map <arith_map>\n");
		log("        mapping file for arithmetic operations.\n");
		log("\n");
		log("    -clkbuf-map <clkbuf_map>\n");
		log("        insert clock buffers using clkbufmap and map to the specified Verilog file.\n");
		log("\n");
		log("    -multiplier-map <multiplier_map> <a_max> <b_max> <a_min> <b_min> <y_min>\n");
		log("        convert multiplications to multiplier primitives and map to the specified Verilog file.\n");
		log("\n");
		log("    -extra-plib <primitive_library.v>\n");
		log("        use the specified Verilog file for extra primitives (can be specified multiple\n");
		log("        times).\n");
		log("\n");
		log("    -extra-map <techmap.v>\n");
		log("        use the specified Verilog file for extra techmap rules (can be specified multiple\n");
		log("        times).\n");
		log("\n");
		log("    -extra-mlibmap <memory_map.txt>\n");
		log("        use the provided library convert memory into hardware supported memory (can be specified\n");
		log("        multiple times).\n");
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
		log("    -noiopad\n");
		log("        disable I/O buffer insertion (useful for hierarchical or \n");
		log("        out-of-context flows).\n");
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
		log("    -latches <info|warn|error>\n");
		log("        select the behaviour for latches that cannot be mapped to a\n");
		log("        dedicated hardware primitive and are implemented using LUTs\n");
		log("        instead. 'error' (the default) aborts synthesis, 'warn' only\n");
		log("        prints a warning, and 'info' permits them with an info-level message.\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_module, json_file, fsm_opts, memory_opts, carry_mode, cells_map, arith_map, clkbuf_map, multiplier_map, latches;
	std::vector<string> extra_plib, extra_map, extra_mlibmap;
	std::vector<std::pair<string, string>> extra_ffs;

	bool autotop, noalumacc, nofsm, noshare, noiopad, flatten;
	int lut, multiplier_a_max, multiplier_b_max, multiplier_a_min, multiplier_b_min, multiplier_y_min;

	void clear_flags() override
	{
		top_module.clear();
		autotop = false;
		lut = 4;
		noalumacc = false;
		nofsm = false;
		noshare = false;
		noiopad = false;
		carry_mode = "none";
		flatten = true;
		json_file = "";
		latches = "error";
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
			if (args[argidx] == "-json" && argidx + 1 < args.size()) {
				json_file = args[++argidx];
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
			if (args[argidx] == "-lut" && argidx + 1 < args.size()) {
				lut = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-ff" && argidx + 2 < args.size()) {
				string cell = args[++argidx];
				string init = args[++argidx];
				extra_ffs.push_back({cell, init});
				continue;
			}
			if (args[argidx] == "-cells-map" && argidx + 1 < args.size()) {
				cells_map = args[++argidx];
				continue;
			}
			if (args[argidx] == "-arith-map" && argidx + 1 < args.size()) {
				arith_map = args[++argidx];
				continue;
			}
			if (args[argidx] == "-clkbuf-map" && argidx + 1 < args.size()) {
				clkbuf_map = args[++argidx];
				continue;
			}
			if (args[argidx] == "-multiplier-map" && argidx + 6 < args.size()) {
				multiplier_map = args[++argidx];
				multiplier_a_max = atoi(args[++argidx].c_str());
				multiplier_b_max = atoi(args[++argidx].c_str());
				multiplier_a_min = atoi(args[++argidx].c_str());
				multiplier_b_min = atoi(args[++argidx].c_str());
				multiplier_y_min = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-extra-plib" && argidx + 1 < args.size()) {
				extra_plib.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-extra-map" && argidx + 1 < args.size()) {
				extra_map.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-extra-mlibmap" && argidx + 1 < args.size()) {
				extra_mlibmap.push_back(args[++argidx]);
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
			if (args[argidx] == "-noiopad") {
				noiopad = true;
				continue;
			}
			if (args[argidx] == "-carry" && argidx + 1 < args.size()) {
				carry_mode = args[++argidx];
				if (carry_mode != "none" && carry_mode != "ha")
					log_cmd_error("Unsupported carry style: %s\n", carry_mode);
				continue;
			}
			if (args[argidx] == "-noflatten") {
				flatten = false;
				continue;
			}
			if (args[argidx] == "-latches" && argidx+1 < args.size()) {
				latches = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");
		if (latches != "info" && latches != "warn" && latches != "error")
			log_cmd_error("Invalid value '%s' for -latches (expected info, warn or error)\n", latches.c_str());

		log_header(design, "Executing SYNTH_FABULOUS pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (help_mode) {
			run("read_verilog -lib <extra_plib.v>", "(for each -extra-plib)");
		} else
			for (auto lib : extra_plib) {
				run("read_verilog -lib " + lib);
			}

		if (check_label("begin")) {
			if (top_module.empty()) {
				if (autotop)
					run("hierarchy -check -auto-top");
				else
					run("hierarchy -check");
			} else
				run(stringf("hierarchy -check -top %s", top_module));
			run("proc -latches " + (latches == "info" ? std::string("info") : std::string("warn")));
		}

		if (check_label("flatten", "(unless -noflatten)")) {
			if (flatten) {
				run("check");
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
			if (help_mode || multiplier_map != "") {
				run("wreduce t:$mul");
				if (help_mode) {
					run("techmap -map +/mul2dsp.v -map <multiplier_map> -D DSP_A_MAXWIDTH=<a_max> -D DSP_B_MAXWIDTH=<b_max> "
					    "-D DSP_A_MINWIDTH=<a_min> -D DSP_B_MINWIDTH=<b_min> -D DSP_Y_MINWIDTH=<y_min> "
					    "-D DSP_NAME=$__FABULOUS_MUL",
					    "(if -multiplier-map)");
				} else {
					run(stringf("techmap -map +/mul2dsp.v -map %s -D DSP_A_MAXWIDTH=%d -D DSP_B_MAXWIDTH=%d "
						    "-D DSP_A_MINWIDTH=%d -D DSP_B_MINWIDTH=%d -D DSP_Y_MINWIDTH=%d "
						    "-D DSP_NAME=$__FABULOUS_MUL",
						    multiplier_map.c_str(), multiplier_a_max, multiplier_b_max, multiplier_a_min, multiplier_b_min,
						    multiplier_y_min));
				}
				run("select a:mul2dsp", "              (if -multiplier-map)");
				run("setattr -unset mul2dsp", "        (if -multiplier-map)");
				run("opt_expr -fine", "                (if -multiplier-map)");
				run("wreduce", "                       (if -multiplier-map)");
				run("select -clear", "                 (if -multiplier-map)");
				run("chtype -set $mul t:$__soft_mul", "(if -multiplier-map)");
			}
			if (!noalumacc)
				run("alumacc", "  (unless -noalumacc)");
			if (!noshare)
				run("share", "    (unless -noshare)");
			run("opt");
			run("memory -nomap" + memory_opts);
			run("opt_clean");
		}

		if (check_label("map_memory")) {
			if (help_mode) {
				run("memory_libmap -lib <memory_map.txt>", "(for each -extra-mlibmap)");
			} else
				for (auto lib : extra_mlibmap) {
					run("memory_libmap -lib " + lib);
				}
		}

		if (check_label("map_ffram")) {
			run("opt -fast -mux_undef -undriven -fine");
			run("memory_map");
			run("opt -undriven -fine");
		}

		if (check_label("map_arith")) {
			if (help_mode) {
				run("techmap -map <arith_map.v> -D ARITH_<carry>");
			} else if (!arith_map.empty()) {
				run(stringf("techmap -map %s -D ARITH_%s", arith_map.c_str(), carry_mode.c_str()));
			}
			run("clean");
		}

		if (check_label("map_gates")) {
			run("opt -full");
			run("techmap -map +/techmap.v");
			run("opt -fast");
		}

		if (check_label("map_iopad", "(skip if -noiopad)") && !noiopad) {
			run("opt -full");
			run("iopadmap -bits "
			    "-inpad $__FABULOUS_IBUF OUT:PAD "
			    "-outpad $__FABULOUS_OBUF IN:PAD "
			    "-toutpad $__FABULOUS_TBUF EN:IN:PAD "
			    "-tinoutpad $__FABULOUS_IOBUF EN:OUT:IN:PAD");
		}

		if (check_label("map_ffs")) {
			if (help_mode) {
				run("dfflegalize -cell <cell_type_pattern> <init_values>...", "(for each -ff)");
			} else if (!extra_map.empty()) {
				std::string dff_str = "dfflegalize";
				for (const auto &[cell, init] : extra_ffs)
					dff_str += stringf(" -cell %s %s", cell, init);
				run(dff_str);
			}
			if (latches == "error" || help_mode)
				run("check -latchonly -assert", "(only if -latches error, the default)");
			run("opt_merge");
		}

		if (check_label("map_extra")) {
			if (help_mode) {
				run("techmap -map <extra_map.v>...", "(for each -extra-map)");
			} else if (!extra_map.empty()) {
				std::string map_str = "techmap";
				for (auto map : extra_map)
					map_str += stringf(" -map %s", map);
				run(map_str);
			}
			run("simplemap");
			run("clean");
		}

		if (check_label("map_luts")) {
			run(stringf("abc -lut %d -dress", lut));
			run("clean");
		}

		if (check_label("map_cells")) {
			if (help_mode) {
				run("techmap -D LUT_K=<lut> -map <cells_map.v>");
			} else if (!cells_map.empty()) {
				run(stringf("techmap -D LUT_K=%d -map %s", lut, cells_map.c_str()));
			}
			run("clean");
		}

		if (check_label("map_clkbufs")) {
			if (help_mode) {
				run("clkbufmap -buf $__FABULOUS_GBUF OUT:IN", "(if -clkbuf-map <clkbuf_map.v>)");
				run("techmap -map <clkbuf_map.v>", "(if -clkbuf-map <clkbuf_map.v>)");
			} else if (clkbuf_map != "") {
				run("clkbufmap -buf $__FABULOUS_GBUF OUT:IN");
				run(stringf("techmap -map %s", clkbuf_map));
				run("clean");
			}
		}

		if (check_label("check")) {
			run("hierarchy -check");
			run("stat");
		}

		if (check_label("json")) {
			if (!json_file.empty() || help_mode)
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file));
		}
	}
} SynthPass;

PRIVATE_NAMESPACE_END
