/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Alexandra Østermark <alex.cramt@gmail.com>
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
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SynthCyclone2Pass : public ScriptPass
{
	SynthCyclone2Pass() : ScriptPass("synth_cyclone2", "synthesis for Intel (Altera) Cyclone II FPGAs") { }

	void on_register() override
	{
		target_register.emplace("cyclone2", Target{
			"Intel (Altera) Cyclone II",
			{
				{"", { // default
					"",
					{"+/cyclone2/cells_sim.v"}
				}}
			}
		});
	}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_cyclone2 [options]\n");
		log("\n");
		log("This command runs synthesis for Cyclone II FPGAs, for place and route with\n");
		log("nextpnr-himbaechel (uarch cyclone2). Block RAM, multipliers and PLLs are not\n");
		log("mapped yet: memories become logic.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -json <file>\n");
		log("        write the design to the specified JSON file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -noiopad\n");
		log("        do not insert I/O buffers on top-level ports\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

	string top_opt, json_file;
	bool noiopad;

	void clear_flags() override
	{
		top_opt = "-auto-top";
		json_file = "";
		noiopad = false;
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
			if (args[argidx] == "-run" && argidx+1 < args.size()) {
				size_t pos = args[argidx+1].find(':');
				if (pos == std::string::npos)
					break;
				run_from = args[++argidx].substr(0, pos);
				run_to = args[argidx].substr(pos+1);
				continue;
			}
			if (args[argidx] == "-noiopad") {
				noiopad = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		log_header(design, "Executing SYNTH_CYCLONE2 pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	void script() override
	{
		if (check_label("begin"))
		{
			run("read_verilog -lib +/cyclone2/cells_bb.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt));
		}

		if (check_label("coarse"))
		{
			run("synth -flatten -run coarse:fine");
		}

		if (check_label("map_ram"))
		{
			run("memory_map");
			run("opt -full");
		}

		if (check_label("map_arith"))
		{
			run("techmap -map +/techmap.v -map +/cyclone2/arith_map.v");
			run("opt -fast");
		}

		if (check_label("map_ffs"))
		{
			// Registers power up 0; making that explicit lets registers that
			// never leave it fold into constants.
			run("setundef -zero -init");
			run("opt -full -sat");
			// Enable, asynchronous clear and synchronous clear are LAB-wide
			// signals; anything else goes into the LUT in front.
			run("dfflegalize -cell $_DFF_P_ 0 -cell $_DFFE_PP_ 0 -cell $_DFF_PP0_ 0 -cell $_DFFE_PP0P_ 0 -cell $_SDFF_PP0_ 0 -cell $_SDFFCE_PP0P_ 0");
			run("attrmap -remove init");
			run("techmap -map +/cyclone2/cells_map.v");
			run("opt_expr -mux_undef");
			run("simplemap");
		}

		if (check_label("map_luts"))
		{
			run("abc -lut 4");
			run("opt -fast");
		}

		if (check_label("map_cells"))
		{
			run("techmap -map +/cyclone2/cells_map.v");
		}

		if (check_label("map_io", "(skip if '-noiopad')") && !noiopad)
		{
			run("iopadmap -bits -inpad CY2_IBUF COMBOUT:PAD -outpad CY2_OBUF DATAOUT:PAD");
		}

		if (check_label("check"))
		{
			run("opt_clean -purge");
			run("hierarchy -check");
			run("stat");
			run("check -noinit");
		}

		if (check_label("json"))
		{
			if (!json_file.empty() || help_mode)
				run(stringf("write_json %s", help_mode ? "<file-name>" : json_file));
		}
	}
} SynthCyclone2Pass;

PRIVATE_NAMESPACE_END
