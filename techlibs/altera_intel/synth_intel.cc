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

struct SynthIntelPass : public ScriptPass {
	SynthIntelPass() : ScriptPass("synth_intel", "synthesis for Intel (Altera) FPGAs.") { }

	virtual void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_intel [options]\n");
		log("\n");
		log("This command runs synthesis for Intel FPGAs. This work is still experimental.\n");
		log("\n");
		log("    -family < max10 | cycloneiv >\n");
		log("        generate the synthesis netlist for the specified family.\n");
		log("        MAX10 is the default target if not family argument specified \n");
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
		log("    -retime\n");
		log("        run 'abc' with -dff option\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		help_script();
		log("\n");
	}

        string top_opt, family_opt, vout_file;
	bool retime;

	virtual void clear_flags() YS_OVERRIDE
	{
		top_opt = "-auto-top";
                family_opt = "max10";
		vout_file = "";
		retime = false;
	}

	virtual void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
	  string run_from, run_to;
		clear_flags();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
		        if (args[argidx] == "-family" && argidx+1 < args.size()) {
				family_opt = args[++argidx];
				continue;
			}
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
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This comannd only operates on fully selected designs!\n");

                if (family_opt != "max10" && family_opt !="cycloneiv" )
		  log_cmd_error("Invalid or not family specified: '%s'\n", family_opt.c_str());

		log_header(design, "Executing SYNTH_INTEL pass.\n");
		log_push();

		run_script(design, run_from, run_to);

		log_pop();
	}

	virtual void script() YS_OVERRIDE
	{
	  if (check_label("begin"))
	  {
		  if(check_label("family") && family_opt=="max10")
		  {
			run("read_verilog -lib +/altera_intel/max10/cells_comb_max10.v");
			run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		  }
		  else
		  {
		      run("read_verilog -lib +/altera_intel/cycloneiv/cells_comb_cycloneiv.v");
		      run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
		  }
	  }

		if (check_label("flatten"))
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

		if (check_label("fine"))
		{
		        run("opt -fast -full");
			run("memory_map");
			run("opt -full");
			run("techmap -map +/techmap.v");
                        run("opt -fast");
			run("clean -purge");
			run("setundef -undriven -zero");
			if (retime || help_mode)
				run("abc -dff", "(only if -retime)");
		}

		if (check_label("map_luts"))
		{
		        run("abc -lut 4");
			run("clean");
		}

		if (check_label("map_cells"))
		{
			run("iopadmap -bits -outpad $__outpad I:O -inpad $__inpad O:I");
			if(family_opt=="max10")
			  run("techmap -map +/altera_intel/max10/cells_map_max10.v");
			else
			  run("techmap -map +/altera_intel/cycloneiv/cells_map_cycloneiv.v");
			run("clean -purge");
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
				run(stringf("write_verilog -nodec -attr2comment -defparam -nohex -renameprefix yosys_ %s",
						help_mode ? "<file-name>" : vout_file.c_str()));
		}
	}
} SynthIntelPass;

PRIVATE_NAMESPACE_END
