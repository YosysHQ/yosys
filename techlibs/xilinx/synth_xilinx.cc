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

bool check_label(bool &active, std::string run_from, std::string run_to, std::string label)
{
	if (label == run_from)
		active = true;
	if (label == run_to)
		active = false;
	return active;
}

struct SynthXilinxPass : public Pass {
	SynthXilinxPass() : Pass("synth_xilinx", "synthesis for Xilinx FPGAs") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    synth_xilinx [options]\n");
		log("\n");
		log("This command runs synthesis for Xilinx FPGAs. This command does not operate on\n");
		log("partly selected designs. At the moment this command creates netlists that are\n");
		log("compatible with 7-Series Xilinx devices.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module\n");
		log("\n");
		log("    -edif <file>\n");
		log("        write the design to the specified edif file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -run <from_label>:<to_label>\n");
		log("        only run the commands between the labels (see below). an empty\n");
		log("        from label is synonymous to 'begin', and empty to label is\n");
		log("        synonymous to the end of the command list.\n");
		log("\n");
		log("    -flatten\n");
		log("        flatten design before synthesis\n");
		log("\n");
		log("    -retime\n");
		log("        run 'abc' with -dff option\n");
		log("\n");
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		log("\n");
		log("    begin:\n");
		log("        read_verilog -lib +/xilinx/cells_sim.v\n");
		log("        read_verilog -lib +/xilinx/cells_xtra.v\n");
		log("        read_verilog -lib +/xilinx/brams_bb.v\n");
		log("        read_verilog -lib +/xilinx/drams_bb.v\n");
		log("        hierarchy -check -top <top>\n");
		log("\n");
		log("    flatten:     (only if -flatten)\n");
		log("        proc\n");
		log("        flatten\n");
		log("\n");
		log("    coarse:\n");
		log("        synth -run coarse\n");
		log("\n");
		log("    bram:\n");
		log("        memory_bram -rules +/xilinx/brams.txt\n");
		log("        techmap -map +/xilinx/brams_map.v\n");
		log("\n");
		log("    dram:\n");
		log("        memory_bram -rules +/xilinx/drams.txt\n");
		log("        techmap -map +/xilinx/drams_map.v\n");
		log("\n");
		log("    fine:\n");
		log("        opt -fast -full\n");
		log("        memory_map\n");
		log("        dffsr2dff\n");
		log("        dff2dffe\n");
		log("        opt -full\n");
		log("        techmap -map +/techmap.v -map +/xilinx/arith_map.v\n");
		log("        opt -fast\n");
		log("\n");
		log("    map_luts:\n");
		log("        abc -luts 2:2,3,6:5,10,20 [-dff]\n");
		log("        clean\n");
		log("\n");
		log("    map_cells:\n");
		log("        techmap -map +/xilinx/cells_map.v\n");
		log("        dffinit -ff FDRE Q INIT -ff FDCE Q INIT -ff FDPE Q INIT\n");
		log("        clean\n");
		log("\n");
		log("    check:\n");
		log("        hierarchy -check\n");
		log("        stat\n");
		log("        check -noinit\n");
		log("\n");
		log("    edif:     (only if -edif)\n");
		log("        write_edif <file-name>\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string top_opt = "-auto-top";
		std::string edif_file;
		std::string run_from, run_to;
		bool flatten = false;
		bool retime = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_opt = "-top " + args[++argidx];
				continue;
			}
			if (args[argidx] == "-edif" && argidx+1 < args.size()) {
				edif_file = args[++argidx];
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
			if (args[argidx] == "-retime") {
				retime = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This comannd only operates on fully selected designs!\n");

		bool active = run_from.empty();

		log_header(design, "Executing SYNTH_XILINX pass.\n");
		log_push();

		if (check_label(active, run_from, run_to, "begin"))
		{
			Pass::call(design, "read_verilog -lib +/xilinx/cells_sim.v");
			Pass::call(design, "read_verilog -lib +/xilinx/cells_xtra.v");
			Pass::call(design, "read_verilog -lib +/xilinx/brams_bb.v");
			Pass::call(design, "read_verilog -lib +/xilinx/drams_bb.v");
			Pass::call(design, stringf("hierarchy -check %s", top_opt.c_str()));
		}

		if (flatten && check_label(active, run_from, run_to, "flatten"))
		{
			Pass::call(design, "proc");
			Pass::call(design, "flatten");
		}

		if (check_label(active, run_from, run_to, "coarse"))
		{
			Pass::call(design, "synth -run coarse");
		}

		if (check_label(active, run_from, run_to, "bram"))
		{
			Pass::call(design, "memory_bram -rules +/xilinx/brams.txt");
			Pass::call(design, "techmap -map +/xilinx/brams_map.v");
		}

		if (check_label(active, run_from, run_to, "dram"))
		{
			Pass::call(design, "memory_bram -rules +/xilinx/drams.txt");
			Pass::call(design, "techmap -map +/xilinx/drams_map.v");
		}

		if (check_label(active, run_from, run_to, "fine"))
		{
			Pass::call(design, "opt -fast -full");
			Pass::call(design, "memory_map");
			Pass::call(design, "dffsr2dff");
			Pass::call(design, "dff2dffe");
			Pass::call(design, "opt -full");
			Pass::call(design, "techmap -map +/techmap.v -map +/xilinx/arith_map.v");
			Pass::call(design, "opt -fast");
		}

		if (check_label(active, run_from, run_to, "map_luts"))
		{
			Pass::call(design, "abc -luts 2:2,3,6:5,10,20" + string(retime ? " -dff" : ""));
			Pass::call(design, "clean");
		}

		if (check_label(active, run_from, run_to, "map_cells"))
		{
			Pass::call(design, "techmap -map +/xilinx/cells_map.v");
			Pass::call(design, "dffinit -ff FDRE Q INIT -ff FDCE Q INIT -ff FDPE Q INIT");
			Pass::call(design, "clean");
		}

		if (check_label(active, run_from, run_to, "check"))
		{
			Pass::call(design, "hierarchy -check");
			Pass::call(design, "stat");
			Pass::call(design, "check -noinit");
		}

		if (check_label(active, run_from, run_to, "edif"))
		{
			if (!edif_file.empty())
				Pass::call(design, stringf("write_edif %s", edif_file.c_str()));
		}

		log_pop();
	}
} SynthXilinxPass;

PRIVATE_NAMESPACE_END
