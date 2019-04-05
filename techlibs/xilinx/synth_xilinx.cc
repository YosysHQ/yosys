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

struct SynthXilinxPass : public Pass
{
	SynthXilinxPass() : Pass("synth_xilinx", "synthesis for Xilinx FPGAs") { }

	void help() YS_OVERRIDE
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
		log("    -blif <file>\n");
		log("        write the design to the specified BLIF file. writing of an output file\n");
		log("        is omitted if this parameter is not specified.\n");
		log("\n");
		log("    -vpr\n");
		log("        generate an output netlist (and BLIF file) suitable for VPR\n");
		log("        (this feature is experimental and incomplete)\n");
		log("\n");
		log("    -nobram\n");
		log("        disable infering of block rams\n");
		log("\n");
		log("    -nodram\n");
		log("        disable infering of distributed rams\n");
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
		log("        hierarchy -check -top <top>\n");
		log("\n");
		log("    flatten:     (only if -flatten)\n");
		log("        proc\n");
		log("        flatten\n");
		log("\n");
		log("    coarse:\n");
		log("        synth -run coarse\n");
		log("\n");
		log("    bram: (only executed when '-nobram' is not given)\n");
		log("        memory_bram -rules +/xilinx/brams.txt\n");
		log("        techmap -map +/xilinx/brams_map.v\n");
		log("\n");
		log("    dram: (only executed when '-nodram' is not given)\n");
		log("        memory_bram -rules +/xilinx/drams.txt\n");
		log("        techmap -map +/xilinx/drams_map.v\n");
		log("\n");
		log("    fine:\n");
		log("        opt -fast -full\n");
		log("        memory_map\n");
		log("        dffsr2dff\n");
		log("        dff2dffe\n");
		log("        opt -full\n");
		log("        techmap -map +/techmap.v -map +/xilinx/arith_map.v -map +/xilinx/ff_map.v\n");
		log("        opt -fast\n");
		log("\n");
		log("    map_luts:\n");
		log("        abc -luts 2:2,3,6:5,10,20 [-dff] (without '-vpr' only!)\n");
		log("        abc -lut 5 [-dff] (with '-vpr' only!)\n");
		log("        clean\n");
		log("\n");
		log("    map_cells:\n");
		log("        techmap -map +/xilinx/cells_map.v\n");
		log("        dffinit -ff FDRE   Q INIT -ff FDCE   Q INIT -ff FDPE   Q INIT -ff FDSE   Q INIT \\\n");
		log("                -ff FDRE_1 Q INIT -ff FDCE_1 Q INIT -ff FDPE_1 Q INIT -ff FDSE_1 Q INIT\n");
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
		log("    blif:     (only if -blif)\n");
		log("        write_blif <file-name>\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		std::string top_opt = "-auto-top";
		std::string edif_file;
		std::string blif_file;
		std::string run_from, run_to;
		bool flatten = false;
		bool retime = false;
		bool vpr = false;
		bool nobram = false;
		bool nodram = false;

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
			if (args[argidx] == "-blif" && argidx+1 < args.size()) {
				blif_file = args[++argidx];
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
			if (args[argidx] == "-vpr") {
				vpr = true;
				continue;
			}
			if (args[argidx] == "-nobram") {
				nobram = true;
				continue;
			}
			if (args[argidx] == "-nodram") {
				nodram = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		bool active = run_from.empty();

		log_header(design, "Executing SYNTH_XILINX pass.\n");
		log_push();

		if (check_label(active, run_from, run_to, "begin"))
		{
			if (vpr) {
				Pass::call(design, "read_verilog -lib -D_EXPLICIT_CARRY +/xilinx/cells_sim.v");
			} else {
				Pass::call(design, "read_verilog -lib +/xilinx/cells_sim.v");
			}

			Pass::call(design, "read_verilog -lib +/xilinx/cells_xtra.v");

			if (!nobram) {
				Pass::call(design, "read_verilog -lib +/xilinx/brams_bb.v");
			}

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
			if (!nobram) {
				Pass::call(design, "memory_bram -rules +/xilinx/brams.txt");
				Pass::call(design, "techmap -map +/xilinx/brams_map.v");
			}
		}

		if (check_label(active, run_from, run_to, "dram"))
		{
			if (!nodram) {
				Pass::call(design, "memory_bram -rules +/xilinx/drams.txt");
				Pass::call(design, "techmap -map +/xilinx/drams_map.v");
			}
		}

		if (check_label(active, run_from, run_to, "fine"))
		{
			Pass::call(design, "opt -fast -full");
			Pass::call(design, "memory_map");
			Pass::call(design, "dffsr2dff");
			Pass::call(design, "dff2dffe");
			Pass::call(design, "opt -full");

			if (vpr) {
				Pass::call(design, "techmap -map +/techmap.v -map +/xilinx/arith_map.v -map +/xilinx/ff_map.v -D _EXPLICIT_CARRY");
			} else {
				Pass::call(design, "techmap -map +/techmap.v -map +/xilinx/arith_map.v -map +/xilinx/ff_map.v");
			}

			Pass::call(design, "hierarchy -check");
			Pass::call(design, "opt -fast");
		}

		if (check_label(active, run_from, run_to, "map_luts"))
		{
			Pass::call(design, "abc -luts 2:2,3,6:5,10,20" + string(retime ? " -dff" : ""));
			Pass::call(design, "clean");
			Pass::call(design, "techmap -map +/xilinx/lut_map.v");
		}

		if (check_label(active, run_from, run_to, "map_cells"))
		{
			Pass::call(design, "techmap -map +/xilinx/cells_map.v");
			Pass::call(design, "dffinit -ff FDRE Q INIT -ff FDCE Q INIT -ff FDPE Q INIT -ff FDSE Q INIT "
					"-ff FDRE_1 Q INIT -ff FDCE_1 Q INIT -ff FDPE_1 Q INIT -ff FDSE_1 Q INIT");
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
				Pass::call(design, stringf("write_edif -pvector bra %s", edif_file.c_str()));
		}
		if (check_label(active, run_from, run_to, "blif"))
		{
			if (!blif_file.empty())
				Pass::call(design, stringf("write_blif %s", edif_file.c_str()));
		}

		log_pop();
	}
} SynthXilinxPass;

PRIVATE_NAMESPACE_END
