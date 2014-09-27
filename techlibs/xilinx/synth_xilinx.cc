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
		log("partly selected designs.\n");
		log("\n");
		log("    -top <module>\n");
		log("        use the specified module as top module (default='top')\n");
		log("\n");
		log("    -arch <arch>\n");
		log("        select architecture. the following architectures are supported:\n");
		log("            spartan6 (default), artix7, kintex7, virtex7, zynq7000\n");
		log("            (this parameter is not used by the command at the moment)\n");
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
		log("\n");
		log("The following commands are executed by this synthesis command:\n");
		log("\n");
		log("    begin:\n");
		log("        hierarchy -check -top <top>\n");
		log("\n");
		log("    coarse:\n");
		log("        proc\n");
		log("        opt\n");
		log("        memory\n");
		log("        clean\n");
		log("        fsm\n");
		log("        opt\n");
		log("\n");
		log("    fine:\n");
		log("        techmap\n");
		log("        opt\n");
		log("\n");
		log("    map_luts:\n");
		log("        abc -lut 6\n");
		log("        clean\n");
		log("\n");
		log("    map_cells:\n");
		log("        techmap -share_map xilinx/cells.v\n");
		log("        clean\n");
		log("\n");
		log("    clkbuf:\n");
		log("        select -set xilinx_clocks <top>/t:FDRE %%x:+FDRE[C] <top>/t:FDRE %%d\n");
		log("        iopadmap -inpad BUFGP O:I @xilinx_clocks\n");
		log("\n");
		log("    iobuf:\n");
		log("        select -set xilinx_nonclocks <top>/w:* <top>/t:BUFGP %%x:+BUFGP[I] %%d\n");
		log("        iopadmap -outpad OBUF I:O -inpad IBUF O:I @xilinx_nonclocks\n");
		log("\n");
		log("    edif:\n");
		log("        write_edif synth.edif\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		std::string top_module = "top";
		std::string arch_name = "spartan6";
		std::string edif_file;
		std::string run_from, run_to;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				top_module = args[++argidx];
				continue;
			}
			if (args[argidx] == "-arch" && argidx+1 < args.size()) {
				arch_name = args[++argidx];
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
			break;
		}
		extra_args(args, argidx, design);

		if (!design->full_selection())
			log_cmd_error("This comannd only operates on fully selected designs!\n");

		if (arch_name == "spartan6") {
			/* set flags */
		} else
		if (arch_name == "artix7") {
			/* set flags */
		} else
		if (arch_name == "kintex7") {
			/* set flags */
		} else
		if (arch_name == "zynq7000") {
			/* set flags */
		} else
			log_cmd_error("Architecture '%s' is not supported!\n", arch_name.c_str());

		bool active = run_from.empty();

		log_header("Executing SYNTH_XILINX pass.\n");
		log_push();

		if (check_label(active, run_from, run_to, "begin"))
		{
			Pass::call(design, stringf("hierarchy -check -top %s", top_module.c_str()));
		}

		if (check_label(active, run_from, run_to, "coarse"))
		{
			Pass::call(design, "proc");
			Pass::call(design, "opt");
			Pass::call(design, "memory");
			Pass::call(design, "clean");
			Pass::call(design, "fsm");
			Pass::call(design, "opt");
		}

		if (check_label(active, run_from, run_to, "fine"))
		{
			Pass::call(design, "techmap");
			Pass::call(design, "opt");
		}

		if (check_label(active, run_from, run_to, "map_luts"))
		{
			Pass::call(design, "abc -lut 6");
			Pass::call(design, "clean");
		}

		if (check_label(active, run_from, run_to, "map_cells"))
		{
			Pass::call(design, "techmap -share_map xilinx/cells.v");
			Pass::call(design, "clean");
		}

		if (check_label(active, run_from, run_to, "clkbuf"))
		{
			Pass::call(design, stringf("select -set xilinx_clocks %s/t:FDRE %%x:+FDRE[C] %s/t:FDRE %%d", top_module.c_str(), top_module.c_str()));
			Pass::call(design, "iopadmap -inpad BUFGP O:I @xilinx_clocks");
		}

		if (check_label(active, run_from, run_to, "iobuf"))
		{
			Pass::call(design, stringf("select -set xilinx_nonclocks %s/w:* %s/t:BUFGP %%x:+BUFGP[I] %%d", top_module.c_str(), top_module.c_str()));
			Pass::call(design, "iopadmap -outpad OBUF I:O -inpad IBUF O:I @xilinx_nonclocks");
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
