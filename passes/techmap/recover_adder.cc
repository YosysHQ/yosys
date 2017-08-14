/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2017 Robert Ou <rqou@robertou.com>
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

// The approach used in this adder recovery pass is vaguely inspired by the paper
// "Improved Carry Chain Mapping for the VTR Flow" by Petkovska et. al. The key takeaway
// from that paper is that it is easy for ABC to find 3-input XOR gates and majority gates
// once the input circuit has been mapped to an AIG. Rather than writing a custom pass
// for ABC, this script simply tells ABC to techmap to a library containing only AND, NOT,
// XOR, and majority gates. ABC thus cannot find any other types of gates. Once the netlist
// has been transformed, it is possible to use the yosys native subcircuit extraction code
// to find half and full adders. A custom yosys pass then looks for these chains and converts
// them back into an $alu/$add/$sub cell. Finally, any combinatorial logic that is left is
// put back into ABC with the normal cell library to be re-optimized.

#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RecoverAdderPass : public ScriptPass
{
    RecoverAdderPass() : ScriptPass("recover_adder", "recovers $alu/$add/$sub cells from gates") {}
    virtual void help() YS_OVERRIDE
    {
        //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
        log("\n");
        log("    recover_adder [options]\n");
        log("\n");
        log("recovers $alu/$add/$sub cells from gates\n");
        log("\n");
        log("Reconstructs adders and subtractors given a netlist of gates. This pass is\n");
        log("intended to be used as part of a circuit reverse-engineering workflow, but it\n");
        log("does also work with synthesis. Note that this command will completely destroy\n");
        log("the structure of combinatorial logic as it works.\n");
        log("\n");
        log("\n");
        log("The following commands are executed by this command:\n");
        help_script();
        log("\n");
    }

    bool keep_bit_adders, keep_gates, no_final_abc;

    virtual void clear_flags() YS_OVERRIDE
    {
        keep_bit_adders = false;
        keep_gates = false;
        no_final_abc = false;
    }

    virtual void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
    {
        clear_flags();

        size_t argidx;
        for (argidx = 1; argidx < args.size(); argidx++)
        {
            if (args[argidx] == "-keep_bit_adders") {
                keep_bit_adders = true;
                continue;
            }
            if (args[argidx] == "-keep_gates") {
                keep_gates = true;
                continue;
            }
            if (args[argidx] == "-no_final_abc") {
                no_final_abc = true;
                continue;
            }
            break;
        }
        extra_args(args, argidx, design);

        log_header(design, "Executing recover_adder.\n");
        log_push();

        run_script(design, "", "");

        log_pop();
    }

    virtual void script() YS_OVERRIDE
    {
        run("abc -liberty +/untechmap/adder_untechmap.lib");
        run("extract -map +/untechmap/adder_untechmap.v -swap __XOR3_ A,B,C -swap __MAJ_ A,B,C");
        run("recover_adder_core");

        if (!keep_bit_adders)
            run("techmap -autoproc -map +/untechmap/adder_untechmap.v");
        else
            run("read_verilog -lib +/untechmap/adder_untechmap.v");

        if (!keep_gates)
            run("techmap -autoproc -map +/untechmap/adder_untechmap_gates.v");
        else
            run("read_verilog -lib +/untechmap/adder_untechmap_gates.v");

        if (!no_final_abc)
            run("abc");

        run("clean");
    }
} RecoverAdderPass;

PRIVATE_NAMESPACE_END
