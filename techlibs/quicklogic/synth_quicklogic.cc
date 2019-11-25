#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SynthQuickLogicPass : public ScriptPass
{
    SynthQuickLogicPass() : ScriptPass("synth_quicklogic", "Synthesis for QuickLogic FPGAs") { }

    void help() override
    {
        log("\n");
        log("   synth_quicklogic [options]\n");
        log("This command runs synthesis for QuickLogic FPGAs\n");
        log("\n");
        log("    -top <module>\n");
        log("         use the specified module as top module\n");
        log("\n");
        log("    -edif <file>\n");
        log("        write the design to the specified edif file. writing of an output file\n");
        log("        is omitted if this parameter is not specified.\n");
        log("\n");
        log("    -blif <file>\n");
        log("        write the design to the specified BLIF file. writing of an output file\n");
        log("        is omitted if this parameter is not specified.\n");
        log("\n");
        help_script();
        log("\n");
    }

    std::string top_opt = "";
    std::string edif_file = "";
    std::string blif_file = "";
    std::string currmodule = "";

    void clear_flags() override
    {
        top_opt = "-auto-top";
        edif_file.clear();
        blif_file.clear();
    }

    void execute(std::vector<std::string> args, RTLIL::Design *design) override
    {
        std::string run_from, run_to;
        clear_flags();

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
            break;
        }
        extra_args(args, argidx, design);

        if (!design->full_selection())
            log_cmd_error("This command only operates on fully selected designs!\n");

        log_header(design, "Executing SYNTH_QUICKLOGIC pass.\n");
        log_push();

        run_script(design, run_from, run_to);

        log_pop();
    }

    void script() override
    {
        if (check_label("begin")) {
            run("read_verilog -lib +/quicklogic/cells_sim.v");
            run(stringf("hierarchy -check %s", top_opt.c_str()));
        }

        if (check_label("prepare")) {
            run("proc");
            run("flatten");
            run("wreduce -keepdc");
            run("muxpack");
        }

        if (check_label("coarse")) {
            run("tribuf -logic");
            run("deminout");
            run("opt");
            run("opt_clean");
            run("peepopt");
            run("techmap");
            run("muxcover -mux8 -mux4");
            run("abc -luts 1,2,2,4");
            run("opt");
            run("check");
        }

        if (check_label("map")) {
            run("techmap -map +/quicklogic/cells_map.v");
            run("opt_clean");
            run("check");
            run("autoname");
        }

        if (check_label("iomap")) {
            run("clkbufmap -buf $_BUF_ Y:A -inpad ckpad Q:P");
            run("iopadmap -bits -outpad outpad A:P -inpad inpad Q:P -tinoutpad bipad EN:Q:A:P A:top");
        }

        if (check_label("finalize")) {
            run("splitnets -ports -format ()");
            run("setundef -zero -params -undriven");
            run("hilomap -hicell logic_1 a -locell logic_0 a -singleton A:top");
            run("opt_clean");
            run("check");
        }

        if (check_label("edif")) {
            if (!edif_file.empty() || help_mode) {
                run(stringf("write_edif -nogndvcc -attrprop -pvector par %s %s", this->currmodule.c_str(), edif_file.c_str()));
            }
        }

        if (check_label("blif")) {
            if (!blif_file.empty() || help_mode)
                run(stringf("write_blif %s %s", top_opt.c_str(), blif_file.c_str()));
        }
    }
} SynthQuickLogicPass;

PRIVATE_NAMESPACE_END
