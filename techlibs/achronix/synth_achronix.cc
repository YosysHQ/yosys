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

struct SynthAchronixPass : public ScriptPass {
  SynthAchronixPass() : ScriptPass("synth_achronix", "synthesis for Acrhonix Speedster22i FPGAs.") { }

  void help() YS_OVERRIDE
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    synth_achronix [options]\n");
    log("\n");
    log("This command runs synthesis for Achronix Speedster eFPGAs. This work is still experimental.\n");
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
    log("    -noflatten\n");
    log("        do not flatten design before synthesis\n");
    log("\n");
    log("    -retime\n");
    log("        run 'abc' with '-dff -D 1' options\n");
    log("\n");
    log("\n");
    log("The following commands are executed by this synthesis command:\n");
    help_script();
    log("\n");
  }

  string top_opt, family_opt, vout_file;
  bool retime, flatten;

  void clear_flags() YS_OVERRIDE
  {
    top_opt = "-auto-top";
    vout_file = "";
    retime = false;
    flatten = true;
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
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
        if (args[argidx] == "-noflatten") {
          flatten = false;
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
      log_cmd_error("This command only operates on fully selected designs!\n");

    log_header(design, "Executing SYNTH_ACHRONIX pass.\n");
    log_push();

    run_script(design, run_from, run_to);

    log_pop();
  }

  void script() YS_OVERRIDE
  {
    if (check_label("begin"))
      {
        run("read_verilog -sv -lib +/achronix/speedster22i/cells_sim.v");
        run(stringf("hierarchy -check %s", help_mode ? "-top <top>" : top_opt.c_str()));
      }

    if (flatten && check_label("flatten", "(unless -noflatten)"))
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
        run("opt -fast -mux_undef -undriven -fine -full");
        run("memory_map");
        run("opt -undriven -fine");
        run("dffsr2dff");
        run("dff2dffe -direct-match $_DFF_*");
        run("opt -fine");
        run("techmap -map +/techmap.v");
        run("opt -full");
        run("clean -purge");
        run("setundef -undriven -zero");
        if (retime || help_mode)
          run("abc -markgroups -dff -D 1", "(only if -retime)");
      }

    if (check_label("map_luts"))
      {
        run("abc -lut 4" + string(retime ? " -dff -D 1" : ""));
        run("clean");
      }

    if (check_label("map_cells"))
      {
        run("iopadmap -bits -outpad $__outpad I:O -inpad $__inpad O:I");
        run("techmap -map +/achronix/speedster22i/cells_map.v");
        // VT: not done yet run("dffinit -highlow -ff DFF q power_up");
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
          run(stringf("write_verilog -nodec -attr2comment -defparam -renameprefix syn_ %s",
                      help_mode ? "<file-name>" : vout_file.c_str()));
      }
  }
} SynthAchronixPass;

PRIVATE_NAMESPACE_END
