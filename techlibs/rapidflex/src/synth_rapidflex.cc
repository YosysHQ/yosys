/*
 * Copyright 2020-2024 RapidFlex
 */
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
using namespace std;
/* Constants for device name */
constexpr const char *ALKDC_DNAME = "alkaidC";
constexpr const char *ALKDL_DNAME = "alkaidL";
constexpr const char *ALKDT_DNAME = "alkaidT";

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#define XSTR(val) #val
#define STR(val) XSTR(val)

#ifndef PASS_NAME
#define PASS_NAME synth_rf_alkaid
#endif

struct SynthRapidFlexPass : public ScriptPass {

  SynthRapidFlexPass()
      : ScriptPass(STR(PASS_NAME), "Synthesis for RapidFlex Alkaid FPGAs") {}

  void help() override {
    log("\n");
    log("   %s [options]\n", STR(PASS_NAME));
    log("This command runs synthesis for RapidFlex Alkaid FPGAs\n");
    log("\n");
    log("    -top <module>\n");
    log("         use the specified module as top module\n");
    log("\n");
    log("    -family <family>\n");
    log("        run synthesis for the specified RapidFlex architecture\n");
    log("        generate the synthesis netlist for the specified family.\n");
    log("        supported values:\n");
    log("        - alkaidL\n");
    log("        - alkaidT\n");
    log("        - alkaidC\n");
    log("\n");
    log("    -edif <file>\n");
    log("        write the design to the specified edif file. Writing of an "
        "output file\n");
    log("        is omitted if this parameter is not specified.\n");
    log("\n");
    log("    -blif <file>\n");
    log("        write the design to the specified BLIF file. Writing of an "
        "output file\n");
    log("        is omitted if this parameter is not specified.\n");
    log("\n");
    log("    -verilog <file>\n");
    log("        write the design to the specified verilog file. Writing of an "
        "output\n");
    log("        file is omitted if this parameter is not specified.\n");
    log("\n");
    log("    -no_dsp\n");
    log("        By default use DSP blocks in output netlist.\n");
    log("        do not use DSP blocks to implement multipliers and associated "
        "logic\n");
    log("\n");
    log("    -no_adder\n");
    log("        By default use adder cells in output netlist.\n");
    log("        Specifying this switch turns it off.\n");
    log("\n");
    log("    -no_bram\n");
    log("        By default use Block RAM in output netlist.\n");
    log("        Specifying this switch turns it off.\n");
    log("\n");
    log("    -insert_clock_buffer\n");
    log("        By default no insertion of clock buffer for output "
        "netlist.\n");
    log("    -cell_map_file <file>\n");
    log("        write the ckbuf into to the specified XML file. Writing of an "
        "output file\n");
    log("        Specifying this switch turns it on.\n");
    log("    -K <int>\n");
    log("        Specify the input size of LUT when running optimization. If "
        "not specified, a default value will be applied. Please do not modify "
        "this parameter except architecture exploration\n");
    log("    -parse_only\n");
    log("        Only apply verilog parsing. This is for rewriting purpose.\n");
    log("        Specifying this switch turns it on.\n");
    log("\n");
    log("The following commands are executed by this synthesis command:\n");
    log("\n");
    log("    -save_block_diagram <file>\n");
    log("        generate a block diagram and save to the specified file\n");
    log("        supported formats: dot, png, svg, eps, pdf\n");
    log("\n");
    help_script();
  }

  std::string top_opt, edif_file, blif_file, family, currmodule, verilog_file,
      cell_map_file, lib_path, block_diagram_file;
  bool nodsp;
  bool no_opt;
  bool abc9;
  bool inferAdder;
  bool inferBram;
  bool show_help;
  bool insert_clock_buffer;
  size_t DEFAULT_K = 5;
  size_t MIN_K = 4;
  size_t MAX_K = 6;
  size_t max_lut_size = DEFAULT_K;
  bool parse_only = false;

  void clear_flags() override {
    top_opt = "-auto-top";
    edif_file = "";
    blif_file = "";
    cell_map_file = "";
    verilog_file = "";
    currmodule = "";
    family = ALKDL_DNAME;
    inferAdder = true;
    inferBram = true;
    nodsp = false;
    no_opt = false;
    abc9 = false;
    lib_path = "+/rapidflex/";
    show_help = false;
    insert_clock_buffer = false;
    max_lut_size = DEFAULT_K;
    parse_only = false;
    block_diagram_file = "";
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override {
    string run_from, run_to;
    clear_flags();
    lib_path = design->scratchpad_get_string("rf.lib_path", lib_path);
    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
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
      if (args[argidx] == "-top" && argidx + 1 < args.size()) {
        top_opt = "-top " + args[++argidx];
        continue;
      }
      if (args[argidx] == "-edif" && argidx + 1 < args.size()) {
        edif_file = args[++argidx];
        continue;
      }

      if (args[argidx] == "-family" && argidx + 1 < args.size()) {
        family = args[++argidx];
        continue;
      }
      if (args[argidx] == "-blif" && argidx + 1 < args.size()) {
        blif_file = args[++argidx];
        continue;
      }
      if (args[argidx] == "-cell_map_file" && argidx + 1 < args.size()) {
        cell_map_file = args[++argidx];
        continue;
      }
      if (args[argidx] == "-verilog" && argidx + 1 < args.size()) {
        verilog_file = args[++argidx];
        continue;
      }
      if (args[argidx] == "-K" && argidx + 1 < args.size()) {
        max_lut_size = std::stoi(args[++argidx]);
        continue;
      }
      if (args[argidx] == "-no_dsp") {
        nodsp = true;
        continue;
      }
      if (args[argidx] == "-no_adder") {
        inferAdder = false;
        continue;
      }
      if (args[argidx] == "-no_bram") {
        inferBram = false;
        continue;
      }
      if (args[argidx] == "-no_opt") {
        no_opt = false;
        continue;
      }
      if (args[argidx] == "-parse_only") {
        parse_only = true;
        continue;
      }
      if (args[argidx] == "-help") {
        show_help = true;
        continue;
      }
      if (args[argidx] == "-insert_clock_buffer") {
        insert_clock_buffer = true;
        continue;
      }
      if (args[argidx] == "-save_block_diagram") {
        if (argidx + 1 < args.size() && args[argidx + 1][0] != '-') {
          block_diagram_file = args[++argidx];
        } else {
          block_diagram_file = "";
        }
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);

    if (show_help) {
      help();
      return;
    }

    if (!design->full_selection()) {
      log_cmd_error("This command only operates on fully selected designs!\n");
    }
    /* Pre-check on family name and confirm on selection*/
    if (family != ALKDL_DNAME && family != ALKDT_DNAME &&
        family != ALKDC_DNAME) {
      log_cmd_error("Invalid family specified: '%s'\n", family.c_str());
    }
    log("Selected device family: %s\n", family.c_str());
    /* Force to enable/disable options upon device limits */
    if (family == ALKDL_DNAME || family == ALKDC_DNAME) {
      if (!nodsp) {
        log_warning("Force to disable dsp inference as the selected device "
                    "does not contain dedicated resources\n");
        nodsp = true;
      }
      if (inferBram) {
        log_warning("Force to disable RAM inference as the selected device "
                    "does not contain dedicated resources\n");
        inferBram = false;
      }
    }
    /* By default, no opt should be enabled. Throw a warning if not */
    if (no_opt) {
      log_warning("Force to disable any optimization, which may cast an "
                  "negative impact on QoR\n");
    }
    if (abc9 && design->scratchpad_get_int("abc9.D", 0) == 0) {
      log_warning("Delay target has not been set via SDC or scratchpad; "
                  "Assuming 1GHz clock.\n");
      design->scratchpad_set_int("abc9.W",
                                 1000); // set interconnet delay as 1ns
    }
    /* Sanity checks on max lut size */
    if (max_lut_size < MIN_K || max_lut_size > MAX_K) {
      log_cmd_error(
          "The provided K=%ld is out of the acceptable range [%ld, %ld]!\n",
          max_lut_size, MIN_K, MAX_K);
      return;
    }

    log_header(design, "Executing SYNTH_RAPIDFLEX pass.\n");
    log_push();

    run_script(design, run_from, run_to);
    log_pop();
  }

  void script() override {
    if (help_mode) {
      family = "<family>";
    }

    std::string noDFFArgs;
    if (check_label("begin")) {
      std::string family_path = " " + lib_path + family;
      std::string read_vlog_args;

      // Read simulation library
      read_vlog_args = family_path + "/cell_sim.v";

      // Use -nomem2reg here to prevent Yosys from complaining about
      // some block ram cell models. After all the only part of the cells
      // library required here is cell port definitions plus specify blocks.
      if (parse_only) {
        run("read_verilog " + lib_path + "common/cells_sim.v" + read_vlog_args);
      } else {
        run("read_verilog -lib -specify -nomem2reg " + lib_path +
            "common/cells_sim.v" + read_vlog_args);
      }
      run("logger -werror \"multiple conflicting drivers\"");
      run("check");
      run(stringf("hierarchy -check %s",
                  help_mode ? "-top <top>" : top_opt.c_str()));
      run("stat");
    }

    if (check_label("prepare")) {
      run("proc");
      run("flatten");
      if (parse_only) {
        log("Running parse-only flow. Exit after flattening the design\n");
        return;
      }
      if (help_mode) {
        run("tribuf -logic");
      }
      if (!no_opt) {
        run("opt_expr");
        run("opt_clean");
      }
      run("deminout");
      if (!no_opt) {
        run("opt -nodffe");
      }

      run("check");
      if (!no_opt) {
        run("opt -nodffe");
        run("fsm");
        run("opt -nodffe");
        run("wreduce -keepdc");
        run("peepopt");
        run("pmuxtree");
        run("opt_clean");
        run("share");
      }
    }

    if (check_label("map_dsp"), "(skip if -no_dsp)") {
      struct DspParams {
        size_t a_maxwidth;
        size_t b_maxwidth;
        size_t a_minwidth;
        size_t b_minwidth;
        std::string type;
      };

      const std::vector<DspParams> dsp_rules = {
          {24, 20, 13, 11, "mult_24x20_map"},
          {12, 10, 2, 2, "mult_12x10_map"},
      };

      if (help_mode || family == ALKDT_DNAME) {
        if (help_mode || !nodsp) {
          run("memory_dff", "                      (for alkaidT)");
          if (!no_opt) {
            run("wreduce t:$mul", "                  (for alkaidT)");
          }
          run("rf_new_dsp");
          for (const auto &rule : dsp_rules) {
            run(stringf("techmap -map +/mul2dsp.v "
                        "-map %s/dsp_map.v "
                        "-D DSP_A_MAXWIDTH=%zu -D DSP_B_MAXWIDTH=%zu "
                        "-D DSP_A_MINWIDTH=%zu -D DSP_B_MINWIDTH=%zu "
                        "-D DSP_NAME=%s",
                        std::string(lib_path + family).c_str(), rule.a_maxwidth,
                        rule.b_maxwidth, rule.a_minwidth, rule.b_minwidth,
                        rule.type.c_str()));
            /* Without the following command, some multiplier may be skipped */
            run("chtype -set $mul t:$__soft_mul", "  (for alkaidT)");
          }
          run("select a:mul2dsp", "                (for alkaidT)");
          run("setattr -unset mul2dsp", "          (for alkaidT)");
          if (!no_opt) {
            run("opt_expr -fine", "                  (for alkaidT)");
            run("wreduce", "                         (for alkaidT)");
          }
          run("select -clear", "                   (for alkaidT)");
          // Comment out for further development
          //                    run("rf_dsp", "                          (for
          //                    alkaidT)");
          run("chtype -set $mul t:$__soft_mul", "  (for alkaidT)");
        }
      }
    }

    if (check_label("coarse")) {
      run("techmap -map +/cmp2lut.v -D LUT_WIDTH=5");
      if (!no_opt) {
        run("opt_expr");
        run("opt_clean");
      }
      run("alumacc");
      run("pmuxtree");
      if (!no_opt) {
        run("opt -nodffe");
      }
      run("memory -nomap");
      if (!no_opt) {
        run("opt_clean");
      }
    }

    if (check_label("map_bram", "(skip if -no_bram)") &&
        ((help_mode || family == ALKDT_DNAME) && inferBram)) {
      if (help_mode || family == ALKDT_DNAME) {
        run("memory_bram -rules " + lib_path + family + "/bram.txt");
      }
      /* TODO: Add bram initilization support */
      run("techmap -map " + lib_path + family + "/bram_map.v");
    }
    if (check_label("map_ffram")) {
      if (!no_opt) {
        run("opt -fast -mux_undef -undriven -fine -nodffe");
      }
      run("memory_map");
      if (!no_opt) {
        run("opt -undriven -fine -nodffe");
      }
    }

    if (check_label("map_gates")) {
      if (help_mode ||
          (inferAdder && (family == ALKDL_DNAME || family == ALKDT_DNAME ||
                          family == ALKDC_DNAME))) {
        run("techmap -map +/techmap.v -map " + lib_path + family +
                "/arith_map.v",
            "(unless -no_adder)");
      } else {
        run("techmap");
      }
      if (!no_opt) {
        run("opt -fast -nodffe");
        run("opt_expr");
        run("opt_merge");
        run("opt_clean");
        run("opt -nodffe");
      }
    }

    if (check_label("map_ffs")) {
      run("memory");
      /* TODO: Support shift-register mapping */
      /* Run 2 times dff mapping incase anything missing */
      run("dfflegalize -cell $_DFF_?_ 01 -cell $_DFF_???_ 01 -cell $_SDFF_???_ "
          "01");
      run("techmap -map " + lib_path + family + "/dff_map.v");
      run("dfflegalize -cell $_DFF_?_ 01 -cell $_DFF_???_ 01 -cell $_SDFF_???_ "
          "01");
      run("techmap -map " + lib_path + family + "/dff_map.v");
      run("opt_expr -mux_undef");
      run("simplemap");
      run("opt_expr");
      if (!no_opt) {
        run("opt_merge");
        run("opt_dff -nodffe");
        run("opt_clean");
        run("opt -nodffe");
      }
    }

    if (check_label("map_luts")) {
      run("abc -lut " + std::to_string(max_lut_size));
      /* Map dff and adder again since ABC may generate new gates */
      run("techmap -map " + lib_path + family + "/dff_map.v");
      run("techmap -map " + lib_path + family + "/arith_map.v");
    }

    if (check_label("check")) {
      run("autoname");
      run("hierarchy -check");
      run("stat");
      run("check -noinit");
    }

    if (check_label("finalize")) {
      if (!no_opt) {
        run("opt_clean -purge");
      }
      run("check");
    }

    if (check_label("insert_clock_buffer", "(if -insert_clock_buffer)")) {
      if (insert_clock_buffer) {
        run(stringf("insert_clock_buffer -top %s -cell_map_file %s",
                    top_opt.c_str(), cell_map_file.c_str()));
      }
    }

    if (check_label("blif", "(if -blif)")) {
      if (help_mode || !blif_file.empty()) {
        run(stringf("write_blif -param %s ",
                    help_mode ? "<file-name>" : blif_file.c_str()));
      }
    }

    if (check_label("verilog", "(if -verilog)")) {
      if (help_mode || !verilog_file.empty()) {
        run("write_verilog -noattr -nohex " +
            (help_mode ? "<file-name>" : verilog_file));
      }
    }

    if (check_label("save_block_diagram", "(if -save_block_diagram)")) {
      if (!block_diagram_file.empty()) {
        size_t dot_pos = block_diagram_file.find_last_of('.');
        std::string ext, prefix;
        if (dot_pos != std::string::npos &&
            dot_pos + 1 < block_diagram_file.length()) {
          ext = block_diagram_file.substr(dot_pos + 1);
          prefix = block_diagram_file.substr(0, dot_pos);
        } else {
          ext = "dot";
          prefix = block_diagram_file;
        }
        if (ext != "dot" && ext != "png" && ext != "svg" && ext != "eps" &&
            ext != "pdf") {
          log_cmd_error("Unsupported block diagram file format: %s. Supported "
                        "formats: dot, png, svg, eps, pdf\n",
                        ext.c_str());
          return;
        }
        run(stringf("show -format %s -prefix %s", ext.c_str(), prefix.c_str()));
      } else {
        run("show -format dot");
      }
    }
  }

} SynthRapidFlexPass;

PRIVATE_NAMESPACE_END
