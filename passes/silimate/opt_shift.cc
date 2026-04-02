/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                      Akash Levy <akash@silimate.com>
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
#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool did_something;

#include "passes/silimate/peepopt_shift.h"

struct OptShiftPass : public Pass {
  OptShiftPass() : Pass("opt_shift", "shift optimizations: combine and expand") { }
  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    opt_shift [options] [selection]\n");
    log("\n");
    log("This pass performs shift optimizations.\n");
    log("\n");
    log("  -combine\n");
    log("      Combine nested shift operations (works with all\n");
    log("      combinations of $shl/$sshl and $shr/$sshr):\n");
    log("        (a <</<< b) <</<< c    ===>  a <</<< (b + c)\n");
    log("        (a >>>/>> b) >>>/>> c  ===>  a >>>/>> (b + c)\n");
    log("        (a <</<< b) >>>/>> c   ===>  a <</<< (b - c)\n");
    log("        (a >>>/>> b) <</<< c   ===>  a >>>/>> (b - c)\n");
    log("      Result uses the inner shift's type.\n");
    log("\n");
    log("  -expand\n");
    log("      Expand shifts across binary operations:\n");
    log("        (a OP b) << c    ===>  (a << c) OP (b << c)\n");
    log("        (a OP b) >> c    ===>  (a >> c) OP (b >> c)\n");
    log("        where OP in {$and, $or, $xor, $add, $sub}\n");
    log("\n");
    log("  -max_iters n\n");
    log("      max number of pass iterations to run.\n");
    log("\n");
    log("If neither -combine nor -expand is given, both are run.\n");
    log("\n");
  }
  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing OPT_SHIFT pass (shift optimizations).\n");

    bool run_combine = false;
    bool run_expand = false;
    int max_iters = 10000;

    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
      if (args[argidx] == "-combine") {
        run_combine = true;
        continue;
      }
      if (args[argidx] == "-expand") {
        run_expand = true;
        continue;
      }
      if (args[argidx] == "-max_iters" && argidx + 1 < args.size()) {
        max_iters = std::stoi(args[++argidx]);
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);

    if (!run_combine && !run_expand) {
      run_combine = true;
      run_expand = true;
    }

    for (auto module : design->selected_modules())
    {
      did_something = true;
      for (int i = 0; did_something && i < max_iters; i++)
      {
        did_something = false;
        peepopt_pm pm(module);
        pm.setup(module->selected_cells());
        if (run_combine)
          pm.run_combine_shifts();
        if (run_expand)
          pm.run_expand_shifts();
      }
    }
  }
} OptShiftPass;

PRIVATE_NAMESPACE_END
