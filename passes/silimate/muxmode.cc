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

#include "passes/silimate/peepopt_muxmode.h"

struct MuxmodePass : public Pass {
  MuxmodePass() : Pass("muxmode", "convert primitives to muxes") { }
  void help() override
  {
    //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log("    muxmode [selection]\n");
    log("\n");
    log("This pass makes muxes of 1-bit primitives having an input coming from a mux.\n");
		log("\n");
  }
  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing MUXMODE pass (make muxes from 1-bit primitives).\n");

    size_t argidx = 1;
    extra_args(args, argidx, design);

    for (auto module : design->selected_modules())
    {
      did_something = true;
      for (int i = 0; did_something; i++)
      {
        log("ITERATION %d OF MUXMODE\n", i);
        did_something = false;
        peepopt_pm pm(module);
        pm.setup(module->selected_cells());
        pm.run_muxmode();
        pm.run_muxinvprop();
      }
    }
  }
} PeepoptPass;

PRIVATE_NAMESPACE_END
