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

// Driver index for the module being processed, rebuilt per module by the sink
// pattern so it can walk back from a shift amount to the cell producing it.
SigMap sink_sigmap;
dict<SigBit, Cell *> sink_drivers;

void sink_index_module(Module *module)
{
  sink_sigmap.set(module);
  sink_drivers.clear();
  for (auto cell : module->cells())
    for (auto &conn : cell->connections())
      if (cell->output(conn.first))
        for (auto bit : sink_sigmap(conn.second))
          sink_drivers[bit] = cell;
}

// Cheap pre-filter for the sink pattern: a constant amount is already folded by
// -combine, so without a variable shifter there is nothing for -sink to match.
bool has_variable_shift(Module *module)
{
  for (auto cell : module->selected_cells())
    if (cell->type == ID($shl) && !cell->getPort(ID::B).is_fully_const())
      return true;
  return false;
}

int min_shift_amount(SigSpec amt, int depth = 3);

// Lower bound on `chunk`, which must be the complete output of `drv`. Only
// unsigned "var + const" is understood; anything else contributes nothing.
int min_driven_value(Cell *drv, const SigSpec &chunk, int depth)
{
  if (drv->type != ID($add))
    return 0;
  if (drv->getParam(ID::A_SIGNED).as_bool() || drv->getParam(ID::B_SIGNED).as_bool())
    return 0;
  if (sink_sigmap(drv->getPort(ID::Y)) != chunk)
    return 0;

  SigSpec a = sink_sigmap(drv->getPort(ID::A)), b = sink_sigmap(drv->getPort(ID::B));
  bool a_const = a.is_fully_const();
  SigSpec cst = a_const ? a : b, var = a_const ? b : a;
  if (!cst.is_fully_const() || !cst.is_fully_def() || GetSize(var) > 24)
    return 0;

  // as_int truncates, which stays correct modulo the chunk width, but a set
  // bit 31 would come back negative and poison the shift in the caller
  int c = cst.as_int();
  if (c < 0)
    return 0;

  // A sum that can wrap would break the bound, so require it to always fit
  if (((1 << GetSize(var)) - 1) + c >= (1 << GetSize(chunk)))
    return 0;
  return c + min_shift_amount(var, depth - 1);
}

// Sound lower bound on the value a shift amount can take. A sum is at least
// the sum of its parts' minima, so each maximal same-driver run of bits is
// bounded on its own and the pieces are weighted back in by bit position.
// Under-estimates rather than over-estimates, so callers stay safe.
int min_shift_amount(SigSpec amt, int depth)
{
  amt = sink_sigmap(amt);
  if (GetSize(amt) > 24) // keep the shifts below inside int range
    return 0;

  int bound = 0;
  for (int i = 0; i < GetSize(amt); ) {
    // Constant bits are set in every reachable value
    if (!amt[i].is_wire()) {
      if (amt[i] == State::S1)
        bound += 1 << i;
      i++;
      continue;
    }
    if (depth <= 0 || !sink_drivers.count(amt[i])) {
      i++;
      continue;
    }

    // Extend over the run of bits fed by the same cell
    Cell *drv = sink_drivers.at(amt[i]);
    int j = i;
    while (j < GetSize(amt) && amt[j].is_wire() && sink_drivers.count(amt[j]) &&
           sink_drivers.at(amt[j]) == drv)
      j++;

    bound += min_driven_value(drv, amt.extract(i, j - i), depth) << i;
    i = j;
  }
  return bound;
}

#include "passes/silimate/peepopt_shift_pm.h"
#include "passes/silimate/peepopt_sink_pm.h"

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
    log("  -sink\n");
    log("      Sink an add through a left shift, so the adder leaves the\n");
    log("      shifter output and can merge with the arithmetic feeding it:\n");
    log("        (x << s) + z    ===>  ((x + (z >> s)) << s) | (z & ~(~0 << s))\n");
    log("      Requires a provable nonzero minimum for s, which is what makes\n");
    log("      (z >> s) narrower than z. This is the inverse of -expand on\n");
    log("      $add, so the two must not be requested together.\n");
    log("\n");
    log("  -max_iters n\n");
    log("      max number of pass iterations to run.\n");
    log("\n");
    log("If none of -combine, -expand or -sink is given, combine and expand\n");
    log("are run.\n");
    log("\n");
  }
  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing OPT_SHIFT pass (shift optimizations).\n");

    bool run_combine = false;
    bool run_expand = false;
    bool run_sink = false;
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
      if (args[argidx] == "-sink") {
        run_sink = true;
        continue;
      }
      if (args[argidx] == "-max_iters" && argidx + 1 < args.size()) {
        max_iters = std::stoi(args[++argidx]);
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);

    if (!run_combine && !run_expand && !run_sink) {
      run_combine = true;
      run_expand = true;
    }

    // -expand undoes -sink on $add, so they would ping-pong until max_iters
    if (run_expand && run_sink)
      log_cmd_error("opt_shift: -expand and -sink are inverses, pick one.\n");

    for (auto module : design->selected_modules())
    {
      did_something = true;
      for (int i = 0; did_something && i < max_iters; i++)
      {
        did_something = false;
        if (run_combine || run_expand) {
          peepopt_shift_pm pm(module);
          pm.setup(module->selected_cells());
          if (run_combine)
            pm.run_combine_shifts();
          if (run_expand)
            pm.run_expand_shifts();
        }
        // Indexing the drivers and every $add is only worth it once we know a
        // variable-amount shifter exists; most modules have none and skip it
        if (run_sink && has_variable_shift(module)) {
          sink_index_module(module);
          peepopt_sink_pm pm(module);
          pm.setup(module->selected_cells());
          pm.run_sink_shifts();
        }
      }
    }
  }
} OptShiftPass;

PRIVATE_NAMESPACE_END
