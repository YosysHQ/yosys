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

#include "passes/opt/rewrite_utils.h"

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

// Fuse a modular gather with the variable shift feeding it. opt_vps lowers a
// bit-select farm to one $shr over its table rotated by a constant and padded
// with x, so when that table is a shifter output the two barrels sit back to
// back and -combine cannot merge them: the rotation leaves the outer A port a
// permutation of the inner Y rather than the same SigSpec.
//
//   out[t] = pad_M(x << b)[(t + a + r) % M]
//     ===>  out[t] = pad_M(x & (~0 >> b))[(t + a + r - b) % M]
//
// Masking x drops the high bits the rotate would otherwise wrap in underneath
// the left shift's zero fill, which is the only place the two disagree. What is
// left is a single barrel over a repeated source, so one shifter leaves every
// path through the gather in exchange for a mask that depends on b alone.
// The shifter itself stays if other cells read it; opt_clean sweeps it if not.
struct GatherFuser
{
  Module *module;
  SigMap sigmap;
  dict<SigBit, Cell *> drivers;
  int max_src_bits;
  int fused = 0;

  GatherFuser(Module *module, int max_src_bits)
    : module(module), sigmap(module), max_src_bits(max_src_bits)
  {
    for (auto cell : module->cells())
      for (auto &conn : cell->connections())
        if (cell->output(conn.first))
          for (auto bit : sigmap(conn.second))
            drivers[bit] = cell;
  }

  // Read `outer`'s A port as one $shl output rotated by a constant: every
  // defined bit must be inner_y[(j + rot) % mod] for a single rot, and every x
  // must rotate above inner_y, where it was padding rather than a table entry.
  Cell *match_rotated_source(Cell *outer, int &rot, int &mod)
  {
    SigSpec s = sigmap(outer->getPort(ID::A));

    Cell *inner = nullptr;
    for (auto bit : s) {
      if (!bit.is_wire())
        continue;
      auto it = drivers.find(bit);
      if (it == drivers.end() || (inner && it->second != inner))
        return nullptr;
      inner = it->second;
    }
    if (!inner || inner->type != ID($shl) || inner->getPort(ID::B).is_fully_const())
      return nullptr;
    if (inner->getParam(ID::A_SIGNED).as_bool() || inner->getParam(ID::B_SIGNED).as_bool())
      return nullptr;

    SigSpec iy = sigmap(inner->getPort(ID::Y));
    int wy = GetSize(iy);
    if (wy < 2 || wy > (1 << 20)) // keep the table and 1 << clog2 in range
      return nullptr;
    mod = 1 << clog2_int(wy);
    if (GetSize(sigmap(inner->getPort(ID::A))) > mod) // mask is only mod bits wide
      return nullptr;

    dict<SigBit, int> index;
    for (int i = 0; i < wy; i++)
      index.emplace(iy[i], i);

    rot = -1;
    for (int j = 0; j < GetSize(s); j++) {
      if (s[j] == State::Sx)
        continue;
      auto it = index.find(s[j]);
      if (it == index.end()) // a defined bit from anywhere but inner_y
        return nullptr;
      int r = ((it->second - j) % mod + mod) % mod;
      if (rot < 0)
        rot = r;
      else if (rot != r)
        return nullptr;
    }
    if (rot < 0)
      return nullptr;

    // An x rotating onto a real inner_y bit was a table entry, not padding
    for (int j = 0; j < GetSize(s); j++)
      if (s[j] == State::Sx && (j + rot) % mod < wy)
        return nullptr;

    return inner;
  }

  // Largest value an amount can take, discounting constant-zero high bits
  int max_amount(SigSpec amt)
  {
    int w = GetSize(amt);
    while (w > 0 && amt[w - 1] == State::S0)
      w--;
    return w > 20 ? -1 : (1 << w) - 1;
  }

  void fuse(Cell *outer, Cell *inner, int rot, int mod)
  {
    SigSpec x = sigmap(inner->getPort(ID::A));
    SigSpec b = sigmap(inner->getPort(ID::B));
    SigSpec a = sigmap(outer->getPort(ID::B));
    int wx = GetSize(x), wo = outer->getParam(ID::Y_WIDTH).as_int();
    int amt_bits = clog2_int(mod);
    std::string src = cell_src(outer);

    // keep[u] = u < mod - b, the positions the left shift did not zero out.
    // Shifting a constant lowers to a decoder, and it depends only on b, so
    // the mask costs no depth on the data path.
    Wire *keep = module->addWire(NEW_ID_SUFFIX("shift_fuse_keep"), mod);
    module->addShr(NEW_ID_SUFFIX("shift_fuse_keep_shr"), Const(State::S1, mod), b,
                   SigSpec(keep), false, src);
    Wire *masked = module->addWire(NEW_ID_SUFFIX("shift_fuse_a"), wx);
    module->addAnd(NEW_ID_SUFFIX("shift_fuse_and"), x, SigSpec(keep).extract(0, wx),
                   SigSpec(masked), false, src);

    // amt = (a + rot - b) mod `mod`, wrapped by the amt_bits-wide arithmetic
    Wire *sum = module->addWire(NEW_ID_SUFFIX("shift_fuse_rot"), amt_bits);
    module->addAdd(NEW_ID_SUFFIX("shift_fuse_add"), a, const_u64(rot, amt_bits),
                   SigSpec(sum), false, src);
    Wire *amt = module->addWire(NEW_ID_SUFFIX("shift_fuse_amt"), amt_bits);
    module->addSub(NEW_ID_SUFFIX("shift_fuse_sub"), SigSpec(sum), b, SigSpec(amt),
                   false, src);

    // Repeating the masked source turns the modular access into a plain shift
    SigSpec period = SigSpec(masked);
    period.append(SigSpec(State::S0, mod - wx));
    SigSpec source;
    while (GetSize(source) < wo + mod - 1)
      source.append(period);
    source = source.extract(0, wo + mod - 1);

    log("  shift fuse: %s absorbs %s (M=%d, rot=%d, src=%d bits)\n",
        log_id(outer->name), log_id(inner->name), mod, rot, GetSize(source));

    // The shifter stays for its other readers; opt_clean sweeps it when the
    // gather was the only one
    outer->setPort(ID::A, source);
    outer->setPort(ID::B, SigSpec(amt));
    outer->fixup_parameters();
    fused++;
  }

  // Fuse at most one gather, so the caller reindexes before looking for more
  bool run()
  {
    for (auto cell : module->selected_cells()) {
      if (cell->type != ID($shr) || cell->getPort(ID::B).is_fully_const())
        continue;
      if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
        continue;

      int rot, mod;
      Cell *inner = match_rotated_source(cell, rot, mod);
      if (!inner)
        continue;

      // A gather that can shift past its source zero-fills there, where the
      // rotate would instead wrap the table back around
      int wo = cell->getParam(ID::Y_WIDTH).as_int();
      int amax = max_amount(sigmap(cell->getPort(ID::B)));
      if (amax < 0 || wo - 1 + amax >= GetSize(cell->getPort(ID::A)))
        continue;
      if (wo + mod - 1 > max_src_bits)
        continue;

      fuse(cell, inner, rot, mod);
      return true;
    }
    return false;
  }
};

#include "passes/silimate/peepopt_shift_pm.h"
#include "passes/silimate/peepopt_sink_pm.h"

struct OptShiftPass : public Pass {
  OptShiftPass() : Pass("opt_shift", "shift optimizations: combine, expand, sink and fuse") { }
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
    log("  -fuse\n");
    log("      Fuse a modular gather with the variable left shift feeding it,\n");
    log("      which -combine cannot do because the gather rotates its table:\n");
    log("        pad_M(x << b)[(t + a + r) %% M]\n");
    log("          ===>  pad_M(x & (~0 >> b))[(t + a + r - b) %% M]\n");
    log("      Masking x replaces the zero fill the rotate would wrap around,\n");
    log("      so two barrels on the data path become one plus a mask that\n");
    log("      depends only on b. Only fires when the gather cannot shift past\n");
    log("      its own source, where it zero-fills but a rotate would wrap.\n");
    log("\n");
    log("  -max_fuse_bits n\n");
    log("      refuse a -fuse rewrite whose repeated source would exceed n\n");
    log("      bits (default 4096).\n");
    log("\n");
    log("  -max_iters n\n");
    log("      max number of pass iterations to run.\n");
    log("\n");
    log("If none of -combine, -expand, -sink or -fuse is given, combine and\n");
    log("expand are run.\n");
    log("\n");
  }
  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing OPT_SHIFT pass (shift optimizations).\n");

    bool run_combine = false;
    bool run_expand = false;
    bool run_sink = false;
    bool run_fuse = false;
    int max_fuse_bits = 4096;
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
      if (args[argidx] == "-fuse") {
        run_fuse = true;
        continue;
      }
      if (args[argidx] == "-max_fuse_bits" && argidx + 1 < args.size()) {
        max_fuse_bits = std::stoi(args[++argidx]);
        continue;
      }
      if (args[argidx] == "-max_iters" && argidx + 1 < args.size()) {
        max_iters = std::stoi(args[++argidx]);
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);

    if (!run_combine && !run_expand && !run_sink && !run_fuse) {
      run_combine = true;
      run_expand = true;
    }

    // -expand undoes -sink on $add, so they would ping-pong until max_iters
    if (run_expand && run_sink)
      log_cmd_error("opt_shift: -expand and -sink are inverses, pick one.\n");

    int total_fused = 0;
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
        // Same pre-filter: a gather only fuses with a variable-amount shifter
        if (run_fuse && has_variable_shift(module)) {
          GatherFuser fuser(module, max_fuse_bits);
          did_something |= fuser.run();
          total_fused += fuser.fused;
        }
      }
    }

    if (run_fuse)
      log("Fused %d gather(s) with the shift feeding them.\n", total_fused);
  }
} OptShiftPass;

PRIVATE_NAMESPACE_END
