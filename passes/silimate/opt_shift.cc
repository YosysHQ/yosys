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

// Compose two back-to-back barrels that -combine cannot see, because the outer
// one reads its operand as a constant-padded slice rather than as the inner Y
// whole. That spelling is what a part-select or an opt_vps gather table leaves
// behind, and it is the usual reason a datapath of cascaded variable shifts
// keeps every one of its barrels.
//
//   out[j] = pad(in_y)[j + so*c],  pad(in_y)[k] = in_y[k + off],
//   in_y[m] = in_a[m + si*b]
//     ===>  out[j] = in_a[j + so*c + si*b + off]
//
// Unlike -fuse this stays a plain shift: the amount is the signed sum of the two
// rather than a residue, so it needs clog2 of their sum rather than of the
// modulus, and the barrel it leaves is narrower than the pair it replaces. The
// sum can go negative where the two shifts oppose, so the A port is pre-padded
// by that much and the padding absorbs it, keeping one unsigned $shr.
struct ChainCombiner
{
  Module *module;
  SigMap sigmap;
  dict<SigBit, Cell *> drivers;
  dict<SigBit, int> readers;
  int max_pad_bits;
  bool keep_live_inner;
  int combined = 0;

  ChainCombiner(Module *module, int max_pad_bits, bool keep_live_inner)
    : module(module), sigmap(module), max_pad_bits(max_pad_bits),
      keep_live_inner(keep_live_inner)
  {
    for (auto cell : module->cells())
      for (auto &conn : cell->connections()) {
        for (auto bit : sigmap(conn.second))
          if (cell->output(conn.first))
            drivers[bit] = cell;
          else
            readers[bit]++;
      }
    // A module port reads without being a cell, so count it as a reader or the
    // inner shift looks dead and its output gets rewritten out from under it.
    for (auto wire : module->wires())
      if (wire->port_output)
        for (auto bit : sigmap(wire))
          readers[bit]++;
  }

  static bool is_plain_shift(Cell *cell)
  {
    return cell != nullptr && cell->type.in(ID($shl), ID($shr)) &&
           !cell->getPort(ID::B).is_fully_const() &&
           !cell->getParam(ID::A_SIGNED).as_bool() &&
           !cell->getParam(ID::B_SIGNED).as_bool();
  }

  // +1 for a right shift, -1 for a left one, so both read Y[j] = A[j + sgn*amt]
  static int direction(Cell *cell) { return cell->type == ID($shr) ? 1 : -1; }

  // Read `outer`'s A port as one shift's Y at a constant offset: every wire bit
  // at position k must be inner_y[k + off] for a single off. Constant lanes are
  // padding and are checked against the composed index separately.
  Cell *match_padded_source(Cell *outer, int &off, const char **why)
  {
    auto no = [&](const char *reason) -> Cell * { *why = reason; return nullptr; };
    SigSpec s = sigmap(outer->getPort(ID::A));

    Cell *inner = nullptr;
    for (auto bit : s) {
      if (!bit.is_wire())
        continue;
      auto it = drivers.find(bit);
      if (it == drivers.end())
        return no("operand bit has no driver");
      if (inner && it->second != inner)
        return no("operand spans several drivers");
      inner = it->second;
    }
    if (!is_plain_shift(inner))
      return no("operand is not driven by a variable shift");

    SigSpec iy = sigmap(inner->getPort(ID::Y));
    dict<SigBit, int> index;
    for (int i = 0; i < GetSize(iy); i++)
      index.emplace(iy[i], i);

    // The inner barrel normally has to die here, or the rewrite adds one
    // instead of moving it. Under -chain-keep it may survive for its other
    // readers, trading that barrel's area for the depth this path saves.
    if (!keep_live_inner)
      for (int i = 0; i < GetSize(iy); i++)
        if (readers.count(iy[i]) && readers.at(iy[i]) > 1)
          return no("inner output has a reader that outlives the rewrite");

    bool have_off = false;
    for (int j = 0; j < GetSize(s); j++) {
      if (!s[j].is_wire())
        continue;
      auto it = index.find(s[j]);
      if (it == index.end()) // a wire bit from anywhere but inner_y
        return no("operand mixes inner output with other logic");
      int o = it->second - j;
      if (!have_off)
        off = o, have_off = true;
      else if (off != o) // a permutation, not a slice: that is -fuse's shape
        return no("operand permutes the inner output rather than slicing it");
    }
    return have_off ? inner : no("operand is all constant");
  }

  // Range of an amount, read off its own bits: a lane that is not a constant 0
  // can be set, and only a constant 1 must be. Local and sound, where
  // min_shift_amount would need the -sink index this pass has not built.
  bool amount_range(Cell *cell, int &lo, int &hi, int &bits)
  {
    SigSpec amt = sigmap(cell->getPort(ID::B));
    bits = GetSize(amt);
    while (bits > 0 && amt[bits - 1] == State::S0)
      bits--;
    if (bits > 20) // keep 1 << bits and the sums below inside int range
      return false;
    lo = 0, hi = 0;
    for (int i = 0; i < bits; i++) {
      if (amt[i] != State::S0)
        hi += 1 << i;
      if (amt[i] == State::S1)
        lo += 1 << i;
    }
    return true;
  }

  // Bounds on sgn*amt, so both directions read out[j] = in[j + sgn*amt]
  bool signed_amount_range(Cell *cell, int sgn, int &lo, int &hi, int &bits)
  {
    int amin, amax;
    if (!amount_range(cell, amin, amax, bits))
      return false;
    if (sgn > 0)
      lo = amin, hi = amax;
    else
      lo = -amax, hi = -amin;
    return true;
  }

  bool run_cell(Cell *outer)
  {
    auto no = [&](const char *why) {
      log_debug("    chain %s: %s\n", log_id(outer->name), why);
      return false;
    };
    if (!is_plain_shift(outer))
      return false;

    int off = 0;
    const char *why = "";
    Cell *inner = match_padded_source(outer, off, &why);
    if (inner == nullptr)
      return no(why);

    int so = direction(outer), si = direction(inner);
    // Only gather leftover `(x << b) >> c`. Inverse align `(x >> b) << c`
    // composed 15 times on qor_fold_tree_2 and cost 4 LoL.
    if (so <= 0 || si >= 0)
      return no("not a right-shift of a leftover left-shift");
    int olo, ohi, ilo, ihi, obits, ibits;
    if (!signed_amount_range(outer, so, olo, ohi, obits) ||
        !signed_amount_range(inner, si, ilo, ihi, ibits))
      return no("amount too wide to bound");

    // out[j] = in_a[j + n] over n in [nlo, nhi]; pad the operand by -nlo so the
    // amount the new barrel takes is unsigned.
    int nlo = olo + ilo + off, nhi = ohi + ihi + off;
    int pad = nlo < 0 ? -nlo : 0;
    if (nhi + pad < 0)
      return no("composed amount range is empty");

    SigSpec in_a = sigmap(inner->getPort(ID::A));
    int wo = outer->getParam(ID::Y_WIDTH).as_int();
    if (pad > max_pad_bits || GetSize(in_a) + pad > max_pad_bits)
      return no("padded operand over -max_chain_pad");

    // The new barrel is one level per amount bit, so it only pays when the one
    // amount is narrower than the two it replaces; equal width would just
    // relocate a barrel and grow the operand.
    int new_bits = clog2_int(nhi + pad + 1);
    if (new_bits < 1 || new_bits >= obits + ibits)
      return no(stringf("no narrower: %d bits vs %d + %d", new_bits, obits,
                        ibits).c_str());

    if (!fill_agrees(outer, off, si, ilo, ihi, GetSize(in_a)))
      return no("a constant lane or a truncated read has no matching fill");

    rewrite(outer, inner, off, so, si, pad, new_bits, in_a, wo);
    return true;
  }

  // Where the outer barrel reads a constant lane or reads past its own operand
  // it produces the shift's own fill, which the composed index has to reproduce
  // by landing outside the inner operand. An x lane is free: refining a don't
  // care is always allowed.
  bool fill_agrees(Cell *outer, int off, int si, int ilo, int ihi, int w_in_a)
  {
    SigSpec s = sigmap(outer->getPort(ID::A));
    int wo = outer->getParam(ID::Y_WIDTH).as_int();
    int olo, ohi, obits;
    if (!signed_amount_range(outer, direction(outer), olo, ohi, obits))
      return false;
    (void)si;

    // Reading past the top of the operand zero-fills, and the composed form has
    // no such edge, so require that the outer barrel cannot reach there.
    if (wo - 1 + ohi >= GetSize(s))
      return false;

    for (int k = 0; k < GetSize(s); k++) {
      if (s[k].is_wire() || s[k] == State::Sx)
        continue;
      if (s[k] != State::S0) // a defined 1 is not a fill any shift produces
        return false;
      // Reachable at all? k = j + so*c for some output lane and amount.
      if (k < olo || k > wo - 1 + ohi)
        continue;
      // in_a index is k + off + si*b; both ends must miss the operand.
      int lo = k + off + ilo, hi = k + off + ihi;
      if (!(hi < 0 || lo >= w_in_a))
        return false;
    }
    return true;
  }

  void rewrite(Cell *outer, Cell *inner, int off, int so, int si, int pad,
               int new_bits, const SigSpec &in_a, int wo)
  {
    std::string src = cell_src(outer);
    SigSpec b = sigmap(inner->getPort(ID::B));
    SigSpec c = sigmap(outer->getPort(ID::B));

    // amt = so*c + si*b + (pad + off). Every term is reduced mod 2^w, and the
    // value it lands on is in range by construction, so a bias that is itself
    // negative is just its two's complement. The two amounts come off
    // configuration, so this arithmetic sits beside the barrel, not on the path
    // through it.
    int w = new_bits;
    int bias = ((pad + off) % (1 << w) + (1 << w)) % (1 << w);
    SigSpec acc = SigSpec(module->addWire(NEW_ID_SUFFIX("shift_chain_acc"), w));
    SigSpec amt = SigSpec(module->addWire(NEW_ID_SUFFIX("shift_chain_amt"), w));

    auto accumulate = [&](const SigSpec &lhs, const SigSpec &rhs, int sgn,
                          const SigSpec &out) {
      if (sgn > 0)
        module->addAdd(NEW_ID_SUFFIX("shift_chain_add"), lhs, rhs, out, false, src);
      else
        module->addSub(NEW_ID_SUFFIX("shift_chain_sub"), lhs, rhs, out, false, src);
    };
    accumulate(const_u64(bias, w), c, so, acc);
    accumulate(acc, b, si, amt);

    // Pre-padding the operand is what lets the amount stay unsigned; the lanes
    // it adds are only ever read where the original produced its zero fill.
    SigSpec source = SigSpec(State::S0, pad);
    source.append(in_a);

    log("  shift chain: %s absorbs %s (off=%d, pad=%d, %d -> %d amt bits)\n",
        log_id(outer->name), log_id(inner->name), off, pad,
        GetSize(b) + GetSize(c), w);

    outer->type = ID($shr);
    outer->setPort(ID::A, source);
    outer->setPort(ID::B, amt);
    outer->setParam(ID::Y_WIDTH, wo);
    outer->fixup_parameters();
    combined++;
  }

  // Compose at most one pair, so the caller reindexes before looking for more
  bool run()
  {
    for (auto cell : module->selected_cells())
      if (run_cell(cell))
        return true;
    return false;
  }
};

// ---------------------------------------------------------------------------
// -descale: collapse a scale-down round trip around a variable right shift
//
//   ((x + 1) >> s) - 1   ===>   c ? (x >> s) : (x >> s) - 1,  c = &x[s-1:0]
//
// Writing x = t*2^s + r, the shift throws r away, so the only thing the
// increment can still contribute past it is its carry out of that window, which
// is exactly c (vacuously true for s == 0). Absorbing that carry downstream
// leaves one carry chain instead of two bracketing the shifter, and the window
// test is a log-depth AND scan that runs beside it rather than ahead of it.
// ---------------------------------------------------------------------------

// Unsigned constant 1 of any width
bool descale_is_one(const SigSpec &sig)
{
  return GetSize(sig) > 0 && sig.is_fully_const() && sig.as_const() == Const(1, GetSize(sig));
}

// `out - 1`, reading `out` from bit 0 up. A narrower read is fine: the carry
// identity holds mod 2^k for any k, so a decrement that wreduce has already
// narrowed to what its own result needs still folds.
bool descale_is_decrement(SigMap &sigmap, Cell *reader, const SigSpec &out)
{
  if (reader->type != ID($sub))
    return false;
  if (reader->getParam(ID::A_SIGNED).as_bool() || reader->getParam(ID::B_SIGNED).as_bool())
    return false;
  if (!descale_is_one(reader->getPort(ID::B)))
    return false;
  SigSpec a = sigmap(reader->getPort(ID::A));
  int common = std::min(GetSize(a), GetSize(out));
  if (common == 0 || a.extract(0, common) != out.extract(0, common))
    return false;
  return a.extract_end(common).is_fully_zero();
}

// `out == 0`, in any of the shapes opt_expr leaves behind. Unlike the decrement
// this has to read all of `out`: at full width t + c cannot carry out, so the
// carry is just another bit to test, but a narrower read can wrap into zero.
bool descale_is_zero_test(SigMap &sigmap, Cell *reader, const SigSpec &out)
{
  if (reader->type.in(ID($logic_not), ID($reduce_or), ID($reduce_bool)))
    return sigmap(reader->getPort(ID::A)) == out;
  if (reader->type.in(ID($eq), ID($ne))) {
    if (reader->getParam(ID::A_SIGNED).as_bool() || reader->getParam(ID::B_SIGNED).as_bool())
      return false;
    SigSpec a = sigmap(reader->getPort(ID::A));
    SigSpec b = sigmap(reader->getPort(ID::B));
    if (a == out)
      return b.is_fully_zero();
    if (b == out)
      return a.is_fully_zero();
  }
  return false;
}

// True when every bit of the (already sigmapped) `sig` stays inside the module,
// so this pass is allowed to change what it carries
bool descale_contained(const SigSpec &sig)
{
  for (auto bit : sig)
    if (!bit.wire || bit.wire->port_output || bit.wire->get_bool_attribute(ID::keep))
      return false;
  return true;
}

// Inclusive AND scan of x, so scan[i] = &x[i:0], in ceil(log2(width)) levels
SigSpec descale_and_scan(Cell *cell, const SigSpec &x)
{
  Module *module = cell->module;
  SigSpec scan = x;
  for (int stride = 1; stride < GetSize(x); stride *= 2) {
    int width = GetSize(x) - stride;
    Wire *merged = module->addWire(NEW_ID2_SUFFIX("wnd"), width);
    module->addAnd(NEW_ID2_SUFFIX("wnd"), scan.extract(stride, width),
                   scan.extract(0, width), merged, false, cell->get_src_attribute());
    SigSpec next = scan.extract(0, stride);
    next.append(merged);
    scan = next;
  }
  return scan;
}

// One matched round trip: the shifter is kept and rewired, its readers absorb
// the increment as a window carry, and the increment itself goes away.
struct DescaleRewrite {
  Cell *shr;
  Cell *add;
  SigSpec x;
  SigSpec out;
  vector<Cell *> decs;
  vector<Cell *> zeros;
};

// Unsigned variable right shifts, keyed by the bits they read. Anchoring on the
// shifters first keeps the common case (a design with no round trip) down to one
// walk, with nothing indexed per design bit behind it.
void descale_find_anchors(Module *module, SigMap &sigmap, dict<SigBit, Cell *> &anchors)
{
  vector<Cell *> shifts;
  for (auto cell : module->selected_cells()) {
    if (cell->type != ID($shr) || cell->getParam(ID::A_SIGNED).as_bool())
      continue;

    // A constant amount is folded by -combine, and it makes the window carry
    // constant anyway, so there is no round trip left to break
    if (cell->getPort(ID::B).is_fully_const())
      continue;

    // The rewrite rescales the shifter in place and renames it, which keep forbids
    if (cell->get_bool_attribute(ID::keep))
      continue;

    shifts.push_back(cell);
  }

  // Binding the SigMap is a walk of the module in itself, so leave it unbound
  // for the common case of a module with no variable right shift at all
  if (shifts.empty())
    return;
  sigmap.set(module);

  for (auto cell : shifts)
    for (auto bit : sigmap(cell->getPort(ID::A))) {
      if (!bit.wire)
        continue;
      // Two shifters on one bit means whatever drives it is shared and so cannot
      // be deleted; the null marker rejects both of them
      auto it = anchors.find(bit);
      anchors[bit] = (it == anchors.end() || it->second == cell) ? cell : nullptr;
    }
}

// Increments feeding an anchor: a whole "+1" that is all the shifter reads
void descale_find_candidates(Module *module, SigMap &sigmap, const dict<SigBit, Cell *> &anchors,
                             vector<DescaleRewrite> &candidates)
{
  for (auto cell : module->selected_cells()) {
    if (cell->type != ID($add))
      continue;
    if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
      continue;
    // The rewrite deletes the increment outright, which keep forbids
    if (cell->get_bool_attribute(ID::keep))
      continue;

    // Every bit of the sum has to land on one and the same shifter
    SigSpec sum = sigmap(cell->getPort(ID::Y));
    Cell *shr = nullptr;
    bool whole = GetSize(sum) > 0;
    for (auto bit : sum) {
      auto it = anchors.find(bit);
      if (it == anchors.end() || !it->second || (shr && it->second != shr)) {
        whole = false;
        break;
      }
      shr = it->second;
    }
    if (!whole)
      continue;

    // The shifter may read the sum zero-extended: RTL that declares the scaled
    // word wider than the increment needs leaves hard zeros above the sum, and
    // shifting a zero right is still a zero. Anything else up there is a value
    // the rescaled shifter, which reads x rather than the sum, cannot reproduce.
    SigSpec shifted = sigmap(shr->getPort(ID::A));
    if (GetSize(shifted) < GetSize(sum) || shifted.extract(0, GetSize(sum)) != sum ||
        !shifted.extract_end(GetSize(sum)).is_fully_zero())
      continue;

    SigSpec a = cell->getPort(ID::A), b = cell->getPort(ID::B);
    SigSpec x = descale_is_one(b) ? a : descale_is_one(a) ? b : SigSpec();
    if (GetSize(x) == 0)
      continue;

    // A truncating increment breaks the carry identity: an all-ones x wraps to
    // 0 instead of carrying into bit width(x)
    if (GetSize(sum) <= GetSize(x))
      continue;

    candidates.push_back({shr, cell, x, sigmap(shr->getPort(ID::Y)), {}, {}});
  }
}

// Readers of just the candidates' own nets: seeding the bits that matter up
// front keeps this to one walk of the module and a pool per candidate bit,
// rather than one per bit in the design.
void descale_index_readers(Module *module, SigMap &sigmap, const vector<DescaleRewrite> &candidates,
                           dict<SigBit, pool<Cell *>> &readers)
{
  for (auto &cand : candidates) {
    for (auto bit : sigmap(cand.add->getPort(ID::Y)))
      readers[bit] = pool<Cell *>();
    for (auto bit : cand.out)
      readers[bit] = pool<Cell *>();
  }

  for (auto cell : module->cells())
    for (auto &conn : cell->connections()) {
      if (cell->output(conn.first))
        continue;
      for (auto bit : sigmap(conn.second)) {
        auto it = readers.find(bit);
        if (it != readers.end())
          it->second.insert(cell);
      }
    }

  // A module-level connection reads bits this pass cannot rewrite; the null
  // marker is a reader no candidate can claim, so those bits are refused
  for (auto &conn : module->connections())
    for (auto bit : sigmap(conn.second)) {
      auto it = readers.find(bit);
      if (it != readers.end())
        it->second.insert(nullptr);
    }
}

int run_descale_shifts(Module *module)
{
  SigMap sigmap; // bound by descale_find_anchors, once it knows it is needed
  dict<SigBit, Cell *> anchors;
  descale_find_anchors(module, sigmap, anchors);
  if (anchors.empty())
    return 0;

  vector<DescaleRewrite> candidates;
  descale_find_candidates(module, sigmap, anchors, candidates);
  if (candidates.empty())
    return 0;

  dict<SigBit, pool<Cell *>> readers;
  descale_index_readers(module, sigmap, candidates, readers);

  vector<DescaleRewrite> rewrites;
  for (auto &cand : candidates) {
    // Both nets end up carrying a different value, so both have to be ours
    SigSpec sum = sigmap(cand.add->getPort(ID::Y));
    if (!descale_contained(sum) || !descale_contained(cand.out))
      continue;

    // The rewrite deletes the increment, so nothing else may be reading it
    pool<Cell *> sharers, consumers;
    for (auto bit : sum)
      for (auto reader : readers.at(bit))
        if (reader != cand.shr)
          sharers.insert(reader);
    if (!sharers.empty())
      continue;

    // Every reader of the shifted result has to be one the carry folds into
    for (auto bit : cand.out)
      for (auto reader : readers.at(bit))
        if (reader != cand.shr)
          consumers.insert(reader);

    bool foldable = true;
    for (auto reader : consumers) {
      // The null marker is a module connection, and an unselected or kept reader
      // is one this pass may not rewire; either way the carry has nowhere to fold
      bool ours = reader && module->selected(reader) && !reader->get_bool_attribute(ID::keep);
      if (ours && descale_is_decrement(sigmap, reader, cand.out))
        cand.decs.push_back(reader);
      else if (ours && descale_is_zero_test(sigmap, reader, cand.out))
        cand.zeros.push_back(reader);
      else {
        foldable = false;
        break;
      }
    }

    // Without a decrement to absorb the carry the increment would just move
    if (!foldable || cand.decs.empty())
      continue;

    log_debug("  %s: descale %s through %s (%d decrement(s), %d zero test(s))\n", log_id(module),
              log_id(cand.add), log_id(cand.shr), GetSize(cand.decs), GetSize(cand.zeros));
    rewrites.push_back(cand);
  }

  for (auto &rewrite : rewrites) {
    Cell *cell = rewrite.shr; // NEW_ID2_SUFFIX names after the shifter
    std::string src = cell->get_src_attribute();

    // Carry out of the discarded window, selected with the data shift amount.
    // Index 0 of the scan is the empty window, so s == 0 reads a hard 1; an
    // amount past width(x) reads a zero bit of the scan and gives 0.
    SigSpec prefix(State::S1);
    prefix.append(descale_and_scan(cell, rewrite.x));
    Wire *carry = module->addWire(NEW_ID2_SUFFIX("carry"));
    module->addShr(NEW_ID2_SUFFIX("carry"), prefix, cell->getPort(ID::B), carry, false, src);

    // The shifter now scales x itself; its readers make up the difference. Its
    // result is a different value than before, so it drives a fresh net rather
    // than leaving a stale meaning on the old name (which formal pairs up).
    Wire *scaled = module->addWire(NEW_ID2_SUFFIX("scaled"), GetSize(rewrite.out));
    cell->setPort(ID::A, rewrite.x);
    cell->setPort(ID::Y, scaled);
    cell->fixup_parameters();

    for (auto dec : rewrite.decs) {
      // The matcher already proved A is the shifter output, zero-extended
      SigSpec operand(scaled);
      operand.extend_u0(GetSize(dec->getPort(ID::A)), false);
      dec->setPort(ID::A, operand);

      // The carry selects rather than borrows: `t - !c` would drag the window
      // test through every result bit, while `c ? t : t - 1` keeps the decrement
      // a constant one and leaves the carry a single-level arc off the shifter
      SigSpec result = dec->getPort(ID::Y);
      Wire *decremented = module->addWire(NEW_ID2_SUFFIX("dec"), GetSize(result));
      dec->setPort(ID::Y, decremented);
      dec->fixup_parameters();
      SigSpec kept(scaled);
      kept.extend_u0(GetSize(result), false);
      module->addMux(NEW_ID2_SUFFIX("dec"), decremented, kept, carry, result, src);
    }
    for (auto zero : rewrite.zeros) {
      // t + carry is zero exactly when neither part is, so the carry can just
      // ride along as a new top bit of the tested word
      IdString port = sigmap(zero->getPort(ID::A)) == rewrite.out ? ID::A : ID::B;
      SigSpec tested(scaled);
      tested.append(carry);
      zero->setPort(port, tested);
      zero->fixup_parameters();
    }

    // equiv_make pairs gold and gate cells by name and then asserts their inputs
    // equivalent, so every cell that now sees a different value has to be renamed
    // or formal reports the intended difference as a failure
    for (const vector<Cell *> &group : {vector<Cell *>{cell}, rewrite.decs, rewrite.zeros})
      for (Cell *touched : group)
        module->rename(touched, module->uniquify(touched->name.str() + "_descale"));

    module->remove(rewrite.add);
    did_something = true;
  }

  return GetSize(rewrites);
}

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
    log("      A right shift discards the low bits, so it only commutes with an\n");
    log("      OP that reads each result bit from the same operand position:\n");
    log("      $add/$sub carry across positions and are restricted to $shl and\n");
    log("      $sshl. The rewrite is also refused where the OP's own width would\n");
    log("      drop a bit the wider shifted result brings back, or where the OP\n");
    log("      and the shift disagree on the signedness a narrow operand is\n");
    log("      padded with.\n");
    log("\n");
    log("  -expand-keep-arith\n");
    log("      Restrict -expand so a variable shift amount is not expanded\n");
    log("      across $add/$sub, only a constant one. A constant amount is\n");
    log("      free rewiring, but a variable amount is a barrel: expanding it\n");
    log("      duplicates the barrel and moves it ahead of the carry chain, so\n");
    log("      the amount's own cone gains the adder's whole depth instead of\n");
    log("      bypassing it. On an N-operand add tree the rewrite cascades, so\n");
    log("      one barrel behind the tree becomes N barrels in front of it.\n");
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
    log("  -chain\n");
    log("      Compose two back-to-back barrels that -combine cannot see because\n");
    log("      the outer one reads its operand as a constant-padded slice rather\n");
    log("      than as the inner output whole, which is what a part-select or an\n");
    log("      opt_vps gather table leaves behind:\n");
    log("        pad(x << b) >> c  ===>  pad'(x) >> (c - b + k)\n");
    log("      Only a right-shift of a leftover left-shift: that is the opt_vps\n");
    log("      gather reading `(x >> 1) << s`. The inverse align pair\n");
    log("      `(x >> b) << c` is left alone. Unlike -fuse the result stays a\n");
    log("      plain shift, so the amount needs clog2 of the sum rather than of\n");
    log("      the modulus. The sum can go negative, so the operand is\n");
    log("      pre-padded and one unsigned $shr is left. Only fires when the\n");
    log("      inner barrel dies with it and the composed amount is narrower.\n");
    log("\n");
    log("  -chain-keep\n");
    log("      Like -chain, but keep the inner barrel when another reader still\n");
    log("      needs it. The compose still rewrites the outer, so a leftover\n");
    log("      `(x >> 1) << s` can fold into a later gather while the inner\n");
    log("      shift stays for the unshifted field.\n");
    log("\n");
    log("  -max_chain_pad n\n");
    log("      refuse a -chain rewrite whose padded operand would exceed n bits\n");
    log("      (default 4096).\n");
    log("\n");
    log("  -max_fuse_bits n\n");
    log("      refuse a -fuse rewrite whose repeated source would exceed n\n");
    log("      bits (default 4096).\n");
    log("\n");
    log("  -descale\n");
    log("      Collapse a scale-down round trip around a variable right shift,\n");
    log("      so one carry chain is left instead of two bracketing the shifter:\n");
    log("        ((x + 1) >> s) - 1  ===>  c ? (x >> s) : (x >> s) - 1\n");
    log("      where c = &x[s-1:0]. Writing x = t*2^s + r, the shift throws r\n");
    log("      away, so all the increment can still contribute is its carry out\n");
    log("      of that window, which is c (vacuously true for s == 0). The carry\n");
    log("      lands on a select rather than the decrement's borrow input, which\n");
    log("      would otherwise drag the window test through every result bit, and\n");
    log("      the test itself is a log-depth AND scan beside the shifter.\n");
    log("      The increment must not truncate: an all-ones x has to carry into\n");
    log("      bit width(x) rather than wrap to zero. Only readers the carry can\n");
    log("      fold into are accepted, which is `- 1` and `== 0`.\n");
    log("\n");
    log("  -max_iters n\n");
    log("      max number of pass iterations to run.\n");
    log("\n");
    log("If none of -combine, -expand, -sink, -fuse, -chain or -descale is given,\n");
    log("combine and expand are run.\n");
    log("\n");
  }
  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    log_header(design, "Executing OPT_SHIFT pass (shift optimizations).\n");

    bool run_combine = false;
    bool run_expand = false;
    bool expand_keep_arith = false;
    bool run_sink = false;
    bool run_fuse = false;
    bool run_chain = false;
    bool chain_keep = false;
    bool run_descale = false;
    int max_fuse_bits = 4096;
    int max_chain_pad = 4096;
    int total_chained = 0;
    int max_iters = 10000;
    int descale_count = 0;

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
      if (args[argidx] == "-expand-keep-arith" ||
          args[argidx] == "-expand_keep_arith") {
        expand_keep_arith = true;
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
      if (args[argidx] == "-chain") {
        run_chain = true;
        continue;
      }
      if (args[argidx] == "-chain-keep" || args[argidx] == "-chain_keep") {
        run_chain = true;
        chain_keep = true;
        continue;
      }
      if (args[argidx] == "-descale") {
        run_descale = true;
        continue;
      }
      if (args[argidx] == "-max_fuse_bits" && argidx + 1 < args.size()) {
        max_fuse_bits = std::stoi(args[++argidx]);
        continue;
      }
      if (args[argidx] == "-max_chain_pad" && argidx + 1 < args.size()) {
        max_chain_pad = std::stoi(args[++argidx]);
        continue;
      }
      if (args[argidx] == "-max_iters" && argidx + 1 < args.size()) {
        max_iters = std::stoi(args[++argidx]);
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);

    if (!run_combine && !run_expand && !run_sink && !run_fuse && !run_chain &&
        !run_descale) {
      run_combine = true;
      run_expand = true;
    }

    // -expand undoes -sink on $add, so they would ping-pong until max_iters
    if (run_expand && run_sink)
      log_cmd_error("opt_shift: -expand and -sink are inverses, pick one.\n");

    int total_fused = 0;
    for (auto module : design->selected_modules())
    {
      // A process can read the nets -descale redirects, and it is not in the
      // cell graph, so that reader can neither be seen nor rewritten. Checked
      // once per module so the warning does not repeat over the iterations.
      bool descale_module = run_descale && !module->has_processes_warn();
      did_something = true;
      for (int i = 0; did_something && i < max_iters; i++)
      {
        did_something = false;
        if (run_combine || run_expand) {
          peepopt_shift_pm pm(module);
          pm.setup(module->selected_cells());
          if (run_combine)
            pm.run_combine_shifts();
          if (run_expand) {
            // setup() zeroes udata, so the flag has to be set after it
            pm.ud_expand_shifts.keep_arith = expand_keep_arith;
            pm.run_expand_shifts();
          }
        }
        // Indexing the drivers and every $add is only worth it once we know a
        // variable-amount shifter exists; most modules have none and skip it
        if (run_sink && has_variable_shift(module)) {
          sink_index_module(module);
          peepopt_sink_pm pm(module);
          pm.setup(module->selected_cells());
          pm.run_sink_shifts();
        }
        // Composes $shr chains too, which has_variable_shift does not see
        if (run_chain) {
          ChainCombiner chainer(module, max_chain_pad, chain_keep);
          did_something |= chainer.run();
          total_chained += chainer.combined;
        }
        // Same pre-filter: a gather only fuses with a variable-amount shifter
        if (run_fuse && has_variable_shift(module)) {
          GatherFuser fuser(module, max_fuse_bits);
          did_something |= fuser.run();
          total_fused += fuser.fused;
        }
        if (descale_module)
          descale_count += run_descale_shifts(module);
      }
    }

    if (run_fuse)
      log("Fused %d gather(s) with the shift feeding them.\n", total_fused);
    if (run_chain)
      log("Composed %d barrel pair(s) across constant padding.\n", total_chained);
    if (run_descale)
      log("Collapsed %d scale-down round trip(s) into window-carry logic.\n", descale_count);
  }
} OptShiftPass;

PRIVATE_NAMESPACE_END
