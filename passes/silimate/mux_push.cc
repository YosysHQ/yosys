/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                      Abhinav Tondapu <abhinav@silimate.com>
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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/io.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>
#include <vector>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/silimate/unit_delay.h"

struct OptMuxPushWorker : UnitDelayTiming
{
  RTLIL::Design *design;

  dict<SigBit, int> fanout_map;
  pool<SigBit> keep_bits;
  pool<SigBit> port_out_bits;

  pool<IdString> target_types;
  int fanout_limit;
  bool timing_guard;
  int slack_margin;
  bool recover_folded;
  int hoist_gain;
  int farm_gain;
  int reindex_gain;
  int reindex_max_bits;
  int total_count;
  int hoist_count;
  int farm_count;
  int reindex_count;
  int chains_seen = 0, chains_cheap = 0, chains_slack = 0;
  int farms_seen = 0, farms_cheap = 0, farms_slack = 0;
  int nests_seen = 0, nests_cheap = 0, nests_slack = 0, nests_big = 0;

  OptMuxPushWorker(RTLIL::Design *design, RTLIL::Module *module,
      const pool<IdString> &target_types, int fanout_limit, bool timing_guard,
      int slack_margin, bool recover_folded, int hoist_gain, int farm_gain,
      int reindex_gain, int reindex_max_bits) :
      UnitDelayTiming(module), design(design),
      target_types(target_types), fanout_limit(fanout_limit),
      timing_guard(timing_guard), slack_margin(slack_margin),
      recover_folded(recover_folded), hoist_gain(hoist_gain), farm_gain(farm_gain),
      reindex_gain(reindex_gain), reindex_max_bits(reindex_max_bits),
      total_count(0), hoist_count(0), farm_count(0), reindex_count(0)
  {
  }

  // A mux between two associable operators blocks the arithmetic tree
  // balancer, so dissolving it pays even when the select arrives early.
  bool push_merges_chain(RTLIL::Cell *cell, const RTLIL::SigSpec &arm_a, const RTLIL::SigSpec &arm_b)
  {
    for (const RTLIL::SigSpec *arm : {&arm_a, &arm_b}) {
      for (auto &bit : sigmap(*arm)) {
        if (bit.wire == nullptr)
          continue;
        auto it = driver_map.find(bit);
        if (it == driver_map.end() || it->second == nullptr)
          continue;
        IdString t = it->second->type;
        if (t == cell->type)
          return true;
        // negopt normalizes add/sub chains, so they reassociate together
        if (t.in(ID($add), ID($sub)) && cell->type.in(ID($add), ID($sub)))
          return true;
      }
    }
    return false;
  }

  // The walk below forks at every mux, so bound it: a deep tree would otherwise
  // cost the guard 2^depth visits.
  static const int max_push_depth = 8;

  // A recovered select costs what a $mux costs in estimate_cell_delay
  static const int mux_delay = 1;

  // Const-folding collapses a select over mostly-constant arms into the arms
  // themselves: `s ? 3'd3 : 3'd0` leaves the bare bits `{1'b0, s, s}` and no mux
  // to push through. Splitting on one of those nets recovers the two constant
  // arms the fold destroyed. Bound the net count so the operand really is a
  // folded select and not just narrow logic.
  static const int max_folded_nets = 2;

  // The latest net of a folded select, if `sig` is one. Splitting on the latest
  // keeps the recovered mux above the arms rather than in series with them.
  bool folded_select(const RTLIL::SigSpec &sig, RTLIL::SigBit &sel)
  {
    // A folded select repeats one net across the bus, and fanout_map counts each
    // repeat, so tally this operand's own reads to discount them below.
    dict<RTLIL::SigBit, int> reads;
    for (auto &bit : sig)
      if (bit.wire != nullptr)
        reads[bit]++;
    if (reads.empty() || GetSize(reads) > max_folded_nets)
      return false;
    // The operator is duplicated per arm, so hold the same fanout trade as the
    // mux case: charge one read for this operator, as a mux output bit would
    // cost, and hold every other consumer to -limit.
    for (auto &it : reads)
      if (fanout_map[it.first] - it.second + 1 > fanout_limit)
        return false;
    sel = reads.begin()->first;
    for (auto &it : reads)
      if (arrival(it.first) > arrival(sel))
        sel = it.first;
    return true;
  }

  // `sig` with `sel` replaced by `val`. Exact under the arm that forces it: the
  // operand's whole dependence on `sel` is the bits that are `sel`.
  RTLIL::SigSpec force_bit(const RTLIL::SigSpec &sig, RTLIL::SigBit sel, bool val)
  {
    RTLIL::SigSpec out;
    for (auto &bit : sig)
      out.append(bit == sel ? RTLIL::SigBit(val ? State::S1 : State::S0) : bit);
    return out;
  }

  // Arrival out of the fully pushed tree: a copy of the operator lands on every
  // leaf and the muxes restack above it, so each path is charged only the levels
  // it really crosses -- an unbalanced tree must not pay its latest arm and its
  // deepest arm at once. Recurse just where a push would be allowed, so the
  // estimate matches what the iteration can reach; elsewhere the operator reads
  // sig as it stands.
  int pushed_arrival(const RTLIL::SigSpec &sig, int d_op, int others, int budget)
  {
    RTLIL::Cell *m = nullptr;
    RTLIL::SigSpec arm_a, arm_b;
    if (budget > 0 && mux_drives_sig(sig, m) && design->selected(module, m) &&
        !m->get_bool_attribute(ID::keep) &&
        !sig_has_keep(m->getPort(ID::Y)) &&
        fanout_within_limit(sigmap(m->getPort(ID::Y))) &&
        slice_arms(m, sigmap(m->getPort(ID::Y)), sig, arm_a, arm_b))
      return std::max({pushed_arrival(sigmap(arm_a), d_op, others, budget - 1),
                       pushed_arrival(sigmap(arm_b), d_op, others, budget - 1),
                       arrival(m->getPort(ID::S))}) + estimate_cell_delay(m);
    // No mux left, but a folded select splits into the same two arms
    RTLIL::SigBit sel;
    if (budget > 0 && recover_folded && folded_select(sig, sel))
      return std::max({pushed_arrival(sigmap(force_bit(sig, sel, false)), d_op, others,
                                      budget - 1),
                       pushed_arrival(sigmap(force_bit(sig, sel, true)), d_op, others,
                                      budget - 1),
                       arrival(sel)}) + mux_delay;
    return std::max(arrival(sig), others) + d_op;
  }

  // Pushing pays when the select is the mux's late input: the operators then
  // evaluate on the early arms in parallel with the select instead of queueing
  // behind it. Otherwise it is pure area for no depth.
  bool should_push(RTLIL::Cell *cell, IdString port,
      const RTLIL::SigSpec &arm_a, const RTLIL::SigSpec &arm_b)
  {
    if (!timing_guard)
      return true;

    // Whatever depth the push buys locally, it can only shorten the module's
    // longest path if this operator sits on one. Anywhere else it duplicates
    // the operator for a win no endpoint ever sees.
    int slack = longest_path() - path_depth(cell->getPort(ID::Y));
    if (slack > slack_margin)
      return false;

    if (push_merges_chain(cell, arm_a, arm_b)) {
      // The balancer reassociates the merged chain, so the payoff is not local
      // and there is no gain here to weigh.
      log_debug("    %s %s port %s: chain merge, slack=%d\n",
          log_id(cell->type), log_id(cell->name), log_id(port), slack);
      return true;
    }

    int d_op = estimate_cell_delay(cell);

    int others = 0;
    for (auto &conn : cell->connections()) {
      if (!cell->input(conn.first) || conn.first == port)
        continue;
      others = std::max(others, arrival(conn.second));
    }

    // A nested ternary builds a chain of muxes on one operand. Pushing one level
    // is break-even there -- the operator still queues behind the rest of the
    // chain -- so weigh the push against the fully pushed tree, which is where
    // the operator finally sees only leaf arrivals. Judging a single level
    // rejects the whole chain and the win is never reached. For a lone mux this
    // reduces exactly to the single-level estimate.
    int before = std::max(arrival(cell->getPort(port)), others) + d_op;
    int after = pushed_arrival(sigmap(cell->getPort(port)), d_op, others, max_push_depth);
    log_debug("    %s %s port %s: others=%d before=%d after=%d slack=%d\n",
        log_id(cell->type), log_id(cell->name), log_id(port), others, before, after, slack);
    return after < before;
  }

  void build_connectivity()
  {
    driver_map.clear();
    fanout_map.clear();
    consumer_map.clear();
    keep_bits.clear();
    port_out_bits.clear();

    // Collect `keep` across every alias, not just the wire sigmap elected: the
    // attribute may sit on any wire of a `connect` group, and testing it on the
    // representative alone silently drops the mux a kept probe was reading.
    for (auto wire : module->wires())
      if (wire->get_bool_attribute(ID::keep))
        for (auto &bit : sigmap(RTLIL::SigSpec(wire)))
          keep_bits.insert(bit);

    // Build per-bit driver and fanout maps for the current module
    for (auto cell : module->cells())
    {
      for (auto &it : cell->connections()) {
        RTLIL::SigSpec sig = sigmap(it.second);
        if (cell->output(it.first)) {
          for (auto &bit : sig) {
            if (bit.wire == nullptr)
              continue;
            auto it_drv = driver_map.find(bit);
            if (it_drv == driver_map.end()) {
              driver_map[bit] = cell;
            } else if (it_drv->second != cell) {
              driver_map[bit] = nullptr;
            }
          }
        }
        if (cell->input(it.first)) {
          for (auto &bit : sig) {
            if (bit.wire == nullptr)
              continue;
            fanout_map[bit]++;
            auto &cons = consumer_map[bit];
            if (cons.empty() || cons.back() != cell)
              cons.push_back(cell);
          }
        }
      }
    }

    // Treat module output ports as consumers
    for (auto wire : module->wires()) {
      if (!wire->port_output)
        continue;
      RTLIL::SigSpec sig = sigmap(RTLIL::SigSpec(wire));
      for (auto &bit : sig) {
        if (bit.wire == nullptr)
          continue;
        fanout_map[bit]++;
        port_out_bits.insert(bit);
      }
    }
  }

  // Sigmaps each bit so callers may pass raw or mapped signals interchangeably.
  bool sig_has_keep(const RTLIL::SigSpec &sig)
  {
    for (auto &bit : sig) {
      if (bit.wire != nullptr && keep_bits.count(sigmap(bit)))
        return true;
    }
    return false;
  }

  bool mux_drives_sig(const RTLIL::SigSpec &sig, RTLIL::Cell *&mux_cell)
  {
    mux_cell = nullptr;
    for (auto &bit : sig) {
      // Zero/sign-extension padding leaves constant bits in the operand (e.g.
      // $lt A = { 3'000, \w_floor }). They are the same in both arms, so
      // slice_arms passes them through and the push stays exact.
      if (bit.wire == nullptr)
        continue;
      // Require a single consistent driver for all variable bits in the SigSpec
      auto it_drv = driver_map.find(bit);
      if (it_drv == driver_map.end() || it_drv->second == nullptr)
        return false;
      if (mux_cell == nullptr)
        mux_cell = it_drv->second;
      else if (mux_cell != it_drv->second)
        return false;
    }
    return mux_cell != nullptr && mux_cell->type == ID($mux);
  }

  bool fanout_within_limit(const RTLIL::SigSpec &sig)
  {
    for (auto &bit : sig) {
      if (bit.wire == nullptr)
        return false;
      // Enforce fanout cap per bit to keep the mux exclusive to this operator
      if (fanout_map[bit] > fanout_limit)
        return false;
    }
    return true;
  }

  // Project `in_sig` onto the mux arms bit by bit. Fails if any bit of in_sig
  // is not a bit of the mux output.
  bool slice_arms(RTLIL::Cell *mux_cell, const RTLIL::SigSpec &mux_out,
      const RTLIL::SigSpec &in_sig, RTLIL::SigSpec &arm_a, RTLIL::SigSpec &arm_b)
  {
    RTLIL::SigSpec mux_a = mux_cell->getPort(ID::A);
    RTLIL::SigSpec mux_b = mux_cell->getPort(ID::B);
    if (GetSize(mux_a) != GetSize(mux_out) || GetSize(mux_b) != GetSize(mux_out))
      return false;

    dict<SigBit, int> pos;
    for (int i = 0; i < GetSize(mux_out); i++)
      pos.emplace(mux_out[i], i);

    arm_a = RTLIL::SigSpec();
    arm_b = RTLIL::SigSpec();
    for (auto &bit : in_sig) {
      auto it = pos.find(bit);
      if (it == pos.end()) {
        // Only extension padding may sit outside the mux output; a variable bit
        // from another driver means this operand is not a view of the mux.
        if (bit.wire != nullptr)
          return false;
        arm_a.append(bit);
        arm_b.append(bit);
        continue;
      }
      arm_a.append(mux_a[it->second]);
      arm_b.append(mux_b[it->second]);
    }
    return true;
  }

  bool fanout_is_one(const RTLIL::SigSpec &sig)
  {
    for (auto &bit : sig) {
      if (bit.wire == nullptr)
        return false;
      if (fanout_map[bit] != 1)
        return false;
    }
    return true;
  }

  // One link of a mux priority chain: the arms that leave the chain here, and
  // the select that takes them. A $pmux link carries S_WIDTH arms at once.
  struct ChainStep {
    RTLIL::Cell *cell;
    RTLIL::SigSpec leaves;
    RTLIL::SigSpec sel;
    bool leaf_on_b;
    bool is_pmux;
    int levels;
  };

  // Is `sig` exactly the output of a private mux, so the chain can absorb it?
  RTLIL::Cell *private_link(const RTLIL::SigSpec &sig)
  {
    RTLIL::Cell *drv = nullptr;
    for (auto &bit : sig) {
      if (bit.wire == nullptr)
        return nullptr;
      auto it = driver_map.find(bit);
      if (it == driver_map.end() || it->second == nullptr)
        return nullptr;
      if (drv == nullptr)
        drv = it->second;
      else if (drv != it->second)
        return nullptr;
    }
    if (drv == nullptr || !drv->type.in(ID($mux), ID($pmux)))
      return nullptr;
    if (!fanout_is_one(sig) || sig_has_keep(sig))
      return nullptr;
    // Absorbing a link deletes it, so one the caller kept or left out of the
    // selection has to end the walk instead. Checking only the arm signal misses
    // both: keep on the cell says nothing about the wire it drives.
    if (!design->selected(module, drv) || drv->get_bool_attribute(ID::keep))
      return nullptr;
    // Partial coverage would leave the inner mux's other bits undriven once the
    // chain is rebuilt, so demand the arm be the whole output.
    return sigmap(drv->getPort(ID::Y)) == sig ? drv : nullptr;
  }

  // Walk down the default arms of a priority chain rooted at `root`. A bottom
  // $mux contributes both arms: the later one is kept as the default, since that
  // is the arm the rewrite lifts out.
  bool collect_chain(RTLIL::Cell *root, std::vector<ChainStep> &steps, RTLIL::SigSpec &def)
  {
    RTLIL::Cell *cur = root;
    int total = 0;
    while (true) {
      RTLIL::SigSpec a = sigmap(cur->getPort(ID::A));
      RTLIL::SigSpec b = sigmap(cur->getPort(ID::B));
      RTLIL::SigSpec s = sigmap(cur->getPort(ID::S));
      bool pm = cur->type == ID($pmux);
      if (pm ? GetSize(b) != GetSize(a) * GetSize(s)
             : (GetSize(s) != 1 || GetSize(a) != GetSize(b)))
        return false;
      // A $pmux lowers to a priority chain, so its default pays per select bit.
      int lv = pm ? log2p1_int(GetSize(s)) : 1;
      total += lv;

      if (RTLIL::Cell *next_a = private_link(a)) {
        steps.push_back({cur, b, s, true, pm, lv});
        cur = next_a;
        continue;
      }
      // Only a $mux can be entered from B: a $pmux's B holds its arms.
      if (!pm) {
        if (RTLIL::Cell *next_b = private_link(b)) {
          steps.push_back({cur, a, s, false, false, lv});
          cur = next_b;
          continue;
        }
      }

      if (pm) {
        steps.push_back({cur, b, s, true, true, lv});
        def = a;
      } else {
        bool def_is_a = arrival(a) >= arrival(b);
        steps.push_back({cur, def_is_a ? b : a, s, def_is_a, false, lv});
        def = def_is_a ? a : b;
      }
      return total >= 2;
    }
  }

  // The rest chain seeds from the bottom link. A bottom $mux collapses into its
  // own leaf, a bottom $pmux still has to select among its arms.
  RTLIL::SigSpec chain_seed(const std::vector<ChainStep> &steps, int width, int &start)
  {
    const ChainStep &bot = steps.back();
    start = GetSize(steps) - (bot.is_pmux ? 1 : 2);
    return bot.is_pmux ? bot.leaves.extract(0, width) : bot.leaves;
  }

  // Lift the chain's default arm to the output under the accumulated not-taken
  // condition. The early arms rebuild beside it, so the late arm ends up one mux
  // from the output instead of paying for every link above it.
  void hoist_chain(RTLIL::Cell *root, std::vector<ChainStep> &steps, const RTLIL::SigSpec &def,
      pool<RTLIL::Cell*> &cells_to_remove)
  {
    const std::string src = root->get_src_attribute();
    int width = GetSize(def), start = 0;
    RTLIL::SigSpec cur = chain_seed(steps, width, start);

    for (int j = start; j >= 0; j--) {
      const ChainStep &st = steps[j];
      RTLIL::Wire *w = module->addWire(NEW_ID_SUFFIX("muxhoist_rest"), width);
      if (st.is_pmux)
        module->addPmux(NEW_ID_SUFFIX("muxhoist_pmux"), cur, st.leaves, st.sel, w, src);
      else
        module->addMux(NEW_ID_SUFFIX("muxhoist_mux"), st.leaf_on_b ? cur : st.leaves,
            st.leaf_on_b ? st.leaves : cur, st.sel, w, src);
      cur = w;
    }

    // Guard: every arm above the default was passed over.
    RTLIL::SigSpec not_taken;
    for (auto &st : steps) {
      if (!st.is_pmux && !st.leaf_on_b) {
        not_taken.append(st.sel);
        continue;
      }
      RTLIL::Wire *inv = module->addWire(NEW_ID_SUFFIX("muxhoist_nsel"), GetSize(st.sel));
      module->addNot(NEW_ID_SUFFIX("muxhoist_not"), st.sel, inv, false, src);
      not_taken.append(inv);
    }
    RTLIL::Wire *guard = module->addWire(NEW_ID_SUFFIX("muxhoist_guard"));
    module->addReduceAnd(NEW_ID_SUFFIX("muxhoist_all"), not_taken, guard, false, src);

    RTLIL::SigSpec out = sigmap(root->getPort(ID::Y));
    RTLIL::Wire *rewritten = module->addWire(NEW_ID_SUFFIX("muxhoist_out"), GetSize(out));
    module->addMux(NEW_ID_SUFFIX("muxhoist_late"), cur, def, guard, rewritten, src);

    for (auto &st : steps)
      cells_to_remove.insert(st.cell);
    module->connect(out, rewritten);
  }

  // Estimated output arrival before and after the hoist, under the same unit
  // model as the push heuristic. Rejecting on this keeps the rewrite from firing
  // where the default is not actually the chain's late arm.
  bool hoist_pays(const std::vector<ChainStep> &steps, const RTLIL::SigSpec &def)
  {
    int n = GetSize(steps), start = 0, sel_bits = 0, sels = 0, cum = 0;
    std::vector<int> to_out(n);
    for (int j = 0; j < n; j++) {
      cum += steps[j].levels;
      to_out[j] = cum;
      sel_bits += GetSize(steps[j].sel);
      sels = std::max(sels, arrival(steps[j].sel));
    }

    int before = arrival(def) + cum;
    for (int j = 0; j < n; j++)
      before = std::max(before,
          std::max(arrival(steps[j].leaves), arrival(steps[j].sel)) + to_out[j]);

    RTLIL::SigSpec seed = chain_seed(steps, GetSize(def), start);
    int rest = arrival(seed) + (start < 0 ? 0 : to_out[start]);
    for (int j = 0; j <= start; j++)
      rest = std::max(rest,
          std::max(arrival(steps[j].leaves), arrival(steps[j].sel)) + to_out[j]);

    int after = std::max({arrival(def) + 1, rest + 1, sels + log2p1_int(sel_bits) + 1});
    // Downstream remapping reshapes shallow wins away, so only take chains where
    // the model predicts a margin worth the extra guard.
    return after + hoist_gain <= before;
  }

  void run_hoist()
  {
    build_connectivity();
    reset_timing();

    pool<RTLIL::Cell*> cells_to_remove;
    for (auto cell : module->selected_cells()) {
      if (!cell->type.in(ID($mux), ID($pmux)) || cells_to_remove.count(cell))
        continue;
      if (cell->get_bool_attribute(ID::keep))
        continue;
      RTLIL::SigSpec out = sigmap(cell->getPort(ID::Y));
      if (sig_has_keep(out) || GetSize(out) == 0)
        continue;
      // Starting mid-chain would rebuild a chain the parent still owns.
      if (fanout_is_one(out)) {
        auto it = consumer_map.find(out[0]);
        if (it != consumer_map.end() && GetSize(it->second) == 1 &&
            it->second[0]->type.in(ID($mux), ID($pmux)))
          continue;
      }

      std::vector<ChainStep> steps;
      RTLIL::SigSpec def;
      if (!collect_chain(cell, steps, def))
        continue;
      chains_seen++;
      bool overlaps = false;
      for (auto &st : steps)
        overlaps |= cells_to_remove.count(st.cell) > 0;
      if (overlaps)
        continue;
      if (!hoist_pays(steps, def)) {
        chains_cheap++;
        continue;
      }
      if (timing_guard && path_depth(out) < longest_path() - slack_margin) {
        chains_slack++;
        continue;
      }

      hoist_chain(cell, steps, def, cells_to_remove);
      hoist_count++;
    }

    log_debug("  hoist: %d chain(s), %d unprofitable, %d off-critical.\n",
        chains_seen, chains_cheap, chains_slack);
    for (auto cell : cells_to_remove)
      module->remove(cell);
  }

  // Shifts map each output bit to one input bit or to a fill value, and that is
  // what makes the farm push below exact: for any such f and a bitwise select,
  //   f(sel ? b : a) == f(sel) ? f(b) : f(a)
  // provided all three clones carry identical parameters, so the index map and
  // the fill agree. $shift/$shiftx are left out: their x fill does not survive
  // being re-selected bit by bit.
  static bool is_farm_shift(RTLIL::Cell *cell)
  {
    return cell->type.in(ID($shl), ID($shr), ID($sshl), ID($sshr));
  }

  // A per-bit select farm: every bit of `sig` carries its own $mux, so the
  // operand is mux_j(sel[j], a[j], b[j]) and there is no bus-wide select for
  // mux_drives_sig to find. Bits that are not a private mux ride into both arms
  // unchanged under a constant select, exactly as slice_arms passes padding.
  // Returns how many muxes the push would actually dissolve.
  int farm_drives_sig(const RTLIL::SigSpec &sig, RTLIL::SigSpec &arm_a,
      RTLIL::SigSpec &arm_b, RTLIL::SigSpec &sel, pool<RTLIL::Cell*> &farm)
  {
    arm_a = RTLIL::SigSpec();
    arm_b = RTLIL::SigSpec();
    sel = RTLIL::SigSpec();
    farm.clear();
    int muxes = 0;

    for (auto &bit : sig) {
      RTLIL::Cell *m = nullptr;
      if (bit.wire != nullptr) {
        auto it = driver_map.find(bit);
        if (it != driver_map.end())
          m = it->second;
      }
      // Only a mux this rewrite may dissolve is worth splitting on; anything
      // else stays whole and the two arms agree on it.
      if (m == nullptr || m->type != ID($mux) || !design->selected(module, m) ||
          m->get_bool_attribute(ID::keep) || sig_has_keep(m->getPort(ID::Y)) ||
          !fanout_within_limit(sigmap(m->getPort(ID::Y)))) {
        arm_a.append(bit);
        arm_b.append(bit);
        sel.append(State::S0);
        continue;
      }
      RTLIL::SigSpec y = sigmap(m->getPort(ID::Y));
      RTLIL::SigSpec ma = sigmap(m->getPort(ID::A));
      RTLIL::SigSpec mb = sigmap(m->getPort(ID::B));
      int pos = -1;
      for (int i = 0; i < GetSize(y); i++)
        if (y[i] == bit)
          pos = i;
      if (pos < 0 || GetSize(ma) != GetSize(y) || GetSize(mb) != GetSize(y)) {
        arm_a.append(bit);
        arm_b.append(bit);
        sel.append(State::S0);
        continue;
      }
      arm_a.append(ma[pos]);
      arm_b.append(mb[pos]);
      sel.append(sigmap(m->getPort(ID::S)));
      farm.insert(m);
      muxes++;
    }
    return muxes;
  }

  // Will -combine absorb `arm >> s` into the shift already driving `arm`? That
  // fold is the whole payoff: without it the push only relocates barrels, and
  // adds one for the select. peepopt_combine_shifts requires nusers == 2 on the
  // inner output, so this arm's clone has to end up its only reader.
  RTLIL::Cell *farm_arm_folds(RTLIL::Cell *cell, const RTLIL::SigSpec &arm,
      const pool<RTLIL::Cell*> &farm, std::initializer_list<const RTLIL::SigSpec *> rivals,
      const char **why = nullptr)
  {
    auto no = [&](const char *reason) -> RTLIL::Cell * {
      if (why != nullptr)
        *why = reason;
      return nullptr;
    };

    RTLIL::Cell *inner = nullptr;
    for (auto &bit : arm) {
      if (bit.wire == nullptr)
        return no("constant bit in arm");
      auto it = driver_map.find(bit);
      if (it == driver_map.end() || it->second == nullptr)
        return no("arm bit has no single driver");
      if (inner == nullptr)
        inner = it->second;
      else if (inner != it->second)
        return no("arm spans several drivers");
    }
    if (inner == nullptr || !is_farm_shift(inner) || !design->selected(module, inner))
      return no("arm is not driven by a shift");
    // A constant-amount inner shift is wiring, not a barrel, so folding it saves
    // nothing and the arm should be charged as it stands.
    if (sigmap(inner->getPort(ID::B)).is_fully_const())
      return no("inner shift amount is constant");
    // The fold rewrites the inner shift in place, so it must cover the arm whole
    // and in order, not just drive its bits.
    RTLIL::SigSpec y = sigmap(inner->getPort(ID::Y));
    if (y != sigmap(arm))
      return no("arm is not the inner output bit for bit");
    // Every reader must vanish here: the farm muxes are deleted, and the shift
    // itself is replaced by the clones. A reader outside both survives and keeps
    // the user count above what -combine accepts.
    for (auto &bit : y) {
      // A module output reads the signal without being a cell, so consumer_map
      // never lists it. Missing it prices a fold that -combine then declines,
      // leaving the clones as pure area.
      if (port_out_bits.count(bit))
        return no("inner output escapes through a module port");
      auto it = consumer_map.find(bit);
      if (it == consumer_map.end())
        continue;
      for (auto cons : it->second)
        if (cons != cell && !farm.count(cons))
          return no("inner output has a reader outside the farm");
    }
    // The other clones outlive the rewrite, so one of them reading this same
    // signal would leave the inner shift with two readers again.
    pool<RTLIL::SigBit> y_bits(y.begin(), y.end());
    for (auto rival : rivals)
      for (auto &bit : *rival)
        if (y_bits.count(bit))
          return no("another clone reads the same inner output");
    return inner;
  }

  // Arrival of one pushed clone. A folded arm keeps a single barrel where there
  // were two, so it is charged from the inner shift's own operand; the combined
  // amount picks up the adder -combine emits for it.
  int farm_clone_arrival(const RTLIL::SigSpec &arm, RTLIL::Cell *inner, int amt,
      int amt_add, int d_op)
  {
    if (inner == nullptr)
      return std::max(arrival(arm), amt) + d_op;
    return std::max(arrival(inner->getPort(ID::A)),
                    std::max(amt, arrival(inner->getPort(ID::B))) + amt_add) + d_op;
  }

  // Pushing a shift through a farm is depth-neutral on its own: three clones run
  // in parallel where one ran alone, so every arm just trades the mux level for
  // the shift level. It only pays when an arm folds into the shift above it.
  bool farm_push_pays(RTLIL::Cell *cell, const RTLIL::SigSpec &arm_a,
      const RTLIL::SigSpec &arm_b, const RTLIL::SigSpec &sel,
      const pool<RTLIL::Cell*> &farm)
  {
    int d_op = estimate_cell_delay(cell);
    int amt = arrival(cell->getPort(ID::B));
    int amt_add = log2p1_int(GetSize(cell->getPort(ID::B)) + 1);
    int sel_arr = arrival(sel);

    const char *why_a = "folds", *why_b = "folds";
    RTLIL::Cell *fold_a = farm_arm_folds(cell, arm_a, farm, {&arm_b, &sel}, &why_a);
    RTLIL::Cell *fold_b = farm_arm_folds(cell, arm_b, farm, {&arm_a, &sel}, &why_b);

    int before = std::max(
        std::max({arrival(arm_a), arrival(arm_b), sel_arr}) + mux_delay, amt) + d_op;
    int after = std::max({std::max(sel_arr, amt) + d_op,
        farm_clone_arrival(arm_a, fold_a, amt, amt_add, d_op),
        farm_clone_arrival(arm_b, fold_b, amt, amt_add, d_op)}) + mux_delay;

    log_debug("    %s %s: farm of %d mux(es), before=%d after=%d, A: %s, B: %s\n",
        log_id(cell->type), log_id(cell->name), GetSize(farm), before, after, why_a, why_b);
    return after + farm_gain <= before;
  }

  // Replace `shift(farm)` with `farm(shift, shift, shift)`, shifting the select
  // vector alongside the arms so each output bit still picks the arm its own
  // mux picked.
  void farm_push(RTLIL::Cell *cell, const RTLIL::SigSpec &arm_a, const RTLIL::SigSpec &arm_b,
      const RTLIL::SigSpec &sel, const pool<RTLIL::Cell*> &farm,
      pool<RTLIL::Cell*> &cells_to_remove)
  {
    const std::string src = cell->get_src_attribute();
    RTLIL::SigSpec out = sigmap(cell->getPort(ID::Y));
    int width = GetSize(out);

    // Identical parameters on all three clones is what keeps the rewrite exact,
    // so copy them wholesale rather than rebuilding them per clone.
    auto clone = [&](const RTLIL::SigSpec &operand, const char *tag) {
      RTLIL::Wire *y = module->addWire(NEW_ID2_SUFFIX(tag), width);
      RTLIL::Cell *c = module->addCell(NEW_ID2, cell->type);
      c->parameters = cell->parameters;
      c->set_src_attribute(src);
      c->setPort(ID::A, operand);
      c->setPort(ID::B, cell->getPort(ID::B));
      c->setPort(ID::Y, y);
      c->fixup_parameters();
      return RTLIL::SigSpec(y);
    };

    RTLIL::SigSpec ya = clone(arm_a, "farmpush_a");
    RTLIL::SigSpec yb = clone(arm_b, "farmpush_b");
    RTLIL::SigSpec ys = clone(sel, "farmpush_s");

    RTLIL::Wire *rewritten = module->addWire(NEW_ID2_SUFFIX("farmpush_y"), width);
    for (int j = 0; j < width; j++)
      module->addMux(NEW_ID2_SUFFIX("farmpush_mux"), ya[j], yb[j], ys[j],
          RTLIL::SigSpec(rewritten, j), src);

    cells_to_remove.insert(cell);
    // A farm mux dies only if this shift read all of it; a bit left out still
    // has a consumer of its own and dropping the mux would leave it undriven.
    RTLIL::SigSpec operand = sigmap(cell->getPort(ID::A));
    pool<RTLIL::SigBit> read_bits(operand.begin(), operand.end());
    for (auto m : farm) {
      RTLIL::SigSpec my = sigmap(m->getPort(ID::Y));
      bool covered = true;
      for (auto &bit : my)
        if (!read_bits.count(bit))
          covered = false;
      if (covered && fanout_is_one(my))
        cells_to_remove.insert(m);
    }
    module->connect(out, rewritten);
  }

  // Bound the walk: each push moves a shift strictly closer to the leaves, so a
  // nested farm converges, but a cap keeps a pathological design from spinning.
  static const int max_farm_iters = 10;

  void run_farm()
  {
    for (int iter = 0; iter < max_farm_iters; iter++) {
      build_connectivity();
      reset_timing();

      pool<RTLIL::Cell*> cells_to_remove;
      pool<RTLIL::SigBit> touched_bits;

      for (auto cell : module->selected_cells()) {
        if (!is_farm_shift(cell) || !target_types.count(cell->type))
          continue;
        if (cell->get_bool_attribute(ID::keep) || cells_to_remove.count(cell))
          continue;
        RTLIL::SigSpec out = sigmap(cell->getPort(ID::Y));
        RTLIL::SigSpec operand = sigmap(cell->getPort(ID::A));
        if (GetSize(out) == 0 || sig_has_keep(out) || sig_has_keep(operand))
          continue;

        RTLIL::SigSpec arm_a, arm_b, sel;
        pool<RTLIL::Cell*> farm;
        if (farm_drives_sig(operand, arm_a, arm_b, sel, farm) == 0)
          continue;
        farms_seen++;
        bool overlaps = cells_to_remove.count(cell) > 0;
        for (auto m : farm)
          overlaps |= cells_to_remove.count(m) > 0;
        for (auto &bit : operand)
          overlaps |= touched_bits.count(bit) > 0;
        if (overlaps)
          continue;
        if (!farm_push_pays(cell, arm_a, arm_b, sel, farm)) {
          farms_cheap++;
          continue;
        }
        if (timing_guard && path_depth(out) < longest_path() - slack_margin) {
          farms_slack++;
          continue;
        }

        for (auto &bit : operand)
          touched_bits.insert(bit);
        farm_push(cell, arm_a, arm_b, sel, farm, cells_to_remove);
        farm_count++;
      }

      for (auto cell : cells_to_remove)
        module->remove(cell);
      if (cells_to_remove.empty())
        break;
    }

    log_debug("  farm: %d shift(s) over a farm, %d unprofitable, %d off-critical.\n",
        farms_seen, farms_cheap, farms_slack);
  }

  // A two-level variable read `V[i][j]` elaborates as a gather nest: one inner
  // lane select per column, all sharing the row select I, under a root select
  // that picks a column with the index J. Both selects sit on the late path, so the
  // read costs |I| + |J| mux levels even though only one index is ever the
  // reason the read is late.
  //
  // When the two indices are offsets of a single computed base -- I = KA ^ L and
  // J = KB ^ L[0 +: |J|], which is how RTL spells a set/way pair derived from
  // one index -- the column index is an early function of the row index:
  //
  //   J = KB ^ (KA ^ I)[0 +: |J|] = (KB ^ KA[0 +: |J|]) ^ I[0 +: |J|] = E ^ I_low
  //
  // Within row i the column index is therefore E with the constant i_low xored
  // in, which is E reading a fixed permutation of that row. Swapping the nesting
  // moves the entire inner stage off the late path:
  //
  //   bmux(J, [bmux(I, col_p)])  ->  bmux(I, [bmux(E, perm_i(row_i))])
  //
  // Xor is its own inverse, so the identity is exact bit for bit and no
  // don't-care is involved; the guards below are only about profit and size.

  // A lane gather, however it is spelled. Verific emits $bmux for a variable
  // index; Yosys's own front end emits $shiftx, which is the same lookup when
  // the shift lands on lane boundaries -- as opt_argmax already treats them.
  // For $shiftx that means single-bit lanes: at wider lanes the index is
  // scaled by the lane width before the shift, so B is not the lane number.
  struct Gather {
    RTLIL::SigSpec sel;    // lane index
    RTLIL::SigSpec table;  // lanes, LSB first
    int lane_width = 0;
  };

  // The match walks every lane and the emit rebuilds every entry, so refuse a
  // select so wide that 1 << its width is not a sane table size to begin with.
  static const int max_sel_bits = 20;

  // Select bits a gather is indexed by, and so the mux levels it costs.
  static int gather_sel_bits(RTLIL::Cell *cell)
  {
    return GetSize(cell->getPort(cell->type == ID($bmux) ? ID::S : ID::B));
  }

  bool gather_geometry(RTLIL::Cell *cell, Gather &g)
  {
    if (cell->type == ID($bmux)) {
      int sel_bits = GetSize(cell->getPort(ID::S));
      g.lane_width = cell->getParam(ID::WIDTH).as_int();
      if (g.lane_width < 1 || sel_bits < 1 || sel_bits > max_sel_bits)
        return false;
      g.sel = sigmap(cell->getPort(ID::S));
      g.table = sigmap(cell->getPort(ID::A));
      // The emit masks the column index with cols - 1, so the table has to be
      // exactly the power of two the select reaches. RTLIL requires that of
      // $bmux, but only check() enforces it, so do not trust it blindly.
      return (long long)g.lane_width << sel_bits == (long long)GetSize(g.table);
    }
    if (cell->type != ID($shiftx))
      return false;
    int sel_bits = cell->getParam(ID::B_WIDTH).as_int();
    // 1 << sel_bits below, and the emit walks every lane, so bound the width.
    if (cell->getParam(ID::Y_WIDTH).as_int() != 1 || sel_bits < 1 || sel_bits > max_sel_bits)
      return false;
    // A signed index reaches negative lanes, where $shiftx returns x rather
    // than a lane, so the permutation below would not be an identity.
    if (cell->getParam(ID::B_SIGNED).as_bool())
      return false;
    // Only a table that exactly covers the index range is a plain select: a
    // short one returns x past its end, a long one is a scaled index.
    if (cell->getParam(ID::A_WIDTH).as_int() != (1 << sel_bits))
      return false;
    g.lane_width = 1;
    g.sel = sigmap(cell->getPort(ID::B));
    g.table = sigmap(cell->getPort(ID::A));
    return true;
  }

  // The two operands of an $xor that drives exactly `sig`. Extension or a
  // partial read would break the bitwise inverse the reindex relies on, so
  // require the whole Y port at the same width as both operands.
  bool xor_operands(const RTLIL::SigSpec &sig, RTLIL::SigSpec &a, RTLIL::SigSpec &b)
  {
    int width = GetSize(sig);
    if (width == 0)
      return false;
    RTLIL::Cell *drv = nullptr;
    for (auto &bit : sig) {
      auto it = driver_map.find(bit);
      if (it == driver_map.end())
        return false;
      if (drv == nullptr)
        drv = it->second;
      else if (drv != it->second)
        return false;
    }
    if (drv == nullptr || drv->type != ID($xor) || sigmap(drv->getPort(ID::Y)) != sig)
      return false;
    a = sigmap(drv->getPort(ID::A));
    b = sigmap(drv->getPort(ID::B));
    return GetSize(a) == width && GetSize(b) == width;
  }

  // Collect the inner gathers under a root: every root lane must be the whole
  // output of its own gather, and all of them must share one row select.
  bool nest_inner_cells(RTLIL::Cell *cell, const Gather &root,
      std::vector<RTLIL::Cell*> &inner, std::vector<Gather> &inner_geo,
      const char **why)
  {
    auto no = [&](const char *reason) {
      if (why != nullptr)
        *why = reason;
      return false;
    };
    inner.clear();
    inner_geo.clear();
    int cols = GetSize(root.table) / root.lane_width;
    if (cols < 2)
      return no("root has fewer than two lanes");
    for (int p = 0; p < cols; p++) {
      RTLIL::SigSpec lane = root.table.extract(p * root.lane_width, root.lane_width);
      RTLIL::Cell *drv = nullptr;
      for (auto &bit : lane) {
        auto it = driver_map.find(bit);
        if (it == driver_map.end())
          return no("root lane is not cell driven");
        if (drv == nullptr)
          drv = it->second;
        else if (drv != it->second)
          return no("root lane spans two drivers");
      }
      // Mixing the two spellings would make the emit pick one arbitrarily, so
      // hold the whole nest to the root's.
      if (drv == nullptr || drv->type != cell->type)
        return no("root lane is not a gather of the root's own type");
      if (!design->selected(module, drv) || drv->get_bool_attribute(ID::keep))
        return no("inner gather is out of scope");
      if (sigmap(drv->getPort(ID::Y)) != lane)
        return no("root reads only part of an inner gather");
      Gather g;
      if (!gather_geometry(drv, g))
        return no("inner gather is not a plain lane select");
      // The inner stage is deleted wholesale, so nothing outside may read it.
      for (auto &bit : lane) {
        if (port_out_bits.count(bit) || keep_bits.count(bit))
          return no("inner gather output is observable");
        auto it = consumer_map.find(bit);
        if (it != consumer_map.end())
          for (auto cons : it->second)
            if (cons != cell)
              return no("inner gather has a reader outside the nest");
      }
      if (p > 0 && inner_geo[0].sel != g.sel)
        return no("inner gathers do not share a select");
      inner.push_back(drv);
      inner_geo.push_back(g);
    }
    return !inner_geo[0].sel.empty();
  }

  // Solve J = E ^ I[0 +: |J|] by finding the base the two selects share. Returns
  // the two halves of E, which the emit xors together.
  bool nest_early_offset(const RTLIL::SigSpec &col_sel, const RTLIL::SigSpec &row_sel,
      RTLIL::SigSpec &ka_lo, RTLIL::SigSpec &kb, const char **why)
  {
    auto no = [&](const char *reason) {
      if (why != nullptr)
        *why = reason;
      return false;
    };
    int cols_bits = GetSize(col_sel);
    if (cols_bits > GetSize(row_sel))
      return no("column select is wider than the row select");
    RTLIL::SigSpec row_a, row_b, col_a, col_b;
    if (!xor_operands(row_sel, row_a, row_b))
      return no("row select is not an $xor");
    if (!xor_operands(col_sel, col_a, col_b))
      return no("column select is not an $xor");
    // Either operand of either xor can be the shared base; the other is the
    // per-index offset.
    for (int r = 0; r < 2; r++)
      for (int c = 0; c < 2; c++) {
        const RTLIL::SigSpec &base = r ? row_b : row_a;
        const RTLIL::SigSpec &offset = r ? row_a : row_b;
        if ((c ? col_b : col_a) != base.extract(0, cols_bits))
          continue;
        ka_lo = offset.extract(0, cols_bits);
        kb = c ? col_a : col_b;
        return true;
      }
    return no("selects do not share a base");
  }

  // The reindex trades the inner stage's place on the late path for the early
  // offset's cone plus that same stage ahead of the root gather. The test is
  // anti-symmetric by construction: run on its own output the roles of the two
  // selects swap, the early side becomes the late one, and it refuses -- so the
  // rewrite cannot rotate back and forth across invocations.
  bool nest_pays(RTLIL::Cell *cell, const RTLIL::SigSpec &row_sel,
      const RTLIL::SigSpec &ka_lo, const RTLIL::SigSpec &kb)
  {
    int col_levels = gather_sel_bits(cell);
    int row_levels = GetSize(row_sel);
    int late = arrival(row_sel);
    int early = std::max(arrival(ka_lo), arrival(kb)) + mux_delay;
    int before = late + row_levels + col_levels;
    int after = std::max(late, early + col_levels) + row_levels;
    log_debug("    %s %s: nest of %d column(s) over %d row(s), before=%d after=%d "
        "(row select at %d, early offset at %d)\n", log_id(cell->type),
        log_id(cell->name), 1 << col_levels, 1 << row_levels, before, after, late, early);
    return after + reindex_gain <= before;
  }

  // Emit a gather in the same spelling as the nest that is being replaced, so a
  // flow that has already lowered one of the two forms does not get it back.
  void add_gather(IdString type, const RTLIL::SigSpec &table, const RTLIL::SigSpec &sel,
      const RTLIL::SigSpec &y, const std::string &src, RTLIL::IdString name)
  {
    if (type == ID($bmux))
      module->addBmux(name, table, sel, y, src);
    else
      module->addShiftx(name, table, sel, y, false, src);
  }

  // bmux(J, [bmux(I, col_p)]) -> bmux(I, [bmux(E, perm_i(row_i))])
  void nest_reindex(RTLIL::Cell *cell, const Gather &root,
      const std::vector<RTLIL::Cell*> &inner, const std::vector<Gather> &inner_geo,
      const RTLIL::SigSpec &ka_lo, const RTLIL::SigSpec &kb,
      pool<RTLIL::Cell*> &cells_to_remove)
  {
    int lane_width = root.lane_width;
    int cols = GetSize(inner);
    int rows = GetSize(inner_geo[0].table) / lane_width;
    std::string src = cell->get_src_attribute();

    // E = KB ^ KA[0 +: |J|]: the column index measured from the row index.
    RTLIL::SigSpec early = module->Xor(NEW_ID2_SUFFIX("reindex_off"), kb, ka_lo, false, src);

    RTLIL::SigSpec rows_out;
    for (int i = 0; i < rows; i++) {
      // Row i holds one entry per column, and xoring the constant i_low into
      // the column index is just a fixed permutation of those entries.
      RTLIL::SigSpec permuted;
      for (int q = 0; q < cols; q++)
        permuted.append(inner_geo[q ^ (i & (cols - 1))].table
            .extract(i * lane_width, lane_width));
      RTLIL::SigSpec row_y = module->addWire(NEW_ID2_SUFFIX("reindex_col"), lane_width);
      add_gather(cell->type, permuted, early, row_y, src,
          NEW_ID2_SUFFIX("reindex_colmux"));
      rows_out.append(row_y);
    }
    add_gather(cell->type, rows_out, inner_geo[0].sel, cell->getPort(ID::Y), src,
        NEW_ID2_SUFFIX("reindex_rowmux"));

    cells_to_remove.insert(cell);
    for (auto col : inner)
      cells_to_remove.insert(col);
  }

  void run_reindex()
  {
    build_connectivity();
    reset_timing();

    pool<RTLIL::Cell*> cells_to_remove;
    for (auto cell : module->selected_cells()) {
      if (!cell->type.in(ID($bmux), ID($shiftx)) || cell->get_bool_attribute(ID::keep))
        continue;
      if (cells_to_remove.count(cell))
        continue;
      RTLIL::SigSpec out = sigmap(cell->getPort(ID::Y));
      if (GetSize(out) == 0 || sig_has_keep(out))
        continue;

      const char *why = "not a gather nest";
      Gather root;
      std::vector<RTLIL::Cell*> inner;
      std::vector<Gather> inner_geo;
      RTLIL::SigSpec ka_lo, kb;
      if (!gather_geometry(cell, root) ||
          !nest_inner_cells(cell, root, inner, inner_geo, &why) ||
          !nest_early_offset(root.sel, inner_geo[0].sel, ka_lo, kb, &why)) {
        log_debug("    %s %s: %s.\n", log_id(cell->type), log_id(cell->name), why);
        continue;
      }
      bool overlaps = false;
      for (auto col : inner)
        overlaps |= cells_to_remove.count(col) > 0;
      if (overlaps)
        continue;
      nests_seen++;

      // The emit lays down one inner gather per row, so the table it writes is
      // rows * cols entries however the nest was spelled.
      int table_bits = GetSize(inner_geo[0].table) * GetSize(inner);
      if (table_bits > reindex_max_bits) {
        log_debug("    %s %s: nest table of %d bit(s) over the cap.\n",
            log_id(cell->type), log_id(cell->name), table_bits);
        nests_big++;
        continue;
      }
      if (!nest_pays(cell, inner_geo[0].sel, ka_lo, kb)) {
        nests_cheap++;
        continue;
      }
      if (timing_guard && path_depth(out) < longest_path() - slack_margin) {
        nests_slack++;
        continue;
      }
      nest_reindex(cell, root, inner, inner_geo, ka_lo, kb, cells_to_remove);
      reindex_count++;
    }

    for (auto cell : cells_to_remove)
      module->remove(cell);

    log_debug("  reindex: %d nested gather(s), %d unprofitable, %d oversized, "
        "%d off-critical.\n", nests_seen, nests_cheap, nests_big, nests_slack);
  }

  void run()
  {
    while (true)
    {
      build_connectivity();
      reset_timing();

      struct candidate_t {
        RTLIL::Cell *cell = nullptr;
        RTLIL::Cell *mux_cell = nullptr;  // null when the select was const-folded away
        IdString port;
        RTLIL::SigSpec arm_a, arm_b, sel;
      };

      std::vector<candidate_t> candidates;

      for (auto cell : module->selected_cells())
      {
        if (!target_types.count(cell->type))
          continue;
        if (cell->get_bool_attribute(ID::keep))
          continue;

        RTLIL::SigSpec cell_out = sigmap(cell->getPort(ID::Y));
        if (sig_has_keep(cell_out))
          continue;

        // Look for one mux driven input to push through per operator
        for (auto &it : cell->connections())
        {
          if (!cell->input(it.first))
            continue;

          RTLIL::SigSpec in_sig = sigmap(it.second);
          RTLIL::Cell *mux_cell = nullptr;
          if (!mux_drives_sig(in_sig, mux_cell)) {
            // Fall back to a select the folder already collapsed into bare bits
            RTLIL::SigBit sel;
            if (!recover_folded || !folded_select(in_sig, sel))
              continue;
            RTLIL::SigSpec arm_a = force_bit(in_sig, sel, false);
            RTLIL::SigSpec arm_b = force_bit(in_sig, sel, true);
            if (!should_push(cell, it.first, arm_a, arm_b))
              continue;
            candidates.push_back({cell, nullptr, it.first, arm_a, arm_b, sel});
            break;
          }
          if (!design->selected(module, mux_cell))
            continue;
          if (mux_cell->get_bool_attribute(ID::keep))
            continue;

          RTLIL::SigSpec mux_out = sigmap(mux_cell->getPort(ID::Y));
          // The operator may read only a slice of the mux (constant-folded
          // adders split into a pass-through part and a carry part), so take
          // the matching bits of each arm rather than the whole mux output.
          RTLIL::SigSpec arm_a, arm_b;
          if (!slice_arms(mux_cell, mux_out, in_sig, arm_a, arm_b))
            continue;
          if (sig_has_keep(mux_out))
            continue;
          if (!fanout_within_limit(mux_out))
            continue;
          if (!should_push(cell, it.first, arm_a, arm_b))
            continue;

          // Only push one mux per operator per iteration
          candidates.push_back({cell, mux_cell, it.first, arm_a, arm_b,
                                mux_cell->getPort(ID::S)});
          break;
        }
      }

      if (candidates.empty())
        break;

      pool<RTLIL::Cell*> cells_to_remove;
      pool<RTLIL::SigBit> touched_bits;

      for (auto &cand : candidates)
      {
        RTLIL::Cell *cell = cand.cell;
        RTLIL::Cell *mux_cell = cand.mux_cell;
        RTLIL::SigSpec cand_in = sigmap(cell->getPort(cand.port));
        bool overlaps = false;
        for (auto &bit : cand_in) {
          if (touched_bits.count(bit)) {
            overlaps = true;
            break;
          }
        }
        if (overlaps)
          continue;
        // Avoid rewriting overlapping signals within a single iteration
        for (auto &bit : cand_in)
          touched_bits.insert(bit);

        std::string via = mux_cell != nullptr
            ? "mux " + std::string(log_id(mux_cell->name)) : "folded select";
        log_debug("    Pushing %s through %s cell %s port %s.\n",
            via.c_str(), log_id(cell->type), log_id(cell->name), log_id(cand.port));

        // Reuse the original operator as branch A to preserve the instance name and metadata
        RTLIL::Cell *branch_a = cell;

        // Create branch B with a deterministic name derived from the original
        RTLIL::IdString branch_b_name = NEW_ID2;
        RTLIL::Cell *branch_b = module->addCell(branch_b_name, cell->type);
        branch_b->parameters = cell->parameters;
        branch_b->set_src_attribute(cell->get_src_attribute());

        RTLIL::SigSpec orig_y = cell->getPort(ID::Y);
        std::vector<std::pair<IdString, RTLIL::SigSpec>> conns;
        for (auto &p : cell->connections())
          conns.push_back(p);
        for (auto &p : conns) {
          RTLIL::SigSpec conn_sig = p.second;
          if (p.first == cand.port) {
            branch_a->setPort(p.first, cand.arm_a);
            branch_b->setPort(p.first, cand.arm_b);
          } else {
            branch_a->setPort(p.first, conn_sig);
            branch_b->setPort(p.first, conn_sig);
          }
        }

        RTLIL::IdString out_a_name = NEW_ID2_SUFFIX("mpa_y");
        RTLIL::IdString out_b_name = NEW_ID2_SUFFIX("mpb_y");
        RTLIL::SigSpec out_a = module->addWire(out_a_name, GetSize(orig_y));
        RTLIL::SigSpec out_b = module->addWire(out_b_name, GetSize(orig_y));
        branch_a->setPort(ID::Y, out_a);
        branch_b->setPort(ID::Y, out_b);
        branch_a->fixup_parameters();
        branch_b->fixup_parameters();

        // Always create a new mux so other consumers of the original mux are unaffected
        RTLIL::IdString new_mux_name = NEW_ID2_SUFFIX("muxpush");
        RTLIL::Cell *new_mux = module->addMux(new_mux_name, out_a, out_b, cand.sel, orig_y);
        new_mux->set_src_attribute(cell->get_src_attribute());

        // Branch A evaluates one speculated arm now, not the original
        // expression, so it must not keep the original name: equiv_make pairs
        // cells by name and then requires their inputs to match, which is
        // exactly what distributing the select breaks.
        module->rename(branch_a, NEW_ID2_SUFFIX("mpa"));

        // Remove the original mux when it becomes dead after the rewrite. The
        // new mux only takes over the bits the operator read, so a bit outside
        // that slice still has a consumer of its own and the mux has to stay --
        // fanout_is_one alone would drop it and leave that bit undriven.
        // A folded select has no mux cell of its own to drop.
        if (mux_cell != nullptr) {
          RTLIL::SigSpec mux_out = sigmap(mux_cell->getPort(ID::Y));
          pool<RTLIL::SigBit> read_bits(cand_in.begin(), cand_in.end());
          bool covers_mux_out = true;
          for (auto &bit : mux_out)
            if (!read_bits.count(bit))
              covers_mux_out = false;
          if (covers_mux_out && fanout_is_one(mux_out))
            cells_to_remove.insert(mux_cell);
        }

        total_count++;
      }

      for (auto cell : cells_to_remove)
        module->remove(cell);
    }
  }
};

struct OptMuxPushPass : public Pass {
  OptMuxPushPass() : Pass("muxpush", "push muxes through lightweight operators") { }

  void help() override
  {
    log("\n");
    log("    muxpush [options] [selection]\n");
    log("\n");
    log("Push $mux cells forward through lightweight operators by cloning\n");
    log("the operator and re-inserting the mux at the output.\n");
    log("\n");
    log("    -limit <int>\n");
    log("        maximum fanout allowed for the mux output (default: 1)\n");
    log("\n");
    log("    -types <string>\n");
    log("        comma-separated list of operator cell types to push through\n");
    log("        (default: $add,$sub,$xor). $mux is rejected: the pass emits a\n");
    log("        $mux, so targeting it would make its own output a candidate and\n");
    log("        never fixpoint\n");
    log("\n");
    log("    -timing\n");
    log("        only push when the push buys depth on a path that is long\n");
    log("        enough to matter: a unit-level delay estimate must say the\n");
    log("        select is the mux's late input (or the mux must split a chain\n");
    log("        of associable operators), and the operator must sit within\n");
    log("        reach of the module's longest path\n");
    log("\n");
    log("    -slack-margin <int>\n");
    log("        how many levels short of the longest path still counts as\n");
    log("        critical for -timing (default: 0)\n");
    log("\n");
    log("    -folded-select\n");
    log("        also push through a select that const-folding already collapsed\n");
    log("        into bare replicated bits, leaving no $mux cell to match on (an\n");
    log("        operand like {1'b0, s, s}). Off by default because it only pays\n");
    log("        where the arms fold back down: on comparators reading a select\n");
    log("        that no later pass has restructured. Enabling it on shifter\n");
    log("        amounts, or on comparators after the pattern matchers have run,\n");
    log("        measured worse than leaving the operand alone\n");
    log("\n");
    log("    -hoist-late\n");
    log("        lift the late arm out of a mux priority chain. A datapath\n");
    log("        feeding the default of a chain of control muxes pays one level\n");
    log("        per control mux, but the chain is a priority select, so that arm\n");
    log("        can be taken under the accumulated not-taken condition and the\n");
    log("        early arms rebuilt beside it. Only fires when a unit-level\n");
    log("        estimate says the default really is the chain's late arm\n");
    log("\n");
    log("    -hoist-gain <int>\n");
    log("        levels the hoist must buy before it fires (default: 2). Shallow\n");
    log("        wins do not survive downstream remapping\n");
    log("\n");
    log("    -farm-select\n");
    log("        also push a shift through a per-bit select farm, where every\n");
    log("        output bit has its own $mux and there is no bus-wide select to\n");
    log("        match on (RTL like `for (i...) p[i] = i < n ? a[i] : b[i];`\n");
    log("        feeding `p >> s`). Shifting such an operand has to shift the\n");
    log("        select vector too, which is why the ordinary push cannot express\n");
    log("        it. Only applies to $shl/$shr/$sshl/$sshr in -types\n");
    log("\n");
    log("    -farm-gain <int>\n");
    log("        levels a farm push must buy before it fires (default: 1). The\n");
    log("        push is depth-neutral by itself -- the clones just trade the mux\n");
    log("        level for the shift level -- so the gain comes entirely from an\n");
    log("        arm that opt_shift -combine can then fold into the shift above\n");
    log("        it. At 0 it would fire on farms that only cost area\n");
    log("\n");
    log("    -gather-reindex\n");
    log("        swap the nesting of a two-level gather (`V[i][j]`, an inner\n");
    log("        lane select per column under a root one -- $bmux either way, or\n");
    log("        single-bit $shiftx) when the two indices are\n");
    log("        xor offsets of one computed base, as a set/way pair derived from\n");
    log("        a single index is. The column index is then an early function of\n");
    log("        the row index, so driving the inner stage with it takes that\n");
    log("        stage off the late path and the read costs only the row select's\n");
    log("        levels. The rewrite is an exact xor identity, not a don't-care\n");
    log("\n");
    log("    -reindex-gain <int>\n");
    log("        levels a reindex must buy before it fires (default: 1)\n");
    log("\n");
    log("    -reindex-max-bits <int>\n");
    log("        cap on the rows * columns * lane-width table the reindex emits\n");
    log("        (default: 4096). The swap is area-neutral in principle, but a\n");
    log("        wide nest still rebuilds every entry\n");
    log("\n");
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    int fanout_limit = 1;
    bool timing_guard = false;
    int slack_margin = 0;
    bool recover_folded = false;
    bool hoist_late = false;
    int hoist_gain = 2;
    bool farm_select = false;
    int farm_gain = 1;
    bool gather_reindex = false;
    int reindex_gain = 1;
    int reindex_max_bits = 4096;
    std::string types = "$add,$sub,$xor";

    log_header(design, "Executing MUXPUSH pass (push muxes through light ops).\n");

    size_t argidx;
    for (argidx = 1; argidx < args.size(); argidx++) {
      if (args[argidx] == "-limit" && argidx+1 < args.size()) {
        fanout_limit = atoi(args[++argidx].c_str());
        continue;
      }
      if (args[argidx] == "-types" && argidx+1 < args.size()) {
        types = args[++argidx];
        continue;
      }
      if (args[argidx] == "-timing") {
        timing_guard = true;
        continue;
      }
      if (args[argidx] == "-folded-select") {
        recover_folded = true;
        continue;
      }
      if (args[argidx] == "-hoist-late") {
        hoist_late = true;
        continue;
      }
      if (args[argidx] == "-hoist-gain" && argidx+1 < args.size()) {
        hoist_gain = atoi(args[++argidx].c_str());
        if (hoist_gain < 1)
          log_cmd_error("muxpush: -hoist-gain must be at least 1.\n");
        continue;
      }
      if (args[argidx] == "-farm-select" || args[argidx] == "-farm_select") {
        farm_select = true;
        continue;
      }
      if ((args[argidx] == "-farm-gain" || args[argidx] == "-farm_gain")
          && argidx+1 < args.size()) {
        farm_gain = atoi(args[++argidx].c_str());
        // At 0 the push fires on farms where no arm folds, which is pure area.
        if (farm_gain < 1)
          log_cmd_error("muxpush: -farm-gain must be at least 1.\n");
        continue;
      }
      if (args[argidx] == "-gather-reindex" || args[argidx] == "-gather_reindex") {
        gather_reindex = true;
        continue;
      }
      if ((args[argidx] == "-reindex-gain" || args[argidx] == "-reindex_gain")
          && argidx+1 < args.size()) {
        reindex_gain = atoi(args[++argidx].c_str());
        // At 0 the reindex fires on nests it buys nothing on, which is pure area.
        if (reindex_gain < 1)
          log_cmd_error("muxpush: -reindex-gain must be at least 1.\n");
        continue;
      }
      if ((args[argidx] == "-reindex-max-bits" || args[argidx] == "-reindex_max_bits")
          && argidx+1 < args.size()) {
        reindex_max_bits = atoi(args[++argidx].c_str());
        if (reindex_max_bits < 1)
          log_cmd_error("muxpush: -reindex-max-bits must be at least 1.\n");
        continue;
      }
      if ((args[argidx] == "-slack-margin" || args[argidx] == "-slack_margin")
          && argidx+1 < args.size()) {
        slack_margin = atoi(args[++argidx].c_str());
        // A negative margin would demand slack below zero, which no candidate
        // can reach, so the guard would silently refuse everything.
        if (slack_margin < 0)
          log_cmd_error("muxpush: -slack-margin must not be negative.\n");
        continue;
      }
      break;
    }
    extra_args(args, argidx, design);

    pool<IdString> target_types;
    for (auto &tok : split_tokens(types, ", \t\r\n")) {
      if (tok.empty())
        continue;
      IdString type = RTLIL::escape_id(tok);
      // The rewrite re-inserts a $mux at the operator's output, so targeting
      // $mux makes the pass's own output a candidate. Each push then just
      // rotates the two muxes -- same cell count, one more level of name -- and
      // run() never reaches a fixpoint. Refuse rather than spin.
      if (type == ID($mux))
        log_cmd_error("muxpush: -types must not include $mux: it is the cell this "
            "pass emits, so pushing a mux through a mux never fixpoints.\n");
      target_types.insert(type);
    }

    // run() and the farm sweep start from a cell of a target type, -hoist-late
    // also from a bare mux chain, and -gather-reindex from a gather nest. A
    // module holding none of those can produce no candidate, so skip it before
    // the worker builds a sigmap and a connectivity map over it. On a design of
    // many small modules that bookkeeping, not the matching, is what the pass
    // spends its time on. Anything added here that sweeps from a new root type
    // has to be admitted below, or its candidates go unseen.
    auto module_has_work = [&](RTLIL::Module *mod) {
      for (auto cell : mod->cells()) {
        if (target_types.count(cell->type))
          return true;
        if (hoist_late && cell->type.in(ID($mux), ID($pmux)))
          return true;
        if (gather_reindex && cell->type.in(ID($bmux), ID($shiftx)))
          return true;
      }
      return false;
    };

    int total_count = 0, hoist_count = 0, farm_count = 0, reindex_count = 0;
    for (auto module : design->selected_modules()) {
      if (module->get_bool_attribute(ID::blackbox))
        continue;
      if (!module_has_work(module))
        continue;
      OptMuxPushWorker worker(design, module, target_types, fanout_limit, timing_guard,
          slack_margin, recover_folded, hoist_gain, farm_gain, reindex_gain,
          reindex_max_bits);
      if (hoist_late)
        worker.run_hoist();
      // Before run(): a farm push leaves the arms readable as ordinary operands,
      // which is the shape the bus-wide push matches on.
      if (farm_select)
        worker.run_farm();
      // Before run() as well: run() can rewrite the offset xor that the nest's
      // index relation is matched on, which would hide the relation.
      if (gather_reindex)
        worker.run_reindex();
      worker.run();
      total_count += worker.total_count;
      hoist_count += worker.hoist_count;
      farm_count += worker.farm_count;
      reindex_count += worker.reindex_count;
    }

    log("  Pushed muxes through %d operator inputs.\n", total_count);
    if (hoist_late)
      log("  Hoisted the late arm out of %d mux priority chain(s).\n", hoist_count);
    if (farm_select)
      log("  Pushed %d shift(s) through a per-bit select farm.\n", farm_count);
    if (gather_reindex)
      log("  Reindexed %d nested gather(s) onto the early column index.\n", reindex_count);
  }
} OptMuxPushPass;

PRIVATE_NAMESPACE_END
