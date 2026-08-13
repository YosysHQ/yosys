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

// Unit-level delay heuristic, same shape as opt_timing_balance's: carry-chain
// operators cost their log-depth, bitwise operators and muxes one level.
static int log2p1_int(int w)
{
  int n = 0;
  while (w > 0) { w >>= 1; n++; }
  return n < 1 ? 1 : n;
}

static int estimate_cell_delay(RTLIL::Cell *cell)
{
  IdString t = cell->type;
  if (t.in(ID($not), ID($pos), ID($_NOT_), ID($_BUF_)))
    return 0;
  int width = 1;
  if (cell->hasParam(ID::Y_WIDTH))
    width = cell->getParam(ID::Y_WIDTH).as_int();
  else if (cell->hasParam(ID::WIDTH))
    width = cell->getParam(ID::WIDTH).as_int();
  if (t.in(ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor)))
    return width < 1 ? 1 : width;
  if (t.in(ID($add), ID($sub), ID($neg), ID($alu),
           ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx)))
    return log2p1_int(width);
  // Comparators and reductions collapse their operand width to one bit.
  if (t.in(ID($lt), ID($le), ID($gt), ID($ge), ID($eq), ID($ne), ID($eqx), ID($nex),
           ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor),
           ID($reduce_bool), ID($logic_not), ID($logic_and), ID($logic_or)))
    return log2p1_int(cell->hasParam(ID::A_WIDTH) ? cell->getParam(ID::A_WIDTH).as_int() : width);
  if (t == ID($pmux))
    return log2p1_int(cell->hasParam(ID::S_WIDTH) ? cell->getParam(ID::S_WIDTH).as_int() : 1);
  return 1;
}

struct OptMuxPushWorker
{
  RTLIL::Design *design;
  RTLIL::Module *module;
  SigMap sigmap;

  dict<SigBit, RTLIL::Cell*> driver_map;
  dict<SigBit, int> fanout_map;
  dict<SigBit, std::vector<RTLIL::Cell*>> consumer_map;
  pool<SigBit> keep_bits;
  dict<SigBit, int> arrival_cache;
  pool<SigBit> arrival_active;
  dict<SigBit, int> depart_cache;
  pool<SigBit> depart_active;
  int module_depth;

  pool<IdString> target_types;
  int fanout_limit;
  bool timing_guard;
  int slack_margin;
  bool recover_folded;
  int total_count;

  OptMuxPushWorker(RTLIL::Design *design, RTLIL::Module *module,
      const pool<IdString> &target_types, int fanout_limit, bool timing_guard,
      int slack_margin, bool recover_folded) :
      design(design), module(module), sigmap(module), module_depth(0),
      target_types(target_types), fanout_limit(fanout_limit),
      timing_guard(timing_guard), slack_margin(slack_margin),
      recover_folded(recover_folded), total_count(0)
  {
  }

  // Cached level, or 0 when absent (start point, constant, or broken loop edge).
  static int level_of(const dict<SigBit, int> &cache, RTLIL::SigBit bit)
  {
    auto it = cache.find(bit);
    return it == cache.end() ? 0 : it->second;
  }

  // Combinational driver of `bit`, and the bits feeding it. Null at a start
  // point (constant, undriven / multi-driven, or register output).
  RTLIL::Cell *driver_inputs(RTLIL::SigBit bit, std::vector<RTLIL::SigBit> &ins)
  {
    ins.clear();
    auto it = driver_map.find(bit);
    RTLIL::Cell *drv = it == driver_map.end() ? nullptr : it->second;
    if (drv == nullptr || drv->is_builtin_ff())
      return nullptr;
    for (auto &conn : drv->connections())
      if (drv->input(conn.first))
        for (auto &in_bit : sigmap(conn.second))
          ins.push_back(in_bit);
    return drv;
  }

  // Output bits of a cell, flattened across its output ports.
  void cell_outputs(RTLIL::Cell *cell, std::vector<RTLIL::SigBit> &outs)
  {
    outs.clear();
    for (auto &conn : cell->connections())
      if (cell->output(conn.first))
        for (auto &out_bit : sigmap(conn.second))
          outs.push_back(out_bit);
  }

  // Levels from a start point up to this bit.
  int arrival_bit(RTLIL::SigBit bit)
  {
    if (bit.wire == nullptr)
      return 0;
    if (arrival_cache.count(bit))
      return arrival_cache.at(bit);

    std::vector<RTLIL::SigBit> stack{bit}, ins;
    while (!stack.empty()) {
      RTLIL::SigBit b = stack.back();
      if (b.wire == nullptr || arrival_cache.count(b)) {
        stack.pop_back();
        continue;
      }

      // Push unresolved inputs; skip actives (loop) and constants (never cached).
      RTLIL::Cell *drv = driver_inputs(b, ins);
      bool ready = true;
      for (auto &in_bit : ins)
        if (in_bit.wire != nullptr && !arrival_cache.count(in_bit) &&
            !arrival_active.count(in_bit)) {
          stack.push_back(in_bit);
          ready = false;
        }
      if (!ready) {
        arrival_active.insert(b);
        continue; // leave b on the stack; neighbours are above it now
      }

      int latest = 0;
      for (auto &in_bit : ins)
        latest = std::max(latest, level_of(arrival_cache, in_bit));
      arrival_cache[b] = drv == nullptr ? 0 : latest + estimate_cell_delay(drv);
      arrival_active.erase(b);
      stack.pop_back();
    }
    return arrival_cache.at(bit);
  }

  int arrival(const RTLIL::SigSpec &sig)
  {
    int t = 0;
    for (auto &bit : sigmap(sig))
      t = std::max(t, arrival_bit(bit));
    return t;
  }

  // Levels from this bit down to the latest endpoint that reads it.
  int depart_bit(RTLIL::SigBit bit)
  {
    if (bit.wire == nullptr)
      return 0;
    if (depart_cache.count(bit))
      return depart_cache.at(bit);

    std::vector<RTLIL::SigBit> stack{bit}, outs;
    while (!stack.empty()) {
      RTLIL::SigBit b = stack.back();
      if (b.wire == nullptr || depart_cache.count(b)) {
        stack.pop_back();
        continue;
      }

      // Push unresolved fanout bits; registers end a path (no neighbours).
      bool ready = true;
      auto it_cons = consumer_map.find(b);
      if (it_cons != consumer_map.end())
        for (auto cons : it_cons->second) {
          if (cons->is_builtin_ff())
            continue;
          cell_outputs(cons, outs);
          for (auto &out_bit : outs)
            if (out_bit.wire != nullptr && !depart_cache.count(out_bit) &&
                !depart_active.count(out_bit)) {
              stack.push_back(out_bit);
              ready = false;
            }
        }
      if (!ready) {
        depart_active.insert(b);
        continue;
      }

      int worst = 0;
      if (it_cons != consumer_map.end())
        for (auto cons : it_cons->second) {
          if (cons->is_builtin_ff())
            continue;
          int latest = 0;
          cell_outputs(cons, outs);
          for (auto &out_bit : outs)
            latest = std::max(latest, level_of(depart_cache, out_bit));
          worst = std::max(worst, estimate_cell_delay(cons) + latest);
        }
      depart_cache[b] = worst;
      depart_active.erase(b);
      stack.pop_back();
    }
    return depart_cache.at(bit);
  }

  // Longest path through this signal, in the same unit-delay currency as the
  // module's own depth.
  int path_depth(const RTLIL::SigSpec &sig)
  {
    int t = 0;
    for (auto &bit : sigmap(sig))
      t = std::max(t, arrival_bit(bit) + depart_bit(bit));
    return t;
  }

  void compute_module_depth()
  {
    module_depth = 0;
    for (auto cell : module->cells()) {
      for (auto &conn : cell->connections()) {
        if (!cell->output(conn.first))
          continue;
        for (auto &bit : sigmap(conn.second))
          module_depth = std::max(module_depth, arrival_bit(bit) + depart_bit(bit));
      }
    }
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
    int slack = module_depth - path_depth(cell->getPort(ID::Y));
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

  void run()
  {
    while (true)
    {
      build_connectivity();
      arrival_cache.clear();
      arrival_active.clear();
      depart_cache.clear();
      depart_active.clear();
      if (timing_guard)
        compute_module_depth();

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
        branch_b->attributes = cell->attributes;
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
    log("        (default: $add,$sub,$xor)\n");
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
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    int fanout_limit = 1;
    bool timing_guard = false;
    int slack_margin = 0;
    bool recover_folded = false;
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
      target_types.insert(RTLIL::escape_id(tok));
    }

    int total_count = 0;
    for (auto module : design->selected_modules()) {
      if (module->get_bool_attribute(ID::blackbox))
        continue;
      OptMuxPushWorker worker(design, module, target_types, fanout_limit, timing_guard,
          slack_margin, recover_folded);
      worker.run();
      total_count += worker.total_count;
    }

    log("  Pushed muxes through %d operator inputs.\n", total_count);
  }
} OptMuxPushPass;

PRIVATE_NAMESPACE_END
