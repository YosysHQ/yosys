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
  dict<SigBit, int> arrival_cache;
  pool<SigBit> arrival_active;
  dict<SigBit, int> depart_cache;
  pool<SigBit> depart_active;
  int module_depth;

  pool<IdString> target_types;
  int fanout_limit;
  bool timing_guard;
  int slack_margin;
  int total_count;

  OptMuxPushWorker(RTLIL::Design *design, RTLIL::Module *module,
      const pool<IdString> &target_types, int fanout_limit, bool timing_guard,
      int slack_margin) :
      design(design), module(module), sigmap(module), module_depth(0),
      target_types(target_types), fanout_limit(fanout_limit),
      timing_guard(timing_guard), slack_margin(slack_margin), total_count(0)
  {
  }

  // Memoized backward level estimate. Sequential and undriven bits are start
  // points; the active set breaks combinational loops.
  int arrival_bit(RTLIL::SigBit bit)
  {
    if (bit.wire == nullptr)
      return 0;
    auto it = arrival_cache.find(bit);
    if (it != arrival_cache.end())
      return it->second;
    if (!arrival_active.insert(bit).second)
      return 0;
    int result = 0;
    auto it_drv = driver_map.find(bit);
    if (it_drv != driver_map.end() && it_drv->second != nullptr) {
      RTLIL::Cell *drv = it_drv->second;
      if (!drv->is_builtin_ff()) {
        int max_in = 0;
        for (auto &conn : drv->connections()) {
          if (!drv->input(conn.first))
            continue;
          for (auto &in_bit : sigmap(conn.second))
            max_in = std::max(max_in, arrival_bit(in_bit));
        }
        result = max_in + estimate_cell_delay(drv);
      }
    }
    arrival_active.erase(bit);
    arrival_cache[bit] = result;
    return result;
  }

  int arrival(const RTLIL::SigSpec &sig)
  {
    int t = 0;
    for (auto &bit : sigmap(sig))
      t = std::max(t, arrival_bit(bit));
    return t;
  }

  // Mirror of arrival_bit walking forward: levels from this bit to the latest
  // endpoint that reads it. Registers and unread bits end a path.
  int depart_bit(RTLIL::SigBit bit)
  {
    if (bit.wire == nullptr)
      return 0;
    auto it = depart_cache.find(bit);
    if (it != depart_cache.end())
      return it->second;
    if (!depart_active.insert(bit).second)
      return 0;
    int result = 0;
    auto it_cons = consumer_map.find(bit);
    if (it_cons != consumer_map.end()) {
      for (auto cons : it_cons->second) {
        if (cons->is_builtin_ff())
          continue;
        int max_out = 0;
        for (auto &conn : cons->connections()) {
          if (!cons->output(conn.first))
            continue;
          for (auto &out_bit : sigmap(conn.second))
            max_out = std::max(max_out, depart_bit(out_bit));
        }
        result = std::max(result, estimate_cell_delay(cons) + max_out);
      }
    }
    depart_active.erase(bit);
    depart_cache[bit] = result;
    return result;
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

  // Pushing pays when the select is the mux's late input: the operators then
  // evaluate on the early arms in parallel with the select instead of queueing
  // behind it. Otherwise it is pure area for no depth.
  bool should_push(RTLIL::Cell *cell, IdString port, RTLIL::Cell *mux_cell,
      const RTLIL::SigSpec &arm_a, const RTLIL::SigSpec &arm_b)
  {
    if (!timing_guard)
      return true;

    // Whatever depth the push buys locally, it can only shorten the module's
    // longest path if this operator sits on one. Anywhere else it duplicates
    // the operator for a win no endpoint ever sees.
    int slack = module_depth - path_depth(cell->getPort(ID::Y));

    if (push_merges_chain(cell, arm_a, arm_b)) {
      // The balancer reassociates the merged chain, so the payoff is not local
      // and there is no gain here to compare the slack against.
      log_debug("    %s %s port %s: chain merge, slack=%d\n",
          log_id(cell->type), log_id(cell->name), log_id(port), slack);
      return slack <= slack_margin;
    }

    int d_a = arrival(arm_a);
    int d_b = arrival(arm_b);
    int d_s = arrival(mux_cell->getPort(ID::S));
    int d_mux = estimate_cell_delay(mux_cell);
    int d_op = estimate_cell_delay(cell);

    int others = 0;
    for (auto &conn : cell->connections()) {
      if (!cell->input(conn.first) || conn.first == port)
        continue;
      others = std::max(others, arrival(conn.second));
    }

    int before = std::max(std::max(std::max(d_a, d_b), d_s) + d_mux, others) + d_op;
    int after = std::max(std::max(std::max(d_a, d_b), others) + d_op, d_s) + d_mux;
    int gain = before - after;
    log_debug("    %s %s port %s: dA=%d dB=%d dS=%d before=%d after=%d slack=%d\n",
        log_id(cell->type), log_id(cell->name), log_id(port), d_a, d_b, d_s,
        before, after, slack);
    // A gain smaller than the slack is absorbed by the path that is actually
    // critical, so require the push to reach it.
    return gain > 0 && slack - slack_margin < gain;
  }

  void build_connectivity()
  {
    driver_map.clear();
    fanout_map.clear();
    consumer_map.clear();

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

  bool sig_has_keep(const RTLIL::SigSpec &sig)
  {
    for (auto &bit : sig) {
      if (bit.wire != nullptr && bit.wire->get_bool_attribute(ID::keep))
        return true;
    }
    return false;
  }

  bool mux_drives_sig(const RTLIL::SigSpec &sig, RTLIL::Cell *&mux_cell)
  {
    mux_cell = nullptr;
    for (auto &bit : sig) {
      if (bit.wire == nullptr)
        return false;
      // Require a single consistent driver for all bits in the SigSpec
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
      if (it == pos.end())
        return false;
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
        RTLIL::Cell *mux_cell = nullptr;
        IdString port;
        RTLIL::SigSpec arm_a, arm_b;
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
          if (!mux_drives_sig(in_sig, mux_cell))
            continue;
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
          if (!should_push(cell, it.first, mux_cell, arm_a, arm_b))
            continue;

          // Only push one mux per operator per iteration
          candidates.push_back({cell, mux_cell, it.first, arm_a, arm_b});
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

        log_debug("    Pushing mux %s through %s cell %s port %s.\n",
            log_id(mux_cell->name), log_id(cell->type), log_id(cell->name), log_id(cand.port));

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
        RTLIL::Cell *new_mux = module->addMux(new_mux_name, out_a, out_b, mux_cell->getPort(ID::S), orig_y);
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
        RTLIL::SigSpec mux_out = sigmap(mux_cell->getPort(ID::Y));
        pool<RTLIL::SigBit> read_bits(cand_in.begin(), cand_in.end());
        bool covers_mux_out = true;
        for (auto &bit : mux_out)
          if (!read_bits.count(bit))
            covers_mux_out = false;
        if (covers_mux_out && fanout_is_one(mux_out))
          cells_to_remove.insert(mux_cell);

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
  }

  void execute(std::vector<std::string> args, RTLIL::Design *design) override
  {
    int fanout_limit = 1;
    bool timing_guard = false;
    int slack_margin = 0;
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
      if ((args[argidx] == "-slack-margin" || args[argidx] == "-slack_margin")
          && argidx+1 < args.size()) {
        slack_margin = atoi(args[++argidx].c_str());
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
          slack_margin);
      worker.run();
      total_count += worker.total_count;
    }

    log("  Pushed muxes through %d operator inputs.\n", total_count);
  }
} OptMuxPushPass;

PRIVATE_NAMESPACE_END
