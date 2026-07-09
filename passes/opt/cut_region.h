/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.     <akash@silimate.com>
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
 */

// Shared cut-region matching infrastructure for the functional rewrite
// passes (opt_argmax, opt_priority_onehot, opt_compact_prefix,
// opt_first_fit_alloc). These passes find combinational regions between
// "cut" signals (module ports, FF data pins, or internal buses), verify
// their function by ConstEval fingerprinting, and replace the region while
// leaving surrounding logic untouched.
//
// This header is designed to be included INSIDE each pass's private
// namespace (after PRIVATE_NAMESPACE_BEGIN), so the shared code has a single
// source without introducing link-level coupling between the passes.
// Tiny shared helpers (is_sequential, clog2_int, const_u64, ...) live in
// rewrite_utils.h so non-cut-region passes can share them too.
//
// All graph walks and fingerprint evaluations are charged against
// per-module work budgets so that adversarial netlist shapes (deep shared
// cones with hundreds of same-width candidate buses) degrade into skipped
// candidates instead of multi-minute runtimes.

#include "passes/opt/rewrite_utils.h"

struct CutRegionWorker
{
	struct RootCand {
		SigSpec sig;
		std::string name;
	};

	struct BusCand {
		SigSpec sig;
		std::string name;
		int entries = 0;
		int elem_width = 0;
		bool is_const = false;
	};

	Module *module;
	SigMap sigmap;
	dict<SigBit, Cell *> bit_to_driver;
	pool<SigBit> input_port_bits;
	pool<SigBit> claimed_bits;
	std::string last_cut_fail;

	// Work budgets, decremented as the search runs. Walk steps count cells
	// visited by cone/cut traversals; eval steps approximate ConstEval cost
	// as (test vectors x cone cells); attempts count cut-closure trials
	// (each one also carries pool/queue setup overhead, so the count is
	// bounded separately from the step total). When a budget runs out the
	// remaining candidates in the module are skipped (matching is
	// best-effort).
	int64_t walk_budget = 20000000;
	int64_t eval_budget = 20000000;
	int64_t attempt_budget = 65536;

	bool walk_exhausted() const { return walk_budget <= 0 || attempt_budget <= 0; }
	bool eval_exhausted() const { return eval_budget <= 0; }
	void charge_walk(int64_t n) { walk_budget -= n; }
	void charge_eval(int64_t n) { eval_budget -= n; }

	// One visible note per module when a budget runs out, so QoR changes
	// caused by truncated candidate searches are diagnosable from the log
	// (the pass options can then raise the budget for that design).
	bool budget_noted = false;
	void note_budget(const char *pass_name, int skipped_roots)
	{
		if (budget_noted)
			return;
		if (!walk_exhausted() && !eval_exhausted())
			return;
		budget_noted = true;
		const char *which = attempt_budget <= 0 ? "attempt budget" :
		                    walk_budget <= 0 ? "walk budget" : "eval budget";
		log_debug("Note: %s search %s exhausted in module %s; %d remaining root candidate(s) skipped. "
		          "Use the pass budget options to raise the limit if QoR matters more than runtime here.\n",
		          pass_name, which, log_id(module), skipped_roots);
	}

	CutRegionWorker(Module *module) : module(module), sigmap(module)
	{
		build_indexes();
	}

	void build_indexes()
	{
		for (auto c : module->cells()) {
			if (is_sequential(c))
				continue;
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire)
						continue;
					auto it = bit_to_driver.find(bit);
					if (it == bit_to_driver.end())
						bit_to_driver[bit] = c;
					else if (it->second != c)
						it->second = nullptr;
				}
			}
		}

		for (auto w : module->wires()) {
			if (!w->port_input)
				continue;
			for (auto bit : sigmap(SigSpec(w)))
				if (bit.wire)
					input_port_bits.insert(bit);
		}
	}

	// Combinational fanin cone of `from`. Leaves are port-input bits or bits
	// driven by sequential cells / undriven. Returns false if size limits
	// are exceeded. `cell_order` records the cells in BFS discovery order
	// (closest to `from` first).
	bool get_cone(SigSpec from, pool<Cell *> &cone_cells, pool<SigBit> &leaf_bits,
	              int max_cone_cells, int max_leaf_bits, vector<Cell *> *cell_order = nullptr)
	{
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		for (auto bit : sigmap(from)) {
			if (!bit.wire)
				continue;
			if (visited.insert(bit).second)
				worklist.push(bit);
		}

		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();

			if (input_port_bits.count(bit)) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits)
					return false;
				continue;
			}

			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr) {
				leaf_bits.insert(bit);
				if (GetSize(leaf_bits) > max_leaf_bits)
					return false;
				continue;
			}

			if (!cone_cells.insert(drv).second)
				continue;
			charge_walk(1);
			if (GetSize(cone_cells) > max_cone_cells)
				return false;
			if (cell_order != nullptr)
				cell_order->push_back(drv);

			for (auto &conn : drv->connections()) {
				if (!drv->input(conn.first))
					continue;
				for (auto in_bit : sigmap(conn.second)) {
					if (!in_bit.wire)
						continue;
					if (visited.insert(in_bit).second)
						worklist.push(in_bit);
				}
			}
		}

		return true;
	}

	// Walk the cone of `root`, cutting it at the bits in `allowed`. Returns
	// true iff the cut cone closes (no other primary input / undriven bit is
	// reached). `hit_bits`, when given, collects the allowed bits the cone
	// actually uses. `forced_bits`, when given, is the subset of allowed
	// bits the fingerprint will force: no forced bit may be driven by a cell
	// inside the cut cone, since ConstEval caches whole cell outputs and
	// evaluating such a driver would conflict with the forced values (when
	// `forced_bits` is null, all of `allowed` is treated as forced).
	bool cut_cone_walk(const SigSpec &root, const pool<SigBit> &allowed, int max_cells,
	                   pool<SigBit> *hit_bits = nullptr, pool<Cell *> *cells_out = nullptr,
	                   const pool<SigBit> *forced_bits = nullptr,
	                   const pool<SigBit> *full_leaves = nullptr,
	                   const pool<Cell *> *full_cells = nullptr)
	{
		attempt_budget--;
		// Walk-free fast path: when no allowed bit has a combinational
		// driver, no cut can shadow any cone leaf, so the cut closes iff it
		// covers every leaf of the full cone (and the cut cone is the full
		// cone). This answers the dominant class of failing candidates
		// (port/FF-level bus pairs) in a handful of hash lookups.
		if (full_leaves != nullptr && full_cells != nullptr) {
			bool allowed_all_leaf = true;
			for (auto bit : allowed)
				if (bit_to_driver.at(bit, nullptr) != nullptr) {
					allowed_all_leaf = false;
					break;
				}
			if (allowed_all_leaf) {
				for (auto leaf : *full_leaves)
					if (!allowed.count(leaf)) {
						last_cut_fail = stringf("leaf %s", log_signal(leaf));
						return false;
					}
				if (GetSize(*full_cells) > max_cells) {
					last_cut_fail = "size limit";
					return false;
				}
				if (hit_bits != nullptr)
					*hit_bits = *full_leaves;
				if (cells_out != nullptr)
					*cells_out = *full_cells;
				return true;
			}
		}

		pool<SigBit> visited;
		pool<Cell *> cells_seen;
		std::queue<SigBit> worklist;
		for (auto bit : sigmap(root)) {
			if (!bit.wire)
				continue;
			if (visited.insert(bit).second)
				worklist.push(bit);
		}

		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();

			if (allowed.count(bit)) {
				if (hit_bits != nullptr)
					hit_bits->insert(bit);
				continue;
			}

			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr) {
				last_cut_fail = stringf("leaf %s", log_signal(bit));
				return false;
			}

			if (!cells_seen.insert(drv).second)
				continue;
			charge_walk(1);
			if (GetSize(cells_seen) > max_cells || walk_exhausted()) {
				last_cut_fail = "size limit";
				return false;
			}

			for (auto &conn : drv->connections()) {
				if (!drv->input(conn.first))
					continue;
				for (auto in_bit : sigmap(conn.second)) {
					if (!in_bit.wire)
						continue;
					if (visited.insert(in_bit).second)
						worklist.push(in_bit);
				}
			}
		}

		const pool<SigBit> &check = (forced_bits != nullptr) ? *forced_bits :
		                            (hit_bits != nullptr) ? *hit_bits : allowed;
		for (auto bit : check) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr && cells_seen.count(drv)) {
				last_cut_fail = stringf("forced bit %s driven inside cone", log_signal(bit));
				return false;
			}
		}

		if (cells_out != nullptr)
			*cells_out = cells_seen;
		return true;
	}

	// Walk the cone of `root` cut at `allowed`, collecting up to `max_extra`
	// remaining boundary bits (inputs the cut does not cover) instead of
	// failing on them. Aborts early once the limit is crossed, since callers
	// only probe small uncovered sets.
	bool cut_cone_extra_leaves(const SigSpec &root, const pool<SigBit> &allowed, int max_cells,
	                           pool<SigBit> &extra_leaves, int max_extra)
	{
		attempt_budget--;
		pool<SigBit> visited;
		pool<Cell *> cells_seen;
		std::queue<SigBit> worklist;
		for (auto bit : sigmap(root)) {
			if (!bit.wire)
				continue;
			if (visited.insert(bit).second)
				worklist.push(bit);
		}

		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();

			if (allowed.count(bit))
				continue;

			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr) {
				extra_leaves.insert(bit);
				if (GetSize(extra_leaves) > max_extra)
					return false;
				continue;
			}

			if (!cells_seen.insert(drv).second)
				continue;
			charge_walk(1);
			if (GetSize(cells_seen) > max_cells || walk_exhausted())
				return false;

			for (auto &conn : drv->connections()) {
				if (!drv->input(conn.first))
					continue;
				for (auto in_bit : sigmap(conn.second)) {
					if (!in_bit.wire)
						continue;
					if (visited.insert(in_bit).second)
						worklist.push(in_bit);
				}
			}
		}

		return true;
	}

	bool sig_fully_driven(const SigSpec &sig)
	{
		for (auto bit : sigmap(sig)) {
			if (!bit.wire)
				return false;
			if (input_port_bits.count(bit))
				return false;
			if (bit_to_driver.at(bit, nullptr) == nullptr)
				return false;
		}
		return true;
	}

	// Collect the bus bits into `seen_bits`, rejecting constant or repeated
	// bits (fingerprints drive each bus bit independently).
	bool sig_bits_unique(const SigSpec &sig, pool<SigBit> &seen_bits)
	{
		for (auto bit : sigmap(sig))
			if (!bit.wire || !seen_bits.insert(bit).second)
				return false;
		return true;
	}

	// Cut buses only need to consist of wire bits; FF outputs (cone leaves)
	// are valid region boundaries even though they have no comb driver.
	bool sig_bus_ok(const SigSpec &sig)
	{
		for (auto bit : sigmap(sig))
			if (!bit.wire)
				return false;
		return true;
	}

	pool<SigBit> sig_bit_pool(const SigSpec &sig)
	{
		pool<SigBit> bits;
		for (auto bit : sigmap(sig))
			if (bit.wire)
				bits.insert(bit);
		return bits;
	}

	// Depth of each cone cell measured from the cone leaves (cells reading
	// only leaf/port bits have depth 1). Used to order candidate cut buses
	// so signals produced by shallow pre-logic are tried first.
	dict<Cell *, int> compute_cone_depths(const pool<Cell *> &cone_cells)
	{
		dict<Cell *, int> depth;
		dict<Cell *, vector<Cell *>> succs;
		dict<Cell *, int> npreds;
		std::queue<Cell *> ready;

		for (auto c : cone_cells) {
			pool<Cell *> preds;
			for (auto &conn : c->connections()) {
				if (!c->input(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire)
						continue;
					Cell *drv = bit_to_driver.at(bit, nullptr);
					if (drv != nullptr && drv != c && cone_cells.count(drv))
						preds.insert(drv);
				}
			}
			npreds[c] = GetSize(preds);
			for (auto p : preds)
				succs[p].push_back(c);
			if (preds.empty()) {
				depth[c] = 1;
				ready.push(c);
			}
		}

		while (!ready.empty()) {
			Cell *c = ready.front();
			ready.pop();
			for (auto s : succs.at(c, vector<Cell *>())) {
				if (depth.at(s, 0) < depth.at(c) + 1)
					depth[s] = depth.at(c) + 1;
				if (--npreds.at(s) == 0)
					ready.push(s);
			}
		}

		return depth;
	}

	bool find_anchor_driver(const SigSpec &out_sig, Cell *&anchor)
	{
		for (auto bit : sigmap(out_sig)) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr) {
				anchor = drv;
				return true;
			}
		}
		return false;
	}

	// Detach the existing drivers of `out_sig` (bit-precise: other bits of
	// shared driver outputs keep their connections). The caller then drives
	// `out_sig` from the replacement logic; the disconnected cells become
	// dead and are removed by the trailing 'clean -purge'.
	void disconnect_root(const SigSpec &out_sig, Cell *anchor, const char *dangling_suffix)
	{
		pool<SigBit> target_bits;
		for (auto bit : sigmap(out_sig))
			if (bit.wire)
				target_bits.insert(bit);

		pool<Cell *> seen_cells;
		for (auto target : target_bits) {
			Cell *drv = bit_to_driver.at(target, nullptr);
			if (drv == nullptr || seen_cells.count(drv))
				continue;
			seen_cells.insert(drv);

			for (auto &conn : drv->connections()) {
				if (!drv->output(conn.first))
					continue;

				SigSpec orig = conn.second;
				SigSpec replacement = orig;
				bool changed = false;
				Cell *cell = drv;
				Wire *dangling = module->addWire(NEW_ID2_SUFFIX(dangling_suffix), GetSize(orig));
				for (int i = 0; i < GetSize(orig); i++) {
					if (target_bits.count(sigmap(orig[i]))) {
						replacement[i] = SigBit(dangling, i);
						changed = true;
					}
				}
				if (changed)
					drv->setPort(conn.first, replacement);
			}
		}
		(void)anchor;
	}

	// Claim the root and every signal produced inside the matched region, so
	// functionally identical sub-roots (e.g. the data input of the region's
	// final mux) are not rewritten again.
	void claim_region(const SigSpec &root_sig, const pool<Cell *> &cut_cells)
	{
		for (auto bit : sigmap(root_sig))
			if (bit.wire)
				claimed_bits.insert(bit);
		for (auto c : cut_cells)
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second))
					if (bit.wire)
						claimed_bits.insert(bit);
			}
	}

	bool root_claimed(const SigSpec &root_sig)
	{
		for (auto bit : sigmap(root_sig))
			if (bit.wire && claimed_bits.count(bit))
				return true;
		return false;
	}

	// Parse a split name of the form "base[index]" (Verific lowers packed
	// multi-dimensional ports, nets and array FFs into per-lane wires named
	// this way).
	bool parse_indexed_port_name(Wire *wire, std::string &base, int &index)
	{
		std::string name = wire->name.str();
		size_t rbrack = name.size();
		if (rbrack == 0 || name[rbrack - 1] != ']')
			return false;
		size_t lbrack = name.rfind('[');
		if (lbrack == std::string::npos || lbrack + 1 >= rbrack - 1)
			return false;
		for (size_t i = lbrack + 1; i < rbrack - 1; i++)
			if (!isdigit(name[i]))
				return false;
		base = name.substr(0, lbrack);
		index = atoi(name.substr(lbrack + 1, rbrack - lbrack - 2).c_str());
		return true;
	}

	// Group per-lane split wires into contiguous, equal-width buses. The run
	// may start at any base index; the resulting sig is the ascending-index
	// concatenation, so lane k is sig[k*elem_width ...] = the (base+k)-th
	// wire.
	vector<BusCand> collect_split_buses(const vector<Wire *> &wires)
	{
		std::map<std::string, vector<std::pair<int, Wire *>>> groups;
		for (auto w : wires) {
			std::string base;
			int index = -1;
			if (parse_indexed_port_name(w, base, index))
				groups[base].push_back({index, w});
		}

		vector<BusCand> buses;
		for (auto &it : groups) {
			auto entries = it.second;
			std::sort(entries.begin(), entries.end(),
			          [](const std::pair<int, Wire *> &a, const std::pair<int, Wire *> &b) {
			              return a.first < b.first;
			          });
			if (entries.empty())
				continue;
			bool contiguous = true;
			int base_index = entries.front().first;
			int elem_width = GetSize(entries.front().second);
			for (int i = 0; i < GetSize(entries); i++) {
				if (entries[i].first != base_index + i ||
				    GetSize(entries[i].second) != elem_width) {
					contiguous = false;
					break;
				}
			}
			if (!contiguous)
				continue;

			SigSpec sig;
			for (auto &entry : entries)
				sig.append(SigSpec(entry.second));
			buses.push_back({sig, it.first, GetSize(entries), elem_width});
		}

		return buses;
	}

	// All bits produced inside the cone or appearing as its leaves; the
	// universe wire-run and split-bus collection draws candidates from.
	pool<SigBit> cone_sig_bit_pool(const pool<Cell *> &cone_cells, const pool<SigBit> &leaf_bits)
	{
		pool<SigBit> bits = leaf_bits;
		for (auto c : cone_cells)
			for (auto &conn : c->connections())
				if (c->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							bits.insert(bit);
		return bits;
	}

	// Maximal contiguous in-cone wire-bit runs, longest first (real region
	// buses are wide; incidental wires are short and must not exhaust the
	// cap). Constant edge bits (e.g. the never-written top bit of a [W:0]
	// vector) are trimmed instead of rejecting the whole wire.
	vector<BusCand> collect_wire_run_buses(const pool<SigBit> &cone_sig_bits, int cap)
	{
		vector<BusCand> wire_runs;
		for (auto wb : module->wires()) {
			if (GetSize(wb) < 2)
				continue;
			SigSpec sig = sigmap(SigSpec(wb));
			int run_start = -1;
			for (int i = 0; i <= GetSize(sig); i++) {
				bool ok = i < GetSize(sig) && sig[i].wire && cone_sig_bits.count(sig[i]);
				if (ok && run_start < 0)
					run_start = i;
				if (!ok && run_start >= 0) {
					int run_len = i - run_start;
					if (run_len >= 2) {
						SigSpec run = sig.extract(run_start, run_len);
						std::string name = (run_len == GetSize(wb))
							? wb->name.str()
							: stringf("%s[%d+:%d]", wb->name.str().c_str(), run_start, run_len);
						wire_runs.push_back({run, name});
					}
					run_start = -1;
				}
			}
		}
		std::stable_sort(wire_runs.begin(), wire_runs.end(),
		                 [](const BusCand &a, const BusCand &b) {
		                     return GetSize(a.sig) > GetSize(b.sig);
		                 });
		if (GetSize(wire_runs) > cap)
			wire_runs.resize(cap);
		return wire_runs;
	}

	// Split-wire buses whose lanes touch the cone.
	vector<BusCand> collect_cone_split_buses(const pool<SigBit> &cone_sig_bits)
	{
		vector<Wire *> cone_wires;
		for (auto wb : module->wires()) {
			bool touches = false;
			for (auto bit : sigmap(SigSpec(wb)))
				if (bit.wire && cone_sig_bits.count(bit)) {
					touches = true;
					break;
				}
			if (touches)
				cone_wires.push_back(wb);
		}
		return collect_split_buses(cone_wires);
	}

	// Per-seed cone cache: the seed sweep is the dominant fixed cost in
	// FF-heavy modules and is shared by every matching mode of a pass.
	struct SeedCone {
		pool<Cell *> cells;
		vector<Cell *> order;
		bool valid = false;
	};
	dict<SigSpec, std::shared_ptr<SeedCone>> seed_cone_cache;

	std::shared_ptr<SeedCone> seed_cone(const SigSpec &seed, int max_cone_cells, int max_leaf_bits)
	{
		auto it = seed_cone_cache.find(seed);
		if (it != seed_cone_cache.end())
			return it->second;
		auto sc = std::make_shared<SeedCone>();
		pool<SigBit> leaf_bits;
		sc->valid = !walk_exhausted() &&
			get_cone(seed, sc->cells, leaf_bits, max_cone_cells, max_leaf_bits, &sc->order);
		seed_cone_cache[seed] = sc;
		return sc;
	}

	// Collect candidate root signals. Module output ports and FF data inputs
	// are seeds; internal signals inside seed cones (cell connections, and
	// optionally whole wires fully inside a seed cone) are added so that
	// regions wrapped in extra combinational post-logic are still found.
	// Internal candidates are taken round-robin across the seed orders so a
	// module with many FFs cannot starve the seeds whose cones hold the
	// region. `width_ok` filters candidate widths; `seed_cone_interesting`
	// gates internal harvesting per seed cone (e.g. "contains $bmux").
	vector<RootCand> collect_root_candidates(
		std::function<bool(int)> width_ok,
		std::function<bool(const pool<Cell *> &)> seed_cone_interesting,
		bool wire_roots, int max_cone_cells, int max_leaf_bits,
		int max_internal_roots = 128)
	{
		vector<RootCand> roots;
		pool<SigSpec> seen;
		vector<SigSpec> seed_sigs;

		auto consider_root = [&](const SigSpec &sig, const std::string &name, bool seed) -> bool {
			if (!width_ok(GetSize(sig)))
				return false;
			if (!seen.insert(sig).second)
				return false;
			roots.push_back({sig, name});
			if (seed)
				seed_sigs.push_back(sig);
			return true;
		};

		for (auto w : module->wires()) {
			if (!w->port_output || w->port_input)
				continue;
			consider_root(sigmap(SigSpec(w)), w->name.str(), true);
		}

		for (auto c : module->cells()) {
			if (!is_storage_ff(c) || !c->hasPort(ID::D))
				continue;
			consider_root(sigmap(c->getPort(ID::D)), stringf("%s.D", log_id(c->name)), true);
		}

		pool<SigBit> cone_out_bits;
		vector<vector<Cell *>> seed_orders;
		for (auto &seed : seed_sigs) {
			auto sc = seed_cone(seed, max_cone_cells, max_leaf_bits);
			vector<Cell *> order;
			if (sc->valid && seed_cone_interesting(sc->cells))
				order = sc->order;
			seed_orders.push_back(order);
			if (wire_roots)
				for (auto c : order)
					for (auto &conn : c->connections())
						if (c->output(conn.first))
							for (auto bit : sigmap(conn.second))
								if (bit.wire)
									cone_out_bits.insert(bit);
		}

		// Internal cell connections in round-robin BFS order (closest to a
		// seed first), so post-logic wrappers are peeled off quickly. These
		// come before wire roots: connection buses are ordered by proximity
		// to the seeds, while wire iteration order is arbitrary.
		int internal_roots = 0;
		size_t longest_order = 0;
		for (auto &order : seed_orders)
			longest_order = std::max(longest_order, order.size());
		for (size_t pos = 0; pos < longest_order && internal_roots < max_internal_roots; pos++) {
			for (auto &order : seed_orders) {
				if (internal_roots >= max_internal_roots)
					break;
				if (pos >= order.size())
					continue;
				Cell *c = order[pos];
				for (auto &conn : c->connections()) {
					SigSpec sig = sigmap(conn.second);
					if (!width_ok(GetSize(sig)))
						continue;
					if (!sig_fully_driven(sig))
						continue;
					if (consider_root(sig, stringf("%s.%s", log_id(c->name), log_id(conn.first)), false))
						internal_roots++;
				}
			}
		}

		// Whole wires fully inside some seed cone (regions written bit by
		// bit, e.g. a |= scatter chain, are only visible as named wires).
		int wire_root_count = 0;
		if (wire_roots) {
			for (auto w : module->wires()) {
				if (wire_root_count >= max_internal_roots)
					break;
				if (!width_ok(GetSize(w)))
					continue;
				SigSpec sig = sigmap(SigSpec(w));
				bool inside = true;
				for (auto bit : sig)
					if (!bit.wire || !cone_out_bits.count(bit)) {
						inside = false;
						break;
					}
				if (!inside)
					continue;
				if (consider_root(sig, w->name.str(), false))
					wire_root_count++;
			}
		}

		return roots;
	}

	SigSpec zext_sig(SigSpec sig, int width)
	{
		sig = sigmap(sig);
		if (GetSize(sig) > width)
			return sig.extract(0, width);
		if (GetSize(sig) < width)
			sig.append(SigSpec(State::S0, width - GetSize(sig)));
		return sig;
	}

	// Shared ConstEval for the whole matching phase. The netlist is not
	// modified until rewrites are applied, so one instance (built once, at
	// O(module) cost) serves every fingerprint eval instead of rebuilding
	// one per candidate. Callers keep push/pop balanced, so the base state
	// stays clean between uses (asserted on each hand-out).
	std::unique_ptr<ConstEval> shared_ce_ptr;
	ConstEval &shared_ce()
	{
		if (!shared_ce_ptr)
			shared_ce_ptr = std::make_unique<ConstEval>(module);
		log_assert(shared_ce_ptr->stack.empty());
		return *shared_ce_ptr;
	}

	// Evaluate `out_sig` under the given input assignments; returns false if
	// the cut does not fully determine the output. Charges the eval budget
	// by `cone_cells_estimate`.
	bool eval_with(ConstEval &ce, const vector<std::pair<SigSpec, Const>> &sets,
	               const SigSpec &out_sig, uint64_t &result, int64_t cone_cells_estimate)
	{
		charge_eval(cone_cells_estimate);
		ce.push();
		for (auto &s : sets)
			ce.set(s.first, s.second);
		SigSpec out = out_sig;
		SigSpec undef;
		bool ok = ce.eval(out, undef);
		if (ok && out.is_fully_const()) {
			Const cv = out.as_const();
			uint64_t r = 0;
			for (int i = 0; i < GetSize(cv) && i < 64; i++)
				if (cv[i] == State::S1)
					r |= 1ULL << i;
			result = r;
		} else {
			ok = false;
		}
		ce.pop();
		return ok;
	}
};
