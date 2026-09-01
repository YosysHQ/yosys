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
		// A whole named wire, rather than one cell connection's bit order.
		// Vectorizing frontends bundle unrelated bits into a cell port in an
		// arbitrary order, so the two spellings of the same bits are not the
		// same candidate and a caller on a budget wants the named one first.
		bool whole_wire = false;
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

	// Every rejected cut records why, but only log_debug ever reads it, and
	// log_signal/stringf on that path costs more than the walk that failed.
	void note_cut_fail(const char *prefix, SigBit bit, const char *suffix = "")
	{
		if (ys_debug())
			last_cut_fail = stringf("%s%s%s", prefix, log_signal(bit), suffix);
	}

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

	// What a cone walk does with a bit it reached.
	enum ConeStep { CONE_EXPAND, CONE_BOUNDARY, CONE_ABORT };

	// Backward BFS over combinational fan-in from `from`, the shared shape of
	// every hashed cone walk below. `on_bit` sees each reached bit with its
	// driver (null when it has none) and says whether to expand through that
	// driver, stop there, or abandon the walk; `on_cell` sees each cell the
	// first time it is entered, after the walk budget is charged, and can
	// abandon it too. `cells_seen` collects the cells entered and doubles as
	// the dedup set. Returns false iff a callback abandoned the walk.
	template <typename FnBit, typename FnCell>
	bool cone_bfs(const SigSpec &from, pool<Cell *> &cells_seen, FnBit on_bit, FnCell on_cell)
	{
		pool<SigBit> visited;
		std::queue<SigBit> worklist;
		for (auto bit : sigmap(from))
			if (bit.wire && visited.insert(bit).second)
				worklist.push(bit);

		while (!worklist.empty()) {
			SigBit bit = worklist.front();
			worklist.pop();

			Cell *drv = bit_to_driver.at(bit, nullptr);
			ConeStep step = on_bit(bit, drv);
			if (step == CONE_ABORT)
				return false;
			if (step == CONE_BOUNDARY)
				continue;

			if (!cells_seen.insert(drv).second)
				continue;
			charge_walk(1);
			if (!on_cell(drv))
				return false;

			for (auto &conn : drv->connections()) {
				if (!drv->input(conn.first))
					continue;
				for (auto in_bit : sigmap(conn.second))
					if (in_bit.wire && visited.insert(in_bit).second)
						worklist.push(in_bit);
			}
		}

		return true;
	}

	// Combinational fanin cone of `from`. Leaves are port-input bits or bits
	// driven by sequential cells / undriven. Returns false if size limits
	// are exceeded. `cell_order` records the cells in BFS discovery order
	// (closest to `from` first).
	bool get_cone(SigSpec from, pool<Cell *> &cone_cells, pool<SigBit> &leaf_bits,
	              int max_cone_cells, int max_leaf_bits, vector<Cell *> *cell_order = nullptr)
	{
		return cone_bfs(from, cone_cells,
			[&](SigBit bit, Cell *drv) {
				if (!input_port_bits.count(bit) && drv != nullptr)
					return CONE_EXPAND;
				leaf_bits.insert(bit);
				return GetSize(leaf_bits) > max_leaf_bits ? CONE_ABORT : CONE_BOUNDARY;
			},
			[&](Cell *drv) {
				if (GetSize(cone_cells) > max_cone_cells)
					return false;
				if (cell_order != nullptr)
					cell_order->push_back(drv);
				return true;
			});
	}

	// Dense fan-in graph of one root's cone, using the cut walk's own rule
	// (a bit is interior iff bit_to_driver names a cell for it). Matchers
	// probe hundreds of cuts per root, and re-running a hashed SigBit BFS
	// that re-sigmaps every connection each time dominates their runtime,
	// so intern the cone once and let the cuts be integer BFS over vectors.
	struct ConeGraph {
		SigSpec root;
		dict<SigBit, int> bit_id;
		vector<SigBit> bits;
		vector<int> bit_drv;     // cell index driving bits[i], or -1 if leaf
		vector<Cell *> cells;
		dict<Cell *, int> cell_id;
		vector<int> in_off;      // CSR offsets into in_bits, size cells+1
		vector<int> in_bits;     // input bit ids, in connection order
		vector<int> root_bits;
	};

	ConeGraph cg;
	bool cg_root_current = false; // cg.root is the cone we last tried to index
	bool cg_usable = false;       // ...and it fit under the cap

	// Scratch reused across cuts; a generation counter avoids clearing it.
	vector<uint32_t> bit_seen, cell_seen, allow_seen;
	uint32_t cg_gen = 0;
	vector<int> cg_queue, cg_cells_hit;

	// Interning explores the whole uncut cone, which a tightly cut walk
	// would not, so refuse roots where that could cost more than it saves.
	static const int max_graph_cells = 1 << 17;

	// Build (or reuse) the dense graph for `root`. Returns null when the
	// cone is too large, leaving the caller on the hashed walk; that verdict
	// is remembered too, so an oversized root is not re-interned per cut.
	const ConeGraph *cone_graph(const SigSpec &root)
	{
		if (cg_root_current && cg.root == root)
			return cg_usable ? &cg : nullptr;

		cg_root_current = true;
		cg_usable = false;
		cg.root = root;
		cg.bit_id.clear();
		cg.bits.clear();
		cg.bit_drv.clear();
		cg.cells.clear();
		cg.cell_id.clear();
		cg.in_off.clear();
		cg.in_bits.clear();
		cg.root_bits.clear();

		// Intern a bit, queueing it for expansion the first time it is seen
		auto intern = [&](SigBit bit) {
			auto it = cg.bit_id.find(bit);
			if (it != cg.bit_id.end())
				return it->second;
			int id = GetSize(cg.bits);
			cg.bit_id[bit] = id;
			cg.bits.push_back(bit);
			cg.bit_drv.push_back(-1);
			return id;
		};

		for (auto bit : sigmap(root))
			if (bit.wire)
				cg.root_bits.push_back(intern(bit));

		// BFS in the same order the hashed walk uses, so cuts visit cells
		// in the same sequence and charge the walk budget identically.
		cg.in_off.push_back(0);
		for (int head = 0; head < GetSize(cg.bits); head++) {
			Cell *drv = bit_to_driver.at(cg.bits[head], nullptr);
			if (drv == nullptr)
				continue;

			auto cit = cg.cell_id.find(drv);
			if (cit != cg.cell_id.end()) {
				cg.bit_drv[head] = cit->second;
				continue;
			}

			if (GetSize(cg.cells) >= max_graph_cells)
				return nullptr;
			int cid = GetSize(cg.cells);
			cg.cell_id[drv] = cid;
			cg.cells.push_back(drv);
			cg.bit_drv[head] = cid;

			for (auto &conn : drv->connections()) {
				if (!drv->input(conn.first))
					continue;
				for (auto in_bit : sigmap(conn.second))
					if (in_bit.wire)
						cg.in_bits.push_back(intern(in_bit));
			}
			cg.in_off.push_back(GetSize(cg.in_bits));
		}

		bit_seen.assign(GetSize(cg.bits), 0);
		allow_seen.assign(GetSize(cg.bits), 0);
		cell_seen.assign(GetSize(cg.cells), 0);
		cg_gen = 0;
		cg_usable = true;
		return &cg;
	}

	void next_cg_gen()
	{
		if (++cg_gen != 0)
			return;
		std::fill(bit_seen.begin(), bit_seen.end(), 0);
		std::fill(allow_seen.begin(), allow_seen.end(), 0);
		std::fill(cell_seen.begin(), cell_seen.end(), 0);
		cg_gen = 1;
	}

	// BFS the dense cone graph from one bit, in the same order and charging
	// the walk budget the same way a hashed traversal would. `interior`
	// decides whether to expand through a bit's driver; `visit` sees every
	// reached bit with that verdict.
	template <typename FnInterior, typename FnVisit>
	void cone_graph_bfs(const ConeGraph &g, SigBit from, FnInterior interior, FnVisit visit)
	{
		auto it = g.bit_id.find(from);
		if (it == g.bit_id.end())
			return;

		next_cg_gen();
		cg_queue.clear();
		cg_queue.push_back(it->second);
		bit_seen[it->second] = cg_gen;

		for (int head = 0; head < GetSize(cg_queue); head++) {
			int id = cg_queue[head];
			charge_walk(1);

			int cid = g.bit_drv[id];
			bool inside = cid >= 0 && interior(cid);
			visit(id, inside);
			if (!inside)
				continue;

			for (int k = g.in_off[cid]; k < g.in_off[cid + 1]; k++) {
				int in_id = g.in_bits[k];
				if (bit_seen[in_id] != cg_gen) {
					bit_seen[in_id] = cg_gen;
					cg_queue.push_back(in_id);
				}
			}
		}
	}

	// Indexed form of cut_cone_walk; see there for the contract.
	bool cut_cone_walk_indexed(const ConeGraph &g, const pool<SigBit> &allowed, int max_cells,
	                           pool<SigBit> *hit_bits, pool<Cell *> *cells_out,
	                           const pool<SigBit> *forced_bits,
	                           pool<SigBit> *conflict_bits = nullptr)
	{
		next_cg_gen();

		for (auto bit : allowed) {
			auto it = g.bit_id.find(bit);
			if (it != g.bit_id.end())
				allow_seen[it->second] = cg_gen;
		}

		cg_queue.clear();
		cg_cells_hit.clear();
		for (int id : g.root_bits)
			if (bit_seen[id] != cg_gen) {
				bit_seen[id] = cg_gen;
				cg_queue.push_back(id);
			}

		for (int head = 0; head < GetSize(cg_queue); head++) {
			int id = cg_queue[head];

			if (allow_seen[id] == cg_gen) {
				if (hit_bits != nullptr)
					hit_bits->insert(g.bits[id]);
				continue;
			}

			int cid = g.bit_drv[id];
			if (cid < 0) {
				note_cut_fail("leaf ", g.bits[id]);
				return false;
			}

			if (cell_seen[cid] == cg_gen)
				continue;
			cell_seen[cid] = cg_gen;
			cg_cells_hit.push_back(cid);
			charge_walk(1);
			if (GetSize(cg_cells_hit) > max_cells || walk_exhausted()) {
				last_cut_fail = "size limit";
				return false;
			}

			for (int k = g.in_off[cid]; k < g.in_off[cid + 1]; k++) {
				int in_id = g.in_bits[k];
				if (bit_seen[in_id] != cg_gen) {
					bit_seen[in_id] = cg_gen;
					cg_queue.push_back(in_id);
				}
			}
		}

		// A forced bit driven from inside the cut cone would conflict with
		// ConstEval's whole-cell output caching.
		const pool<SigBit> &check = (forced_bits != nullptr) ? *forced_bits :
		                            (hit_bits != nullptr) ? *hit_bits : allowed;
		bool conflict = false;
		for (auto bit : check) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr)
				continue;
			int cid = g.cell_id.at(drv, -1);
			if (cid >= 0 && cell_seen[cid] == cg_gen) {
				note_cut_fail("forced bit ", bit, " driven inside cone");
				conflict = true;
				// Callers that can retire single points want the whole
				// set, so the cut converges in one retry per level
				// rather than one per offending bit.
				if (conflict_bits == nullptr)
					return false;
				conflict_bits->insert(bit);
			}
		}
		if (conflict)
			return false;

		if (cells_out != nullptr) {
			cells_out->clear();
			for (int cid : cg_cells_hit)
				cells_out->insert(g.cells[cid]);
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
	                   const pool<Cell *> *full_cells = nullptr,
	                   pool<SigBit> *conflict_bits = nullptr)
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
				// The cut has to cover every cone leaf, so a cone with
				// more leaves than the cut has bits cannot close: that
				// rejects most candidate buses without touching the cone.
				if (GetSize(*full_leaves) > GetSize(allowed)) {
					last_cut_fail = "leaf count";
					return false;
				}
				for (auto leaf : *full_leaves)
					if (!allowed.count(leaf)) {
						note_cut_fail("leaf ", leaf);
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

		if (const ConeGraph *g = cone_graph(root))
			return cut_cone_walk_indexed(*g, allowed, max_cells, hit_bits, cells_out,
			                             forced_bits, conflict_bits);

		pool<Cell *> cells_seen;
		bool closed = cone_bfs(root, cells_seen,
			[&](SigBit bit, Cell *drv) {
				if (allowed.count(bit)) {
					if (hit_bits != nullptr)
						hit_bits->insert(bit);
					return CONE_BOUNDARY;
				}
				if (drv != nullptr)
					return CONE_EXPAND;
				note_cut_fail("leaf ", bit);
				return CONE_ABORT;
			},
			[&](Cell *) {
				if (GetSize(cells_seen) <= max_cells && !walk_exhausted())
					return true;
				last_cut_fail = "size limit";
				return false;
			});
		if (!closed)
			return false;

		const pool<SigBit> &check = (forced_bits != nullptr) ? *forced_bits :
		                            (hit_bits != nullptr) ? *hit_bits : allowed;
		bool conflict = false;
		for (auto bit : check) {
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv != nullptr && cells_seen.count(drv)) {
				note_cut_fail("forced bit ", bit, " driven inside cone");
				conflict = true;
				if (conflict_bits == nullptr)
					return false;
				conflict_bits->insert(bit);
			}
		}
		if (conflict)
			return false;

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
		pool<Cell *> cells_seen;
		return cone_bfs(root, cells_seen,
			[&](SigBit bit, Cell *drv) {
				if (allowed.count(bit))
					return CONE_BOUNDARY;
				if (drv != nullptr)
					return CONE_EXPAND;
				extra_leaves.insert(bit);
				return GetSize(extra_leaves) > max_extra ? CONE_ABORT : CONE_BOUNDARY;
			},
			[&](Cell *) { return GetSize(cells_seen) <= max_cells && !walk_exhausted(); });
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

	// sigmap() copies and unpacks the whole SigSpec on every call, and the
	// matchers re-map the same handful of candidate buses once per cut they
	// try, so hundreds of times per root. SigSpec caches its own hash, which
	// makes the memo lookup much cheaper than redoing the mapping.
	dict<SigSpec, vector<SigBit>> mapped_bits_cache;

	const vector<SigBit> &mapped_bits(const SigSpec &sig)
	{
		auto it = mapped_bits_cache.find(sig);
		if (it != mapped_bits_cache.end())
			return it->second;
		vector<SigBit> &out = mapped_bits_cache[sig];
		for (auto bit : sigmap(sig))
			out.push_back(bit);
		return out;
	}

	// Collect the bus bits into `seen_bits`, rejecting constant or repeated
	// bits (fingerprints drive each bus bit independently).
	bool sig_bits_unique(const SigSpec &sig, pool<SigBit> &seen_bits)
	{
		for (auto bit : mapped_bits(sig))
			if (!bit.wire || !seen_bits.insert(bit).second)
				return false;
		return true;
	}

	// The facts a matcher phase needs about a candidate bus in order to rule
	// out a cut before building it: how many distinct bits it can contribute,
	// whether any of them has a combinational driver, whether the bus is
	// usable as a fingerprint target at all (constant or repeated bits are
	// not), and a Bloom filter over its bits so two buses can be shown
	// disjoint without a set operation.
	struct BusCutInfo {
		int nbits = 0;
		bool leaf_only = true;
		bool has_const = false;
		bool has_dup = false;
		uint64_t bit_hash = 0;
	};

	// Bus facts are asked for once per candidate pair, so hundreds of times
	// per root and repeatedly across roots, while depending only on the
	// module. Memoize them on the bus signal.
	//
	// Returned by value on purpose: a pair test needs the facts for both
	// buses at once, and looking up the second one can rehash the cache and
	// invalidate a reference to the first.
	dict<SigSpec, BusCutInfo> bus_cut_info_cache;

	BusCutInfo bus_cut_info(const SigSpec &sig)
	{
		auto it = bus_cut_info_cache.find(sig);
		if (it != bus_cut_info_cache.end())
			return it->second;
		BusCutInfo info;
		pool<SigBit> distinct;
		for (auto bit : mapped_bits(sig)) {
			if (!bit.wire) {
				info.has_const = true;
				continue;
			}
			if (!distinct.insert(bit).second)
				info.has_dup = true;
			if (bit_to_driver.at(bit, nullptr) != nullptr)
				info.leaf_only = false;
			info.bit_hash |= uint64_t(1) << (run_hash(bit) & 63);
		}
		info.nbits = GetSize(distinct);
		return bus_cut_info_cache[sig] = info;
	}

	// Sound one-word test for "these buses share no bit": the filters only
	// ever over-approximate the bit sets, so a zero intersection is proof of
	// disjointness (a non-zero one proves nothing).
	static bool bus_bits_disjoint(const BusCutInfo &a, const BusCutInfo &b)
	{
		return (a.bit_hash & b.bit_hash) == 0;
	}

	// True when a cut bounded by these two buses provably cannot close, by
	// the same argument cut_cone_walk makes on its walk-free path: if no bit
	// of either bus has a combinational driver then no cut can shadow a cone
	// leaf, so the cut has to cover every leaf, which takes at least as many
	// distinct bits as the cone has leaves. `nbits` sums to an upper bound on
	// the cut size (the buses may share bits), so this only ever agrees with
	// the walk.
	//
	// This is the dominant verdict in the pair phases -- three quarters of
	// all cut attempts on a large design end here -- and reaching it through
	// cut_cone_walk costs a cut-set pool plus a driver lookup per bus bit,
	// all to compute one integer comparison. Phases that can consult this
	// first skip building the cut set at all; they must then charge the
	// attempt with charge_cut_reject() so the search still terminates on the
	// same budget.
	bool cut_pair_cannot_close(const BusCutInfo &a, const BusCutInfo &b, int cone_leaves) const
	{
		return a.leaf_only && b.leaf_only && a.nbits + b.nbits < cone_leaves;
	}

	bool cut_single_cannot_close(const BusCutInfo &a, int cone_leaves) const
	{
		return a.leaf_only && a.nbits < cone_leaves;
	}

	// Account for a cut rejected by cut_pair_cannot_close() exactly as the
	// cut_cone_walk call it stands in for would have.
	void charge_cut_reject()
	{
		attempt_budget--;
		last_cut_fail = "leaf count";
	}

	// Cut buses only need to consist of wire bits; FF outputs (cone leaves)
	// are valid region boundaries even though they have no comb driver.
	bool sig_bus_ok(const SigSpec &sig)
	{
		for (auto bit : mapped_bits(sig))
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
	// so signals produced by shallow pre-logic are tried first. `order`
	// collects the walk's own order, which is topological; a cell in a
	// cell-level loop never comes ready and appears in neither result.
	dict<Cell *, int> compute_cone_depths(const pool<Cell *> &cone_cells,
	                                      vector<Cell *> *order = nullptr)
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

		// at() hands back its default by reference and a range-for does not
		// extend that temporary before C++23, so the fallback has to be named.
		static const vector<Cell *> no_succs;
		while (!ready.empty()) {
			Cell *c = ready.front();
			ready.pop();
			if (order != nullptr)
				order->push_back(c);
			for (auto s : succs.at(c, no_succs)) {
				if (depth.at(s, 0) < depth.at(c) + 1)
					depth[s] = depth.at(c) + 1;
				if (--npreds.at(s) == 0)
					ready.push(s);
			}
		}

		return depth;
	}

	// ---------------------------------------------- cell-level loop census
	//
	// A vectorizing frontend can pack two independent bitwise operations
	// into one wide cell each, with each cell needing a bit of the other's
	// output. That is acyclic bit by bit but cyclic cell by cell, and
	// ConstEval -- which resolves whole cells -- then declares the cone
	// unresolvable. Those cones are the only ones the bit-level evaluator
	// can rescue, and they are rare (a handful of cells in a module), so
	// finding them once lets every other cone fail fast as before.

	pool<Cell *> scc_cells;
	bool scc_done = false;

	// Iterative Tarjan over the cell fan-in graph induced by bit_to_driver.
	void find_scc_cells()
	{
		scc_done = true;
		dict<Cell *, vector<Cell *>> succ;
		for (auto c : module->cells()) {
			pool<Cell *> preds;
			for (auto &conn : c->connections()) {
				if (c->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					Cell *d = bit_to_driver.at(bit, nullptr);
					if (d != nullptr && d != c)
						preds.insert(d);
					else if (d == c)
						scc_cells.insert(c);  // self-loop
				}
			}
			auto &v = succ[c];
			v.insert(v.end(), preds.begin(), preds.end());
		}

		dict<Cell *, int> index, lowlink;
		pool<Cell *> on_stack;
		vector<Cell *> stack;
		int next_index = 0;

		// Explicit DFS stack of (cell, next successor to visit).
		vector<std::pair<Cell *, int>> work;
		for (auto root : module->cells()) {
			if (index.count(root))
				continue;
			work.push_back({root, 0});
			index[root] = lowlink[root] = next_index++;
			stack.push_back(root);
			on_stack.insert(root);

			while (!work.empty()) {
				Cell *c = work.back().first;
				int &i = work.back().second;
				auto &ss = succ.at(c);
				if (i < GetSize(ss)) {
					Cell *n = ss[i++];
					if (!index.count(n)) {
						index[n] = lowlink[n] = next_index++;
						stack.push_back(n);
						on_stack.insert(n);
						work.push_back({n, 0});
					} else if (on_stack.count(n)) {
						lowlink[c] = std::min(lowlink[c], index[n]);
					}
					continue;
				}
				work.pop_back();
				if (!work.empty()) {
					Cell *p = work.back().first;
					lowlink[p] = std::min(lowlink[p], lowlink[c]);
				}
				if (lowlink[c] != index[c])
					continue;
				// Root of an SCC: pop it, and keep it only if non-trivial.
				vector<Cell *> comp;
				while (true) {
					Cell *m = stack.back();
					stack.pop_back();
					on_stack.erase(m);
					comp.push_back(m);
					if (m == c)
						break;
				}
				if (GetSize(comp) > 1)
					for (auto m : comp)
						scc_cells.insert(m);
			}
		}
	}

	// True if any cell in `cone` sits on a cell-level combinational loop.
	bool cone_has_cell_loop(const pool<Cell *> &cone)
	{
		if (!scc_done)
			find_scc_cells();
		bool hit = false;
		for (auto c : cone)
			if (scc_cells.count(c)) {
				hit = true;
				break;
			}
		return hit;
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
		// Rewiring a port in place moves no cell or connection count, so the
		// size check in shared_ce() cannot see it. Drop the driver index here
		// instead: a pass that keeps matching after a rewrite must not go on
		// evaluating through the port this just detached.
		shared_ce_ptr.reset();
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
		// Asked of every wire touching a cone, once per root candidate. Most
		// wires are not lane wires, and materializing the name to find that
		// out is what the scan spends its time on, so reject on the interned
		// string before copying it.
		if (!wire->name.ends_with("]"))
			return false;
		std::string name = wire->name.str();
		size_t rbrack = name.size();
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

	// Wires indexed by the bits they map onto, so a cone can find the wires
	// it touches without re-mapping every wire in the module. Both bus
	// collectors below run once per root, and rescanning the whole module
	// each time is what makes them dominate on large designs.
	dict<SigBit, vector<Wire *>> bit_to_wires;
	dict<Wire *, vector<SigBit>> wire_mapped_bits;
	dict<Wire *, int> wire_order;
	bool wire_index_built = false;

	void build_wire_index()
	{
		if (wire_index_built)
			return;
		wire_index_built = true;
		for (auto w : module->wires()) {
			wire_order[w] = GetSize(wire_order);
			vector<SigBit> &bits = wire_mapped_bits[w];
			for (auto bit : sigmap(SigSpec(w))) {
				bits.push_back(bit);
				if (bit.wire)
					bit_to_wires[bit].push_back(w);
			}
		}
	}

	// Wires of a given width, in module order. Callers ask once per root
	// candidate, and walking every wire in the module each time is what makes
	// that scan visible on designs with many roots.
	dict<int, vector<Wire *>> wires_by_width;
	int wires_by_width_count = -1;
	const vector<Wire *> no_wires;

	const vector<Wire *> &wires_of_width(int width)
	{
		int count = GetSize(module->wires());
		if (wires_by_width_count != count) {
			wires_by_width_count = count;
			wires_by_width.clear();
			for (auto w : module->wires())
				wires_by_width[GetSize(w)].push_back(w);
		}
		auto it = wires_by_width.find(width);
		return it == wires_by_width.end() ? no_wires : it->second;
	}

	// Wires with at least one bit in the cone, in module order so that the
	// size-capped, stably sorted bus lists come out exactly as before.
	vector<Wire *> wires_touching(const pool<SigBit> &cone_sig_bits)
	{
		build_wire_index();
		pool<Wire *> seen;
		vector<Wire *> out;
		for (auto bit : cone_sig_bits) {
			auto it = bit_to_wires.find(bit);
			if (it == bit_to_wires.end())
				continue;
			for (auto w : it->second)
				if (seen.insert(w).second)
					out.push_back(w);
		}
		std::sort(out.begin(), out.end(), [&](Wire *a, Wire *b) {
			return wire_order.at(a) < wire_order.at(b);
		});
		return out;
	}

	// Maximal contiguous in-cone wire-bit runs, longest first (real region
	// buses are wide; incidental wires are short and must not exhaust the
	// cap). Constant edge bits (e.g. the never-written top bit of a [W:0]
	// vector) are trimmed instead of rejecting the whole wire.
	vector<BusCand> collect_wire_run_buses(const pool<SigBit> &cone_sig_bits, int cap)
	{
		vector<BusCand> wire_runs;
		for (auto wb : wires_touching(cone_sig_bits)) {
			if (GetSize(wb) < 2)
				continue;
			const vector<SigBit> &sig = wire_mapped_bits.at(wb);
			int run_start = -1;
			for (int i = 0; i <= GetSize(sig); i++) {
				bool ok = i < GetSize(sig) && sig[i].wire && cone_sig_bits.count(sig[i]);
				if (ok && run_start < 0)
					run_start = i;
				if (!ok && run_start >= 0) {
					int run_len = i - run_start;
					if (run_len >= 2) {
						SigSpec run(vector<SigBit>(sig.begin() + run_start,
						                           sig.begin() + run_start + run_len));
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
		return collect_split_buses(wires_touching(cone_sig_bits));
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
	// `seed_width_ok`, when given, filters seeds instead of `width_ok`: a
	// seed only anchors a cone, so a pass looking for narrow regions can
	// still reach them behind an output the pass would never rewrite.
	vector<RootCand> collect_root_candidates(
		std::function<bool(int)> width_ok,
		std::function<bool(const pool<Cell *> &)> seed_cone_interesting,
		bool wire_roots, int max_cone_cells, int max_leaf_bits,
		int max_internal_roots = 128,
		std::function<bool(int)> seed_width_ok = nullptr)
	{
		vector<RootCand> roots;
		pool<SigSpec> seen;
		vector<SigSpec> seed_sigs;

		auto consider_root = [&](const SigSpec &sig, const std::string &name, bool seed,
		                         bool whole_wire = false) -> bool {
			bool root_ok = width_ok(GetSize(sig));
			if (seed && seed_width_ok != nullptr) {
				if (!seed_width_ok(GetSize(sig)))
					return false;
			} else if (!root_ok) {
				return false;
			}
			if (!seen.insert(sig).second)
				return false;
			if (root_ok)
				roots.push_back({sig, name, whole_wire});
			if (seed)
				seed_sigs.push_back(sig);
			return true;
		};

		for (auto w : module->wires()) {
			if (!w->port_output || w->port_input)
				continue;
			consider_root(sigmap(SigSpec(w)), w->name.str(), true, true);
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
				if (consider_root(sig, w->name.str(), false, true))
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

	// Shared ConstEval for the whole matching phase. The constructor indexes
	// every cell in the module, so building one per candidate charges a
	// module-sized cost even to candidates that are rejected before they
	// evaluate anything; built once, it serves every fingerprint eval
	// instead. Callers keep push/pop balanced, so the base state stays clean
	// between uses (asserted on each hand-out).
	//
	// A pass that applies a rewrite between two matches, rather than
	// collecting every match first, would otherwise keep evaluating against
	// a driver index describing a netlist that no longer exists. Cell and
	// connection counts are O(1) to read and cannot move while matching, so
	// checking them costs nothing on the passes that never mutate mid-match
	// and drops the stale instance on the passes that do. A pass that
	// removes cells goes through clear_cell_caches(), which resets this
	// along with the other indexes.
	std::unique_ptr<ConstEval> shared_ce_ptr;
	int shared_ce_cells = -1, shared_ce_conns = -1;
	ConstEval &shared_ce()
	{
		int cells = GetSize(module->cells());
		int conns = GetSize(module->connections());
		if (!shared_ce_ptr || shared_ce_cells != cells || shared_ce_conns != conns) {
			shared_ce_ptr = std::make_unique<ConstEval>(module);
			shared_ce_cells = cells;
			shared_ce_conns = conns;
		}
		log_assert(shared_ce_ptr->stack.empty());
		return *shared_ce_ptr;
	}

	// Resolve a region cell by cell in topological order, so that the eval
	// below finds every value it needs already in the map. ConstEval's own
	// descent is demand-driven: for each signal it wants it re-derives the
	// drivers through a SigSet lookup and tracks the cells in progress in a
	// std::set, once per port and per probe -- and an exhaustive sweep probes
	// the same region thousands of times. This only gets there first:
	// whatever it leaves unresolved the descent still resolves as before, and
	// each cell computes the same value either way.
	void prefetch_region(ConstEval &ce, const vector<Cell *> &order)
	{
		SigSpec undef;
		for (auto c : order)
			// Reached through the signal it drives, a cell always has an
			// output ConstEval knows how to write; asked for directly it
			// has to be checked, because a cell with no Y port -- a memory
			// port, a register -- trips an assert rather than declining.
			if (c->hasPort(ID::Y) || c->type == ID($lcu))
				ce.eval(c, undef);
	}

	// Evaluate `out_sig` under the given input assignments; returns false if
	// the cut does not fully determine the output. Charges the eval budget
	// by `cone_cells_estimate`.
	bool eval_with(ConstEval &ce, const vector<std::pair<SigSpec, Const>> &sets,
	               const SigSpec &out_sig, uint64_t &result, int64_t cone_cells_estimate,
	               const vector<Cell *> *order = nullptr)
	{
		charge_eval(cone_cells_estimate);
		ce.push();
		for (auto &s : sets)
			ce.set(s.first, s.second);
		if (order != nullptr)
			prefetch_region(ce, *order);
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

	// As eval_with, but per bit: `ok_mask` marks the bits the cut determines
	// instead of failing whenever one of them escapes it. A cone's outputs
	// are whole cell ports, and a vectorizing frontend shares a port between
	// a reduction and unrelated logic, so demanding that every bit resolve
	// discards the bits that do.
	void eval_masked(ConstEval &ce, const vector<std::pair<SigSpec, Const>> &sets,
	                 const SigSpec &out_sig, uint64_t &result, uint64_t &ok_mask,
	                 int64_t cone_cells_estimate)
	{
		charge_eval(cone_cells_estimate);
		ce.push();
		for (auto &s : sets)
			ce.set(s.first, s.second);
		SigSpec out = out_sig;
		SigSpec undef;
		ce.eval(out, undef);
		result = 0;
		ok_mask = 0;
		for (int i = 0; i < GetSize(out) && i < 64; i++) {
			if (out[i].wire != nullptr)
				continue;
			if (out[i].data != State::S0 && out[i].data != State::S1)
				continue;
			ok_mask |= 1ULL << i;
			if (out[i].data == State::S1)
				result |= 1ULL << i;
		}
		ce.pop();
	}

	// Bit-level counterpart of eval_masked.
	void eval_masked_bits(const vector<std::pair<SigSpec, Const>> &sets, const SigSpec &out_sig,
	                      uint64_t &result, uint64_t &ok_mask, int64_t cone_cells_estimate)
	{
		begin_bit_eval(cone_cells_estimate, sets);
		result = 0;
		ok_mask = 0;
		SigSpec mapped = sigmap(out_sig);
		for (int i = 0; i < GetSize(mapped) && i < 64; i++) {
			State v;
			if (!bit_value(mapped[i], v) || (v != State::S0 && v != State::S1))
				continue;
			ok_mask |= 1ULL << i;
			if (v == State::S1)
				result |= 1ULL << i;
		}
	}

	// ------------------------------------------- bit-level fallback eval
	//
	// ConstEval resolves one whole cell at a time. A vectorizing frontend
	// bundles unrelated bitwise operations into single wide cells, and two
	// of those routinely each need a bit of the other's output: acyclic bit
	// by bit, deadlocked cell by cell, and ConstEval reports the whole cone
	// unresolvable. `eval_with_bits` walks the cone a bit at a time instead.
	//
	// Only a handful of operators are given semantics here; every other cell
	// is still evaluated by ConstEval, with its inputs resolved first. So
	// this is a fallback, not a second implementation of RTLIL.

	static bool is01(State s) { return s == State::S0 || s == State::S1; }

	// How the bit walk evaluates a driver. Anything else falls back to
	// ConstEval, which costs a push, a fresh set of input assignments and a
	// SigSpec copy per bit -- worth avoiding for the types a residue's
	// consumers are actually built from.
	enum BitKind : uint8_t { BK_OPAQUE, BK_ELEMENTWISE, BK_COMPARE };

	static BitKind bit_kind(Cell *c)
	{
		if (c->type.in(ID($and), ID($or), ID($xor), ID($xnor), ID($not), ID($pos),
		               ID($buf), ID($mux), ID($bwmux)))
			return BK_ELEMENTWISE;
		// A decode network is nothing but these, and each is one bit that
		// every operand bit feeds -- not elementwise, but no harder.
		if (c->type.in(ID($eq), ID($ne)))
			return BK_COMPARE;
		return BK_OPAQUE;
	}

	// Per-bit walk state. Tagged with the generation of the eval that wrote
	// it rather than cleared between evals: the tables reach a few hundred
	// live bits, and freeing and regrowing them tens of thousands of times
	// costs more than the walk itself.
	//
	// DEAD is as load-bearing as VALUE. A bit's value depends only on its
	// driver and the pinned inputs, so one that fails once fails for the
	// whole eval; without recording that, the walk re-explores a failing
	// subtree once per parent that reaches it.
	enum BitStatus : uint8_t { BS_NONE, BS_ACTIVE, BS_VALUE, BS_DEAD };
	struct BitRec {
		int gen = -1;
		BitStatus st = BS_NONE;
		State val = State::Sx;
		// Where the bit comes from. Netlist-derived, so unlike the rest it
		// outlives the generation and is only dropped when a rewrite
		// invalidates the indexes.
		bool src_ok = false;
		BitKind kind = BK_OPAQUE;
		int yi = -1;  // its position in the driver's Y port, or -1
		Cell *drv = nullptr;
	};
	dict<SigBit, BitRec> bit_rec;
	int bit_gen = 0;

	// This re-looks-up rather than take a reference: the walk recurses
	// between reading and writing, and an insert would dangle it.
	void mark_bit(SigBit bit, BitStatus st, State val = State::Sx)
	{
		BitRec &r = bit_rec[bit];
		r.gen = bit_gen;
		r.st = st;
		r.val = val;
	}

	// Sigmapping a port is O(width) and indexing a SigSpec walks its chunks;
	// the bit walk asks for one bit at a time, so both are cached flat.
	dict<std::pair<Cell *, IdString>, vector<SigBit>> port_cache;

	const vector<SigBit> &port_sig(Cell *c, IdString port)
	{
		auto key = std::make_pair(c, port);
		auto it = port_cache.find(key);
		if (it != port_cache.end())
			return it->second;
		return port_cache[key] = sigmap(c->getPort(port)).bits();
	}

	// Every input bit of a cell, sigmapped, with constants dropped. The
	// backward walks ask each cell for this once per visit, and going through
	// connections() re-derives the port directions from the global cell-type
	// table and re-unpacks a SigSpec every time.
	dict<Cell *, vector<SigBit>> fanin_cache;

	const vector<SigBit> &cell_fanin(Cell *c)
	{
		auto it = fanin_cache.find(c);
		if (it != fanin_cache.end())
			return it->second;
		vector<SigBit> v;
		for (auto &conn : c->connections())
			if (c->input(conn.first))
				for (auto bit : sigmap(conn.second))
					if (bit.wire != nullptr)
						v.push_back(bit);
		return fanin_cache[c] = std::move(v);
	}

	// Everything keyed on a cell, or on a bit's driver. A rewrite removes the
	// cells it orphaned, so these have to go when the indexes they mirror are
	// rebuilt -- including the ConstEvals, which hold a sigmap taken when they
	// were built.
	void clear_cell_caches()
	{
		port_cache.clear();
		fanin_cache.clear();
		y_index_cache.clear();
		bit_rec.clear();
		shared_ce_ptr.reset();
		bits_ce_ptr.reset();
	}

	// Bit `i` of an operand, with the width extension RTLIL gives it.
	bool operand_bit(Cell *c, IdString port, IdString signed_param, int i, State &out)
	{
		const vector<SigBit> &s = port_sig(c, port);
		int n = GetSize(s);
		if (n == 0)
			return false;
		if (i >= n) {
			if (signed_param == IdString() || !c->getParam(signed_param).as_bool()) {
				out = State::S0;
				return true;
			}
			i = n - 1;
		}
		return bit_value(s[i], out);
	}

	bool eval_elementwise(Cell *c, int i, State &out)
	{
		State a, b, s;
		if (c->type == ID($mux) || c->type == ID($bwmux)) {
			IdString sel = ID::S;
			int si = c->type == ID($mux) ? 0 : i;
			if (!bit_value(port_sig(c, sel)[si], s))
				return false;
			if (s != State::S0 && s != State::S1)
				return false;
			return operand_bit(c, s == State::S1 ? ID::B : ID::A, IdString(), i, out);
		}
		if (!operand_bit(c, ID::A, ID::A_SIGNED, i, a))
			return false;
		if (c->type.in(ID($not), ID($pos), ID($buf))) {
			if (!is01(a))
				return false;
			out = (c->type == ID($not)) == (a == State::S0) ? State::S1 : State::S0;
			return true;
		}
		if (!operand_bit(c, ID::B, ID::B_SIGNED, i, b))
			return false;
		if (!is01(a) || !is01(b))
			return false;
		bool x = a == State::S1, y = b == State::S1, r;
		if (c->type == ID($and))
			r = x && y;
		else if (c->type == ID($or))
			r = x || y;
		else
			r = (x != y) == (c->type == ID($xor));
		out = r ? State::S1 : State::S0;
		return true;
	}

	// Bit `i` of an $eq/$ne: the comparison in bit 0, zero above it. Stops
	// on the first pair that decides the answer, so a bit the cut leaves
	// unresolved elsewhere is not fatal -- the same answer ConstEval gives.
	bool eval_compare(Cell *c, int i, State &out)
	{
		if (i > 0) {
			out = State::S0;
			return true;
		}
		bool ne = c->type == ID($ne), unknown = false;
		int n = std::max(GetSize(port_sig(c, ID::A)), GetSize(port_sig(c, ID::B)));
		for (int j = 0; j < n; j++) {
			State a, b;
			if (!operand_bit(c, ID::A, ID::A_SIGNED, j, a) ||
			    !operand_bit(c, ID::B, ID::B_SIGNED, j, b) || !is01(a) || !is01(b)) {
				unknown = true;
				continue;
			}
			if (a != b) {
				out = ne ? State::S1 : State::S0;
				return true;
			}
		}
		if (unknown)
			return false;
		out = ne ? State::S0 : State::S1;
		return true;
	}

	// Position of `bit` in a cell's Y port, or -1. Cached for the same
	// reason as the ports themselves: the walk asks one bit at a time.
	dict<Cell *, dict<SigBit, int>> y_index_cache;

	int y_index(Cell *c, SigBit bit)
	{
		auto it = y_index_cache.find(c);
		if (it == y_index_cache.end()) {
			vector<SigBit> y = port_sig(c, ID::Y);
			auto &m = y_index_cache[c];
			for (int i = 0; i < GetSize(y); i++)
				m.emplace(y[i], i);
			it = y_index_cache.find(c);
		}
		return it->second.at(bit, -1);
	}

	// Separate ConstEval for the bit walk. `push()` deep-copies the value
	// map, so per-cell push/pop is quadratic in the cells already resolved.
	// Every cell in one walk sees the same input vector, so instead the
	// values accumulate and get cleared once per eval.
	std::unique_ptr<ConstEval> bits_ce_ptr;
	ConstEval &bits_ce()
	{
		if (!bits_ce_ptr)
			bits_ce_ptr = std::make_unique<ConstEval>(module);
		return *bits_ce_ptr;
	}

	// Everything the elementwise table does not cover: resolve every input
	// bit, then let ConstEval apply the cell's real semantics to them.
	bool eval_opaque(Cell *c, State &out, SigBit want)
	{
		// This needs every input of the cell whichever output bit was asked
		// for, so a failure belongs to the cell rather than to that bit.
		// Retire the whole output port on the way out: otherwise every other
		// bit of it repeats the resolve-and-eval and fails in the same place.
		SigSpec outs;
		for (auto &conn : c->connections())
			if (c->output(conn.first))
				outs.append(SigSpec(port_sig(c, conn.first)));
		auto retire = [&]() {
			for (auto bit : outs)
				if (bit.wire)
					mark_bit(bit, BS_DEAD);
			return false;
		};

		ConstEval &ce = bits_ce();
		vector<std::pair<SigSpec, Const>> sets;
		for (auto &conn : c->connections()) {
			if (c->output(conn.first))
				continue;
			// By value: resolving the bits below recurses into
			// port_sig, and a rehash would dangle a reference.
			vector<SigBit> s = port_sig(c, conn.first);
			Const v;
			for (auto bit : s) {
				State b;
				if (!bit_value(bit, b))
					return retire();
				v.bits().push_back(b);
			}
			sets.push_back({SigSpec(s), v});
		}

		for (auto &s : sets)
			ce.set(s.first, s.second);
		SigSpec ev = outs, undef;
		if (!ce.eval(ev, undef) || !ev.is_fully_const())
			return retire();
		bool found = false;
		for (int i = 0; i < GetSize(outs); i++)
			if (outs[i].wire) {
				mark_bit(outs[i], BS_VALUE, ev[i].data);
				if (outs[i] == want) {
					out = ev[i].data;
					found = true;
				}
			}
		return found;
	}

	bool bit_value(SigBit bit, State &out)
	{
		if (!bit.wire) {
			out = bit.data;
			return out == State::S0 || out == State::S1;
		}
		Cell *drv;
		int yi;
		BitKind kind;
		{
			// One lookup covers the memo read, the driver, and the
			// in-progress mark: nothing in between touches bit_rec, so
			// the reference cannot be invalidated. The walk visits
			// millions of bits, and hashing one dominated the walk.
			BitRec &r = bit_rec[bit];
			if (r.gen == bit_gen) {
				if (r.st == BS_VALUE) {
					out = r.val;
					return true;
				}
				// Either already given up on, or reached while its
				// own evaluation is in progress -- a genuine
				// bit-level loop, so it stays unresolvable.
				if (r.st == BS_ACTIVE)
					r.st = BS_DEAD;
				return false;
			}
			if (eval_exhausted() || bit_visits_left <= 0)
				return false;
			if (!r.src_ok) {
				r.drv = bit_to_driver.at(bit, nullptr);
				r.kind = r.drv != nullptr ? bit_kind(r.drv) : BK_OPAQUE;
				r.yi = r.kind != BK_OPAQUE ? y_index(r.drv, bit) : -1;
				r.src_ok = true;
			}
			drv = r.drv;
			yi = r.yi;
			kind = r.kind;
			r.gen = bit_gen;
			r.st = BS_ACTIVE;
		}
		charge_eval(1);
		bit_visits_left--;
		// An input the caller did not pin down.
		if (drv == nullptr) {
			mark_bit(bit, BS_DEAD);
			return false;
		}
		bool ok = kind == BK_OPAQUE
		              ? eval_opaque(drv, out, bit)
		              : yi >= 0 && (kind == BK_ELEMENTWISE
		                                ? eval_elementwise(drv, yi, out)
		                                : eval_compare(drv, yi, out));
		mark_bit(bit, ok ? BS_VALUE : BS_DEAD, out);
		return ok;
	}

	// Bits this eval may still visit. A cone whose cut points do not
	// dominate the root leads the walk off into the rest of the design,
	// where it fails only after touching everything; the cap turns that
	// from a whole-design walk into a bounded one.
	int64_t bit_visits_left = 0;

	void begin_bit_eval(int64_t cone_cells_estimate,
	                    const vector<std::pair<SigSpec, Const>> &sets)
	{
		charge_eval(cone_cells_estimate);
		bit_visits_left = 64 * cone_cells_estimate + 4096;
		bit_gen++;
		if (bits_ce_ptr) {
			bits_ce_ptr->values_map.clear();
			bits_ce_ptr->busy.clear();
		}
		for (auto &s : sets) {
			SigSpec pinned = sigmap(s.first);
			for (int i = 0; i < GetSize(pinned); i++)
				if (pinned[i].wire)
					mark_bit(pinned[i], BS_VALUE, s.second[i]);
		}
	}

	bool eval_with_bits(const vector<std::pair<SigSpec, Const>> &sets, const SigSpec &out_sig,
	                    uint64_t &result, int64_t cone_cells_estimate)
	{
		begin_bit_eval(cone_cells_estimate, sets);
		SigSpec out_mapped = sigmap(out_sig);
		uint64_t r = 0;
		for (int i = 0; i < GetSize(out_mapped) && i < 64; i++) {
			State v;
			if (!bit_value(out_mapped[i], v))
				return false;
			if (v == State::S1)
				r |= 1ULL << i;
			else if (v != State::S0)
				return false;
		}
		result = r;
		return true;
	}
};
