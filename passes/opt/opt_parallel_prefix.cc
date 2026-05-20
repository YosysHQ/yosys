/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Akash Levy        <akash@silimate.com>
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

enum class Topology { KOGGE_STONE, SKLANSKY, BRENT_KUNG, HAN_CARLSON };

static const char* topology_name(Topology t) {
	switch (t) {
		case Topology::KOGGE_STONE: return "Kogge-Stone";
		case Topology::SKLANSKY:    return "Sklansky";
		case Topology::BRENT_KUNG:  return "Brent-Kung";
		case Topology::HAN_CARLSON: return "Han-Carlson";
	}
	return "?";
}

// One linearized cascade ready to be rebuilt as a prefix network.
struct PrefixChain {
	IdString op;
	bool a_signed = false;
	bool b_signed = false;
	// leaves[0..N-1] are the fresh operands fed into the original cascade.
	// The original chain computes prefix[i] = leaves[0] op leaves[1] op ... op leaves[i].
	vector<SigSpec> leaves;
	// cells[i] is the original cell whose Y is prefix[i+1] (i in [0..N-2]).
	vector<Cell*> cells;
	// demands[i] = the original SigSpec that must equal prefix[i] after rewrite.
	// i ranges over [1..N-1]; i=0 is never demanded (prefix[0] is a leaf).
	dict<int, SigSpec> demands;
	// First-cell attributes propagated to emitted cells (for src tracking).
	dict<RTLIL::IdString, RTLIL::Const> ref_attributes;
};

// Owns cell emission for a single chain rewrite. Tracks per-signal depth so
// the worker can log the critical-path depth of the resulting network.
struct PrefixNet {
	Module* m;
	IdString op;
	bool a_signed;
	bool b_signed;
	const dict<RTLIL::IdString, RTLIL::Const>* ref_attributes;
	Cell* ref_cell;
	dict<IdString, int>* cell_count;
	dict<SigSpec, int> depth;
	int max_depth = 0;

	PrefixNet(Module* m, const PrefixChain& chain, dict<IdString, int>* cc)
		: m(m), op(chain.op), a_signed(chain.a_signed), b_signed(chain.b_signed),
		  ref_attributes(&chain.ref_attributes), ref_cell(chain.cells.front()), cell_count(cc) {}

	int depth_of(const SigSpec& s) {
		auto it = depth.find(s);
		return it == depth.end() ? 0 : it->second;
	}

	SigSpec emit(const SigSpec& a, const SigSpec& b) {
		// Match opt_balance_tree's natural-width convention so wreduce/equiv_opt
		// behave identically. The cell itself handles A/B extension via the
		// signedness parameters; we never pad operands manually.
		int out_width;
		if (op == ID($add))
			out_width = std::max(GetSize(a), GetSize(b)) + 1;
		else if (op == ID($mul))
			out_width = GetSize(a) + GetSize(b);
		else
			out_width = std::max(GetSize(a), GetSize(b));

		Cell* cell = ref_cell;
		Wire* y = m->addWire(NEW_ID2_SUFFIX("pp_y"), out_width);
		Cell* c = m->addCell(NEW_ID2_SUFFIX("pp"), op);
		c->attributes = *ref_attributes;
		c->setPort(ID::A, a);
		c->setPort(ID::B, b);
		c->setPort(ID::Y, y);
		c->fixup_parameters();
		c->setParam(ID::A_SIGNED, a_signed);
		c->setParam(ID::B_SIGNED, b_signed);
		(*cell_count)[op]++;

		SigSpec y_sig(y);
		int d = std::max(depth_of(a), depth_of(b)) + 1;
		depth[y_sig] = d;
		if (d > max_depth) max_depth = d;
		return y_sig;
	}
};

struct OptParallelPrefixWorker {
	Module* module;
	SigMap sigmap;
	Topology topology;

	dict<SigSpec, Cell*> sig_to_driver;
	dict<SigSpec, pool<Cell*>> sig_to_sinks;
	pool<SigBit> output_port_bits;

	dict<IdString, int> cell_count;
	int chains_built = 0;
	int max_depth = 0;
	int leaves_total = 0;

	OptParallelPrefixWorker(Module* m, Topology t) : module(m), sigmap(m), topology(t) {
		build_indexes();
	}

	void build_indexes() {
		for (auto cell : module->cells()) {
			for (auto& conn : cell->connections()) {
				SigSpec s = sigmap(conn.second);
				if (cell->output(conn.first))
					sig_to_driver[s] = cell;
				if (cell->input(conn.first)) {
					sig_to_sinks[s].insert(cell);
					for (auto bit : s)
						sig_to_sinks[SigSpec(bit)].insert(cell);
				}
			}
		}
		for (auto wire : module->wires()) {
			if (!wire->port_output) continue;
			SigSpec s = sigmap(wire);
			for (auto bit : s) output_port_bits.insert(bit);
		}
	}

	// A cell can participate in a prefix chain if it is of the right op and its
	// declared Y width is large enough to fit the natural result width.
	// (Truncating chains can change semantics, so we refuse them - same rule as
	// opt_balance_tree's is_right_type.)
	bool is_chainable(Cell* c, IdString op) {
		if (c->type != op) return false;
		int y_width = c->getParam(ID::Y_WIDTH).as_int();
		int a_width = c->getParam(ID::A_WIDTH).as_int();
		int b_width = c->getParam(ID::B_WIDTH).as_int();
		int natural_width;
		if (op == ID($add))
			natural_width = std::max(a_width, b_width); // ignore carry bit (same as opt_balance_tree)
		else if (op == ID($mul))
			natural_width = a_width + b_width;
		else
			natural_width = std::max(a_width, b_width);
		return y_width >= natural_width;
	}

	// A signal is a "leaf" w.r.t. an ongoing chain iff it is NOT produced by a
	// chainable cell of the same op + signedness that is free to be merged.
	bool is_leaf(const SigSpec& sig, IdString op, bool a_signed, bool b_signed, const pool<Cell*>& claimed) {
		auto it = sig_to_driver.find(sig);
		if (it == sig_to_driver.end()) return true;
		Cell* drv = it->second;
		if (claimed.count(drv)) return true;
		if (!is_chainable(drv, op)) return true;
		if (drv->getParam(ID::A_SIGNED).as_bool() != a_signed) return true;
		if (drv->getParam(ID::B_SIGNED).as_bool() != b_signed) return true;
		return false;
	}

	// Greedy forward growth: extend the chain as long as the current running
	// output drives EXACTLY ONE chainable successor whose other operand is itself
	// a leaf. Any additional fanout doesn't prevent growth; it just marks the
	// current node as a demand point later.
	void extend_chain(PrefixChain& chain, const pool<Cell*>& claimed) {
		while (true) {
			Cell* cur = chain.cells.back();
			SigSpec cur_Y = sigmap(cur->getPort(ID::Y));

			auto sinks_it = sig_to_sinks.find(cur_Y);
			if (sinks_it == sig_to_sinks.end()) return;

			Cell* next = nullptr;
			SigSpec next_leaf;
			int chainable_count = 0;
			for (auto s : sinks_it->second) {
				if (s == cur) continue;
				if (claimed.count(s)) continue;
				if (!is_chainable(s, chain.op)) continue;
				if (s->getParam(ID::A_SIGNED).as_bool() != chain.a_signed) continue;
				if (s->getParam(ID::B_SIGNED).as_bool() != chain.b_signed) continue;

				SigSpec sA = sigmap(s->getPort(ID::A));
				SigSpec sB = sigmap(s->getPort(ID::B));
				SigSpec other;
				if (sA == cur_Y && sB != cur_Y) other = sB;
				else if (sB == cur_Y && sA != cur_Y) other = sA;
				else continue; // Y on both inputs, or partial overlap; not chain-linear.

				if (!is_leaf(other, chain.op, chain.a_signed, chain.b_signed, claimed))
					continue;

				chainable_count++;
				if (chainable_count > 1) break;
				next = s;
				next_leaf = other;
			}

			if (chainable_count != 1) return;

			chain.leaves.push_back(next_leaf);
			chain.cells.push_back(next);
		}
	}

	// After the chain is built, mark each cell whose output is consumed outside
	// the chain (port output or any non-next-cell sink) as a demand point.
	void detect_demands(PrefixChain& chain) {
		int N = GetSize(chain.cells);
		for (int i = 0; i < N; i++) {
			Cell* c = chain.cells[i];
			SigSpec Y = sigmap(c->getPort(ID::Y));

			bool demanded = false;
			for (auto bit : Y) {
				if (output_port_bits.count(bit)) { demanded = true; break; }
			}

			if (!demanded) {
				Cell* next_chain_cell = (i + 1 < N) ? chain.cells[i+1] : nullptr;
				auto sinks_it = sig_to_sinks.find(Y);
				if (sinks_it != sig_to_sinks.end()) {
					for (auto s : sinks_it->second) {
						if (s != next_chain_cell) { demanded = true; break; }
					}
				}
				// Bit-level fanout (e.g. someone reads Y[3]): also a demand.
				if (!demanded) {
					for (auto bit : Y) {
						auto bit_it = sig_to_sinks.find(SigSpec(bit));
						if (bit_it == sig_to_sinks.end()) continue;
						for (auto s : bit_it->second) {
							if (s != next_chain_cell) { demanded = true; break; }
						}
						if (demanded) break;
					}
				}
			}

			// The chain's terminal cell is the chain's reason for existing.
			if (i == N - 1) demanded = true;

			if (demanded) {
				// chain.cells[i] produces prefix[i+1] (in 0-based leaf indexing).
				chain.demands[i + 1] = chain.cells[i]->getPort(ID::Y);
			}
		}
	}

	// ------------ topology builders ------------
	// Each returns prefix[0..N-1] where prefix[i] = reduce(leaves[0..i]).
	// They are pure dispatchers over PrefixNet::emit and therefore work for all
	// five supported ops.

	vector<SigSpec> build_kogge_stone(PrefixNet& net, const vector<SigSpec>& leaves) {
		int N = GetSize(leaves);
		vector<SigSpec> cur = leaves;
		for (int offset = 1; offset < N; offset *= 2) {
			vector<SigSpec> nxt(N);
			for (int i = 0; i < N; i++) {
				if (i >= offset) nxt[i] = net.emit(cur[i - offset], cur[i]);
				else nxt[i] = cur[i];
			}
			cur = std::move(nxt);
		}
		return cur;
	}

	vector<SigSpec> build_sklansky(PrefixNet& net, const vector<SigSpec>& leaves) {
		int N = GetSize(leaves);
		vector<SigSpec> cur = leaves;
		for (int group = 1; group < N; group *= 2) {
			vector<SigSpec> nxt(N);
			for (int i = 0; i < N; i++) {
				int block = i / (2 * group);
				int within = i - block * 2 * group;
				if (within >= group) {
					int boundary = block * 2 * group + group - 1;
					nxt[i] = net.emit(cur[boundary], cur[i]);
				} else {
					nxt[i] = cur[i];
				}
			}
			cur = std::move(nxt);
		}
		return cur;
	}

	vector<SigSpec> build_brent_kung(PrefixNet& net, const vector<SigSpec>& leaves) {
		int N = GetSize(leaves);
		vector<SigSpec> cur = leaves;
		// Upsweep: classic reduction tree, touches indices (2*stride - 1) + k*(2*stride).
		for (int stride = 1; stride < N; stride *= 2) {
			for (int i = 2*stride - 1; i < N; i += 2*stride)
				cur[i] = net.emit(cur[i - stride], cur[i]);
		}
		// Downsweep: fill in the holes left by upsweep. Touches indices
		// (3*stride - 1) + k*(2*stride), going from coarse stride down to 1.
		int max_stride = 1;
		while (3 * max_stride * 2 - 1 < N) max_stride *= 2;
		for (int stride = max_stride; stride >= 1; stride /= 2) {
			for (int i = 3*stride - 1; i < N; i += 2*stride)
				cur[i] = net.emit(cur[i - stride], cur[i]);
		}
		return cur;
	}

	vector<SigSpec> build_han_carlson(PrefixNet& net, const vector<SigSpec>& leaves) {
		int N = GetSize(leaves);
		vector<SigSpec> cur = leaves;
		// Step 1: pairwise reduce into odd indices.
		for (int i = 1; i < N; i += 2)
			cur[i] = net.emit(cur[i - 1], cur[i]);
		// Step 2: Kogge-Stone on odd indices (offset doubled in original space).
		int num_odd = (N + 1) / 2 - (N % 2 == 0 ? 0 : 0);
		// Simpler: count odd indices directly.
		num_odd = 0;
		for (int i = 1; i < N; i += 2) num_odd++;
		for (int off_odd = 1; off_odd < num_odd; off_odd *= 2) {
			int off = 2 * off_odd;
			vector<SigSpec> nxt = cur;
			for (int i = 1; i < N; i += 2) {
				if (i >= off) nxt[i] = net.emit(cur[i - off], cur[i]);
			}
			cur = std::move(nxt);
		}
		// Step 3: fill in even indices from their left-neighbour odd prefix.
		for (int i = 2; i < N; i += 2)
			cur[i] = net.emit(cur[i - 1], cur[i]);
		return cur;
	}

	vector<SigSpec> build_network(PrefixNet& net, const vector<SigSpec>& leaves) {
		switch (topology) {
			case Topology::KOGGE_STONE: return build_kogge_stone(net, leaves);
			case Topology::SKLANSKY:    return build_sklansky(net, leaves);
			case Topology::BRENT_KUNG:  return build_brent_kung(net, leaves);
			case Topology::HAN_CARLSON: return build_han_carlson(net, leaves);
		}
		return {};
	}

	void transform_chain(const PrefixChain& chain) {
		PrefixNet net(module, chain, &cell_count);
		// Seed prefix[0] = leaves[0]; treat leaves as depth-0 signals.
		for (auto& l : chain.leaves) net.depth[l] = 0;

		vector<SigSpec> prefix = build_network(net, chain.leaves);

		log_debug("  Built %s network with %d leaves -> depth %d\n",
		          topology_name(topology), GetSize(chain.leaves), net.max_depth);

		// Wire each demanded prefix to the original destination signal, matching
		// opt_balance_tree's width/sign-extension recipe so wreduce can clean up.
		for (auto& d : chain.demands) {
			int i = d.first;
			SigSpec dst = d.second;
			SigSpec src = prefix[i];
			int w = std::min(GetSize(dst), GetSize(src));
			module->connect(dst.extract(0, w), src.extract(0, w));
			if (GetSize(dst) > w) {
				SigBit pad = (chain.a_signed || chain.b_signed) ? src[w - 1] : SigBit(State::S0);
				module->connect(dst.extract(w, GetSize(dst) - w),
				                SigSpec(pad, GetSize(dst) - w));
			}
		}

		if (net.max_depth > max_depth) max_depth = net.max_depth;
	}

	void run(const vector<IdString>& ops) {
		pool<Cell*> claimed;
		vector<PrefixChain> chains;

		// Snapshot cell list once: we'll be adding cells later (the network) and
		// don't want to re-scan them.
		vector<Cell*> initial_cells(module->cells().begin(), module->cells().end());

		for (auto op : ops) {
			for (auto c : initial_cells) {
				if (claimed.count(c)) continue;
				if (!is_chainable(c, op)) continue;

				bool a_signed = c->getParam(ID::A_SIGNED).as_bool();
				bool b_signed = c->getParam(ID::B_SIGNED).as_bool();
				SigSpec A = sigmap(c->getPort(ID::A));
				SigSpec B = sigmap(c->getPort(ID::B));

				// A head is a cell whose BOTH operands are leaves. That gives us
				// the start of a maximal linear chain.
				if (!is_leaf(A, op, a_signed, b_signed, claimed)) continue;
				if (!is_leaf(B, op, a_signed, b_signed, claimed)) continue;

				PrefixChain chain;
				chain.op = op;
				chain.a_signed = a_signed;
				chain.b_signed = b_signed;
				chain.leaves.push_back(A);
				chain.leaves.push_back(B);
				chain.cells.push_back(c);
				chain.ref_attributes = c->attributes;

				extend_chain(chain, claimed);
				detect_demands(chain);

				// Only rewrite chains with 2+ demand points; single-output
				// reductions are opt_balance_tree's job.
				if (GetSize(chain.demands) < 2) continue;

				log_debug("  Candidate chain of %d leaves, %d demands (op=%s)\n",
				          GetSize(chain.leaves), GetSize(chain.demands), log_id(op));

				for (auto cc : chain.cells) claimed.insert(cc);
				chains.push_back(std::move(chain));
			}
		}

		for (auto& chain : chains) {
			transform_chain(chain);
			chains_built++;
			leaves_total += GetSize(chain.leaves);
		}

		// Remove the original chain cells.
		for (auto c : claimed) module->remove(c);
	}
};

struct OptParallelPrefixPass : public Pass {
	OptParallelPrefixPass() : Pass("opt_parallel_prefix",
		"rebuild $add/$and/$or/$xor/$mul cascades as parallel-prefix networks") {}

	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_parallel_prefix [options] [selection]\n");
		log("\n");
		log("This pass detects linear cascades of an associative operator (add, and,\n");
		log("or, xor, mul) where two or more intermediate results in the cascade are\n");
		log("consumed externally (port outputs or non-chain fanout) and rebuilds the\n");
		log("cascade as a parallel-prefix network. Intermediate prefix nodes are\n");
		log("shared across all demanded outputs so the cost is O(N log N) cells (or\n");
		log("less, depending on topology) instead of N independent balanced trees.\n");
		log("\n");
		log("Cascades with fewer than two demanded prefix points are left alone for\n");
		log("opt_balance_tree to handle.\n");
		log("\n");
		log("    -arith\n");
		log("        only convert arithmetic cells ($add, $mul).\n");
		log("\n");
		log("    -logic\n");
		log("        only convert logic cells ($and, $or, $xor).\n");
		log("\n");
		log("    -kogge-stone\n");
		log("        use the Kogge-Stone topology (default). Minimum depth log2(N),\n");
		log("        approximately N*log2(N) cells, fanout 2.\n");
		log("\n");
		log("    -sklansky\n");
		log("        use the Sklansky topology. Minimum depth log2(N), approximately\n");
		log("        (N/2)*log2(N) cells, fanout up to N/2.\n");
		log("\n");
		log("    -brent-kung\n");
		log("        use the Brent-Kung topology. Depth 2*log2(N)-2, approximately\n");
		log("        2*N cells, fanout 2.\n");
		log("\n");
		log("    -han-carlson\n");
		log("        use the Han-Carlson topology. Depth log2(N)+1, hybrid between\n");
		log("        Kogge-Stone (on odd indices) and Brent-Kung's outer layers.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_PARALLEL_PREFIX pass (cell cascades to prefix networks).\n");

		vector<IdString> cell_types = {ID($and), ID($or), ID($xor), ID($add), ID($mul)};
		Topology topology = Topology::KOGGE_STONE;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-arith") { cell_types = {ID($add), ID($mul)}; continue; }
			if (args[argidx] == "-logic") { cell_types = {ID($and), ID($or), ID($xor)}; continue; }
			if (args[argidx] == "-kogge-stone") { topology = Topology::KOGGE_STONE; continue; }
			if (args[argidx] == "-sklansky")    { topology = Topology::SKLANSKY;    continue; }
			if (args[argidx] == "-brent-kung")  { topology = Topology::BRENT_KUNG;  continue; }
			if (args[argidx] == "-han-carlson") { topology = Topology::HAN_CARLSON; continue; }
			break;
		}
		extra_args(args, argidx, design);

		log("Topology: %s\n", topology_name(topology));

		dict<IdString, int> total_cells;
		int total_chains = 0;
		int total_leaves = 0;
		int total_max_depth = 0;
		for (auto module : design->selected_modules()) {
			OptParallelPrefixWorker worker(module, topology);
			worker.run(cell_types);
			for (auto& kv : worker.cell_count) total_cells[kv.first] += kv.second;
			total_chains += worker.chains_built;
			total_leaves += worker.leaves_total;
			if (worker.max_depth > total_max_depth) total_max_depth = worker.max_depth;
		}

		log("Rewrote %d chain(s) covering %d leaves (max network depth %d).\n",
		    total_chains, total_leaves, total_max_depth);
		for (auto op : cell_types)
			log("  Emitted %d %s cells.\n", total_cells[op], log_id(op));

		Yosys::run_pass("clean -purge");
	}
} OptParallelPrefixPass;

PRIVATE_NAMESPACE_END
