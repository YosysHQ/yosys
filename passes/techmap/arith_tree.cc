/**
 * Replaces chains of $add/$sub/$alu and $macc cells with carry-save compression trees
 *
 * Terminology:
 * - parent:    Cells that consume another cell's output
 * - chainable: Adds/subs with no carry-out usage
 * - chain:     Connected path of chainable cells
 */

#include "kernel/compressor_tree.h"
#include "kernel/macc.h"
#include "kernel/newcelltypes.h"
#include "kernel/sigtools.h"
#include "kernel/yosys.h"

#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ArithTreeOptions {
	CompressorTree::Strategy strategy = CompressorTree::Strategy::PREFER_42;
	CompressorTree::FinalMode final_mode = CompressorTree::FinalMode::RIPPLE;
	bool fma_fusion = true;
	// A compressor level costs roughly fixed depth at any width, so
	// compression only pays when it removes a wide carry-propagate adder.
	int min_width = 0;
	// Hold late operands out of the tree until the level they arrive at
	bool schedule_arrival = true;
};

struct ArithTreeWorker {
	const ArithTreeOptions &opt;
	Module *module;
	SigMap sigmap;

	dict<SigBit, pool<Cell *>> bit_consumers;
	dict<SigBit, int> fanout;
	dict<SigBit, Cell *> bit_driver;
	dict<SigBit, int> arrival_cache;
	pool<Cell *> arrival_visiting;

	pool<Cell *> addsub;
	pool<Cell *> alu;
	pool<Cell *> macc;

	struct Operand {
		SigSpec sig;
		bool is_signed;
		bool negate;
		// With FMA, when both factors are set, the operand represents a product to
		// be expanded into partial products at extraction time, is_signed then
		// applies to factor_a, and factor_b carries its own signedness
		SigSpec factor_b; // empty for regular operands
		bool factor_b_signed = false;
	};

	ArithTreeWorker(const ArithTreeOptions &opt, Module *module) : opt(opt), module(module), sigmap(module)
	{
		// Build traversal data
		for (auto cell : module->cells()) {
			for (auto &[name, sig] : cell->connections()) {
				if (cell->input(name)) {
					for (auto bit : sigmap(sig)) {
						bit_consumers[bit].insert(cell);
					}
				}
				if (cell->output(name))
					for (auto bit : sigmap(sig))
						bit_driver[bit] = cell;
			}
		}

		for (auto &[sig, consumers] : bit_consumers)
			fanout[sig] = consumers.size();

		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(SigSpec(wire)))
					fanout[bit]++;

		// Collect cell data
		for (auto cell : module->cells()) {
			if (is_addsub(cell))
				addsub.insert(cell);
			else if (is_alu(cell))
				alu.insert(cell);
			else if (is_macc(cell))
				macc.insert(cell);
		}
	}

	static int clog2(int n)
	{
		int r = 0;
		while ((1 << r) < n)
			r++;
		return r;
	}

	// Compressor levels a row of `rows` operands takes to reach two
	static int tree_levels(int rows)
	{
		int levels = 0;
		for (double n = rows; n > 2; n = std::ceil(n * 2.0 / 3.0))
			levels++;
		return levels;
	}

	// Gate delays across a carry-propagate adder, taken as parallel-prefix since
	// that is what a wide $add lowers to
	static int adder_levels(int width) { return 2 * std::max(1, clog2(width)); }

	// Partial-product rows a $macc reduces, i.e. its addends plus a row per
	// multiplied bit
	static int macc_rows(Cell *cell)
	{
		Macc macc;
		macc.from_cell(cell);
		int rows = 0;
		for (auto &term : macc.terms)
			rows += GetSize(term.in_b) ? std::min(GetSize(term.in_a), GetSize(term.in_b)) : 1;
		return rows;
	}

	// Depth of a cell's own logic in gate delays. Word-level cells survive to the
	// netlist as the network they stand for, so each is costed as that network: a
	// prefix adder is logarithmic in its width, a multiplier is a compressor tree
	// over its rows plus that adder, and a shifter is a mux level per amount bit.
	int cell_levels(Cell *cell)
	{
		auto w = [&](IdString port) { return cell->hasPort(port) ? GetSize(cell->getPort(port)) : 1; };

		if (cell->type.in(ID($add), ID($sub), ID($alu), ID($neg)))
			return adder_levels(w(ID::Y));
		if (cell->type == ID($mul))
			return 2 * tree_levels(std::min(w(ID::A), w(ID::B))) + adder_levels(w(ID::Y));
		if (cell->type.in(ID($macc), ID($macc_v2)))
			return 2 * tree_levels(macc_rows(cell)) + adder_levels(w(ID::Y));
		// Restoring division is a subtract and a select per result bit
		if (cell->type.in(ID($div), ID($mod), ID($divfloor), ID($modfloor)))
			return w(ID::Y) * (adder_levels(w(ID::Y)) + 1);
		if (cell->type.in(ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx)))
			return std::max(1, w(ID::B));
		if (cell->type.in(ID($lt), ID($le), ID($gt), ID($ge)))
			return adder_levels(std::max(w(ID::A), w(ID::B)));
		if (cell->type.in(ID($eq), ID($ne), ID($eqx), ID($nex)))
			return 1 + clog2(std::max(w(ID::A), w(ID::B)));
		if (cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
				  ID($logic_and), ID($logic_or), ID($logic_not)))
			return 1 + clog2(w(ID::A));
		if (cell->type == ID($pmux))
			return 1 + clog2(w(ID::S));
		if (cell->type == ID($fa))
			return 2;
		return 1; // bitwise logic, muxes, and anything unmodelled
	}

	// State elements end the walk: their outputs are there when the cycle starts
	bool is_start(Cell *cell)
	{
		return StaticCellTypes::Compat::mem_ff(cell->type) || cell->type.in(ID($anyseq), ID($anyconst));
	}

	// Arrival of `bit` in gate delays, memoised across the whole module
	int arrival(SigBit bit)
	{
		bit = sigmap(bit);
		auto cached = arrival_cache.find(bit);
		if (cached != arrival_cache.end())
			return cached->second;

		auto driven = bit_driver.find(bit);
		if (!bit.is_wire() || driven == bit_driver.end() || is_start(driven->second))
			return arrival_cache[bit] = 0;

		// A bit already on the stack is part of a combinational loop, which has no
		// arrival to speak of; treat it as a start point rather than recursing
		Cell *cell = driven->second;
		if (!arrival_visiting.insert(cell).second)
			return 0;

		int in = 0;
		for (auto &[name, sig] : cell->connections())
			if (cell->input(name))
				in = std::max(in, arrival(sig));
		arrival_visiting.erase(cell);

		int out = in + cell_levels(cell);
		for (auto &[name, sig] : cell->connections())
			if (cell->output(name))
				for (auto b : sigmap(sig))
					arrival_cache[b] = out;
		return out;
	}

	int arrival(const SigSpec &sig)
	{
		int a = 0;
		for (auto bit : sigmap(sig))
			a = std::max(a, arrival(bit));
		return a;
	}

	bool is_addsub(Cell *cell) {
		return cell->type == ID($add) || cell->type == ID($sub);
	}

	bool is_alu(Cell *cell) {
		return cell->type == ID($alu);
	}

	bool is_macc(Cell *cell) {
		return cell->type == ID($macc) || cell->type == ID($macc_v2);
	}

	bool is_sub(Cell *cell) {
		SigSpec bi = sigmap(cell->getPort(ID::BI));
		SigSpec ci = sigmap(cell->getPort(ID::CI));
		return GetSize(bi) == 1 && bi[0] == State::S1 && GetSize(ci) == 1 && ci[0] == State::S1;
	}

	bool is_add(Cell *cell)
	{
		SigSpec bi = sigmap(cell->getPort(ID::BI));
		SigSpec ci = sigmap(cell->getPort(ID::CI));
		return GetSize(bi) == 1 && bi[0] == State::S0 && GetSize(ci) == 1 && ci[0] == State::S0;
	}

	bool is_chainable(Cell *cell)
	{
		if (!(is_add(cell) || is_sub(cell)))
			return false;
		for (auto bit : sigmap(cell->getPort(ID::X)))
			if (fanout.count(bit) && fanout[bit] > 0)
				return false;
		for (auto bit : sigmap(cell->getPort(ID::CO)))
			if (fanout.count(bit) && fanout[bit] > 0)
				return false;
		return true;
	}

	// A link truncates its result at its own Y width, so flattening it into a wider
	// consumer is only sound when that truncation provably never fires. This is the
	// same question macc_may_overflow() answers for the structurally identical $macc
	// merge in alumacc, and it is answered the same way: from operand widths alone.
	bool link_may_overflow(Cell *link)
	{
		// Only unsigned addition has a bound this simple. Subtraction borrows below
		// zero and wraps into the discarded bits, and a signed operand changes what
		// those bits mean, so neither is proven here.
		if (!(link->type == ID($add) || (is_alu(link) && is_add(link))))
			return true;
		if (link->getParam(ID::A_SIGNED).as_bool() || link->getParam(ID::B_SIGNED).as_bool())
			return true;

		// a + b never needs more than one bit beyond the wider operand, since
		// (2**wa - 1) + (2**wb - 1) < 2**(max(wa, wb) + 1).
		int wa = GetSize(link->getPort(ID::A)), wb = GetSize(link->getPort(ID::B));
		int need = wb ? std::max(wa, wb) + 1 : wa;
		return GetSize(link->getPort(ID::Y)) < need;
	}

	Cell *sole_chainable_consumer(Cell *cell, const pool<Cell *> &candidates)
	{
		SigSpec sig = sigmap(cell->getPort(ID::Y));
		Cell *consumer = nullptr;
		for (auto bit : sig) {
			if (!fanout.count(bit) || fanout[bit] != 1)
				return nullptr;
			if (!bit_consumers.count(bit) || bit_consumers[bit].size() != 1)
				return nullptr;

			Cell *c = *bit_consumers[bit].begin();
			if (!candidates.count(c))
				return nullptr;

			if (consumer == nullptr)
				consumer = c;
			else if (consumer != c)
				return nullptr;
		}
		// A link narrower than its consumer discards a carry the wider consumer would
		// otherwise see, since (x % 2**link) % 2**parent == x % 2**parent only when
		// parent <= link. Flatten it anyway when the link cannot reach that carry, but
		// only if the consumer zero-extends it: a sign-extended narrow link means
		// something different from the full-width sum that replaces it.
		if (consumer != nullptr && GetSize(sig) < GetSize(consumer->getPort(ID::Y))) {
			bool consumer_extends_unsigned = !consumer->getParam(ID::A_SIGNED).as_bool() &&
			                                 !consumer->getParam(ID::B_SIGNED).as_bool();
			if (!consumer_extends_unsigned || link_may_overflow(cell))
				return nullptr;
		}
		return consumer;
	}

	dict<Cell *, Cell *> find_parents(const pool<Cell *> &candidates)
	{
		dict<Cell *, Cell *> parent_of;
		for (auto cell : candidates) {
			Cell *consumer = sole_chainable_consumer(cell, candidates);
			if (consumer && consumer != cell)
				parent_of[cell] = consumer;
		}
		return parent_of;
	}

	std::pair<dict<Cell *, pool<Cell *>>, pool<Cell *>> invert_parent_map(const dict<Cell *, Cell *> &parent_of)
	{
		dict<Cell *, pool<Cell *>> children_of;
		pool<Cell *> has_parent;
		for (auto &[child, parent] : parent_of) {
			children_of[parent].insert(child);
			has_parent.insert(child);
		}
		return {children_of, has_parent};
	}

	pool<Cell *> collect_chain(Cell *root, const dict<Cell *, pool<Cell *>> &children_of)
	{
		pool<Cell *> chain;
		std::queue<Cell *> q;
		q.push(root);
		while (!q.empty()) {
			Cell *cur = q.front();
			q.pop();
			if (!chain.insert(cur).second)
				continue;
			auto it = children_of.find(cur);
			if (it != children_of.end())
				for (auto child : it->second)
					q.push(child);
		}
		return chain;
	}

	pool<SigBit> internal_bits(const pool<Cell *> &chain)
	{
		pool<SigBit> bits;
		for (auto cell : chain)
			for (auto bit : sigmap(cell->getPort(ID::Y)))
				bits.insert(bit);
		return bits;
	}

	bool overlaps(SigSpec sig, const pool<SigBit> &bits)
	{
		for (auto bit : sig)
			if (bits.count(bit))
				return true;
		return false;
	}

	bool feeds_subtracted_port(Cell *child, Cell *parent)
	{
		bool parent_subtracts;
		if (parent->type == ID($sub))
			parent_subtracts = true;
		else if (is_alu(parent))
			parent_subtracts = is_sub(parent);
		else
			return false;

		if (!parent_subtracts)
			return false;

		SigSpec child_y = sigmap(child->getPort(ID::Y));
		SigSpec parent_b = sigmap(parent->getPort(ID::B));
		for (auto bit : child_y)
			for (auto pbit : parent_b)
				if (bit == pbit)
					return true;
		return false;
	}

	std::vector<Operand> extract_chain_operands(const pool<Cell *> &chain, Cell *root, const dict<Cell *, Cell *> &parent_of, int &neg_compensation)
	{
		pool<SigBit> chain_bits = internal_bits(chain);

		// Propagate negation flags through chain
		dict<Cell *, bool> negated;
		negated[root] = false;
		{
			std::queue<Cell *> q;
			q.push(root);
			while (!q.empty()) {
				Cell *cur = q.front();
				q.pop();
				for (auto cell : chain) {
					if (!parent_of.count(cell) || parent_of.at(cell) != cur)
						continue;
					if (negated.count(cell))
						continue;
					negated[cell] = negated[cur] ^ feeds_subtracted_port(cell, cur);
					q.push(cell);
				}
			}
		}

		// Extract leaf operands
		std::vector<Operand> operands;
		neg_compensation = 0;

		for (auto cell : chain) {
			bool cell_neg = negated.count(cell) ? negated[cell] : false;

			SigSpec a = sigmap(cell->getPort(ID::A));
			SigSpec b = sigmap(cell->getPort(ID::B));
			bool a_signed = cell->getParam(ID::A_SIGNED).as_bool();
			bool b_signed = cell->getParam(ID::B_SIGNED).as_bool();
			bool b_sub = (cell->type == ID($sub)) || (is_alu(cell) && is_sub(cell));

			if (!overlaps(a, chain_bits)) {
				operands.push_back({a, a_signed, cell_neg, SigSpec(), false});
				if (cell_neg)
					neg_compensation++;
			}
			if (!overlaps(b, chain_bits)) {
				bool neg = cell_neg ^ b_sub;
				operands.push_back({b, b_signed, neg, SigSpec(), false});
				if (neg)
					neg_compensation++;
			}
		}
		return operands;
	}

	bool extract_macc_operands(Cell *cell, std::vector<Operand> &operands, int &neg_compensation)
	{
		Macc macc(cell);
		neg_compensation = 0;

		for (auto &term : macc.terms) {
			if (GetSize(term.in_b) != 0) {
				if (!opt.fma_fusion)
					return false;

				// Preserve term as a multiplicative operand which is expanded into partial products
				Operand op;
				op.sig = term.in_a;
				op.is_signed = term.is_signed;
				op.negate = term.do_subtract;
				op.factor_b = term.in_b;
				op.factor_b_signed = term.is_signed;
				operands.push_back(op);
				continue;
			}
			operands.push_back({term.in_a, term.is_signed, term.do_subtract, SigSpec(), false});
			if (term.do_subtract)
				neg_compensation++;
		}
		return true;
	}

	std::vector<CompressorTree::DepthSig> build_operand_pool(Cell *cell, std::vector<Operand> &operands, int width, int &neg_compensation)
	{
		// Expand operands into a flat list of signals for reduction
		std::vector<CompressorTree::DepthSig> pool;
		pool.reserve(operands.size() * 2);

		for (auto &op : operands) {
			if (GetSize(op.factor_b) == 0) {
				// Additive operand
				int depth = arrival(op.sig);
				op.sig.extend_u0(width, op.is_signed);
				if (op.negate) {
					op.sig = module->Not(NEW_ID2_SUFFIX("not"), op.sig); // SILIMATE: Improve the naming
					depth++;
				}
				pool.push_back({op.sig, depth});
			} else {
				// Multiplicative operand: every row is one AND past both factors
				int depth = std::max(arrival(op.sig), arrival(op.factor_b)) + 1;
				auto pps = CompressorTree::generate_partial_products(module, op.sig, op.factor_b, op.is_signed, op.factor_b_signed, width, cell->name); // SILIMATE: Improve the naming

				if (!op.negate) {
					for (auto &pp : pps)
						pool.push_back({pp.sig, depth});
					continue;
				}

				auto [pa, pb] = CompressorTree::reduce_scheduled(module, pps, width, opt.strategy, cell->name); // SILIMATE: Improve the naming
				SigSpec p = module->addWire(NEW_ID2_SUFFIX("prod"), width); // SILIMATE: Improve the naming
				module->addAdd(NEW_ID2_SUFFIX("add"), pa, pb, p, false); // SILIMATE: Improve the naming
				SigSpec np = module->addWire(NEW_ID2_SUFFIX("nprod"), width); // SILIMATE: Improve the naming
				module->addNot(NEW_ID2_SUFFIX("not"), p, np); // SILIMATE: Improve the naming
				// Its own rows, the adder above, and the inverter
				pool.push_back({np, depth + 2 * tree_levels(GetSize(pps)) + adder_levels(width) + 1});
				neg_compensation++;
			}
		}

		if (neg_compensation > 0)
			pool.push_back({SigSpec(neg_compensation, width), 0});

		rebase_depths(pool);
		return pool;
	}

	// Turn arrival estimates into levels the tree can act on. Both sides count gate
	// delays, so the origin moves to the earliest operand, and operands within a
	// compressor of each other share a level: the tree cannot separate them by less
	// than that, and doing so only fragments its groupings for a difference the
	// estimate cannot resolve anyway.
	//
	// Three operands reduce in one level whatever their arrivals, so scheduling
	// them can only reorder one compressor's ports. Bit-level detail decides that
	// -- an operand zero in a column degenerates the compressor there -- and a
	// word-level arrival estimate does not see it, so leave those pools alone.
	void rebase_depths(std::vector<CompressorTree::DepthSig> &pool)
	{
		if (!opt.schedule_arrival || GetSize(pool) <= 3) {
			for (auto &e : pool)
				e.depth = 0;
			return;
		}

		std::vector<int> sorted;
		for (auto &e : pool)
			sorted.push_back(e.depth);
		std::sort(sorted.begin(), sorted.end());

		// Collapse each run of near-equal arrivals onto the earliest of that run
		dict<int, int> level;
		int start = sorted.front();
		for (int d : sorted) {
			if (d - start >= CompressorTree::FA_GATE_DEPTH)
				start = d;
			level[d] = start - sorted.front();
		}
		for (auto &e : pool)
			e.depth = level.at(e.depth);
	}

	void emit_tree(Cell *cell, std::vector<Operand> &operands, SigSpec result_y, int neg_compensation)
	{
		int width = GetSize(result_y);
		auto pool = build_operand_pool(cell, operands, width, neg_compensation);
		int final_depth = 0;
		auto [a, b] = CompressorTree::reduce_scheduled(module, std::move(pool), width, opt.strategy, cell->name, nullptr, &final_depth); // SILIMATE: Improve the naming
		auto final_choice = CompressorTree::pick_final_adder(width, final_depth, opt.final_mode);
		CompressorTree::emit_final_adder(module, a, b, result_y, final_choice, cell->name); // SILIMATE: Improve the naming
	}

	void process_chains()
	{
		pool<Cell *> candidates;
		for (auto cell : addsub)
			candidates.insert(cell);
		for (auto cell : alu)
			if (is_chainable(cell))
				candidates.insert(cell);

		if (candidates.empty())
			return;

		auto parent_of = find_parents(candidates);
		auto [children_of, has_parent] = invert_parent_map(parent_of);

		pool<Cell *> to_remove;
		for (auto root : candidates) {
			if (has_parent.count(root) || to_remove.count(root))
				continue; // Not a tree root

			if (GetSize(root->getPort(ID::Y)) < opt.min_width)
				continue;

			pool<Cell *> chain = collect_chain(root, children_of);
			if (chain.size() < 2)
				continue;

			int neg_compensation;
			auto operands = extract_chain_operands(chain, root, parent_of, neg_compensation);
			if (operands.size() < 3)
				continue;

			for (auto c : chain)
				to_remove.insert(c);

			emit_tree(root, operands, root->getPort(ID::Y), neg_compensation);
		}

		for (auto cell : to_remove)
			module->remove(cell);
	}

	void process_maccs()
	{
		pool<Cell *> to_remove;
		for (auto cell : macc) {
			if (GetSize(cell->getPort(ID::Y)) < opt.min_width)
				continue;

			std::vector<Operand> operands;
			int neg_compensation;
			if (!extract_macc_operands(cell, operands, neg_compensation))
				continue;
			if (operands.size() < 1)
				continue;
			int mul_terms = 0;
			for (auto &op : operands)
				if (GetSize(op.factor_b) > 0)
					mul_terms++;
			bool has_mul = (mul_terms > 0);
			if (mul_terms == 1 && operands.size() == 1)
				continue;
			if (!has_mul && operands.size() < 3)
				continue;
			emit_tree(cell, operands, cell->getPort(ID::Y), neg_compensation);
			to_remove.insert(cell);
		}
		for (auto cell : to_remove)
			module->remove(cell);
}

	void run()
	{
		if (addsub.empty() && alu.empty() && macc.empty())
			return;

		process_chains();
		process_maccs();
	}
};

struct ArithTreePass : public Pass {
	ArithTreePass() : Pass("arith_tree", "convert add/sub/macc/alu chains to carry-save adder trees") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    arith_tree [options] [selection]\n");
		log("\n");
		log("This pass replaces chains of $add/$sub cells, $alu cells (with constant\n");
		log("BI/CI), and $macc/$macc_v2 cells with carry-save adder trees \n");
		log("using $fa cells and a single final adder.\n");
		log("\n");
		log("    -strategy <fa|42>\n");
		log("        Compressor strategy. 'fa' uses only 3:2 full-adder groupings\n");
		log("        '42' (the default) prefers 4:2 compressor groupings, with\n");
		log("        fallback to 3:2 compressors for residuals\n");
		log("\n");
		log("    -final <auto|ripple|prefix>\n");
		log("        Selects the architecture used for the final two-vector add.\n");
		log("\n");
		log("    -no-fma\n");
		log("        Disable fused multiply-add expansion in $macc cells\n");
		log("\n");
		log("    -no-schedule\n");
		log("        Feed every operand into the tree at level 0. By default each\n");
		log("        one enters at the level its own logic arrives, estimated from\n");
		log("        the depth of the network driving it, so a late operand is held\n");
		log("        back and crosses one compressor level instead of all of them.\n");
		log("        A product feeding a sum of products is the usual case.\n");
		log("\n");
		log("    -min-width <n>\n");
		log("        Skip chains and $macc cells whose result is narrower than <n>\n");
		log("        bits (default 0, i.e. no limit). A compressor level costs about\n");
		log("        the same depth at any width, so compression only pays when it\n");
		log("        removes a wide carry-propagate adder; below that the plain chain\n");
		log("        (or 'opt_balance_tree') wins. Prefer this over restricting the\n");
		log("        selection: this pass indexes every cell in a selected module, so\n");
		log("        a cell-level selection only gates which modules run, and one wide\n");
		log("        adder anywhere would otherwise pull in all the narrow chains too.\n");
		log("\n");
		log("The default behaviour delivers 4:2 compression, FMA fusion, and a\n");
		log("final standard adder\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing ARITH_TREE pass.\n");

		ArithTreeOptions opt;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			const std::string &arg = args[argidx];
			if (arg == "-strategy" && argidx + 1 < args.size()) {
				const std::string &v = args[++argidx];
				if (v == "fa") { opt.strategy = CompressorTree::Strategy::FA_ONLY; }
				else if (v == "42") { opt.strategy = CompressorTree::Strategy::PREFER_42; }
				else { log_cmd_error("arith_tree: unknown -strategy '%s'\n", v.c_str()); }
				continue;
			}
			if (arg == "-final" && argidx + 1 < args.size()) {
				const std::string &v = args[++argidx];
				if (v == "auto") { opt.final_mode = CompressorTree::FinalMode::AUTO; }
				else if (v == "ripple") { opt.final_mode = CompressorTree::FinalMode::RIPPLE; }
				else if (v == "prefix") { opt.final_mode = CompressorTree::FinalMode::PREFIX; }
				else { log_cmd_error("arith_tree: unknown -final '%s'\n", v.c_str()); }
				continue;
			}
			if (arg == "-no-fma") {
				opt.fma_fusion = false;
				continue;
			}
			if (arg == "-no-schedule") {
				opt.schedule_arrival = false;
				continue;
			}
			if (arg == "-min-width" && argidx + 1 < args.size()) {
				opt.min_width = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			ArithTreeWorker worker(opt, mod);
			worker.run();
		}
	}
} ArithTreePass;

PRIVATE_NAMESPACE_END
