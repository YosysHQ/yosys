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
#include "kernel/sigtools.h"
#include "kernel/yosys.h"

#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ArithTreeOptions {
	CompressorTree::Strategy strategy = CompressorTree::Strategy::PREFER_42;
	CompressorTree::FinalMode final_mode = CompressorTree::FinalMode::RIPPLE;
	bool fma_fusion = true;
};

struct ArithTreeWorker {
	const ArithTreeOptions &opt;
	Module *module;
	SigMap sigmap;

	dict<SigBit, pool<Cell *>> bit_consumers;
	dict<SigBit, int> fanout;

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

	Cell *sole_chainable_consumer(SigSpec sig, const pool<Cell *> &candidates)
	{
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
		return consumer;
	}

	dict<Cell *, Cell *> find_parents(const pool<Cell *> &candidates)
	{
		dict<Cell *, Cell *> parent_of;
		for (auto cell : candidates) {
			Cell *consumer = sole_chainable_consumer(sigmap(cell->getPort(ID::Y)), candidates);
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
				op.sig.extend_u0(width, op.is_signed);
				if (op.negate)
					op.sig = module->Not(NEW_ID2_SUFFIX("not"), op.sig); // SILIMATE: Improve the naming
				pool.push_back({op.sig, 0});
			} else {
				// Multiplicative operand
				auto pps = CompressorTree::generate_partial_products(module, op.sig, op.factor_b, op.is_signed, op.factor_b_signed, width);

				if (!op.negate) {
					for (auto &pp : pps)
						pool.push_back(pp);
					continue;
				}

				auto [pa, pb] = CompressorTree::reduce_scheduled(module, pps, width, opt.strategy);
				SigSpec p = module->addWire(NEW_ID2_SUFFIX("prod"), width); // SILIMATE: Improve the naming
				module->addAdd(NEW_ID2_SUFFIX("add"), pa, pb, p, false); // SILIMATE: Improve the naming
				SigSpec np = module->addWire(NEW_ID2_SUFFIX("nprod"), width); // SILIMATE: Improve the naming
				module->addNot(NEW_ID2_SUFFIX("not"), p, np); // SILIMATE: Improve the naming
				pool.push_back({np, 0});
				neg_compensation++;
			}
		}

		if (neg_compensation > 0)
			pool.push_back({SigSpec(neg_compensation, width), 0});

		return pool;
	}

	void emit_tree(Cell *cell, std::vector<Operand> &operands, SigSpec result_y, int neg_compensation)
	{
		int width = GetSize(result_y);
		auto pool = build_operand_pool(cell, operands, width, neg_compensation);
		int final_depth = 0;
		auto [a, b] = CompressorTree::reduce_scheduled(module, std::move(pool), width, opt.strategy, nullptr, &final_depth);
		auto final_choice = CompressorTree::pick_final_adder(width, final_depth, opt.final_mode);
		CompressorTree::emit_final_adder(module, a, b, result_y, final_choice);
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
