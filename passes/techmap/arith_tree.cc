/**
 * Replaces chains of $add/$sub and $macc cells with carry-save adder trees
 *
 * Terminology:
 * - parent:    Cells that consume another cell's output
 * - chainable: Adds/subs with no carry-out usage
 * - chain:     Connected path of chainable cells
 */

#include "kernel/macc.h"
#include "kernel/sigtools.h"
#include "kernel/wallace_tree.h"
#include "kernel/yosys.h"

#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Operand {
	SigSpec sig;
	bool is_signed;
	bool negate;
};

struct Traversal {
	SigMap sigmap;
	dict<SigBit, pool<Cell *>> bit_consumers;
	dict<SigBit, int> fanout;
	Traversal(Module *module) : sigmap(module)
	{
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						bit_consumers[bit].insert(cell);

		for (auto &pair : bit_consumers)
			fanout[pair.first] = pair.second.size();

		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(SigSpec(wire)))
					fanout[bit]++;
	}
};

struct Cells {
	pool<Cell *> addsub;
	pool<Cell *> alu;
	pool<Cell *> macc;

	static bool is_addsub(Cell *cell) { return cell->type == ID($add) || cell->type == ID($sub); }

	static bool is_alu(Cell *cell) { return cell->type == ID($alu); }

	static bool is_macc(Cell *cell) { return cell->type == ID($macc) || cell->type == ID($macc_v2); }

	bool empty() { return addsub.empty() && alu.empty() && macc.empty(); }

	Cells(Module *module)
	{
		for (auto cell : module->cells()) {
			if (is_addsub(cell))
				addsub.insert(cell);
			else if (is_alu(cell))
				alu.insert(cell);
			else if (is_macc(cell))
				macc.insert(cell);
		}
	}
};

struct AluInfo {
	Cells &cells;
	Traversal &traversal;
	bool is_subtract(Cell *cell)
	{
		SigSpec bi = traversal.sigmap(cell->getPort(ID::BI));
		SigSpec ci = traversal.sigmap(cell->getPort(ID::CI));
		return GetSize(bi) == 1 && bi[0] == State::S1 && GetSize(ci) == 1 && ci[0] == State::S1;
	}

	bool is_add(Cell *cell)
	{
		SigSpec bi = traversal.sigmap(cell->getPort(ID::BI));
		SigSpec ci = traversal.sigmap(cell->getPort(ID::CI));
		return GetSize(bi) == 1 && bi[0] == State::S0 && GetSize(ci) == 1 && ci[0] == State::S0;
	}

	bool is_chainable(Cell *cell)
	{
		if (!(is_add(cell) || is_subtract(cell)))
			return false;

		for (auto bit : traversal.sigmap(cell->getPort(ID::X)))
			if (traversal.fanout.count(bit) && traversal.fanout[bit] > 0)
				return false;
		for (auto bit : traversal.sigmap(cell->getPort(ID::CO)))
			if (traversal.fanout.count(bit) && traversal.fanout[bit] > 0)
				return false;

		return true;
	}
};

struct Rewriter {
	Module *module;
	Cells &cells;
	Traversal traversal;
	AluInfo alu_info;

	Rewriter(Module *module, Cells &cells) : module(module), cells(cells), traversal(module), alu_info{cells, traversal} {}

	Cell *sole_chainable_consumer(SigSpec sig, const pool<Cell *> &candidates)
	{
		Cell *consumer = nullptr;
		for (auto bit : sig) {
			if (!traversal.fanout.count(bit) || traversal.fanout[bit] != 1)
				return nullptr;
			if (!traversal.bit_consumers.count(bit) || traversal.bit_consumers[bit].size() != 1)
				return nullptr;

			Cell *c = *traversal.bit_consumers[bit].begin();
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
			Cell *consumer = sole_chainable_consumer(traversal.sigmap(cell->getPort(ID::Y)), candidates);
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
			for (auto bit : traversal.sigmap(cell->getPort(ID::Y)))
				bits.insert(bit);
		return bits;
	}

	static bool overlaps(SigSpec sig, const pool<SigBit> &bits)
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
		else if (cells.is_alu(parent))
			parent_subtracts = alu_info.is_subtract(parent);
		else
			return false;

		if (!parent_subtracts)
			return false;

		// Check if any bit of child's Y connects to parent's B
		SigSpec child_y = traversal.sigmap(child->getPort(ID::Y));
		SigSpec parent_b = traversal.sigmap(parent->getPort(ID::B));
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

			SigSpec a = traversal.sigmap(cell->getPort(ID::A));
			SigSpec b = traversal.sigmap(cell->getPort(ID::B));
			bool a_signed = cell->getParam(ID::A_SIGNED).as_bool();
			bool b_signed = cell->getParam(ID::B_SIGNED).as_bool();
			bool b_sub = (cell->type == ID($sub)) || (cells.is_alu(cell) && alu_info.is_subtract(cell));

			// Only add operands not produced by other chain cells
			if (!overlaps(a, chain_bits)) {
				operands.push_back({a, a_signed, cell_neg});
				if (cell_neg)
					neg_compensation++;
			}
			if (!overlaps(b, chain_bits)) {
				bool neg = cell_neg ^ b_sub;
				operands.push_back({b, b_signed, neg});
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
			// Bail on multiplication
			if (GetSize(term.in_b) != 0)
				return false;
			operands.push_back({term.in_a, term.is_signed, term.do_subtract});
			if (term.do_subtract)
				neg_compensation++;
		}
		return true;
	}

	SigSpec extend_operand(SigSpec sig, bool is_signed, int width)
	{
		if (GetSize(sig) < width) {
			SigBit pad;
			if (is_signed && GetSize(sig) > 0)
				pad = sig[GetSize(sig) - 1];
			else
				pad = State::S0;
			sig.append(SigSpec(pad, width - GetSize(sig)));
		}
		if (GetSize(sig) > width)
			sig = sig.extract(0, width);
		return sig;
	}

	void replace_with_carry_save_tree(std::vector<Operand> &operands, SigSpec result_y, int neg_compensation, const char *desc)
	{
		int width = GetSize(result_y);
		std::vector<SigSpec> extended;
		extended.reserve(operands.size() + 1);

		for (auto &op : operands) {
			SigSpec s = extend_operand(op.sig, op.is_signed, width);
			if (op.negate)
				s = module->Not(NEW_ID, s);
			extended.push_back(s);
		}

		// Add correction for negated operands (-x = ~x + 1 so 1 per negation)
		if (neg_compensation > 0)
			extended.push_back(SigSpec(neg_compensation, width));

		int compressor_count;
		auto [a, b] = wallace_reduce_scheduled(module, extended, width, &compressor_count);
		log("  %s -> %d $fa + 1 $add (%d operands, module %s)\n", desc, compressor_count, (int)operands.size(), module);

		// Emit final add
		module->addAdd(NEW_ID, a, b, result_y, false);
	}

	void process_chains()
	{
		pool<Cell *> candidates;
		for (auto cell : cells.addsub)
			candidates.insert(cell);
		for (auto cell : cells.alu)
			if (alu_info.is_chainable(cell))
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

			replace_with_carry_save_tree(operands, root->getPort(ID::Y), neg_compensation, "Replaced add/sub chain");
		}

		for (auto cell : to_remove)
			module->remove(cell);
	}

	void process_maccs()
	{
		for (auto cell : cells.macc) {
			std::vector<Operand> operands;
			int neg_compensation;
			if (!extract_macc_operands(cell, operands, neg_compensation))
				continue;
			if (operands.size() < 3)
				continue;

			replace_with_carry_save_tree(operands, cell->getPort(ID::Y), neg_compensation, "Replaced $macc");
			module->remove(cell);
		}
	}
};

void run(Module *module)
{
	Cells cells(module);

	if (cells.empty())
		return;

	Rewriter rewriter{module, cells};
	rewriter.process_chains();
	rewriter.process_maccs();
}

struct ArithTreePass : public Pass {
	ArithTreePass() : Pass("arith_tree", "convert add/sub/macc chains to carry-save adder trees") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    arith_tree [selection]\n");
		log("\n");
		log("This pass replaces chains of $add/$sub cells, $alu cells (with constant\n");
		log("BI/CI), and $macc/$macc_v2 cells (without multiplications) with carry-save\n");
		log("adder trees using $fa cells and a single final $add.\n");
		log("\n");
		log("The tree uses Wallace-tree scheduling: at each level, ready operands are\n");
		log("grouped into triplets and compressed via full adders, giving\n");
		log("O(log_{1.5} N) depth for N input operands.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing ARITH_TREE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
			break;
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			run(module);
		}
	}
} ArithTreePass;

PRIVATE_NAMESPACE_END
