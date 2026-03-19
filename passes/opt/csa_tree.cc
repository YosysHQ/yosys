#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/macc.h"

#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Operand {
	SigSpec sig;
	bool is_signed;
	bool negate;
};

struct CsaTreeWorker
{
	Module* module;
	SigMap sigmap;

	dict<SigBit, pool<Cell*>> bit_consumers;
	dict<SigBit, int> fanout;

	pool<Cell*> addsub_cells;
	pool<Cell*> alu_cells;
	pool<Cell*> macc_cells;

	CsaTreeWorker(Module* module) : module(module), sigmap(module) {}

	static bool is_addsub(Cell* cell)
	{
		return cell->type == ID($add) || cell->type == ID($sub);
	}

	static bool is_alu(Cell* cell)
	{
		return cell->type == ID($alu);
	}

	static bool is_macc(Cell* cell)
	{
		return cell->type == ID($macc) || cell->type == ID($macc_v2);
	}

	bool alu_is_subtract(Cell* cell)
	{
		SigSpec bi = sigmap(cell->getPort(ID::BI));
		SigSpec ci = sigmap(cell->getPort(ID::CI));
		return GetSize(bi) == 1 && bi[0] == State::S1 && GetSize(ci) == 1 && ci[0] == State::S1;
	}

	bool alu_is_add(Cell* cell)
	{
		SigSpec bi = sigmap(cell->getPort(ID::BI));
		SigSpec ci = sigmap(cell->getPort(ID::CI));
		return GetSize(bi) == 1 && bi[0] == State::S0 && GetSize(ci) == 1 && ci[0] == State::S0;
	}

	bool alu_is_chainable(Cell* cell)
	{
		if (!(alu_is_add(cell) || alu_is_subtract(cell)))
			return false;

		for (auto bit : sigmap(cell->getPort(ID::X)))
			if (fanout.count(bit) && fanout[bit] > 0)
				return false;
		for (auto bit : sigmap(cell->getPort(ID::CO)))
			if (fanout.count(bit) && fanout[bit] > 0)
				return false;

		return true;
	}

	bool is_chainable(Cell* cell)
	{
		return is_addsub(cell) || (is_alu(cell) && alu_is_chainable(cell));
	}

	void classify_cells()
	{
		for (auto cell : module->cells()) {
			if (is_addsub(cell))
				addsub_cells.insert(cell);
			else if (is_alu(cell))
				alu_cells.insert(cell);
			else if (is_macc(cell))
				macc_cells.insert(cell);
		}
	}

	void build_fanout_map()
	{
		for (auto cell : module->cells())
			for (auto& conn : cell->connections())
				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						bit_consumers[bit].insert(cell);

		for (auto& pair : bit_consumers)
			fanout[pair.first] = pair.second.size();

		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(SigSpec(wire)))
					fanout[bit]++;
	}

	Cell* sole_chainable_consumer(SigSpec sig, const pool<Cell*>& candidates)
	{
		Cell* consumer = nullptr;
		for (auto bit : sig) {
			if (!fanout.count(bit) || fanout[bit] != 1)
				return nullptr;
			if (!bit_consumers.count(bit) || bit_consumers[bit].size() != 1)
				return nullptr;

			Cell* c = *bit_consumers[bit].begin();
			if (!candidates.count(c))
				return nullptr;

			if (consumer == nullptr)
				consumer = c;
			else if (consumer != c)
				return nullptr;
		}
		return consumer;
	}

	dict<Cell*, Cell*> find_parents(const pool<Cell*>& candidates)
	{
		dict<Cell*, Cell*> parent_of;
		for (auto cell : candidates) {
			Cell* consumer = sole_chainable_consumer(
				sigmap(cell->getPort(ID::Y)), candidates);
			if (consumer && consumer != cell)
				parent_of[cell] = consumer;
		}
		return parent_of;
	}

	pool<Cell*> collect_chain(Cell* root, const dict<Cell*, pool<Cell*>>& children_of)
	{
		pool<Cell*> chain;
		std::queue<Cell*> q;
		q.push(root);
		while (!q.empty()) {
			Cell* cur = q.front(); q.pop();
			if (!chain.insert(cur).second)
				continue;
			auto it = children_of.find(cur);
			if (it != children_of.end())
				for (auto child : it->second)
					q.push(child);
		}
		return chain;
	}

	pool<SigBit> internal_bits(const pool<Cell*>& chain)
	{
		pool<SigBit> bits;
		for (auto cell : chain)
			for (auto bit : sigmap(cell->getPort(ID::Y)))
				bits.insert(bit);
		return bits;
	}

	static bool overlaps(SigSpec sig, const pool<SigBit>& bits)
	{
		for (auto bit : sig)
			if (bits.count(bit))
				return true;
		return false;
	}

	bool feeds_subtracted_port(Cell* child, Cell* parent)
	{
		bool parent_subtracts;
		if (parent->type == ID($sub))
			parent_subtracts = true;
		else if (is_alu(parent))
			parent_subtracts = alu_is_subtract(parent);
		else
			return false;

		if (!parent_subtracts)
			return false;

		SigSpec child_y  = sigmap(child->getPort(ID::Y));
		SigSpec parent_b = sigmap(parent->getPort(ID::B));
		for (auto bit : child_y)
			for (auto pbit : parent_b)
				if (bit == pbit)
					return true;
		return false;
	}

	std::vector<Operand> extract_chain_operands(
		const pool<Cell*>& chain,
		Cell* root,
		const dict<Cell*, Cell*>& parent_of,
		int& correction
	) {
		pool<SigBit> chain_bits = internal_bits(chain);
		dict<Cell*, bool> negated;
		negated[root] = false;
		{
			std::queue<Cell*> q;
			q.push(root);
			while (!q.empty()) {
				Cell* cur = q.front(); q.pop();
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

		std::vector<Operand> operands;
		correction = 0;

		for (auto cell : chain) {
			bool cell_neg;
			if (negated.count(cell))
				cell_neg = negated[cell];
			else
				cell_neg = false;

			SigSpec a = sigmap(cell->getPort(ID::A));
			SigSpec b = sigmap(cell->getPort(ID::B));
			bool a_signed = cell->getParam(ID::A_SIGNED).as_bool();
			bool b_signed = cell->getParam(ID::B_SIGNED).as_bool();
			bool b_sub = (cell->type == ID($sub)) || (is_alu(cell) && alu_is_subtract(cell));

			if (!overlaps(a, chain_bits)) {
				bool neg = cell_neg;
				operands.push_back({a, a_signed, neg});
				if (neg) correction++;
			}
			if (!overlaps(b, chain_bits)) {
				bool neg = cell_neg ^ b_sub;
				operands.push_back({b, b_signed, neg});
				if (neg) correction++;
			}
		}
		return operands;
	}

	bool extract_macc_operands(Cell* cell, std::vector<Operand>& operands, int& correction)
	{
		Macc macc(cell);
		correction = 0;

		for (auto& term : macc.terms) {
			if (GetSize(term.in_b) != 0)
				return false;
			operands.push_back({term.in_a, term.is_signed, term.do_subtract});
			if (term.do_subtract)
				correction++;
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

	SigSpec emit_not(SigSpec sig, int width)
	{
		SigSpec out = module->addWire(NEW_ID, width);
		Cell* inv = module->addCell(NEW_ID, ID($not));
		inv->setParam(ID::A_SIGNED, false);
		inv->setParam(ID::A_WIDTH, width);
		inv->setParam(ID::Y_WIDTH, width);
		inv->setPort(ID::A, sig);
		inv->setPort(ID::Y, out);
		return out;
	}

	std::pair<SigSpec, SigSpec> emit_fa(SigSpec a, SigSpec b, SigSpec c, int width)
	{
		SigSpec sum  = module->addWire(NEW_ID, width);
		SigSpec cout = module->addWire(NEW_ID, width);

		Cell* fa = module->addCell(NEW_ID, ID($fa));
		fa->setParam(ID::WIDTH, width);
		fa->setPort(ID::A, a);
		fa->setPort(ID::B, b);
		fa->setPort(ID::C, c);
		fa->setPort(ID::X, cout);
		fa->setPort(ID::Y, sum);

		SigSpec carry;
		carry.append(State::S0);
		carry.append(cout.extract(0, width - 1));
		return {sum, carry};
	}

	void emit_final_add(SigSpec a, SigSpec b, SigSpec y, int width)
	{
		Cell* add = module->addCell(NEW_ID, ID($add));
		add->setParam(ID::A_SIGNED, false);
		add->setParam(ID::B_SIGNED, false);
		add->setParam(ID::A_WIDTH, width);
		add->setParam(ID::B_WIDTH, width);
		add->setParam(ID::Y_WIDTH, width);
		add->setPort(ID::A, a);
		add->setPort(ID::B, b);
		add->setPort(ID::Y, y);
	}

	struct DepthSig {
		SigSpec sig;
		int depth;
	};

	std::pair<SigSpec, SigSpec> reduce_wallace(std::vector<SigSpec>& sigs, int width, int& fa_count)
	{
		std::vector<DepthSig> ops;
		ops.reserve(sigs.size());
		for (auto& s : sigs)
			ops.push_back({s, 0});

		fa_count = 0;

		for (int level = 0; ops.size() > 2; level++) {
			log_assert(level <= 100);

			std::vector<DepthSig> ready, waiting;
			for (auto& op : ops) {
				if (op.depth <= level)
					ready.push_back(op);
				else
					waiting.push_back(op);
			}

			if (ready.size() < 3) continue;

			std::vector<DepthSig> next;
			size_t i = 0;
			while (i + 2 < ready.size()) {
				auto [sum, carry] = emit_fa(ready[i].sig, ready[i + 1].sig, ready[i + 2].sig, width);
				int d = std::max({ready[i].depth, ready[i + 1].depth,ready[i + 2].depth}) + 1;
				next.push_back({sum, d});
				next.push_back({carry, d});
				fa_count++;
				i += 3;
			}
			for (; i < ready.size(); i++)
				next.push_back(ready[i]);
			for (auto& op : waiting)
				next.push_back(op);

			ops = std::move(next);
		}

		log_assert(ops.size() == 2);
		log("    Tree depth: %d FA levels + 1 final add\n",
			std::max(ops[0].depth, ops[1].depth));
		return {ops[0].sig, ops[1].sig};
	}

	void replace_with_csa_tree(
		std::vector<Operand>& operands,
		SigSpec result_y,
		int correction,
		const char* desc
	) {
		int width = GetSize(result_y);
		std::vector<SigSpec> extended;
		extended.reserve(operands.size() + 1);

		for (auto& op : operands) {
			SigSpec s = extend_operand(op.sig, op.is_signed, width);
			if (op.negate)
				s = emit_not(s, width);
			extended.push_back(s);
		}

		if (correction > 0)
			extended.push_back(SigSpec(correction, width));

		int fa_count;
		auto [a, b] = reduce_wallace(extended, width, fa_count);

		log("  %s → %d $fa + 1 $add (%d operands, module %s)\n",
			desc, fa_count, (int)operands.size(), log_id(module));

		emit_final_add(a, b, result_y, width);
	}

	void process_chains()
	{
		pool<Cell*> candidates;
		for (auto cell : addsub_cells)
			candidates.insert(cell);
		for (auto cell : alu_cells)
			if (alu_is_chainable(cell))
				candidates.insert(cell);

		if (candidates.empty())
			return;

		auto parent_of = find_parents(candidates);

		dict<Cell*, pool<Cell*>> children_of;
		pool<Cell*> has_parent;
		for (auto& [child, parent] : parent_of) {
			children_of[parent].insert(child);
			has_parent.insert(child);
		}

		pool<Cell*> processed;
		for (auto root : candidates) {
			if (has_parent.count(root) || processed.count(root))
				continue;

			pool<Cell*> chain = collect_chain(root, children_of);
			if (chain.size() < 2)
				continue;

			for (auto c : chain)
				processed.insert(c);

			int correction;
			auto operands = extract_chain_operands(
				chain, root, parent_of, correction);
			if (operands.size() < 3)
				continue;

			replace_with_csa_tree(operands, root->getPort(ID::Y),
				correction, "Replaced add/sub chain");
			for (auto cell : chain)
				module->remove(cell);
		}
	}

	void process_maccs()
	{
		for (auto cell : macc_cells) {
			std::vector<Operand> operands;
			int correction;
			if (!extract_macc_operands(cell, operands, correction))
				continue;
			if (operands.size() < 3)
				continue;

			replace_with_csa_tree(operands, cell->getPort(ID::Y),
				correction, "Replaced $macc");
			module->remove(cell);
		}
	}

	void run()
	{
		classify_cells();

		if (addsub_cells.empty() && alu_cells.empty() && macc_cells.empty())
			return;

		build_fanout_map();
		process_chains();
		process_maccs();
	}
};

struct CsaTreePass : public Pass {
	CsaTreePass() : Pass("csa_tree",
		"convert add/sub/macc chains to carry-save adder trees") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    csa_tree [selection]\n");
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

	void execute(std::vector<std::string> args, RTLIL::Design* design) override
	{
		log_header(design, "Executing CSA_TREE pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
			break;
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			CsaTreeWorker worker(module);
			worker.run();
		}
	}
} CsaTreePass;

PRIVATE_NAMESPACE_END
