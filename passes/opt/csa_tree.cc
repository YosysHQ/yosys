#include "kernel/yosys.h"
#include "kernel/sigtools.h"

#include <queue>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct CsaTreeWorker
{
	Module *module;
	SigMap sigmap;

	dict<SigBit, pool<Cell*>> bit_consumers;
	dict<SigBit, int> fanout;
	pool<Cell*> all_adds;

	CsaTreeWorker(Module *module) : module(module), sigmap(module) {}

	struct DepthSig {
		SigSpec sig;
		int depth;
	};

	void find_adds()
	{
		for (auto cell : module->cells())
			if (cell->type == ID($add))
				all_adds.insert(cell);
	}

	void build_fanout_map()
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

	Cell*single_add_consumer(SigSpec sig)
	{
		Cell*consumer = nullptr;

		for (auto bit : sig) {
			if (!fanout.count(bit) || fanout[bit] != 1)
				return nullptr;
			if (!bit_consumers.count(bit) || bit_consumers[bit].size() != 1)
				return nullptr;

			Cell* c = *bit_consumers[bit].begin();
			if (!all_adds.count(c))
				return nullptr;

			if (consumer == nullptr)
				consumer = c;
			else if (consumer != c)
				return nullptr;
		}

		return consumer;
	}

	dict<Cell*, Cell*> find_add_parents()
	{
		dict<Cell*, Cell*> parent_of;

		for (auto cell : all_adds) {
			SigSpec y = sigmap(cell->getPort(ID::Y));
			Cell* consumer = single_add_consumer(y);
			if (consumer != nullptr && consumer != cell)
				parent_of[cell] = consumer;
		}

		return parent_of;
	}

	pool<Cell*> collect_chain(Cell* root, const dict<Cell*, pool<Cell*>> &children_of)
	{
		pool<Cell*> chain;
		std::queue<Cell*> worklist;
		worklist.push(root);

		while (!worklist.empty()) {
			Cell* cur = worklist.front();
			worklist.pop();

			if (chain.count(cur))
				continue;
			chain.insert(cur);

			if (children_of.count(cur))
				for (auto child : children_of.at(cur))
					worklist.push(child);
		}

		return chain;
	}

	bool is_chain_internal(SigSpec sig, const pool<SigBit> &chain_y_bits)
	{
		for (auto bit : sig)
			if (chain_y_bits.count(bit))
				return true;
		return false;
	}

	pool<SigBit> collect_chain_outputs(const pool<Cell*> &chain)
	{
		pool<SigBit> bits;
		for (auto cell : chain)
			for (auto bit : sigmap(cell->getPort(ID::Y)))
				bits.insert(bit);
		return bits;
	}

	struct Operand {
		SigSpec sig;
		bool is_signed;
	};

	std::vector<Operand> collect_leaf_operands(const pool<Cell*> &chain, const pool<SigBit> &chain_y_bits)
	{
		std::vector<Operand> operands;

		for (auto cell : chain) {
			SigSpec a = sigmap(cell->getPort(ID::A));
			SigSpec b = sigmap(cell->getPort(ID::B));
			bool a_signed = cell->getParam(ID::A_SIGNED).as_bool();
			bool b_signed = cell->getParam(ID::B_SIGNED).as_bool();

			if (!is_chain_internal(a, chain_y_bits))
				operands.push_back({a, a_signed});
			if (!is_chain_internal(b, chain_y_bits))
				operands.push_back({b, b_signed});
		}

		return operands;
	}

	SigSpec extend_to(SigSpec sig, bool is_signed, int width)
	{
		if (GetSize(sig) < width) {
			SigBit pad = (is_signed && GetSize(sig) > 0) ? sig[GetSize(sig) - 1] : State::S0;
			sig.append(SigSpec(pad, width - GetSize(sig)));
		}
		if (GetSize(sig) > width)
			sig = sig.extract(0, width);
		return sig;
	}

	std::pair<SigSpec, SigSpec> emit_fa(SigSpec a, SigSpec b, SigSpec c, int width)
	{
		SigSpec sum = module->addWire(NEW_ID, width);
		SigSpec cout = module->addWire(NEW_ID, width);

		Cell* fa = module->addCell(NEW_ID, ID($fa));
		fa->setParam(ID::WIDTH, width);
		fa->setPort(ID::A, a);
		fa->setPort(ID::B, b);
		fa->setPort(ID::C, c);
		fa->setPort(ID::X, cout);
		fa->setPort(ID::Y, sum);

		SigSpec carry_shifted;
		carry_shifted.append(State::S0);
		carry_shifted.append(cout.extract(0, width - 1));

		return {sum, carry_shifted};
	}

	std::pair<SigSpec, SigSpec> build_wallace_tree(std::vector<SigSpec> &operands, int width, int &fa_count)
	{
		std::vector<DepthSig> ops;
		for (auto &s : operands)
			ops.push_back({s, 0});

		fa_count = 0;
		int level = 0;

		while (ops.size() > 2)
		{
			std::vector<DepthSig> ready, waiting;
			for (auto &op : ops) {
				if (op.depth <= level)
					ready.push_back(op);
				else
					waiting.push_back(op);
			}

			if (ready.size() < 3) {
				level++;
				log_assert(level <= 100);
				continue;
			}

			std::vector<DepthSig> next;
			size_t i = 0;
			while (i + 2 < ready.size()) {
				auto [sum, carry] = emit_fa(ready[i].sig, ready[i+1].sig, ready[i+2].sig, width);
				int d = std::max({ready[i].depth, ready[i+1].depth, ready[i+2].depth}) + 1;
				next.push_back({sum, d});
				next.push_back({carry, d});
				fa_count++;
				i += 3;
			}

			for (; i < ready.size(); i++)
				next.push_back(ready[i]);

			for (auto &op : waiting)
				next.push_back(op);

			ops = std::move(next);
			level++;
			log_assert(level <= 100);
		}

		log_assert(ops.size() == 2);

		int max_depth = std::max(ops[0].depth, ops[1].depth);
		log("    Tree depth: %d FA levels + 1 final add\n", max_depth);

		return {ops[0].sig, ops[1].sig};
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

	void run()
	{
		find_adds();
		if (all_adds.empty())
			return;

		build_fanout_map();

		auto parent_of = find_add_parents();

		pool<Cell*> has_parent;
		dict<Cell*, pool<Cell*>> children_of;
		for (auto &pair : parent_of) {
			has_parent.insert(pair.first);
			children_of[pair.second].insert(pair.first);
		}

		pool<Cell*> processed;

		for (auto root : all_adds)
		{
			if (has_parent.count(root))
				continue;
			if (processed.count(root))
				continue;

			pool<Cell*> chain = collect_chain(root, children_of);
			if (chain.size() < 2)
				continue;

			for (auto c : chain)
				processed.insert(c);

			pool<SigBit> chain_y_bits = collect_chain_outputs(chain);
			auto operands = collect_leaf_operands(chain, chain_y_bits);

			if (operands.size() < 3)
				continue;

			SigSpec root_y = root->getPort(ID::Y);
			int width = GetSize(root_y);

			std::vector<SigSpec> extended;
			for (auto &op : operands)
				extended.push_back(extend_to(op.sig, op.is_signed, width));

			int fa_count;
			auto [final_a, final_b] = build_wallace_tree(extended, width, fa_count);

			log("  Replaced chain of %d $add cells with %d $fa + 1 $add (%d operands, module %s)\n",
					(int)chain.size(), fa_count, (int)operands.size(), log_id(module));

			emit_final_add(final_a, final_b, root_y, width);

			for (auto cell : chain)
				module->remove(cell);
		}
	}
};

struct CsaTreePass : public Pass {
	CsaTreePass() : Pass("csa_tree", "convert $add chains to carry-save adder trees") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    csa_tree [selection]\n");
		log("\n");
		log("This pass finds chains of $add cells and replaces them with\n");
		log("carry-save adder (CSA) trees built from $fa cells, followed by\n");
		log("a single final $add for the carry-propagate step.\n");
		log("\n");
		log("The tree uses Wallace-tree scheduling for optimal depth:\n");
		log("at each level, all ready operands are grouped into triplets\n");
		log("and compressed via full adders.  This gives ceil(log_1.5(N))\n");
		log("FA levels for N input operands.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
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
