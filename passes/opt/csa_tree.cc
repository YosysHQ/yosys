#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct CsaTreeWorker
{
	RTLIL::Module *module;
	SigMap sigmap;
	int min_operands;

	dict<RTLIL::SigBit, RTLIL::Cell*> sig_to_driver;
	dict<RTLIL::Cell*, int> cell_fanout;
	pool<RTLIL::Cell*> consumed;

	int stat_trees = 0;
	int stat_fa_cells = 0;
	int stat_removed_cells = 0;

	CsaTreeWorker(RTLIL::Module *module, int min_operands) :
		module(module), sigmap(module), min_operands(min_operands) {}

	void build_maps()
	{
		dict<RTLIL::SigBit, int> sig_consumers;

		for (auto cell : module->cells())
		{
			if (cell->type.in(ID($add), ID($sub)))
			{
				RTLIL::SigSpec y = sigmap(cell->getPort(ID::Y));
				for (auto bit : y)
					if (bit.wire != nullptr)
						sig_to_driver[bit] = cell;
			}

			for (auto &conn : cell->connections())
			{
				if (cell->input(conn.first))
				{
					for (auto bit : sigmap(conn.second))
						if (bit.wire != nullptr)
							sig_consumers[bit]++;
				}
			}
		}

		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					if (bit.wire != nullptr)
						sig_consumers[bit]++;

		for (auto cell : module->cells())
		{
			if (!cell->type.in(ID($add), ID($sub)))
				continue;
			int fo = 0;
			for (auto bit : sigmap(cell->getPort(ID::Y)))
				if (bit.wire != nullptr)
					fo = std::max(fo, sig_consumers.count(bit) ? sig_consumers.at(bit) : 0);
			cell_fanout[cell] = fo;
		}
	}

	struct Operand {
		RTLIL::SigSpec sig;
		bool is_signed;
		bool do_subtract;
	};

	bool can_absorb(RTLIL::Cell *cell)
	{
		if (cell == nullptr)
			return false;
		if (!cell->type.in(ID($add), ID($sub)))
			return false;
		if (consumed.count(cell))
			return false;
		if (cell_fanout.count(cell) ? cell_fanout.at(cell) != 1 : true)
			return false;
		return true;
	}

	RTLIL::Cell *get_driver(RTLIL::SigSpec sig)
	{
		sig = sigmap(sig);
		if (sig.empty())
			return nullptr;

		RTLIL::Cell *driver = nullptr;
		for (auto bit : sig)
		{
			if (bit.wire == nullptr)
				continue;
			auto it = sig_to_driver.find(bit);
			if (it == sig_to_driver.end())
				return nullptr;
			if (driver == nullptr)
				driver = it->second;
			else if (driver != it->second)
				return nullptr; // mixed
		}
		return driver;
	}

	void collect_operands(
		RTLIL::Cell *cell,
		bool negate,
		std::vector<Operand> &operands,
		std::vector<RTLIL::Cell*> &tree_cells
	) {
		tree_cells.push_back(cell);
		consumed.insert(cell);

		bool a_signed = cell->getParam(ID::A_SIGNED).as_bool();
		bool b_signed = cell->getParam(ID::B_SIGNED).as_bool();
		bool is_sub = (cell->type == ID($sub));

		RTLIL::SigSpec sig_a = cell->getPort(ID::A);
		RTLIL::SigSpec sig_b = cell->getPort(ID::B);

		RTLIL::Cell *driver_a = get_driver(sig_a);
		if (can_absorb(driver_a)) {
			collect_operands(driver_a, negate, operands, tree_cells);
		} else {
			operands.push_back({sig_a, a_signed, negate});
		}

		bool b_negate = negate ^ is_sub;
		RTLIL::Cell *driver_b = get_driver(sig_b);
		if (can_absorb(driver_b)) {
			collect_operands(driver_b, b_negate, operands, tree_cells);
		} else {
			operands.push_back({sig_b, b_signed, b_negate});
		}
	}

	void create_fa(
		RTLIL::SigSpec a,
		RTLIL::SigSpec b,
		RTLIL::SigSpec c,
		int width,
		RTLIL::SigSpec &sum_out,
		RTLIL::SigSpec &carry_out
	) {
		RTLIL::Wire *w_sum = module->addWire(NEW_ID, width);
		RTLIL::Wire *w_carry = module->addWire(NEW_ID, width);

		RTLIL::Cell *fa = module->addCell(NEW_ID, ID($fa));
		fa->setParam(ID::WIDTH, width);
		fa->setPort(ID::A, a);
		fa->setPort(ID::B, b);
		fa->setPort(ID::C, c);
		fa->setPort(ID::Y, w_sum);
		fa->setPort(ID::X, w_carry);

		sum_out = w_sum;
		carry_out = w_carry;
		stat_fa_cells++;
	}

	RTLIL::SigSpec extend_to(RTLIL::SigSpec sig, bool is_signed, int target_width)
	{
		if (GetSize(sig) >= target_width)
			return sig.extract(0, target_width);

		RTLIL::SigSpec result = sig;
		RTLIL::SigBit pad = is_signed ? sig[GetSize(sig) - 1] : RTLIL::S0;
		while (GetSize(result) < target_width)
			result.append(pad);
		return result;
	}

	RTLIL::SigSpec build_csa_tree(std::vector<Operand> &operands, int output_width)
	{
		int width = output_width;
		std::vector<RTLIL::SigSpec> summands;
		int sub_count = 0;

		for (auto &op : operands)
		{
			RTLIL::SigSpec sig = extend_to(op.sig, op.is_signed, width);

			if (op.do_subtract) {
				sig = module->Not(NEW_ID, sig);
				sub_count++;
			}

			summands.push_back(sig);
		}

		if (sub_count > 0) {
			RTLIL::Const correction(sub_count, width);
			summands.push_back(RTLIL::SigSpec(correction));
		}

		if (summands.empty())
			return RTLIL::SigSpec(0, width);

		if (summands.size() == 1)
			return summands[0];

		if (summands.size() == 2) {
			RTLIL::Wire *result = module->addWire(NEW_ID, width);
			module->addAdd(NEW_ID, summands[0], summands[1], result);
			return result;
		}

		while (summands.size() > 2)
		{
			std::vector<RTLIL::SigSpec> next;
			int i = 0;

			while (i + 2 < (int)summands.size())
			{
				RTLIL::SigSpec a = summands[i];
				RTLIL::SigSpec b = summands[i + 1];
				RTLIL::SigSpec c = summands[i + 2];

				RTLIL::SigSpec sum, carry;
				create_fa(a, b, c, width, sum, carry);

				RTLIL::SigSpec carry_shifted;
				carry_shifted.append(RTLIL::S0);
				carry_shifted.append(carry.extract(0, width - 1));

				next.push_back(sum);
				next.push_back(carry_shifted);
				i += 3;
			}

			while (i < (int)summands.size())
				next.push_back(summands[i++]);

			summands.swap(next);
		}

		RTLIL::Wire *result = module->addWire(NEW_ID, width);
		module->addAdd(NEW_ID, summands[0], summands[1], result);
		return result;
	}

	void run()
	{
		build_maps();

		std::vector<RTLIL::Cell*> roots;
		for (auto cell : module->selected_cells())
			if (cell->type.in(ID($add), ID($sub)))
				roots.push_back(cell);

		std::sort(roots.begin(), roots.end(),
			[](RTLIL::Cell *a, RTLIL::Cell *b) {
				return a->name < b->name;
			});

		std::sort(roots.begin(), roots.end(),
			[&](RTLIL::Cell *a, RTLIL::Cell *b) {
				return (cell_fanout.count(a) ? cell_fanout.at(a) : 0) >
			       (cell_fanout.count(b) ? cell_fanout.at(b) : 0);
			});

		for (auto root : roots)
		{
			if (consumed.count(root))
				continue;

			std::vector<Operand> operands;
			std::vector<RTLIL::Cell*> tree_cells;

			collect_operands(root, false, operands, tree_cells);

			if ((int)operands.size() < min_operands) {
				for (auto c : tree_cells)
					consumed.erase(c);
				continue;
			}

			int output_width = root->getParam(ID::Y_WIDTH).as_int();

			log("  Found adder tree rooted at %s with %d operands (depth %d cells)\n",
				log_id(root), (int)operands.size(), (int)tree_cells.size());

			RTLIL::SigSpec new_output = build_csa_tree(operands, output_width);
			RTLIL::SigSpec old_output = root->getPort(ID::Y);
			module->connect(old_output, new_output);

			for (auto c : tree_cells) {
				module->remove(c);
				stat_removed_cells++;
			}

			stat_trees++;
		}
	}
};

struct CsaTreePass : public Pass
{
	CsaTreePass() : Pass("csa_tree",
		"convert adder chains to carry-save adder trees") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    csa_tree [options] [selection]\n");
		log("\n");
		log("This pass converts chains of $add/$sub cells into carry-save adder trees using\n");
		log("$fa (full adder / 3:2 compressor) cells to reduce the critical path depth of\n");
		log("multi-operand addition.\n");
		log("\n");
		log("For N operands of width W, the critical path is reduced from\n");
		log("O(N * log W) to O(log_1.5(N) + log W).\n");
		log("\n");
		log("    -min_operands N\n");
		log("        Minimum number of operands to trigger CSA tree construction.\n");
		log("        Default: 3. Values below 3 are clamped to 3.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int min_operands = 3;

		log_header(design, "Executing CSA_TREE pass (carry-save adder tree optimization).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-min_operands" && argidx + 1 < args.size()) {
				min_operands = std::max(3, atoi(args[++argidx].c_str()));
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			log("Processing module %s...\n", log_id(module));

			CsaTreeWorker worker(module, min_operands);
			worker.run();

			if (worker.stat_trees > 0)
				log("  Converted %d adder tree(s): created %d $fa cells, "
					"removed %d $add/$sub cells.\n",
					worker.stat_trees, worker.stat_fa_cells,
					worker.stat_removed_cells);
		}
	}
} CsaTreePass;

PRIVATE_NAMESPACE_END
