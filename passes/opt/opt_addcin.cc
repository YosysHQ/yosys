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

static void merge_add_attributes(Cell *dst, const Cell *outer, const Cell *inner)
{
	dst->attributes = outer->attributes;

	for (const auto &attr : inner->attributes)
		if (attr.first != ID::src && !dst->attributes.count(attr.first))
			dst->attributes[attr.first] = attr.second;

	std::string outer_src = outer->get_src_attribute();
	std::string inner_src = inner->get_src_attribute();
	if (outer_src.empty()) {
		if (!inner_src.empty())
			dst->set_src_attribute(inner_src);
	} else if (!inner_src.empty() && inner_src != outer_src) {
		dst->set_src_attribute(outer_src + "|" + inner_src);
	}
}

struct OptAddcinWorker
{
	struct Leaf {
		SigSpec sig;
		bool is_signed;
	};

	struct Rewrite {
		Cell *outer;
		Cell *inner;
		Leaf a;
		Leaf b;
		SigSpec cin;
		SigSpec y;
		int width;
	};

	Module *module;
	SigMap sigmap;
	dict<SigSpec, Cell*> add_driver;
	pool<SigBit> tracked_output_bits;
	dict<SigBit, int> input_users;
	pool<Cell*> claimed;
	vector<Rewrite> rewrites;

	OptAddcinWorker(Module *module) : module(module), sigmap(module)
	{
	}

	void build_indexes()
	{
		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($add))
				continue;
			SigSpec y = sigmap(cell->getPort(ID::Y));
			add_driver[y] = cell;
			for (auto bit : y)
				tracked_output_bits.insert(bit);
		}

		for (auto wire : module->wires()) {
			if (!wire->port_output)
				continue;
			for (auto bit : sigmap(wire))
				if (tracked_output_bits.count(bit))
					input_users[bit]++;
		}

		for (auto cell : module->cells()) {
			for (auto &conn : cell->connections()) {
				if (!cell->input(conn.first))
					continue;
				for (auto bit : sigmap(conn.second))
					if (tracked_output_bits.count(bit))
						input_users[bit]++;
			}
		}
	}

	Cell *driver_of(const SigSpec &sig)
	{
		auto it = add_driver.find(sig);
		return it == add_driver.end() ? nullptr : it->second;
	}

	bool has_single_use(const SigSpec &sig)
	{
		for (auto bit : sig) {
			auto it = input_users.find(bit);
			if (it == input_users.end() || it->second != 1)
				return false;
		}
		return true;
	}

	bool collect(Cell *outer)
	{
		if (claimed.count(outer) || outer->type != ID($add))
			return false;

		SigSpec outer_a = sigmap(outer->getPort(ID::A));
		SigSpec outer_b = sigmap(outer->getPort(ID::B));
		SigSpec outer_y = sigmap(outer->getPort(ID::Y));
		Cell *inner_a = driver_of(outer_a);
		Cell *inner_b = driver_of(outer_b);

		if ((inner_a != nullptr) == (inner_b != nullptr))
			return false;

		Cell *inner = inner_a ? inner_a : inner_b;
		if (inner == outer || claimed.count(inner) || inner->type != ID($add))
			return false;

		SigSpec inner_y = sigmap(inner->getPort(ID::Y));
		SigSpec inner_operand = inner_a ? outer_a : outer_b;
		if (inner_y != inner_operand)
			return false;

		int width = GetSize(outer_y);
		if (width == 0 || GetSize(inner_y) != width)
			return false;
		if (inner->getParam(ID::Y_WIDTH).as_int() != width)
			return false;
		if (outer->getParam(ID::Y_WIDTH).as_int() != width)
			return false;
		if (!has_single_use(inner_y))
			return false;

		vector<Leaf> leaves;
		leaves.push_back({sigmap(inner->getPort(ID::A)), inner->getParam(ID::A_SIGNED).as_bool()});
		leaves.push_back({sigmap(inner->getPort(ID::B)), inner->getParam(ID::B_SIGNED).as_bool()});
		if (inner_a)
			leaves.push_back({outer_b, outer->getParam(ID::B_SIGNED).as_bool()});
		else
			leaves.push_back({outer_a, outer->getParam(ID::A_SIGNED).as_bool()});

		int cin_index = -1;
		for (int i = 0; i < GetSize(leaves); i++) {
			if (GetSize(leaves[i].sig) > width)
				return false;
			if (GetSize(leaves[i].sig) == 1 && !leaves[i].is_signed) {
				if (cin_index != -1)
					return false;
				cin_index = i;
			}
		}
		if (cin_index == -1)
			return false;

		vector<Leaf> operands;
		for (int i = 0; i < GetSize(leaves); i++) {
			if (i == cin_index)
				continue;
			operands.push_back(leaves[i]);
		}
		log_assert(GetSize(operands) == 2);

		claimed.insert(outer);
		claimed.insert(inner);
		rewrites.push_back({outer, inner, operands[0], operands[1], leaves[cin_index].sig, outer_y, width});
		return true;
	}

	SigSpec extend_leaf(const Leaf &leaf, int width)
	{
		SigSpec sig = leaf.sig;
		sig.extend_u0(width, leaf.is_signed);
		return sig;
	}

	void apply(const Rewrite &rewrite)
	{
		Cell *cell = rewrite.outer;

		SigSpec a = extend_leaf(rewrite.a, rewrite.width);
		SigSpec b = extend_leaf(rewrite.b, rewrite.width);

		SigSpec wide_a(State::S1);
		wide_a.append(a);

		SigSpec wide_b = rewrite.cin;
		wide_b.append(b);

		Wire *wide_y_wire = module->addWire(NEW_ID2_SUFFIX("addcin_y"), rewrite.width + 1);
		SigSpec wide_y(wide_y_wire);
		Cell *wide_add = module->addCell(NEW_ID2_SUFFIX("addcin"), ID($add));
		merge_add_attributes(wide_add, rewrite.outer, rewrite.inner);
		wide_add->setPort(ID::A, wide_a);
		wide_add->setPort(ID::B, wide_b);
		wide_add->setPort(ID::Y, wide_y);
		wide_add->setParam(ID::A_SIGNED, false);
		wide_add->setParam(ID::B_SIGNED, false);
		wide_add->fixup_parameters();

		module->connect(rewrite.y, wide_y.extract(1, rewrite.width));
		module->remove(rewrite.outer);
		module->remove(rewrite.inner);
	}

	int run()
	{
		build_indexes();

		vector<Cell*> cells;
		for (auto cell : module->selected_cells())
			cells.push_back(cell);
		for (auto cell : cells)
			collect(cell);

		for (auto &rewrite : rewrites)
			apply(rewrite);

		return GetSize(rewrites);
	}
};

struct OptAddcinPass : public Pass {
	OptAddcinPass() : Pass("opt_addcin", "rewrite add-with-carry-in patterns as widened adders") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_addcin [selection]\n");
		log("\n");
		log("This pass rewrites a conservative two-$add, three-leaf carry-in pattern\n");
		log("into a single widened $add:\n");
		log("\n");
		log("    (A + B) + CI    ->    ({A_ext, 1'b1} + {B_ext, CI})[WIDTH:1]\n");
		log("\n");
		log("Only one leaf may be a one-bit unsigned carry input. The other two leaves\n");
		log("are explicitly sign- or zero-extended to the shared add width before the\n");
		log("widened add is emitted. The pass rejects $sub/$alu patterns, mismatched\n");
		log("intermediate/final widths, multi-bit carry operands, signed carry operands,\n");
		log("and intermediate sums with fanout outside the final add.\n");
		log("\n");
		log("This pass is not invoked by the default 'opt' or 'peepopt' scripts. It is\n");
		log("intended for flows that want to map carry-in adds onto adders without an\n");
		log("explicit carry input. Run add-chain timing transforms such as\n");
		log("'opt_balance_tree -arith' or 'opt_parallel_prefix -arith' before this pass,\n");
		log("then run 'alumacc' or technology mapping afterwards.\n");
		log("\n");
		log("Runtime is linear in the number of module connections plus the total width\n");
		log("of rewritten candidates. The implementation builds driver and input-use\n");
		log("indexes once per module and does not scan all cells per candidate.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_ADDCIN pass (carry-in add widening).\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		int total = 0;
		for (auto module : design->selected_modules()) {
			OptAddcinWorker worker(module);
			int count = worker.run();
			total += count;
			if (count)
				log("Rewrote %d add-carry-in pattern%s in module %s.\n",
					count, count == 1 ? "" : "s", log_id(module));
		}

		if (total)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Rewrote %d add-carry-in pattern%s total.\n", total, total == 1 ? "" : "s");
	}
} OptAddcinPass;

PRIVATE_NAMESPACE_END
