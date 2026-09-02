/**
 * Distribute a truncated increment out of a multiplier operand.
 *
 * Authored by Akash Levy of Silimate, Inc. under ISC license.
 *
 *   y = (x + 1)[hi:lo] * z,   s = y + <rest of the add chain>
 *     ===>   c = &x[lo-1:0]        // all the increment can carry past lo
 *            w = &x[hi:0]          // the window wraps to zero
 *            y = w ? 0 : x[hi:lo] * z
 *            s = <rest of the add chain> + ((c & ~w) ? z : 0)
 *
 * (x + 1)[hi:lo] is (x[hi:lo] + c) mod 2^(hi-lo+1): all the increment can carry
 * past the dropped low bits is the AND of them, and the modulo only bites when
 * x[hi:0] is all ones. So the increment distributes into the product, leaving one
 * gated row and a mask.
 *
 * That trade is the point. An incrementer in front of a multiplier is a prefix
 * adder on the operand's critical path; here the multiply reads x directly and
 * both corrections sit off that path -- the mask behind the product, where it runs
 * alongside the multiply rather than ahead of it, and the row as one more operand
 * of a sum that is waiting on the product anyway.
 *
 * The row is only free if something carry-saves it, so the pass fires only where
 * the product already feeds an add chain wide and long enough for arith_tree to
 * fold it in. It goes to the top of that chain rather than onto the product: there
 * it would be an adder arith_tree cannot flatten, needing a bit the product's own
 * width does not have, and would leave a carry-propagate adder in series behind
 * the multiply -- costing more than the incrementer it removed.
 */

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#include "passes/opt/rewrite_utils.h"

struct OptMulDistWorker {
	Module *module;
	SigMap sigmap;
	dict<SigBit, Cell *> driver;
	dict<SigBit, pool<Cell *>> consumers;
	pool<SigBit> escapes;
	int max_reduce;
	int min_chain;
	int min_chain_width;
	// Several multiplies commonly read the same slice of the same increment, and
	// the wrap test and its gated carry depend only on that slice
	dict<std::string, std::pair<SigBit, SigBit>> shared;

	struct Target {
		Cell *mul;
		Cell *inc;   // the $add being distributed away
		Cell *root;  // top of the add chain, where the leftover row goes
		IdString port; // the multiplier operand it drives
		SigSpec x;   // the incremented value
		int lo, hi;  // the slice of (x + 1) the operand takes
	};

	OptMulDistWorker(Module *module, int max_reduce, int min_chain, int min_chain_width)
	    : module(module), sigmap(module), max_reduce(max_reduce), min_chain(min_chain),
	      min_chain_width(min_chain_width)
	{
		index();
	}

	void index()
	{
		sigmap.clear();
		sigmap.set(module);
		index_module_bits(module, sigmap, driver, consumers, escapes);
	}

	// The incremented operand of an unsigned `x + 1`, or an empty SigSpec
	SigSpec increment_input(Cell *cell)
	{
		if (cell->type != ID($add))
			return SigSpec();
		if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
			return SigSpec();

		for (auto port : {ID::A, ID::B}) {
			SigSpec k = sigmap(cell->getPort(port));
			if (k.is_fully_const() && k.as_const().as_int() == 1)
				return sigmap(cell->getPort(port == ID::A ? ID::B : ID::A));
		}
		return SigSpec();
	}

	// Where `sig` sits in `whole`, if it is one contiguous ascending run of it
	int slice_offset(const SigSpec &sig, const SigSpec &whole)
	{
		if (GetSize(sig) == 0 || GetSize(sig) > GetSize(whole))
			return -1;
		for (int off = 0; off + GetSize(sig) <= GetSize(whole); off++)
			if (whole.extract(off, GetSize(sig)) == sig)
				return off;
		return -1;
	}

	// Bits an unsigned operand can actually set. Constant zeros above the value
	// cannot carry, so a port wreduce has not narrowed is no less exact than one
	// it has.
	int value_width(const SigSpec &sig)
	{
		SigSpec s = sigmap(sig);
		int w = GetSize(s);
		while (w > 0 && s[w - 1] == State::S0)
			w--;
		return w;
	}

	// An add that cannot truncate, since a + b never needs more than one bit past
	// the wider operand. The leftover row is moved from the product up to the chain
	// root, which is only exact if nothing between them drops a carry -- the same
	// width question arith_tree answers before flattening a link.
	bool exact_link(Cell *cell)
	{
		int wa = value_width(cell->getPort(ID::A)), wb = value_width(cell->getPort(ID::B));
		int need = (wa && wb) ? std::max(wa, wb) + 1 : std::max(wa, wb);
		return GetSize(cell->getPort(ID::Y)) >= need;
	}

	// The sole consumer of `sig`, if the row can pass through it unchanged: an
	// unsigned add taking all of `sig` zero-extended from bit 0. Anything above it
	// in the port scales the product, and a subtraction taking it negates it, so
	// either way the row moved up would no longer be the term that left.
	Cell *link_above(const SigSpec &sig)
	{
		SigSpec s = sigmap(sig);
		auto it = consumers.find(s[0]);
		if (it == consumers.end() || GetSize(it->second) != 1)
			return nullptr;
		Cell *cell = *it->second.begin();
		if (cell->type != ID($add))
			return nullptr;
		if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
			return nullptr;

		for (auto port : {ID::A, ID::B}) {
			SigSpec p = sigmap(cell->getPort(port));
			if (GetSize(p) >= GetSize(s) && p.extract(0, GetSize(s)) == s)
				return cell;
		}
		return nullptr;
	}

	// Everything from the product up to the chain root sums to something different
	// once the row moves past it, so those cells and nets have to give up their
	// names: an equivalence checker pairs both across the rewrite by name, and a
	// stale name on a changed value reads as a mismatch rather than as a move.
	bool stale_names(Cell *mul, Cell *root, std::vector<Wire *> &wires, std::vector<Cell *> &cells)
	{
		SigSpec sig = mul->getPort(ID::Y);
		for (Cell *cur = mul;;) {
			// wreduce leaves ports narrower than the wires behind them, so take
			// the wires the sum lands on rather than expecting a whole one
			for (auto &chunk : sig.chunks()) {
				if (!chunk.wire)
					continue;
				if (chunk.wire->port_id || chunk.wire->get_bool_attribute(ID::keep))
					return false;
				wires.push_back(chunk.wire);
			}

			cur = link_above(sig);
			if (!cur)
				return false;
			// The root keeps its output net, which still carries the whole sum, but
			// its own result is now the sum without the row
			cells.push_back(cur);
			if (cur == root)
				return true;
			sig = cur->getPort(ID::Y);
		}
	}

	// Root of the add chain fed by `prod`, if the row can be moved there and
	// arith_tree will rebuild the chain once it arrives. One more row is only a
	// compressor level if the chain clears the thresholds arith_tree is run with.
	Cell *feeds_tree(const SigSpec &prod)
	{
		Cell *root = link_above(prod);
		if (!root)
			return nullptr;

		// Every add the row passes on its way up has to be exact. The root itself
		// may truncate: the row lands directly on its output, so both designs
		// reduce modulo the same width there.
		while (Cell *next = link_above(root->getPort(ID::Y))) {
			if (!exact_link(root))
				return nullptr;
			root = next;
		}

		if (GetSize(root->getPort(ID::Y)) < min_chain_width)
			return nullptr;

		// Count the chain's leaves: an add whose operand is another add is a link,
		// anything else is an addend arith_tree will compress
		int addends = 0;
		std::vector<Cell *> todo = {root};
		pool<Cell *> seen = {root};
		while (!todo.empty()) {
			Cell *cur = todo.back();
			todo.pop_back();
			for (auto port : {ID::A, ID::B}) {
				SigSpec sig = sigmap(cur->getPort(port));
				if (GetSize(sig) == 0 || sig.is_fully_const())
					continue;
				auto d = driver.find(sig[0]);
				if (d != driver.end() && d->second->type.in(ID($add), ID($sub)) && !seen.count(d->second)) {
					seen.insert(d->second);
					todo.push_back(d->second);
					continue;
				}
				addends++;
			}
		}

		return addends >= min_chain ? root : nullptr;
	}

	void distribute(const Target &t)
	{
		Cell *cell = t.mul;
		IdString other_port = (t.port == ID::A) ? ID::B : ID::A;
		SigSpec z = cell->getPort(other_port);
		SigSpec y = cell->getPort(ID::Y);
		int n = t.hi - t.lo + 1;
		std::string src = cell->get_src_attribute();

		log("opt_muldist: distributing %s out of %s, operand (%s + 1)[%d:%d]\n", log_id(t.inc), log_id(cell),
		    log_signal(t.x), t.hi, t.lo);

		// The increment can only reach the window through the bits it drops, and it
		// only wraps the window when everything below the top of it is set. Both
		// tests are shared with any other multiply reading the same slice.
		std::string key = stringf("%s|%d|%d", log_signal(t.x), t.lo, t.hi);
		if (!shared.count(key)) {
			SigBit carry = (t.lo == 0) ? State::S1
						  : module->ReduceAnd(NEW_ID2_SUFFIX("carry"), t.x.extract(0, t.lo), false, src);
			SigBit wrap = module->ReduceAnd(NEW_ID2_SUFFIX("wrap"), t.x.extract(0, t.hi + 1), false, src);
			// z once, when the dropped window carries into the operand and the
			// operand did not wrap away
			SigBit take = module->Mux(NEW_ID2_SUFFIX("take"), carry, State::S0, wrap, src);
			shared[key] = {wrap, take};
		}
		auto [wrap, take] = shared.at(key);

		SigSpec row = module->addWire(NEW_ID2_SUFFIX("row"), GetSize(z));
		module->addAnd(NEW_ID2_SUFFIX("row"), z, SigSpec(take, GetSize(z)), row, false, src);

		// The multiply now takes the slice straight off whatever drives x, with the
		// modulo charged to the product instead of the operand: the wrap test is an
		// AND reduction over x, and behind the multiply it costs nothing at all,
		// while in front of it it is the whole reason to keep the incrementer.
		SigSpec prod = module->addWire(NEW_ID2_SUFFIX("prod"), GetSize(y));
		Cell *new_mul = module->addMul(NEW_ID2_SUFFIX("mul"), t.x.extract(t.lo, n), z, prod, false, src);
		new_mul->set_bool_attribute(ID(opt_muldist));
		module->addMux(NEW_ID2_SUFFIX("mask"), prod, SigSpec(State::S0, GetSize(y)), wrap, y, src);

		// The row goes in at the chain root rather than on the product. Sitting on
		// the product it would be an adder arith_tree cannot flatten, since
		// prod + row needs a bit the product's own width does not have; at the root
		// it is just one more operand of the sum, which is what it mathematically is.
		// Everything it passes on the way up now sums to something different, so
		// those cells and nets are renamed rather than left carrying a stale name.
		std::vector<Wire *> stale_wires;
		std::vector<Cell *> stale_cells;
		stale_names(cell, t.root, stale_wires, stale_cells);
		for (auto wire : stale_wires)
			module->rename(wire, module->uniquify(wire->name.str() + "_predist"));
		for (auto c : stale_cells)
			module->rename(c, module->uniquify(c->name.str() + "_predist"));

		SigSpec root_y = t.root->getPort(ID::Y);
		SigSpec presum = module->addWire(NEW_ID2_SUFFIX("presum"), GetSize(root_y));
		t.root->setPort(ID::Y, presum);
		Cell *row_add = module->addAdd(NEW_ID2_SUFFIX("row_add"), presum, row, root_y, false, src);
		row_add->set_bool_attribute(ID(opt_muldist));

		module->remove(cell);
	}

	// Every reader of the increment has to be a slice we are rewriting, or it
	// survives and the prefix adder we were paying for is still there
	bool inc_only_feeds(Cell *inc, const std::vector<Target> &targets)
	{
		if (inc->get_bool_attribute(ID::keep))
			return false;
		for (auto bit : sigmap(inc->getPort(ID::Y))) {
			if (escapes.count(bit))
				return false;
			for (auto user : consumers[bit]) {
				bool rewritten = false;
				for (auto &t : targets)
					if (t.inc == inc && t.mul == user)
						rewritten = true;
				if (!rewritten)
					return false;
			}
		}
		return true;
	}

	std::vector<Target> collect()
	{
		std::vector<Target> targets;
		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($mul))
				continue;
			if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
				continue;

			Cell *root = feeds_tree(cell->getPort(ID::Y));
			if (!root)
				continue;

			for (auto port : {ID::A, ID::B}) {
				SigSpec sig = sigmap(cell->getPort(port));
				auto d = driver.find(sig[0]);
				if (d == driver.end())
					continue;
				Cell *inc = d->second;
				SigSpec x = increment_input(inc);
				if (GetSize(x) == 0)
					continue;

				int lo = slice_offset(sig, sigmap(inc->getPort(ID::Y)));
				if (lo < 0)
					continue;
				int hi = lo + GetSize(sig) - 1;
				// The wrap test is an AND over everything below the top of the
				// window, so a wide window buys a reduction deeper than the
				// prefix adder it replaces
				if (hi + 1 > max_reduce || hi >= GetSize(x))
					continue;
				// Moving the row up the chain is only exact if the product it came
				// off does not truncate, since a truncated product differs from the
				// real one by a multiple of its width that the wider sum would see
				int other = GetSize(cell->getPort(port == ID::A ? ID::B : ID::A));
				if (GetSize(cell->getPort(ID::Y)) < GetSize(sig) + other)
					continue;
				// The sums the row passes have to be renamable, since their
				// values change and a checker pairs cells and nets by name
				std::vector<Wire *> stale_wires;
				std::vector<Cell *> stale_cells;
				if (!stale_names(cell, root, stale_wires, stale_cells))
					continue;

				targets.push_back({cell, inc, root, port, x, lo, hi});
				break;
			}
		}

		// Drop any target whose increment survives anyway: the prefix adder is then
		// still paid for and the distribution is pure cost
		std::vector<Target> keep;
		for (auto &t : targets)
			if (inc_only_feeds(t.inc, targets) && !stranded_peer(t, targets))
				keep.push_back(t);
		return keep;
	}

	// The row this rewrite leaves behind can cost the chain a compressor level,
	// and every operand pays for it. A sibling multiply sitting behind an
	// increment we cannot distribute is as deep as the one we can, so it becomes
	// critical and the level buys nothing -- do not take the trade at all.
	bool stranded_peer(const Target &t, const std::vector<Target> &targets)
	{
		for (auto cell : module->cells()) {
			if (cell->type != ID($mul) || cell == t.mul)
				continue;
			if (feeds_tree(cell->getPort(ID::Y)) != t.root)
				continue;

			bool behind_increment = false;
			for (auto port : {ID::A, ID::B}) {
				auto d = driver.find(sigmap(cell->getPort(port))[0]);
				if (d != driver.end() && GetSize(increment_input(d->second)) != 0)
					behind_increment = true;
			}
			if (!behind_increment)
				continue;

			bool distributed = false;
			for (auto &o : targets)
				if (o.mul == cell)
					distributed = true;
			if (!distributed)
				return true;
		}
		return false;
	}

	void run()
	{
		// One rewrite at a time: each moves a row onto the chain root, which the
		// next one has to see, so the maps are rebuilt in between. Each rewrite
		// consumes one multiply, which bounds the loop.
		int budget = 0;
		for (auto cell : module->cells())
			if (cell->type == ID($mul))
				budget++;

		while (budget-- > 0) {
			index();
			std::vector<Target> targets = collect();
			if (targets.empty())
				break;
			Target next = targets.front();
			Cell *inc = next.inc;
			distribute(next);
			// The increment is dead once the last multiply reading it is rewritten
			index();
			bool dead = true;
			for (auto bit : sigmap(inc->getPort(ID::Y)))
				if (escapes.count(bit) || !consumers[bit].empty())
					dead = false;
			if (dead)
				module->remove(inc);
		}
	}
};

struct OptMulDistPass : public Pass {
	OptMulDistPass() : Pass("opt_muldist", "distribute increments out of multiplier operands") {}

	void help() override
	{
		log("\n");
		log("    opt_muldist [options] [selection]\n");
		log("\n");
		log("Distribute a truncated increment out of an unsigned multiplier operand:\n");
		log("\n");
		log("    y = (x + 1)[hi:lo] * z\n");
		log("      ->  c = &x[lo-1:0]        // carry out of the dropped window\n");
		log("          w = &x[hi:0]          // the window wraps to zero\n");
		log("          y = ((x[hi:lo] & ~w) * z) + ((c & ~w) ? z : 0)\n");
		log("\n");
		log("(x + 1)[hi:lo] is (x[hi:lo] + c) mod 2^(hi-lo+1), since all the increment can\n");
		log("carry past the dropped low bits is the AND of them, and the modulo only bites\n");
		log("when x[hi:0] is all ones. Distributing it trades a prefix adder on the\n");
		log("operand's critical path for an AND reduction of the same logarithmic depth,\n");
		log("plus one gated addend row that arrives as early as z does.\n");
		log("\n");
		log("That row is only cheap if something carry-saves it, so this fires only where\n");
		log("the product already feeds an add chain arith_tree will rebuild. Cells the\n");
		log("rewrite creates carry the 'opt_muldist' attribute.\n");
		log("\n");
		log("    -max-reduce n\n");
		log("        distribute only when the wrap test spans at most n bits, beyond\n");
		log("        which the AND reduction is deeper than the adder it replaces\n");
		log("        (default: 16).\n");
		log("\n");
		log("    -min-chain n\n");
		log("        require the add chain behind the product to have at least n\n");
		log("        addends, so the row lands as a compressor level rather than as\n");
		log("        another carry-propagate adder (default: 3).\n");
		log("\n");
		log("    -min-chain-width n\n");
		log("        require that chain to be at least n bits wide, matching the\n");
		log("        width gate arith_tree is run with (default: 16).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int max_reduce = 16;
		int min_chain = 3;
		int min_chain_width = 16;

		log_header(design, "Executing OPT_MULDIST pass (distribute increments out of multiplier operands).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max-reduce" && argidx + 1 < args.size()) {
				max_reduce = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min-chain" && argidx + 1 < args.size()) {
				min_chain = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min-chain-width" && argidx + 1 < args.size()) {
				min_chain_width = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			OptMulDistWorker worker(module, max_reduce, min_chain, min_chain_width);
			worker.run();
		}
	}
} OptMulDistPass;

PRIVATE_NAMESPACE_END
