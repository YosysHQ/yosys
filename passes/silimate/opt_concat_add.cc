/**
 * Split an adder at a concatenation boundary and push a mux through the wide half.
 *
 * Authored by Akash Levy of Silimate, Inc. under ISC license.
 *
 *   y = {sel ? p : q, t} + b
 *     ===>   lo = t + b[k-1:0]                                       // k+1 bits
 *            y  = {sel ? (p + b[:k] + lo[k]) : (q + b[:k] + lo[k]), lo[k-1:0]}
 *
 * A concatenation is already a sum of disjoint shifted parts, but an adder
 * sitting on top of one cannot see that: its carry chain runs straight through
 * the boundary, so the mux only ever reaches the adder as part of a wider port.
 * That strands it. A carry-save pass cannot cross a mux, and mux pushing needs a
 * whole port to push into, which the concatenation denies it. The two adders stay
 * in series with the mux between them.
 *
 * Splitting at the boundary gives the wide half its own adder, which the mux can
 * then be pushed through in the same rewrite. Each arm's copy of the adder lands
 * directly on the arithmetic behind that arm, where arith_tree folds it into that
 * arm's compressor tree, so both carry-propagate adders collapse into one.
 *
 * The split alone is a loss -- the tail add's carry feeds the wide half, so the
 * two are in series -- so it fires only where the push pays for it:
 *
 *   - the wide half must be driven by a mux over arithmetic, used nowhere else.
 *     Arithmetic driving it directly is already in the adder's own chain, which a
 *     tree pass reaches unaided, so splitting there only breaks the chain.
 *   - the tail must not be constant. A constant tail is bit alignment, which a
 *     tree pass already reads as weights, not two producers to separate.
 *   - the addend handed to the wide half must be wide enough that the adder
 *     folded away costs more than the compressor level that folds it.
 */

#include "kernel/sigtools.h"
#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptConcatAddWorker {
	Module *module;
	SigMap sigmap;
	dict<SigBit, Cell *> driver;
	dict<SigBit, pool<Cell *>> consumers;
	pool<SigBit> escapes; // outlives its driver, so no cell owns it
	int max_tail;
	int min_width;
	int min_addend;
	int max_arms;
	int max_mux_depth;

	struct Target {
		Cell *add;
		Cell *mux;
		IdString port; // the concatenated operand
		int boundary;
	};

	OptConcatAddWorker(Module *module, int max_tail, int min_width, int min_addend, int max_arms, int max_mux_depth)
	    : module(module), sigmap(module), max_tail(max_tail), min_width(min_width), min_addend(min_addend),
	      max_arms(max_arms), max_mux_depth(max_mux_depth)
	{
		for (auto cell : module->cells())
			for (auto &[name, sig] : cell->connections())
				for (auto bit : sigmap(sig)) {
					if (cell->output(name))
						driver[bit] = cell;
					if (cell->input(name))
						consumers[bit].insert(cell);
				}

		// A kept wire has to stay driven, so treat it like a port output rather
		// than letting the mux that drives it be removed
		for (auto wire : module->wires())
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(SigSpec(wire)))
					escapes.insert(bit);
	}

	bool is_arith(Cell *cell)
	{
		return cell->type.in(ID($add), ID($sub), ID($mul), ID($alu), ID($macc), ID($macc_v2));
	}

	// Only a mux is worth splitting for, and only one with arithmetic behind it:
	// that is what turns each pushed copy of the adder into a tree operand rather
	// than a second adder.
	bool mux_over_arith(Cell *cell, int depth)
	{
		if (!cell->type.in(ID($mux), ID($pmux)) || depth >= max_mux_depth)
			return false;

		for (auto port : {ID::A, ID::B})
			for (auto bit : sigmap(cell->getPort(port))) {
				auto arm = driver.find(bit);
				if (arm == driver.end())
					continue;
				if (is_arith(arm->second) || mux_over_arith(arm->second, depth + 1))
					return true;
			}
		return false;
	}

	// The arms a pushed adder has to be copied into: both inputs of a $mux, or
	// the default plus every case of a $pmux.
	std::vector<SigSpec> mux_arms(Cell *mux)
	{
		std::vector<SigSpec> arms;
		int w = GetSize(mux->getPort(ID::Y));
		if (mux->type == ID($mux)) {
			arms.push_back(mux->getPort(ID::A));
			arms.push_back(mux->getPort(ID::B));
			return arms;
		}
		arms.push_back(mux->getPort(ID::A));
		SigSpec b = mux->getPort(ID::B);
		for (int i = 0; i < GetSize(mux->getPort(ID::S)); i++)
			arms.push_back(b.extract(i * w, w));
		return arms;
	}

	// Lowest bit of the topmost run the operand takes from one cell, along with
	// that cell. The concatenation puts a boundary there, and it is the only
	// place a split can hand the wide half over whole. Constant padding above
	// the payload is skipped: it belongs to the wide half, not to a run.
	int concat_boundary(const SigSpec &sig, Cell **top_out)
	{
		int i = GetSize(sig) - 1;
		while (i >= 0 && !driver.count(sigmap(sig[i])))
			i--;
		if (i < 0)
			return -1;

		Cell *top = driver.at(sigmap(sig[i]));
		int k = i;
		while (k > 0) {
			auto below = driver.find(sigmap(sig[k - 1]));
			if (below == driver.end() || below->second != top)
				break;
			k--;
		}
		*top_out = top;
		return k;
	}

	// Rebuild `sig` with the mux's output bits replaced by the same bits of one
	// arm, which keeps whatever else the wide half holds -- constant padding, or
	// bits from another producer -- exactly where it was.
	SigSpec on_arm(const SigSpec &sig, const SigSpec &mux_y, const SigSpec &arm)
	{
		dict<SigBit, int> index;
		for (int i = 0; i < GetSize(mux_y); i++)
			index[mux_y[i]] = i;

		SigSpec out;
		for (auto bit : sig) {
			auto it = index.find(sigmap(bit));
			out.append(it == index.end() ? bit : arm[it->second]);
		}
		return out;
	}

	void split(const Target &t)
	{
		Cell *cell = t.add;
		int k = t.boundary;
		IdString other_port = (t.port == ID::A) ? ID::B : ID::A;
		SigSpec a = cell->getPort(t.port);
		SigSpec b = cell->getPort(other_port);
		SigSpec y = cell->getPort(ID::Y);
		int wy = GetSize(y);
		std::string src = cell->get_src_attribute();

		log("opt_concat_add: splitting %s (%d bits) at bit %d of %s, pushing %s (%s)\n", log_id(cell), wy, k,
		    log_id(t.port), log_id(t.mux), log_id(t.mux->type));

		// The tail keeps one bit for the carry it hands to the wide half
		SigSpec a_lo = a.extract(0, k);
		SigSpec b_lo = b.extract(0, std::min(k, GetSize(b)));
		SigSpec lo = module->addWire(NEW_ID2_SUFFIX("lo"), k + 1);
		module->addAdd(NEW_ID2_SUFFIX("add_lo"), a_lo, b_lo, lo, false, src);

		// The wide half keeps every carry the original adder kept, but only as
		// far as its operands can reach: one bit past the wider of them covers
		// the carry-in too, and the result is zero above that
		SigSpec a_hi = a.extract_end(k);
		SigSpec b_hi = (GetSize(b) > k) ? b.extract_end(k) : SigSpec();
		int w_hi = std::min(wy - k, std::max(GetSize(a_hi), GetSize(b_hi)) + 1);

		// One copy of the wide half per arm, each landing on that arm's own
		// arithmetic instead of behind the mux
		SigSpec mux_y = sigmap(t.mux->getPort(ID::Y));
		std::vector<SigSpec> sums;
		for (auto &arm : mux_arms(t.mux)) {
			SigSpec sum = module->addWire(NEW_ID2_SUFFIX("hi"), w_hi);
			Cell *hi_add = module->addAdd(NEW_ID2_SUFFIX("add_hi"), on_arm(a_hi, mux_y, arm), b_hi, sum, false, src);
			SigSpec with_cin = module->addWire(NEW_ID2_SUFFIX("hi_cin"), w_hi);
			Cell *cin_add = module->addAdd(NEW_ID2_SUFFIX("add_cin"), sum, lo.extract(k, 1), with_cin, false, src);
			// Tagged so tests and debugging can tell the rewrite apart from the
			// adders it was built out of
			hi_add->set_bool_attribute(ID(opt_concat_add));
			cin_add->set_bool_attribute(ID(opt_concat_add));
			sums.push_back(with_cin);
		}

		SigSpec hi = module->addWire(NEW_ID2_SUFFIX("hi_sel"), w_hi);
		SigSpec s = t.mux->getPort(ID::S);
		if (t.mux->type == ID($mux)) {
			module->addMux(NEW_ID2_SUFFIX("mux"), sums[0], sums[1], s, hi, src);
		} else {
			SigSpec cases;
			for (size_t i = 1; i < sums.size(); i++)
				cases.append(sums[i]);
			module->addPmux(NEW_ID2_SUFFIX("pmux"), sums[0], cases, s, hi, src);
		}

		module->remove(cell);
		module->remove(t.mux);
		module->connect(y, {SigSpec(State::S0, wy - k - w_hi), hi, lo.extract(0, k)});
	}

	// The mux is replaced by one over the pushed sums, so anything else reading
	// it would have to keep the old one alongside the new
	bool mux_used_only_by(Cell *mux, Cell *add)
	{
		if (mux->get_bool_attribute(ID::keep))
			return false;
		for (auto bit : sigmap(mux->getPort(ID::Y))) {
			if (escapes.count(bit))
				return false;
			for (auto user : consumers[bit])
				if (user != add)
					return false;
		}
		return true;
	}

	void run()
	{
		// Collect first: splitting rewires the netlist the driver map describes
		std::vector<Target> targets;
		for (auto cell : module->selected_cells()) {
			if (cell->type != ID($add))
				continue;
			if (cell->getParam(ID::A_SIGNED).as_bool() || cell->getParam(ID::B_SIGNED).as_bool())
				continue;

			SigSpec y = cell->getPort(ID::Y);
			if (GetSize(y) < min_width)
				continue;

			for (auto port : {ID::A, ID::B}) {
				SigSpec sig = sigmap(cell->getPort(port));
				Cell *mux = nullptr;
				int k = concat_boundary(sig, &mux);

				// A tail is what makes this a concatenation, and a narrow one is
				// what keeps the adder it costs cheap
				if (k < 1 || k > max_tail)
					continue;
				// Nothing above the boundary survives in the result, so there is
				// no wide half to hand over
				if (GetSize(y) <= k)
					continue;
				// A constant tail is alignment, not a concatenation of two
				// producers: the tree pass already reads it as bit weights, and
				// splitting there only buys an adder for the constant
				if (sig.extract(0, k).is_fully_const())
					continue;
				// What the split hands to each arm is the addend above the
				// boundary, and it has to be wide enough that the adder folded
				// away costs more than the compressor level it takes to fold it
				SigSpec other = sigmap(cell->getPort(port == ID::A ? ID::B : ID::A));
				if (GetSize(other) - k < min_addend)
					continue;
				if (!mux_over_arith(mux, 0))
					continue;
				if (GetSize(mux_arms(mux)) > max_arms)
					continue;
				if (!mux_used_only_by(mux, cell))
					continue;

				targets.push_back({cell, mux, port, k});
				break;
			}
		}

		for (auto &t : targets)
			split(t);
	}
};

struct OptConcatAddPass : public Pass {
	OptConcatAddPass() : Pass("opt_concat_add", "split adders at concatenation boundaries") {}

	void help() override
	{
		log("\n");
		log("    opt_concat_add [options] [selection]\n");
		log("\n");
		log("Split an unsigned adder at a concatenation boundary in one of its operands,\n");
		log("and push the mux driving the wide half through the adder it just gained:\n");
		log("\n");
		log("    y = {sel ? p : q, t} + b\n");
		log("      ->  lo = t + b[k-1:0]\n");
		log("          y  = {sel ? (p + b[:k] + lo[k]) : (q + b[:k] + lo[k]), lo[k-1:0]}\n");
		log("\n");
		log("A concatenation is a sum of disjoint shifted parts, but an adder on top of one\n");
		log("cannot see that, so the mux only reaches it as part of a wider port. That\n");
		log("strands the mux: a carry-save pass cannot cross it, and mux pushing needs a\n");
		log("whole port. After the split each arm's copy of the adder lands on that arm's\n");
		log("own arithmetic, where arith_tree folds it in and the two carry-propagate\n");
		log("adders become one.\n");
		log("\n");
		log("Fires only where that push pays: the wide half must be driven by a mux over\n");
		log("arithmetic that nothing else reads, the tail must not be constant, and the\n");
		log("addend must be wide enough to pay for the compressor level. Adders the\n");
		log("rewrite creates carry the 'opt_concat_add' attribute.\n");
		log("\n");
		log("    -max-tail n\n");
		log("        split only when the tail below the boundary is at most n bits\n");
		log("        wide, since the tail adder's carry feeds the wide half and is\n");
		log("        therefore in series with it (default: 8).\n");
		log("\n");
		log("    -min-width n\n");
		log("        skip adders narrower than n bits, where the carry chain removed\n");
		log("        does not pay for the one added (default: 16).\n");
		log("\n");
		log("    -min-addend n\n");
		log("        split only when the addend handed to the wide half is at least n\n");
		log("        bits, since a narrow addend makes for a cheap adder that does not\n");
		log("        pay for the compressor level needed to fold it (default: 8).\n");
		log("\n");
		log("    -max-arms n\n");
		log("        push through at most n mux arms, one copy of the wide adder each\n");
		log("        (default: 4).\n");
		log("\n");
		log("    -max-mux-depth n\n");
		log("        how many muxes to look through when deciding whether the wide\n");
		log("        half is a mux over arithmetic (default: 2).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int max_tail = 8;
		int min_width = 16;
		int min_addend = 8;
		int max_arms = 4;
		int max_mux_depth = 2;

		log_header(design, "Executing OPT_CONCAT_ADD pass (split adders at concatenation boundaries).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max-tail" && argidx + 1 < args.size()) {
				max_tail = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min-width" && argidx + 1 < args.size()) {
				min_width = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min-addend" && argidx + 1 < args.size()) {
				min_addend = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max-arms" && argidx + 1 < args.size()) {
				max_arms = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max-mux-depth" && argidx + 1 < args.size()) {
				max_mux_depth = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			OptConcatAddWorker worker(module, max_tail, min_width, min_addend, max_arms, max_mux_depth);
			worker.run();
		}
	}
} OptConcatAddPass;

PRIVATE_NAMESPACE_END
