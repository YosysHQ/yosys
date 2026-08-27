/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.     <akash@silimate.com>
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
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/ff.h"
#include "kernel/ffinit.h"
#include <cmath>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static inline double log2p1(int n) { return std::log2(double(std::max(1, n)) + 1.0); }

// Heuristic, model-free per-cell delay, used only to rank candidate hold
// conditions by how late they arrive. Mirrors opt_carry_select's estimator so
// the two passes agree on which arrivals dominate.
static double estimate_cell_delay(const Cell *cell, int out_width)
{
	if (cell == nullptr)
		return 1.0;
	IdString t = cell->type;
	if (t.in(ID($add), ID($sub), ID($neg), ID($alu), ID($shl), ID($shr), ID($sshl), ID($sshr)))
		return log2p1(out_width);
	if (t.in(ID($mul), ID($div), ID($mod)))
		return out_width;
	if (t == ID($pmux)) {
		int s_width = cell->hasParam(ID::S_WIDTH) ? cell->getParam(ID::S_WIDTH).as_int() : 1;
		return log2p1(s_width);
	}
	// Compares and reductions collapse their operand to one bit through a tree,
	// so they cost like the width, not like a gate. Ranking a hold condition
	// behind a wide compare as a single level would hide the pass's best
	// candidate behind the one-hot muxes sitting next to the adder.
	if (t.in(ID($eq), ID($ne), ID($eqx), ID($nex), ID($lt), ID($le), ID($gt), ID($ge)))
		return log2p1(std::max(cell->hasParam(ID::A_WIDTH) ? cell->getParam(ID::A_WIDTH).as_int() : 1,
		                       cell->hasParam(ID::B_WIDTH) ? cell->getParam(ID::B_WIDTH).as_int() : 1));
	if (t.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool)))
		return log2p1(cell->hasParam(ID::A_WIDTH) ? cell->getParam(ID::A_WIDTH).as_int() : 1);
	if (t.in(ID($and), ID($or)))
		return 0.5;
	// $mux, $xor, $xnor, $not, gate-level $_*_ and everything else: one level.
	return 1.0;
}

struct OptAccumEnableWorker
{
	// A cell whose output is held at zero by one control bit.
	struct Gate {
		Cell *cell = nullptr;
		SigBit cond;             // output is zero while cond is 0 ...
		bool cond_inverted = false;  // ... or while cond is 1, when set
		SigSpec bypass;          // value the output takes once the gate is dropped
		double cond_arrival = 0.0;
		int depth = 0;           // cells between the gate and the update
	};

	struct Plan {
		Cell *ff;
		Gate gate;
	};

	Module *module;
	SigMap sigmap;
	FfInitVals initvals;
	CellTypes cell_types;

	dict<SigBit, Cell *> bit_to_driver;
	dict<SigBit, pool<Cell *>> bit_to_consumers;
	pool<SigBit> escaping_bits;  // observed outside the module, or explicitly kept

	dict<SigBit, double> arrival_cache;
	pool<SigBit> arrival_stack;

	pool<SigBit> known_zero;  // reset per candidate gate

	int max_cone_cells;
	int max_gates;
	int max_peel;

	vector<Plan> plans;

	OptAccumEnableWorker(Module *module, int max_cone_cells, int max_gates, int max_peel)
		: module(module), sigmap(module), initvals(&sigmap, module),
		  max_cone_cells(max_cone_cells), max_gates(max_gates), max_peel(max_peel)
	{
		cell_types.setup();
		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							bit_to_driver[bit] = cell;
				if (cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							bit_to_consumers[bit].insert(cell);
			}

		for (auto wire : module->wires())
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(wire))
					escaping_bits.insert(bit);
	}

	// Cells that observe a value for anything other than the accumulate under
	// test. Bypassing a gate changes every net in its cone, so reaching one of
	// these means the change would be visible somewhere we cannot guard.
	bool is_observer(Cell *c)
	{
		if (c->get_bool_attribute(ID::keep) || c->get_bool_attribute(ID::blackbox))
			return true;
		if (c->is_builtin_ff())
			return true;
		if (c->type.in(ID($dlatch), ID($adlatch), ID($dlatchsr), ID($sr),
		               ID($mem), ID($mem_v2), ID($memrd), ID($memrd_v2),
		               ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2),
		               ID($assert), ID($assume), ID($live), ID($fair), ID($cover)))
			return true;
		return !cell_types.cell_known(c->type);
	}

	// Explicit-stack post-order walk: cones here can be arbitrarily deep and a
	// worker thread's stack is not.
	double arrival_bit(SigBit start)
	{
		start = sigmap(start);
		if (!start.wire)
			return 0.0;
		if (auto it = arrival_cache.find(start); it != arrival_cache.end())
			return it->second;

		struct Frame { SigBit bit; bool finalize; };
		std::vector<Frame> stack;
		stack.push_back({start, false});

		while (!stack.empty()) {
			Frame &top = stack.back();
			SigBit bit = top.bit;
			if (!bit.wire || arrival_cache.count(bit)) {
				stack.pop_back();
				continue;
			}
			Cell *drv = bit_to_driver.at(bit, nullptr);
			if (drv == nullptr || is_observer(drv)) {
				arrival_cache[bit] = 0.0;
				stack.pop_back();
				continue;
			}
			if (!top.finalize) {
				top.finalize = true;
				arrival_stack.insert(bit);
				for (auto &conn : drv->connections())
					if (drv->input(conn.first))
						for (auto in_bit : sigmap(conn.second)) {
							if (!in_bit.wire || arrival_cache.count(in_bit))
								continue;
							if (arrival_stack.count(in_bit))  // combinational loop
								continue;
							stack.push_back({in_bit, false});
						}
				continue;
			}
			double max_in = 0.0;
			int out_width = 1;
			for (auto &conn : drv->connections())
				if (drv->output(conn.first))
					out_width = std::max(out_width, GetSize(conn.second));
			for (auto &conn : drv->connections())
				if (drv->input(conn.first))
					for (auto in_bit : sigmap(conn.second))
						if (auto it = arrival_cache.find(in_bit); it != arrival_cache.end())
							max_in = std::max(max_in, it->second);
			arrival_cache[bit] = max_in + estimate_cell_delay(drv, out_width);
			arrival_stack.erase(bit);
			stack.pop_back();
		}
		return arrival_cache.at(start);
	}

	// The one cell driving all of `sig`, where `sig` is exactly its Y port: a
	// slice or a mix of drivers is not a value we can reason about as a whole.
	Cell *whole_driver(const SigSpec &sig)
	{
		if (sig.empty())
			return nullptr;
		Cell *drv = nullptr;
		for (auto bit : sigmap(sig)) {
			if (!bit.wire)
				return nullptr;
			Cell *c = bit_to_driver.at(bit, nullptr);
			if (c == nullptr || (drv != nullptr && c != drv))
				return nullptr;
			drv = c;
		}
		if (!drv->hasPort(ID::Y) || sigmap(drv->getPort(ID::Y)) != sigmap(sig))
			return nullptr;
		return drv;
	}

	// True when `cell` is the only thing that reads `sig` and it stays inside
	// the module.
	bool exclusive_to(const SigSpec &sig, Cell *cell)
	{
		for (auto bit : sigmap(sig)) {
			if (!bit.wire || escaping_bits.count(bit))
				return false;
			auto it = bit_to_consumers.find(bit);
			if (it == bit_to_consumers.end() || GetSize(it->second) != 1 || !it->second.count(cell))
				return false;
		}
		return true;
	}

	bool zero_gate(Cell *c, Gate &gate)
	{
		if (c->type == ID($mux)) {
			SigSpec a = c->getPort(ID::A), b = c->getPort(ID::B);
			SigBit s = sigmap(c->getPort(ID::S))[0];
			if (sigmap(a).is_fully_zero() == sigmap(b).is_fully_zero())
				return false;  // both arms zero: nothing to gate; neither: not a gate
			gate.cell = c;
			gate.cond = s;
			gate.cond_inverted = sigmap(b).is_fully_zero();
			gate.bypass = gate.cond_inverted ? a : b;
			return true;
		}
		if (c->type == ID($and)) {
			int w = c->getParam(ID::Y_WIDTH).as_int();
			for (int i = 0; i < 2; i++) {
				IdString mask_port = i ? ID::B : ID::A, data_port = i ? ID::A : ID::B;
				SigSpec mask = c->getPort(mask_port);
				mask.extend_u0(w, c->getParam(i ? ID::B_SIGNED : ID::A_SIGNED).as_bool());
				mask = sigmap(mask);
				// Only a full-width replication of one bit gates the whole word;
				// a narrower mask also clears the high bits, which a bypass would
				// not reproduce.
				if (mask.empty() || !mask[0].wire)
					continue;
				bool uniform = true;
				for (auto bit : mask)
					uniform &= (bit == mask[0]);
				if (!uniform)
					continue;
				SigSpec data = c->getPort(data_port);
				data.extend_u0(w, c->getParam(i ? ID::A_SIGNED : ID::B_SIGNED).as_bool());
				gate.cell = c;
				gate.cond = mask[0];
				gate.cond_inverted = false;
				gate.bypass = data;
				return true;
			}
		}
		return false;
	}

	bool sig_zero(const SigSpec &sig)
	{
		for (auto bit : sigmap(sig)) {
			if (!bit.wire) {
				if (bit != State::S0)
					return false;
				continue;
			}
			if (!known_zero.count(bit))
				return false;
		}
		return true;
	}

	// Output provably zero given what is already known zero.
	bool cell_zero(Cell *c)
	{
		IdString t = c->type;
		if (t.in(ID($and), ID($mul), ID($logic_and), ID($_AND_)))
			return sig_zero(c->getPort(ID::A)) || sig_zero(c->getPort(ID::B));
		if (t.in(ID($or), ID($xor), ID($add), ID($sub), ID($mux), ID($pmux),
		         ID($_OR_), ID($_XOR_), ID($_MUX_)))
			return sig_zero(c->getPort(ID::A)) && sig_zero(c->getPort(ID::B));
		// Shifting, negating or or-reducing zero keeps it zero; $shiftx is left
		// out because its out-of-range fill is x, not 0.
		if (t.in(ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($neg),
		         ID($pos), ID($reduce_or), ID($reduce_bool), ID($bmux)))
			return sig_zero(c->getPort(ID::A));
		return false;
	}

	// Everything the gate's output feeds, up to (but not through) the
	// accumulate. Fails if any of it is observed elsewhere, since those nets
	// change value once the gate is gone.
	bool build_cone(const Gate &gate, Cell *acc, pool<Cell *> &cone)
	{
		std::vector<Cell *> queue = {gate.cell};
		cone.insert(gate.cell);
		for (size_t i = 0; i < queue.size(); i++) {
			Cell *c = queue[i];
			for (auto &conn : c->connections()) {
				if (!c->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (!bit.wire || escaping_bits.count(bit))
						return false;
					for (auto user : bit_to_consumers[bit]) {
						if (user == acc || cone.count(user))
							continue;
						if (is_observer(user) || GetSize(cone) >= max_cone_cells)
							return false;
						cone.insert(user);
						queue.push_back(user);
					}
				}
			}
		}
		return true;
	}

	// Monotone forward sweep: which cone nets are zero while the gate holds its
	// own output at zero.
	void propagate_zero(const pool<Cell *> &cone)
	{
		for (bool changed = true; changed;) {
			changed = false;
			for (auto c : cone) {
				if (!c->hasPort(ID::Y))
					continue;
				SigSpec y = sigmap(c->getPort(ID::Y));
				if (y.empty() || sig_zero(y) || !cell_zero(c))
					continue;
				for (auto bit : y)
					if (bit.wire)
						known_zero.insert(bit);
				changed = true;
			}
		}
	}

	// `q OP z` equals q for z == 0, so a condition that zeroes z is a hold.
	static bool is_identity_op(IdString t)
	{
		return t.in(ID($add), ID($sub), ID($or), ID($xor));
	}

	void collect_gates(const SigSpec &addend, vector<Gate> &gates)
	{
		pool<Cell *> seen;
		std::vector<std::pair<Cell *, int>> queue;
		auto push = [&](const SigSpec &s, int depth) {
			for (auto bit : sigmap(s)) {
				if (!bit.wire)
					continue;
				Cell *c = bit_to_driver.at(bit, nullptr);
				if (c == nullptr || seen.count(c) || is_observer(c))
					continue;
				seen.insert(c);
				queue.push_back(std::make_pair(c, depth));
			}
		};
		push(addend, 0);
		for (size_t i = 0; i < queue.size() && GetSize(seen) < max_cone_cells; i++) {
			Cell *c = queue[i].first;
			int depth = queue[i].second;
			Gate gate;
			if (zero_gate(c, gate)) {
				gate.cond_arrival = arrival_bit(gate.cond);
				gate.depth = depth;
				gates.push_back(gate);
			}
			for (auto &conn : c->connections())
				if (c->input(conn.first))
					push(conn.second, depth + 1);
		}
	}

	void run_ff(Cell *ff_cell)
	{
		if (!ff_cell->is_builtin_ff())
			return;
		FfData ff(&initvals, ff_cell);
		// Async load and clockless FFs have no enable to fold into. An enable
		// that also gates the sync reset would start suppressing that reset.
		if (!ff.has_clk || ff.has_gclk || ff.has_aload)
			return;
		if (ff.has_srst && ff.ce_over_srst)
			return;

		SigSpec q = sigmap(ff.sig_q);
		SigSpec upd = sigmap(ff.sig_d);

		// Walk back past any enable muxes already sitting on D; they stay put,
		// the new condition rides on the register's own enable pin.
		Cell *acc = nullptr;
		Cell *reader = ff_cell;
		for (int peel = 0; peel <= max_peel; peel++) {
			if (!exclusive_to(upd, reader))
				return;
			Cell *drv = whole_driver(upd);
			if (drv == nullptr)
				return;
			if (is_identity_op(drv->type)) {
				acc = drv;
				break;
			}
			if (drv->type != ID($mux))
				return;
			SigSpec a = sigmap(drv->getPort(ID::A)), b = sigmap(drv->getPort(ID::B));
			if (a == q)
				upd = b;
			else if (b == q)
				upd = a;
			else
				return;
			reader = drv;
		}
		if (acc == nullptr)
			return;

		// One operand must be the register's own value at full width, so the
		// update really is `q OP addend` with no truncation or extension.
		SigSpec a = sigmap(acc->getPort(ID::A)), b = sigmap(acc->getPort(ID::B));
		SigSpec addend;
		if (a == q && GetSize(a) == GetSize(q))
			addend = acc->getPort(ID::B);
		else if (b == q && GetSize(b) == GetSize(q) && acc->type != ID($sub))
			addend = acc->getPort(ID::A);
		else
			return;

		vector<Gate> gates;
		collect_gates(addend, gates);
		log_debug("opt_accum_enable: %s updates via %s, %d candidate gate(s)\n",
		          log_id(ff_cell), log_id(acc), GetSize(gates));
		// Latest condition first: that is the one whose cone leaving the
		// datapath shortens the register's arrival the most. On a tie prefer
		// the gate furthest from the update, whose zero covers the others.
		std::sort(gates.begin(), gates.end(), [](const Gate &x, const Gate &y) {
			if (x.cond_arrival != y.cond_arrival)
				return x.cond_arrival > y.cond_arrival;
			return x.depth > y.depth;
		});

		int tried = 0;
		for (auto &gate : gates) {
			if (++tried > max_gates)
				return;
			pool<Cell *> cone;
			if (!build_cone(gate, acc, cone)) {
				log_debug("opt_accum_enable:   %s rejected: value escapes the update\n",
				          log_id(gate.cell));
				continue;
			}
			known_zero.clear();
			for (auto bit : sigmap(gate.cell->getPort(ID::Y)))
				if (bit.wire)
					known_zero.insert(bit);
			propagate_zero(cone);
			if (!sig_zero(addend)) {
				log_debug("opt_accum_enable:   %s rejected: zero does not reach the update\n",
				          log_id(gate.cell));
				continue;
			}
			log_debug("opt_accum_enable: %s/%s holds %s via %s (arrival %.2f)\n",
			          log_id(module), log_id(ff_cell), log_id(acc), log_id(gate.cell),
			          gate.cond_arrival);
			plans.push_back({ff_cell, gate});
			return;
		}
	}

	SigBit make_not(Cell *cell, SigBit a, bool is_fine)
	{
		std::string src = cell->get_src_attribute();
		if (is_fine)
			return module->NotGate(NEW_ID2_SUFFIX("hold_not"), a, src);
		return module->Not(NEW_ID2_SUFFIX("hold_not"), a, false, src);
	}

	SigBit make_and(Cell *cell, SigBit a, SigBit b, bool is_fine)
	{
		std::string src = cell->get_src_attribute();
		if (is_fine)
			return module->AndGate(NEW_ID2_SUFFIX("hold_and"), a, b, src);
		return module->And(NEW_ID2_SUFFIX("hold_and"), a, b, false, src);
	}

	void apply(const Plan &plan)
	{
		// Drop the gate: the datapath now carries the ungated value, which only
		// the guarded register ever sees.
		SigBit cond = plan.gate.cond;
		Cell *gate_cell = plan.gate.cell;
		module->connect(gate_cell->getPort(ID::Y), plan.gate.bypass);
		if (plan.gate.cond_inverted)
			cond = make_not(gate_cell, cond, false);
		module->remove(gate_cell);

		// The condition that used to zero the update now holds the register.
		Cell *cell = plan.ff;
		FfData ff(&initvals, cell);
		if (ff.has_ce) {
			SigBit ce = ff.sig_ce;
			if (!ff.pol_ce) {
				ce = make_not(cell, ce, ff.is_fine);
				ff.pol_ce = true;
			}
			ff.sig_ce = make_and(cell, ce, cond, ff.is_fine);
		} else {
			ff.has_ce = true;
			ff.pol_ce = true;
			ff.sig_ce = cond;
			ff.ce_over_srst = false;
		}
		ff.emit();
	}

	int run()
	{
		for (auto cell : module->cells())
			run_ff(cell);
		// Cones are exclusive to one accumulate each, so no two plans can touch
		// the same cells and they can all be applied off the same analysis.
		for (auto &plan : plans)
			apply(plan);
		return GetSize(plans);
	}
};

struct OptAccumEnablePass : public Pass {
	OptAccumEnablePass() : Pass("opt_accum_enable",
		"fold a zero-gated register update into the register enable") {}

	void help() override
	{
		log("\n");
		log("    opt_accum_enable [options] [selection]\n");
		log("\n");
		log("Folds a gated accumulator update into the register's enable. When a register's\n");
		log("next value is `q + z` (or -, |, ^) and some condition holds `z` at zero, the\n");
		log("register keeps its value, so that condition can be ANDed onto the enable and\n");
		log("the zeroing mux dropped from the datapath.\n");
		log("\n");
		log("This takes the condition's whole cone -- typically a wide compare -- off the\n");
		log("path into the adder, leaving only a one-bit term on the enable, and exposes the\n");
		log("register to clock gating. Only rewrites when every net the gate feeds is read\n");
		log("by that one accumulate, so dropping the gate cannot be observed anywhere else.\n");
		log("\n");
		log("    -strict\n");
		log("        disable the rewrite. The update the gate used to zero becomes an\n");
		log("        observability don't-care once the register holds, so gold and gate\n");
		log("        diverge on internal nodes and a node-matching equivalence check\n");
		log("        cannot confirm it.\n");
		log("\n");
		log("    -max-cone-cells N\n");
		log("        give up on cones wider than N cells (default 512).\n");
		log("\n");
		log("    -max-gates N\n");
		log("        verify at most N candidate conditions per register (default 8).\n");
		log("\n");
		log("    -max-peel N\n");
		log("        look through at most N enable muxes on D (default 4).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_ACCUM_ENABLE pass (gated update to register enable).\n");

		int max_cone_cells = 512, max_gates = 8, max_peel = 4;
		bool strict = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-strict") {
				strict = true;
				continue;
			}
			if (args[argidx] == "-max-cone-cells" && argidx + 1 < args.size()) {
				max_cone_cells = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max-gates" && argidx + 1 < args.size()) {
				max_gates = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max-peel" && argidx + 1 < args.size()) {
				max_peel = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total = 0;
		for (auto module : design->selected_modules()) {
			if (strict)
				break;  // still log the count, so the flow reads the same either way
			OptAccumEnableWorker worker(module, max_cone_cells, max_gates, max_peel);
			total += worker.run();
		}

		if (total)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Folded %d gated update%s into register enable(s).\n", total, total == 1 ? "" : "s");
	}
} OptAccumEnablePass;

PRIVATE_NAMESPACE_END
