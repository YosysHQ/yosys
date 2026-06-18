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
#include "kernel/celltypes.h"
#include <cmath>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// Marks the incrementer/mux a carry-select rewrite emits so peepopt -muxorder
// (which would otherwise fold `s ? (a+1) : a` back into `a + s`, putting the
// late select on a wide ripple carry) leaves them alone.
static const IdString kAttrCarrySelect = ID(carry_select);

static inline double log2p1(int n) { return std::log2(double(std::max(1, n)) + 1.0); }

// Heuristic, model-free per-cell delay used only to rank "early" vs "late"
// operands. Mirrors opt_timing_balance's heuristic so the two passes agree on
// which arrivals dominate.
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
	if (t.in(ID($and), ID($or)))
		return 0.5;
	// $mux, $xor, $xnor, $not, gate-level $_*_ and everything else: one level.
	return 1.0;
}

struct OptCarrySelectWorker {
	Module *module;
	SigMap sigmap;
	CellTypes cell_types;

	dict<SigBit, Cell*> driver;          // sigmap'd output bit -> driving cell
	dict<SigBit, double> arrival_cache;  // memoized arrival per bit
	pool<SigBit> on_stack;               // combinational-loop guard

	int max_narrow;
	int min_wide;
	double margin;

	int converted = 0;

	OptCarrySelectWorker(Module *m, int max_narrow, int min_wide, double margin)
		: module(m), sigmap(m), max_narrow(max_narrow), min_wide(min_wide), margin(margin)
	{
		cell_types.setup();
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (cell->output(conn.first))
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							driver[bit] = cell;
	}

	bool is_boundary(Cell *cell) {
		if (cell == nullptr)
			return true;
		if (cell->get_bool_attribute(ID::keep) || cell->get_bool_attribute(ID::blackbox))
			return true;
		if (cell->is_builtin_ff())
			return true;
		if (cell->type.in(ID($dlatch), ID($adlatch), ID($dlatchsr),
				ID($mem), ID($mem_v2), ID($memrd), ID($memrd_v2),
				ID($memwr), ID($memwr_v2), ID($meminit), ID($meminit_v2)))
			return true;
		return !cell_types.cell_known(cell->type);
	}

	Cell *driver_of(SigBit bit) {
		auto it = driver.find(bit);
		return (it == driver.end()) ? nullptr : it->second;
	}

	// Explicit-stack post-order traversal so arbitrarily deep combinational cones
	// cannot overflow the C++ stack (worker threads can have small stacks).
	double arrival_bit(SigBit start) {
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
			Cell *drv = driver_of(bit);
			if (drv == nullptr || is_boundary(drv)) {
				arrival_cache[bit] = 0.0;
				stack.pop_back();
				continue;
			}

			if (!top.finalize) {
				// Expand: schedule finalize, then push not-yet-resolved inputs.
				top.finalize = true;
				on_stack.insert(bit);
				for (auto &conn : drv->connections())
					if (drv->input(conn.first))
						for (auto in_bit : sigmap(conn.second)) {
							if (!in_bit.wire || arrival_cache.count(in_bit))
								continue;
							if (on_stack.count(in_bit)) // combinational loop: break it
								continue;
							stack.push_back({in_bit, false});
						}
				continue;
			}

			// Finalize: all resolvable inputs are now cached.
			double max_in = 0.0;
			int out_width = 1;
			for (auto &conn : drv->connections())
				if (drv->output(conn.first))
					out_width = std::max(out_width, GetSize(conn.second));
			for (auto &conn : drv->connections())
				if (drv->input(conn.first))
					for (auto in_bit : sigmap(conn.second)) {
						auto it = arrival_cache.find(in_bit);
						if (it != arrival_cache.end())
							max_in = std::max(max_in, it->second);
					}
			arrival_cache[bit] = max_in + estimate_cell_delay(drv, out_width);
			on_stack.erase(bit);
			stack.pop_back();
		}
		return arrival_cache.at(start);
	}

	double arrival(const SigSpec &sig) {
		double t = 0.0;
		for (auto bit : sigmap(sig))
			t = std::max(t, arrival_bit(bit));
		return t;
	}

	// Decision record so we never iterate over a mutating cell list.
	struct Plan {
		Cell *add;
		bool wide_is_a;
		int k;   // narrow width / split point
		int w;   // result width
	};

	bool qualifies(Cell *c, Plan &plan) {
		if (c->type != ID($add))
			return false;
		if (c->get_bool_attribute(kAttrCarrySelect))
			return false;
		if (c->getParam(ID::A_SIGNED).as_bool() || c->getParam(ID::B_SIGNED).as_bool())
			return false; // v1: unsigned operands only (exact zero-extension)

		int a_w = c->getParam(ID::A_WIDTH).as_int();
		int b_w = c->getParam(ID::B_WIDTH).as_int();
		int w = c->getParam(ID::Y_WIDTH).as_int();

		bool wide_is_a = a_w >= b_w;
		int narrow_w = std::min(a_w, b_w);
		int k = narrow_w;

		if (k < 1 || k >= w)
			return false;
		if (k > max_narrow)
			return false;
		if (w - k < min_wide)
			return false;

		SigSpec wide_sig = c->getPort(wide_is_a ? ID::A : ID::B);
		SigSpec narrow_sig = c->getPort(wide_is_a ? ID::B : ID::A);

		double arr_wide = arrival(wide_sig);
		double arr_narrow = arrival(narrow_sig);
		if (arr_narrow <= arr_wide + margin)
			return false; // no timing benefit: narrow operand is not the late one

		plan.add = c;
		plan.wide_is_a = wide_is_a;
		plan.k = k;
		plan.w = w;
		return true;
	}

	void apply(const Plan &plan) {
		Cell *cell = plan.add;
		int k = plan.k;
		int w = plan.w;
		std::string src = cell->get_src_attribute();

		SigSpec wide_sig = cell->getPort(plan.wide_is_a ? ID::A : ID::B);
		SigSpec narrow_sig = cell->getPort(plan.wide_is_a ? ID::B : ID::A);
		SigSpec y = cell->getPort(ID::Y);

		// Zero-extend the wide operand to the full result width.
		SigSpec wext = wide_sig;
		wext.extend_u0(w, /*is_signed=*/false);
		SigSpec wlow = wext.extract(0, k);
		SigSpec whigh = wext.extract(k, w - k);

		// Low add: produces the low k sum bits plus the carry into bit k.
		Wire *losum = module->addWire(NEW_ID2_SUFFIX("cs_lo"), k + 1);
		module->addAdd(NEW_ID2_SUFFIX("cs_lo_add"), wlow, narrow_sig, SigSpec(losum), /*is_signed=*/false, src);
		SigSpec losum_low = SigSpec(losum).extract(0, k);
		SigBit carry = SigSpec(losum)[k];

		// High part precomputed from the (early) wide operand, then selected by
		// the (late) low carry: hi = carry ? (whigh + 1) : whigh.
		Wire *hiinc = module->addWire(NEW_ID2_SUFFIX("cs_hi_inc"), w - k);
		Cell *inc = module->addAdd(NEW_ID2_SUFFIX("cs_hi_inc_add"), whigh, SigSpec(State::S1), SigSpec(hiinc), /*is_signed=*/false, src);
		inc->set_bool_attribute(kAttrCarrySelect);

		Wire *hi = module->addWire(NEW_ID2_SUFFIX("cs_hi"), w - k);
		Cell *mux = module->addMux(NEW_ID2_SUFFIX("cs_hi_mux"), /*A=*/whigh, /*B=*/SigSpec(hiinc), /*S=*/carry, SigSpec(hi), src);
		mux->set_bool_attribute(kAttrCarrySelect);

		// Reassemble result and drive the original adder output.
		SigSpec result = losum_low;
		result.append(SigSpec(hi));
		module->connect(y, result);
		module->remove(cell);
		converted++;
	}

	void run() {
		vector<Cell*> adds;
		for (auto cell : module->cells())
			if (cell->type == ID($add))
				adds.push_back(cell);

		vector<Plan> plans;
		for (auto c : adds) {
			Plan plan;
			if (qualifies(c, plan))
				plans.push_back(plan);
		}
		for (auto &plan : plans)
			apply(plan);
	}
};

struct OptCarrySelectPass : public Pass {
	OptCarrySelectPass() : Pass("opt_carry_select",
		"decompose wide-early + narrow-late adders into carry-select form") {}

	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_carry_select [options] [selection]\n");
		log("\n");
		log("Rewrites a $add of the shape `wide_early + narrow_late` into a low add plus\n");
		log("a high carry-select. The low add absorbs the late, narrow operand and emits a\n");
		log("carry; the wide high half is precomputed from the early operand (as `hi` and\n");
		log("`hi + 1`) and selected by that carry through a single mux. This moves the wide\n");
		log("carry propagation onto the early operand, so the late operand only sees a\n");
		log("small add plus one mux instead of a full-width ripple carry.\n");
		log("\n");
		log("Only unsigned adders whose narrow operand arrives later (per a heuristic\n");
		log("logic-depth model) than the wide operand are rewritten, so adders that would\n");
		log("not benefit are left untouched. Emitted cells are tagged so peepopt -muxorder\n");
		log("does not fold the carry-select back into a late-carry ripple adder.\n");
		log("\n");
		log("    -max-narrow N\n");
		log("        only rewrite when the narrow operand width is <= N (default 16).\n");
		log("\n");
		log("    -min-wide N\n");
		log("        only rewrite when the wide (high) part width is >= N (default 8).\n");
		log("\n");
		log("    -margin F\n");
		log("        require narrow_arrival > wide_arrival + F (default 0.0).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_CARRY_SELECT pass (late-operand carry-select).\n");

		int max_narrow = 16;
		int min_wide = 8;
		double margin = 0.0;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max-narrow" && argidx + 1 < args.size()) {
				max_narrow = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min-wide" && argidx + 1 < args.size()) {
				min_wide = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-margin" && argidx + 1 < args.size()) {
				margin = atof(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total = 0;
		for (auto module : design->selected_modules()) {
			OptCarrySelectWorker worker(module, max_narrow, min_wide, margin);
			worker.run();
			total += worker.converted;
		}
		log("Converted %d adder(s) to carry-select form.\n", total);
	}
} OptCarrySelectPass;

PRIVATE_NAMESPACE_END
