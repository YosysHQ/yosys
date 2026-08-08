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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// opt_mux_odc: fold a mux select into its own data cone.
//
// A mux arm is only observable for one value of the select, so anything inside
// that arm's cone which the select already forces to a constant may be replaced
// by that constant. The shape this targets is a control signal that ORs in the
// very select that gates it:
//
//     wire hit  = valid | (fmt == A) | (fmt == B) | ...;   // valid forces hit
//     wire [1:0] res = hit ? f(x) : g(x);                  // deep cone
//     assign out = valid ? res : bypass;                   // arm gated by valid
//
// Under `valid` the OR is 1, so the whole `fmt` decode ahead of it is dead
// weight on the path -- but only along the arm, which is why plain constant
// propagation cannot do this. Folding it deletes the decode from the cone
// (usually shrinking area too, since the classifier disappears).
//
// Soundness rests on two conditions, both checked before rewriting:
//
//   1. Implication. The select must force the signal structurally: an OR whose
//      inputs include the select (forced to 1 when the select is 1), or the
//      dual AND (forced to 0 when the select is 0). No SAT, no don't-care
//      guessing -- just the gate's own truth table.
//
//   2. Exclusivity. Everything reachable forward from the folded signal must
//      terminate in this mux's arm. If any of it escapes -- to a module output,
//      to a cell outside the arm's cone, or to the mux's own select or opposite
//      arm -- the value is observed under the other select value too and the
//      fold would be wrong. This pass never duplicates a cone to buy
//      exclusivity, so a rewrite can only ever remove logic.
//
//   3. Combinational reach. The path from the folded signal to the arm must
//      cross only combinational cells. A flip-flop or latch on it would capture
//      the forced value during a cycle when the arm is not selected and replay
//      it on a later cycle when it is, which the argument above does not cover:
//      it only says the arm's value is irrelevant *in the same instant*. A
//      submodule instance counts as combinational only if it, and everything it
//      instantiates, is -- hierarchy is common here since opt_boundary keeps it.
//
// The rewrite is an observability don't-care: gold and gate genuinely differ on
// internal nodes (that is the point), so `-strict` disables the pass for the
// formal flow, the same way opt_argmax's learned-table mode is gated.

struct OptMuxOdcWorker
{
	Module *module;
	SigMap sigmap;
	CellTypes ct;

	// Index over the module, rebuilt once per run(). The index deliberately
	// covers *all* cells, not just selected ones: escape analysis is only sound
	// if it can see every reader. Only the rewrite honours the selection.
	dict<SigBit, Cell *> drivers;
	dict<SigBit, pool<Cell *>> readers;
	pool<SigBit> escape_bits; // bits leaving through a module output port
	pool<Cell *> selected;    // cells this invocation is allowed to touch

	int regions = 0;
	int cells_removed = 0;

	// Tunables (see Pass::execute).
	int max_cone_cells = 100000;
	int max_hier_depth = 16;

	OptMuxOdcWorker(Module *module) : module(module), sigmap(module)
	{
		ct.setup(module->design);
	}

	// An empty fallback for readers.at() has to outlive the range-for that
	// walks it, since dict::at(key, defval) hands back a reference to defval.
	static const pool<Cell *> no_readers;

	void index()
	{
		for (auto cell : module->cells())
			for (auto &conn : cell->connections()) {
				bool is_out = cell->output(conn.first);
				for (auto bit : sigmap(conn.second)) {
					if (is_out)
						drivers[bit] = cell;
					else
						readers[bit].insert(cell);
				}
			}

		for (auto wire : module->wires())
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					escape_bits.insert(bit);

		for (auto cell : module->selected_cells())
			selected.insert(cell);
	}

	// Memoized: may the forward walk cross this cell type without leaving the
	// instant the select justified? Builtins are trusted to the cell table;
	// a submodule qualifies only if everything inside it does too.
	dict<IdString, bool> comb_cache;

	bool type_is_combinational(IdString type, int depth = 0)
	{
		auto it = comb_cache.find(type);
		if (it != comb_cache.end())
			return it->second;
		if (depth > max_hier_depth)
			return false;

		Module *sub = module->design->module(type);
		bool result;
		if (sub == nullptr)
			result = ct.cell_evaluable(type);
		else if (sub->get_blackbox_attribute())
			result = false; // contents unknown, so assume it can hold state
		else {
			comb_cache[type] = false; // breaks recursive hierarchies
			result = true;
			for (auto sub_cell : sub->cells())
				if (!type_is_combinational(sub_cell->type, depth + 1)) {
					result = false;
					break;
				}
		}
		comb_cache[type] = result;
		return result;
	}

	// Cells feeding `sig`, bounded so a pathological cone cannot stall the pass.
	bool backward_cone(const SigSpec &sig, pool<Cell *> &cone)
	{
		std::vector<SigBit> stack = sigmap(sig).bits();
		pool<SigBit> seen;
		while (!stack.empty()) {
			SigBit bit = stack.back();
			stack.pop_back();
			if (!seen.insert(bit).second)
				continue;
			auto it = drivers.find(bit);
			if (it == drivers.end())
				continue;
			Cell *drv = it->second;
			if (!cone.insert(drv).second)
				continue;
			if (GetSize(cone) > max_cone_cells)
				return false;
			for (auto &conn : drv->connections())
				if (!drv->output(conn.first))
					for (auto in_bit : sigmap(conn.second))
						stack.push_back(in_bit);
		}
		return true;
	}

	// True when anything reachable forward from `start` is observed outside
	// `mux`'s `arm` port -- see condition 2 in the header comment.
	bool escapes(Cell *start, Cell *mux, const pool<Cell *> &cone, const pool<SigBit> &arm_bits,
	             const pool<SigBit> &guard_bits)
	{
		std::vector<Cell *> stack = {start};
		pool<Cell *> seen;
		while (!stack.empty()) {
			Cell *cell = stack.back();
			stack.pop_back();
			if (!seen.insert(cell).second)
				continue;
			for (auto &conn : cell->connections()) {
				if (!cell->output(conn.first))
					continue;
				for (auto bit : sigmap(conn.second)) {
					if (escape_bits.count(bit))
						return true;
					// Reaching the select or the opposite arm would change the
					// value the mux produces under the other select value.
					if (guard_bits.count(bit))
						return true;
					for (auto reader : readers.at(bit, no_readers)) {
						if (reader == mux) {
							// Only the arm we are specializing may consume it.
							if (!arm_bits.count(bit))
								return true;
							continue;
						}
						if (!cone.count(reader))
							return true;
						// A state element here would hold the forced value past
						// the cycle whose select justified it -- see condition 3.
						if (!type_is_combinational(reader->type))
							return true;
						stack.push_back(reader);
					}
				}
			}
		}
		return false;
	}

	// Input bits that on their own decide the output, per the gate's truth table.
	// Being an input is not enough: a bitwise $or may have wide operands but a
	// 1-bit result, in which case only bit 0 of each operand is even read.
	void controlling_bits(Cell *cell, std::vector<SigBit> &out)
	{
		IdString type = cell->type;
		for (auto &conn : cell->connections()) {
			if (cell->output(conn.first))
				continue;
			SigSpec in = sigmap(conn.second);
			if (GetSize(in) == 0)
				continue;
			if (type.in(ID($or), ID($and), ID($_OR_), ID($_AND_)))
				out.push_back(in[0]);
			else if (type.in(ID($reduce_or), ID($reduce_and), ID($logic_or)))
				// Any one bit settles an OR/AND reduction or a nonzero test.
				for (auto bit : in)
					out.push_back(bit);
			else if (type == ID($logic_and))
				// Needs a whole operand to be zero, so only a 1-bit one counts.
				if (GetSize(in) == 1)
					out.push_back(in[0]);
		}
	}

	// The gate's own truth table must force the output, given `sel` at `value`.
	bool forces_output(Cell *cell, SigBit sel, bool value)
	{
		IdString type = cell->type;
		bool or_shaped = type.in(ID($or), ID($_OR_), ID($reduce_or), ID($logic_or));
		bool and_shaped = type.in(ID($and), ID($_AND_), ID($reduce_and), ID($logic_and));
		if (!(or_shaped || and_shaped))
			return false;
		// An OR pins high on a 1 input; an AND pins low on a 0 input.
		if (value != or_shaped)
			return false;
		// Restrict to single-bit results so the whole output can be replaced;
		// forcing one bit of a wide bitwise op would need the cell split first.
		if (GetSize(sigmap(cell->getPort(ID::Y))) != 1)
			return false;
		std::vector<SigBit> ctrl;
		controlling_bits(cell, ctrl);
		for (auto bit : ctrl)
			if (bit == sel)
				return true;
		return false;
	}

	void run()
	{
		index();

		// Snapshot the mux list: the rewrite deletes cells as it goes.
		std::vector<Cell *> muxes;
		for (auto cell : module->selected_cells())
			if (cell->type.in(ID($mux), ID($_MUX_)))
				muxes.push_back(cell);

		for (auto mux : muxes) {
			SigSpec sel_sig = sigmap(mux->getPort(ID::S));
			if (GetSize(sel_sig) != 1 || !sel_sig[0].is_wire())
				continue;
			SigBit sel = sel_sig[0];

			// $mux drives B when S is 1 and A when S is 0.
			for (int arm = 0; arm < 2; arm++) {
				IdString arm_port = arm ? ID::B : ID::A;
				IdString other_port = arm ? ID::A : ID::B;
				bool value = arm != 0;

				SigSpec arm_sig = sigmap(mux->getPort(arm_port));
				pool<Cell *> cone;
				if (!backward_cone(arm_sig, cone))
					continue;

				pool<SigBit> arm_bits;
				for (auto bit : arm_sig)
					arm_bits.insert(bit);
				pool<SigBit> guard_bits;
				guard_bits.insert(sel);
				for (auto bit : sigmap(mux->getPort(other_port)))
					guard_bits.insert(bit);

				for (auto cell : cone) {
					// The cone spans the whole module, so a partial selection
					// must not have its unselected cells rewritten.
					if (!selected.count(cell) || !forces_output(cell, sel, value))
						continue;
					if (escapes(cell, mux, cone, arm_bits, guard_bits))
						continue;

					SigSpec y = sigmap(cell->getPort(ID::Y));
					log("  %s: forcing %s (%s) to %d under select %s\n",
					    log_id(module), log_id(cell), log_id(cell->type), value ? 1 : 0,
					    log_signal(sel));
					// Drop the driver first; the wire is then free to take the
					// constant that the select already implies along this arm.
					module->remove(cell);
					module->connect(y, value ? State::S1 : State::S0);
					regions++;
					cells_removed++;
					// The index now describes a cell that is gone, so stop
					// touching this module and let the caller re-run us.
					return;
				}
			}
		}
	}
};

const pool<Cell *> OptMuxOdcWorker::no_readers;

struct OptMuxOdcPass : public Pass {
	OptMuxOdcPass() : Pass("opt_mux_odc", "fold a mux select into its own data cone") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_mux_odc [options] [selection]\n");
		log("\n");
		log("Fold a mux select into the cone of its own data arm. A mux arm only matters\n");
		log("for one value of the select, so a signal that the select structurally forces\n");
		log("to a constant -- an OR that takes the select as an input, or the dual AND --\n");
		log("can be replaced by that constant along the arm. This deletes control logic\n");
		log("(typically a decode or classifier) that is redundant once the select is known.\n");
		log("\n");
		log("The fold is only applied when everything reachable from the forced signal\n");
		log("terminates in that arm, so the pass never duplicates logic and can only\n");
		log("shrink the design.\n");
		log("\n");
		log("    -strict\n");
		log("        disable the rewrite. It is an observability don't-care, so gold and\n");
		log("        gate diverge on internal nodes and a node-matching equivalence check\n");
		log("        cannot confirm it.\n");
		log("\n");
		log("    -max-cone-cells N\n");
		log("        skip an arm whose cone exceeds N cells (default 100000).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_MUX_ODC pass (fold mux select into its data cone).\n");

		bool strict = false;
		int max_cone_cells = 100000;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-strict") {
				strict = true;
				continue;
			}
			if ((args[argidx] == "-max-cone-cells" || args[argidx] == "-max_cone_cells") &&
			    argidx + 1 < args.size()) {
				max_cone_cells = std::stoi(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total_regions = 0, total_removed = 0;
		if (!strict)
			for (auto module : design->selected_modules()) {
				// Each fold invalidates the index, so re-run until a pass over
				// the module finds nothing left to do.
				while (true) {
					OptMuxOdcWorker worker(module);
					worker.max_cone_cells = max_cone_cells;
					worker.run();
					if (!worker.regions)
						break;
					total_regions += worker.regions;
					total_removed += worker.cells_removed;
				}
			}

		log("Rewrote %d mux observability region(s); removed %d cell(s).\n",
		    total_regions, total_removed);

		if (total_regions)
			Yosys::run_pass("opt_expr -full");
	}
} OptMuxOdcPass;

PRIVATE_NAMESPACE_END
