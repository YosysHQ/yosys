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

// Cap on the flattened select width, so `1 << width` and the emitted port stay sane.
static const int MAX_SEL_BITS = 24;

struct OptBmuxNestWorker {
	Module *module;
	SigMap sigmap;
	int max_entries;
	int flattened = 0;

	dict<SigBit, Cell *> bit_drivers;
	// Cells reading each bit, plus a poison entry for bits a cell cannot claim
	// exclusively (module output, keep, or a module-level connection).
	dict<SigBit, pool<Cell *>> readers;
	pool<SigBit> escaped;

	OptBmuxNestWorker(Module *m, int max_entries) : module(m), sigmap(m), max_entries(max_entries) {}

	void index()
	{
		bit_drivers.clear();
		readers.clear();
		escaped.clear();
		for (auto cell : module->cells())
			for (auto &conn : cell->connections())
				if (cell->output(conn.first)) {
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							bit_drivers[bit] = cell;
				} else {
					for (auto bit : sigmap(conn.second))
						if (bit.wire)
							readers[bit].insert(cell);
				}
		for (auto &conn : module->connections())
			for (auto bit : sigmap(conn.second))
				escaped.insert(bit);
		for (auto wire : module->wires())
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (auto bit : sigmap(SigSpec(wire)))
					escaped.insert(bit);
	}

	// One outer $bmux and the inner row selects tiling its table.
	struct Nest {
		Cell *outer;
		std::vector<Cell *> inner; // 1 << lo of them, in element order
		SigSpec hi_sel;
		int w, lo, hi;
	};

	// An outer $bmux whose every table element is the whole Y of an inner $bmux,
	// with all inner cells sharing one select, computes tbl[hi_sel][lo_sel]. That
	// is one flat $bmux over the concatenated table, selected by {hi_sel, lo_sel}:
	// the outer picks a column and each inner picks a row, so the flat entry index
	// is exactly (row << lo) | column. RTL reaches this shape by declaring a FIFO
	// as rows-of-words and splitting a flat pointer into row and column fields.
	bool match(Cell *outer, Nest &n)
	{
		// The rewrite retires the outer, so a kept outer is off limits.
		if (outer->get_bool_attribute(ID::keep))
			return false;
		int w = outer->getParam(ID::WIDTH).as_int();
		int lo = outer->getParam(ID::S_WIDTH).as_int();
		if (w < 1 || lo < 1 || lo > MAX_SEL_BITS)
			return false;
		SigSpec a = sigmap(outer->getPort(ID::A));
		int elems = 1 << lo;
		if (GetSize(a) != w * elems)
			return false;

		std::vector<Cell *> inner;
		inner.reserve(elems);
		SigSpec hi_sel;
		int hi = -1;

		for (int c = 0; c < elems; c++) {
			SigSpec chunk = a.extract(c * w, w);
			if (!chunk[0].wire)
				return false;
			Cell *in = bit_drivers.at(chunk[0], nullptr);
			if (!in || in == outer || in->type != ID($bmux))
				return false;
			// Must be the inner's whole result in order: a partial or permuted
			// read of it is not a row select.
			if (sigmap(in->getPort(ID::Y)) != chunk)
				return false;
			if (in->getParam(ID::WIDTH).as_int() != w)
				return false;
			int ihi = in->getParam(ID::S_WIDTH).as_int();
			if (hi < 0) {
				hi = ihi;
				if (hi < 1 || hi + lo > MAX_SEL_BITS || (1 << (hi + lo)) > max_entries)
					return false;
				hi_sel = sigmap(in->getPort(ID::S));
			} else if (ihi != hi || sigmap(in->getPort(ID::S)) != hi_sel) {
				return false;
			}
			if (GetSize(sigmap(in->getPort(ID::A))) != w * (1 << hi))
				return false;
			// Only fold when this outer is the inner's sole consumer. Otherwise
			// the inner survives and we pay its mux tree plus the wider flat one,
			// which is strictly worse than the nest we started from. A kept inner
			// survives opt_clean for the same reason, so it counts as a consumer.
			if (in->get_bool_attribute(ID::keep))
				return false;
			for (auto bit : chunk)
				if (escaped.count(bit) || !readers.count(bit) ||
				    readers.at(bit).size() != 1)
					return false;
			inner.push_back(in);
		}

		n = Nest{outer, inner, hi_sel, w, lo, hi};
		return true;
	}

	void flatten(const Nest &n)
	{
		// Entry (r << lo | c) is inner[c]'s row r. SigSpec appends at the high
		// end, so appending c-major within r-major lands each entry at its index.
		SigSpec table;
		for (int r = 0; r < (1 << n.hi); r++)
			for (int c = 0; c < (1 << n.lo); c++)
				table.append(sigmap(n.inner[c]->getPort(ID::A)).extract(r * n.w, n.w));

		SigSpec sel = sigmap(n.outer->getPort(ID::S));
		sel.append(n.hi_sel);

		Cell *flat = module->addBmux(NEW_ID, table, sel, n.outer->getPort(ID::Y));
		flat->attributes = n.outer->attributes;
		module->remove(n.outer);
		flattened++;
	}

	void run()
	{
		// Deeper nests need more than one round: an outer whose inner is itself
		// an outer is deferred below, and becomes matchable once that inner has
		// collapsed. Rounds are bounded by the nesting depth.
		for (int round = 0; round < MAX_SEL_BITS; round++) {
			index();

			std::vector<Nest> plans;
			pool<Cell *> outers;
			for (auto cell : module->selected_cells())
				if (cell->type == ID($bmux)) {
					Nest n;
					if (match(cell, n)) {
						plans.push_back(n);
						outers.insert(cell);
					}
				}

			int applied = 0;
			for (auto &n : plans) {
				// Flattening reads each inner's table, so an inner that another
				// plan is about to remove has to wait for the next round.
				bool blocked = false;
				for (auto in : n.inner)
					if (outers.count(in))
						blocked = true;
				if (blocked)
					continue;
				flatten(n);
				applied++;
			}
			if (!applied)
				break;
		}
	}
};

struct OptBmuxNestPass : public Pass {
	OptBmuxNestPass() : Pass("opt_bmux_nest", "flatten nested $bmux row/column selects") {}

	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_bmux_nest [options] [selection]\n");
		log("\n");
		log("Collapses a two-level $bmux select into one flat $bmux. An outer $bmux whose\n");
		log("every table element is the whole Y of an inner $bmux, with all inner cells\n");
		log("sharing one select, reads tbl[inner_sel][outer_sel]; that is a single $bmux\n");
		log("over the concatenated table selected by {inner_sel, outer_sel}.\n");
		log("\n");
		log("RTL reaches this shape by declaring a memory as rows-of-words and indexing it\n");
		log("with the two halves of a flat pointer, `mem[p[hi]][p[lo]]`. Verific lowers that\n");
		log("per lane as one row select per column plus one column select, so every lane ends\n");
		log("up with a private row-selected table. That is what makes the rewrite worth\n");
		log("doing beyond the cell count: opt_vps' uniform-gather folding groups candidates\n");
		log("by their table, so a private table per lane leaves every group a singleton and\n");
		log("a sliding window that should be one barrel shift folds not at all.\n");
		log("\n");
		log("The emitted mux tree is the same size as the nest's (a balanced select over\n");
		log("2^(hi+lo) entries costs the same however it is decomposed) and the table holds\n");
		log("the same bits, so this never grows the design. It does dedup the per-cell\n");
		log("one-hot decode that bmuxmap -pmux would otherwise emit once per inner cell.\n");
		log("\n");
		log("Only folds when the outer is each inner's sole consumer: a shared inner would\n");
		log("survive the rewrite, costing its mux tree plus the wider flat one.\n");
		log("\n");
		log("    -max-entries N\n");
		log("        skip nests whose flattened table would exceed N entries\n");
		log("        (default 65536).\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing OPT_BMUX_NEST pass (flatten nested $bmux selects).\n");

		int max_entries = 65536;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-max-entries" && argidx + 1 < args.size()) {
				max_entries = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		int total = 0;
		for (auto module : design->selected_modules()) {
			OptBmuxNestWorker worker(module, max_entries);
			worker.run();
			if (worker.flattened)
				log("Module %s: flattened %d nested $bmux select(s).\n",
				    log_id(module), worker.flattened);
			total += worker.flattened;
		}
		log("Flattened %d nested $bmux select(s).\n", total);
	}
} OptBmuxNestPass;

PRIVATE_NAMESPACE_END
