/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

#undef MUX_UNDEF_SEL_TO_UNDEF_RESULTS

#include "opt_status.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <set>

bool did_something;

void replace_cell(RTLIL::Module *module, RTLIL::Cell *cell, std::string info, std::string out_port, RTLIL::SigSpec out_val)
{
	RTLIL::SigSpec Y = cell->connections[out_port];
	log("Replacing %s cell `%s' (%s) in module `%s' with constant driver `%s = %s'.\n",
			cell->type.c_str(), cell->name.c_str(), info.c_str(),
			module->name.c_str(), log_signal(Y), log_signal(out_val));
	OPT_DID_SOMETHING = true;
	// ILANG_BACKEND::dump_cell(stderr, "--> ", cell);
	module->connections.push_back(RTLIL::SigSig(Y, out_val));
	module->cells.erase(cell->name);
	delete cell;
	did_something = true;
}

void replace_const_cells(RTLIL::Design *design, RTLIL::Module *module)
{
	if (!design->selected(module))
		return;

	SigMap assign_map(module);

	std::vector<RTLIL::Cell*> cells;
	cells.reserve(module->cells.size());
	for (auto &cell_it : module->cells)
		if (design->selected(module, cell_it.second))
			cells.push_back(cell_it.second);

	for (auto cell : cells)
	{
#define ACTION_DO(_p_, _s_) do { replace_cell(module, cell, input.as_string(), _p_, _s_); goto next_cell; } while (0)
#define ACTION_DO_Y(_v_) ACTION_DO("\\Y", RTLIL::SigSpec(RTLIL::State::S ## _v_))

		if (cell->type == "$_INV_") {
			RTLIL::SigSpec input = cell->connections["\\A"];
			assign_map.apply(input);
			if (input.match("1")) ACTION_DO_Y(0);
			if (input.match("0")) ACTION_DO_Y(1);
			if (input.match("*")) ACTION_DO_Y(x);
		}

		if (cell->type == "$_AND_") {
			RTLIL::SigSpec input;
			input.append(cell->connections["\\B"]);
			input.append(cell->connections["\\A"]);
			assign_map.apply(input);
			if (input.match(" 0")) ACTION_DO_Y(0);
			if (input.match("0 ")) ACTION_DO_Y(0);
			if (input.match("11")) ACTION_DO_Y(1);
			if (input.match(" *")) ACTION_DO_Y(x);
			if (input.match("* ")) ACTION_DO_Y(x);
			if (input.match(" 1")) ACTION_DO("\\Y", input.extract(1, 1));
			if (input.match("1 ")) ACTION_DO("\\Y", input.extract(0, 1));
		}

		if (cell->type == "$_OR_") {
			RTLIL::SigSpec input;
			input.append(cell->connections["\\B"]);
			input.append(cell->connections["\\A"]);
			assign_map.apply(input);
			if (input.match(" 1")) ACTION_DO_Y(1);
			if (input.match("1 ")) ACTION_DO_Y(1);
			if (input.match("00")) ACTION_DO_Y(0);
			if (input.match(" *")) ACTION_DO_Y(x);
			if (input.match("* ")) ACTION_DO_Y(x);
			if (input.match(" 0")) ACTION_DO("\\Y", input.extract(1, 1));
			if (input.match("0 ")) ACTION_DO("\\Y", input.extract(0, 1));
		}

		if (cell->type == "$_XOR_") {
			RTLIL::SigSpec input;
			input.append(cell->connections["\\B"]);
			input.append(cell->connections["\\A"]);
			assign_map.apply(input);
			if (input.match("00")) ACTION_DO_Y(0);
			if (input.match("01")) ACTION_DO_Y(1);
			if (input.match("10")) ACTION_DO_Y(1);
			if (input.match("11")) ACTION_DO_Y(0);
			if (input.match(" *")) ACTION_DO_Y(x);
			if (input.match("* ")) ACTION_DO_Y(x);
			if (input.match(" 0")) ACTION_DO("\\Y", input.extract(1, 1));
			if (input.match("0 ")) ACTION_DO("\\Y", input.extract(0, 1));
		}

		if (cell->type == "$_MUX_" ||(cell->type == "$mux" && cell->parameters["\\WIDTH"].as_int() == 1)) {
			RTLIL::SigSpec input;
			input.append(cell->connections["\\S"]);
			input.append(cell->connections["\\B"]);
			input.append(cell->connections["\\A"]);
			assign_map.apply(input);
			if (input.extract(2, 1) == input.extract(1, 1))
				ACTION_DO("\\Y", input.extract(2, 1));
			if (input.match("  0")) ACTION_DO("\\Y", input.extract(2, 1));
			if (input.match("  1")) ACTION_DO("\\Y", input.extract(1, 1));
#ifdef MUX_UNDEF_SEL_TO_UNDEF_RESULTS
			if (input.match("01 ")) ACTION_DO("\\Y", input.extract(0, 1));
			// TODO: "10 " -> replace with "!S" gate
			// TODO: "0  " -> replace with "B AND S" gate
			// TODO: " 1 " -> replace with "A OR S" gate
			// TODO: "1  " -> replace with "B OR !S" gate
			// TODO: " 0 " -> replace with "A AND !S" gate
			if (input.match("  *")) ACTION_DO_Y(x);
#endif
		}

		if (cell->type == "$eq" || cell->type == "$ne")
		{
			if (cell->parameters["\\A_WIDTH"].as_int() != cell->parameters["\\B_WIDTH"].as_int()) {
				int width = std::max(cell->parameters["\\A_WIDTH"].as_int(), cell->parameters["\\B_WIDTH"].as_int());
				cell->connections["\\A"].extend(width, cell->parameters["\\A_SIGNED"].as_bool());
				cell->connections["\\B"].extend(width, cell->parameters["\\B_SIGNED"].as_bool());
				cell->parameters["\\A_WIDTH"] = width;
				cell->parameters["\\B_WIDTH"] = width;
			}

			RTLIL::SigSpec a = cell->connections["\\A"];
			RTLIL::SigSpec b = cell->connections["\\B"];
			RTLIL::SigSpec new_a, new_b;
			a.expand(), b.expand();

			assert(a.chunks.size() == b.chunks.size());
			for (size_t i = 0; i < a.chunks.size(); i++) {
				if (a.chunks[i].wire == NULL && a.chunks[i].data.bits[0] > RTLIL::State::S1)
					continue;
				if (b.chunks[i].wire == NULL && b.chunks[i].data.bits[0] > RTLIL::State::S1)
					continue;
				new_a.append(a.chunks[i]);
				new_b.append(b.chunks[i]);
			}

			if (new_a.width != a.width) {
				new_a.optimize();
				new_b.optimize();
				cell->connections["\\A"] = new_a;
				cell->connections["\\B"] = new_b;
				cell->parameters["\\A_WIDTH"] = new_a.width;
				cell->parameters["\\B_WIDTH"] = new_b.width;
			}

			if (new_a.width == 0) {
				replace_cell(module, cell, "empty", "\\Y", RTLIL::SigSpec(cell->type == "$eq" ? RTLIL::State::S1 : RTLIL::State::S0));
				goto next_cell;
			}
		}

#define FOLD_1ARG_CELL(_t) \
		if (cell->type == "$" #_t) { \
			RTLIL::SigSpec a = cell->connections["\\A"]; \
			assign_map.apply(a); \
			if (a.is_fully_const()) { \
				a.optimize(); \
				RTLIL::Const dummy_arg(RTLIL::State::S0, 1); \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.chunks[0].data, dummy_arg, \
						cell->parameters["\\A_SIGNED"].as_bool(), false, \
						cell->parameters["\\Y_WIDTH"].as_int())); \
				replace_cell(module, cell, stringf("%s", log_signal(a)), "\\Y", y); \
				goto next_cell; \
			} \
		}
#define FOLD_2ARG_CELL(_t) \
		if (cell->type == "$" #_t) { \
			RTLIL::SigSpec a = cell->connections["\\A"]; \
			RTLIL::SigSpec b = cell->connections["\\B"]; \
			assign_map.apply(a), assign_map.apply(b); \
			if (a.is_fully_const() && b.is_fully_const()) { \
				a.optimize(), b.optimize(); \
				RTLIL::SigSpec y(RTLIL::const_ ## _t(a.chunks[0].data, b.chunks[0].data, \
						cell->parameters["\\A_SIGNED"].as_bool(), \
						cell->parameters["\\B_SIGNED"].as_bool(), \
						cell->parameters["\\Y_WIDTH"].as_int())); \
				replace_cell(module, cell, stringf("%s, %s", log_signal(a), log_signal(b)), "\\Y", y); \
				goto next_cell; \
			} \
		}

		FOLD_1ARG_CELL(not)
		FOLD_2ARG_CELL(and)
		FOLD_2ARG_CELL(or)
		FOLD_2ARG_CELL(xor)
		FOLD_2ARG_CELL(xnor)

		FOLD_1ARG_CELL(reduce_and)
		FOLD_1ARG_CELL(reduce_or)
		FOLD_1ARG_CELL(reduce_xor)
		FOLD_1ARG_CELL(reduce_xnor)
		FOLD_1ARG_CELL(reduce_bool)

		FOLD_1ARG_CELL(logic_not)
		FOLD_2ARG_CELL(logic_and)
		FOLD_2ARG_CELL(logic_or)

		FOLD_2ARG_CELL(shl)
		FOLD_2ARG_CELL(shr)
		FOLD_2ARG_CELL(sshl)
		FOLD_2ARG_CELL(sshr)

		FOLD_2ARG_CELL(lt)
		FOLD_2ARG_CELL(le)
		FOLD_2ARG_CELL(eq)
		FOLD_2ARG_CELL(ne)
		FOLD_2ARG_CELL(gt)
		FOLD_2ARG_CELL(ge)

		FOLD_2ARG_CELL(add)
		FOLD_2ARG_CELL(sub)
		FOLD_2ARG_CELL(mul)
		FOLD_2ARG_CELL(div)
		FOLD_2ARG_CELL(mod)
		FOLD_2ARG_CELL(pow)

		FOLD_1ARG_CELL(pos)
		FOLD_1ARG_CELL(neg)

		if (cell->type == "$mux") {
			RTLIL::SigSpec input = cell->connections["\\S"];
			assign_map.apply(input);
			if (input.is_fully_const())
				ACTION_DO("\\Y", input.as_bool() ? cell->connections["\\B"] : cell->connections["\\A"]);
		}

	next_cell:;
#undef ACTION_DO
#undef ACTION_DO_Y
#undef FOLD_1ARG_CELL
#undef FOLD_2ARG_CELL
	}
}

struct OptConstPass : public Pass {
	OptConstPass() : Pass("opt_const", "perform const folding") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_const [selection]\n");
		log("\n");
		log("This pass performs const folding on internal cell types with constant inputs.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing OPT_CONST pass (perform const folding).\n");
		log_push();

		extra_args(args, 1, design);

		for (auto &mod_it : design->modules)
			do {
				did_something = false;
				replace_const_cells(design, mod_it.second);
			} while (did_something);

		log_pop();
	}
} OptConstPass;

