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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct AssertpmuxWorker
{
	Module *module;
	SigMap sigmap;

	bool flag_noinit;
	bool flag_always;

	// get<0> ... mux cell
	// get<1> ... mux port index
	// get<2> ... mux bit index
	dict<SigBit, pool<tuple<Cell*, int, int>>> sigbit_muxusers;

	dict<SigBit, SigBit> sigbit_actsignals;
	dict<SigSpec, SigBit> sigspec_actsignals;
	dict<tuple<Cell*, int>, SigBit> muxport_actsignal;

	AssertpmuxWorker(Module *module, bool flag_noinit, bool flag_always) :
			module(module), sigmap(module), flag_noinit(flag_noinit), flag_always(flag_always)
	{
		for (auto wire : module->wires())
		{
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					sigbit_actsignals[bit] = State::S1;
		}

		for (auto cell : module->cells())
		{
			if (cell->type.in("$mux", "$pmux"))
			{
				int width = cell->getParam("\\WIDTH").as_int();
				int numports = cell->type == "$mux" ? 2 : cell->getParam("\\S_WIDTH").as_int() + 1;

				SigSpec sig_a = sigmap(cell->getPort("\\A"));
				SigSpec sig_b = sigmap(cell->getPort("\\B"));
				SigSpec sig_s = sigmap(cell->getPort("\\S"));

				for (int i = 0; i < numports; i++) {
					SigSpec bits = i == 0 ? sig_a : sig_b.extract(width*(i-1), width);
					for (int k = 0; k < width; k++) {
						tuple<Cell*, int, int> muxuser(cell, i, k);
						sigbit_muxusers[bits[k]].insert(muxuser);
					}
				}
			}
			else
			{
				for (auto &conn : cell->connections()) {
					if (!cell->known() || cell->input(conn.first))
						for (auto bit : sigmap(conn.second))
							sigbit_actsignals[bit] = State::S1;
				}
			}
		}
	}

	SigBit get_bit_activation(SigBit bit)
	{
		sigmap.apply(bit);

		if (sigbit_actsignals.count(bit) == 0)
		{
			SigSpec output;

			for (auto muxuser : sigbit_muxusers.at(bit))
			{
				Cell *cell = std::get<0>(muxuser);
				int portidx = std::get<1>(muxuser);
				int bitidx = std::get<2>(muxuser);

				tuple<Cell*, int> muxport(cell, portidx);

				if (muxport_actsignal.count(muxport) == 0) {
					if (portidx == 0)
						muxport_actsignal[muxport] = module->LogicNot(NEW_ID, cell->getPort("\\S"));
					else
						muxport_actsignal[muxport] = cell->getPort("\\S")[portidx-1];
				}

				output.append(module->LogicAnd(NEW_ID, muxport_actsignal.at(muxport), get_bit_activation(cell->getPort("\\Y")[bitidx])));
			}

			output.sort_and_unify();

			if (GetSize(output) == 0)
				output = State::S0;
			else if (GetSize(output) > 1)
				output = module->ReduceOr(NEW_ID, output);

			sigbit_actsignals[bit] = output.as_bit();
		}

		return sigbit_actsignals.at(bit);
	}

	SigBit get_activation(SigSpec sig)
	{
		sigmap.apply(sig);
		sig.sort_and_unify();

		if (sigspec_actsignals.count(sig) == 0)
		{
			SigSpec output;

			for (auto bit : sig)
				output.append(get_bit_activation(bit));

			output.sort_and_unify();

			if (GetSize(output) == 0)
				output = State::S0;
			else if (GetSize(output) > 1)
				output = module->ReduceOr(NEW_ID, output);

			sigspec_actsignals[sig] = output.as_bit();
		}

		return sigspec_actsignals.at(sig);
	}

	void run(Cell *pmux)
	{
		log("Adding assert for $pmux cell %s.%s.\n", log_id(module), log_id(pmux));

		int swidth = pmux->getParam("\\S_WIDTH").as_int();
		int cntbits = ceil_log2(swidth+1);

		SigSpec sel = pmux->getPort("\\S");
		SigSpec cnt(State::S0, cntbits);

		for (int i = 0; i < swidth; i++)
			cnt = module->Add(NEW_ID, cnt, sel[i]);

		SigSpec assert_a = module->Le(NEW_ID, cnt, SigSpec(1, cntbits));
		SigSpec assert_en;

		if (flag_noinit)
			assert_en.append(module->LogicNot(NEW_ID, module->Initstate(NEW_ID)));

		if (!flag_always)
			assert_en.append(get_activation(pmux->getPort("\\Y")));

		if (GetSize(assert_en) == 0)
			assert_en = State::S1;

		if (GetSize(assert_en) == 2)
			assert_en = module->LogicAnd(NEW_ID, assert_en[0], assert_en[1]);

		Cell *assert_cell = module->addAssert(NEW_ID, assert_a, assert_en);

		if (pmux->attributes.count("\\src") != 0)
			assert_cell->attributes["\\src"] = pmux->attributes.at("\\src");
	}
};

struct AssertpmuxPass : public Pass {
	AssertpmuxPass() : Pass("assertpmux", "adds asserts for parallel muxes") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    assertpmux [options] [selection]\n");
		log("\n");
		log("This command adds asserts to the design that assert that all parallel muxes\n");
		log("($pmux cells) have a maximum of one of their inputs enable at any time.\n");
		log("\n");
		log("    -noinit\n");
		log("        do not enforce the pmux condition during the init state\n");
		log("\n");
		log("    -always\n");
		log("        usually the $pmux condition is only checked when the $pmux output\n");
		log("        is used by the mux tree it drives. this option will deactivate this\n");
		log("        additional constraint and check the $pmux condition always.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool flag_noinit = false;
		bool flag_always = false;

		log_header(design, "Executing ASSERTPMUX pass (add asserts for $pmux cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-noinit") {
				flag_noinit = true;
				continue;
			}
			if (args[argidx] == "-always") {
				flag_always = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			AssertpmuxWorker worker(module, flag_noinit, flag_always);
			vector<Cell*> pmux_cells;

			for (auto cell : module->selected_cells())
				if (cell->type == "$pmux")
					pmux_cells.push_back(cell);

			for (auto cell : pmux_cells)
				worker.run(cell);
		}

	}
} AssertpmuxPass;

PRIVATE_NAMESPACE_END
