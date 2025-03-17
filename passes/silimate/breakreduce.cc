/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *  Copyright (C) 2025  Akash Levy <akash@silimate.com>
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

static void logic_reduce(RTLIL::Module *module, RTLIL::SigSpec &sig, RTLIL::Cell *cell)
{
	while (sig.size() > 1)
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID2_SUFFIX("t"), sig.size() / 2); // SILIMATE: Improve the naming

		for (int i = 0; i < sig.size(); i += 2)
		{
			if (i+1 == sig.size()) {
				sig_t.append(sig[i]);
				continue;
			}

			RTLIL::Cell *gate = module->addCell(NEW_ID2, ID($or)); // SILIMATE: Improve the naming
			gate->attributes = cell->attributes;
			gate->setPort(ID::A, sig[i]);
			gate->setPort(ID::B, sig[i+1]);
			gate->setPort(ID::Y, sig_t[i/2]);
			gate->fixup_parameters();
		}

		sig = sig_t;
	}

	if (sig.size() == 0)
		sig = State::S0;
}

void breakreduce(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	if (sig_y.size() == 0)
		return;

	if (sig_a.size() == 0) {
		if (cell->type == ID($reduce_and))  module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.size())));
		if (cell->type == ID($reduce_or))   module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		if (cell->type == ID($reduce_xor))  module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		if (cell->type == ID($reduce_xnor)) module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(1, sig_y.size())));
		if (cell->type == ID($reduce_bool)) module->connect(RTLIL::SigSig(sig_y, RTLIL::SigSpec(0, sig_y.size())));
		return;
	}

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	IdString gate_type;
	if (cell->type == ID($reduce_and))  gate_type = ID($and);
	if (cell->type == ID($reduce_or))   gate_type = ID($or);
	if (cell->type == ID($reduce_xor))  gate_type = ID($xor);
	if (cell->type == ID($reduce_xnor)) gate_type = ID($xor);
	if (cell->type == ID($reduce_bool)) gate_type = ID($or);
	log_assert(!gate_type.empty());

	RTLIL::Cell *last_output_cell = NULL;

	while (sig_a.size() > 1)
	{
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID2_SUFFIX("t"), sig_a.size() / 2); // SILIMATE: Improve the naming

		for (int i = 0; i < sig_a.size(); i += 2)
		{
			if (i+1 == sig_a.size()) {
				sig_t.append(sig_a[i]);
				continue;
			}

			RTLIL::Cell *gate = module->addCell(NEW_ID2, gate_type); // SILIMATE: Improve the naming
			gate->attributes = cell->attributes;
			gate->setPort(ID::A, sig_a[i]);
			gate->setPort(ID::B, sig_a[i+1]);
			gate->setPort(ID::Y, sig_t[i/2]);
			gate->fixup_parameters();
			last_output_cell = gate;
		}

		sig_a = sig_t;
	}

	if (cell->type == ID($reduce_xnor)) {
		RTLIL::SigSpec sig_t = module->addWire(NEW_ID2_SUFFIX("t")); // SILIMATE: Improve the naming
		RTLIL::Cell *gate = module->addCell(NEW_ID2, ID($not)); // SILIMATE: Improve the naming
		gate->attributes = cell->attributes;
		gate->setPort(ID::A, sig_a);
		gate->setPort(ID::Y, sig_t);
		gate->fixup_parameters();
		last_output_cell = gate;
		sig_a = sig_t;
	}

	if (last_output_cell == NULL) {
		module->connect(RTLIL::SigSig(sig_y, sig_a));
	} else {
		last_output_cell->setPort(ID::Y, sig_y);
	}

	module->remove(cell);
}

void breaklognot(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	logic_reduce(module, sig_a, cell);

	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	if (sig_y.size() == 0)
		return;

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	RTLIL::Cell *gate = module->addCell(NEW_ID2, ID($not)); // SILIMATE: Improve the naming
	gate->attributes = cell->attributes;
	gate->setPort(ID::A, sig_a);
	gate->setPort(ID::Y, sig_y);
	gate->fixup_parameters();

	module->remove(cell);
}

void breaklogbin(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	logic_reduce(module, sig_a, cell);

	RTLIL::SigSpec sig_b = cell->getPort(ID::B);
	logic_reduce(module, sig_b, cell);

	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

	if (sig_y.size() == 0)
		return;

	if (sig_y.size() > 1) {
		module->connect(RTLIL::SigSig(sig_y.extract(1, sig_y.size()-1), RTLIL::SigSpec(0, sig_y.size()-1)));
		sig_y = sig_y.extract(0, 1);
	}

	IdString gate_type;
	if (cell->type == ID($logic_and)) gate_type = ID($and);
	if (cell->type == ID($logic_or))  gate_type = ID($or);
	log_assert(!gate_type.empty());

	RTLIL::Cell *gate = module->addCell(NEW_ID2, gate_type); // SILIMATE: Improve the naming
	gate->attributes = cell->attributes;
	gate->setPort(ID::A, sig_a);
	gate->setPort(ID::B, sig_b);
	gate->setPort(ID::Y, sig_y);
	gate->fixup_parameters();

	module->remove(cell);
}

void breakeqne(RTLIL::Module *module, RTLIL::Cell *cell)
{
	RTLIL::SigSpec sig_a = cell->getPort(ID::A);
	RTLIL::SigSpec sig_b = cell->getPort(ID::B);
	RTLIL::SigSpec sig_y = cell->getPort(ID::Y);
	bool is_signed = cell->parameters.at(ID::A_SIGNED).as_bool();
	bool is_ne = cell->type.in(ID($ne), ID($nex));

	RTLIL::SigSpec xor_out = module->addWire(NEW_ID2_SUFFIX("xor"), max(GetSize(sig_a), GetSize(sig_b))); // SILIMATE: Improve the naming
	RTLIL::Cell *xor_cell = module->addXor(NEW_ID2, sig_a, sig_b, xor_out, is_signed, cell->get_src_attribute()); // SILIMATE: Improve the naming
	xor_cell->attributes = cell->attributes;

	RTLIL::SigSpec reduce_out = is_ne ? sig_y : module->addWire(NEW_ID2_SUFFIX("reduce_out")); // SILIMATE: Improve the naming
	RTLIL::Cell *reduce_cell = module->addReduceOr(NEW_ID2_SUFFIX("reduce_or"), xor_out, reduce_out, false, cell->get_src_attribute()); // SILIMATE: Improve the naming
	reduce_cell->attributes = cell->attributes;
	breakreduce(module, reduce_cell);

	if (!is_ne) {
		RTLIL::Cell *not_cell = module->addLogicNot(NEW_ID2_SUFFIX("not"), reduce_out, sig_y, false, cell->get_src_attribute()); // SILIMATE: Improve the naming
		not_cell->attributes = cell->attributes;
		breaklognot(module, not_cell);
	}

	module->remove(cell);
}

struct BreakReducePass : public Pass {
	BreakReducePass() : Pass("breakreduce", "break reduce-style cells into trees of primitives") { }
	void help() override
	{
		log("\n");
		log("    breakreduce [selection]\n");
		log("\n");
		log("Break reduce-style ($reduce_*/$logic_*/$*eq*) cells into trees of primitives.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing BREAKREDUCE pass (break reduce-style cells into trees of primitives).\n");
		extra_args(args, 1, design);

		for (auto module : design->selected_modules())
			for (auto cell : module->selected_cells())
				if (cell->type.in("$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor", "$reduce_bool"))
					breakreduce(module, cell);
				else if (cell->type.in("$logic_and", "$logic_or"))
					breaklogbin(module, cell);
				else if (cell->type.in("$logic_not"))
					breaklognot(module, cell);
				else if (cell->type.in("$eq", "$ne", "$eqx", "$nex"))
					breakeqne(module, cell);
	}
} BreakReducePass;

PRIVATE_NAMESPACE_END
