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

struct EquivAddPass : public Pass {
	EquivAddPass() : Pass("equiv_add", "add a $equiv cell") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_add gold_sig gate_sig\n");
		log("\n");
		log("This command adds an $equiv cell for the specified signals.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, Design *design)
	{
		if (GetSize(args) != 3)
			 cmd_error(args, GetSize(args)-1, "Invalid number of arguments.");

		if (design->selected_active_module.empty())
			log_cmd_error("This command must be executed in module context!\n");

		Module *module = design->module(design->selected_active_module);
		log_assert(module != nullptr);

		SigSpec gold_signal, gate_signal;

		if (!SigSpec::parse(gate_signal, module, args[2]))
			log_cmd_error("Error in gate signal: %s\n", args[2].c_str());

		if (!SigSpec::parse_rhs(gate_signal, gold_signal, module, args[1]))
			log_cmd_error("Error in gold signal: %s\n", args[1].c_str());

		log_assert(GetSize(gold_signal) == GetSize(gate_signal));
		SigSpec equiv_signal = module->addWire(NEW_ID, GetSize(gold_signal));

		SigMap sigmap(module);
		sigmap.apply(gold_signal);
		sigmap.apply(gate_signal);

		dict<SigBit, SigBit> to_equiv_bits;
		pool<Cell*> added_equiv_cells;

		for (int i = 0; i < GetSize(gold_signal); i++) {
			Cell *equiv_cell = module->addEquiv(NEW_ID, gold_signal[i], gate_signal[i], equiv_signal[i]);
			equiv_cell->set_bool_attribute("\\keep");
			to_equiv_bits[gold_signal[i]] = equiv_signal[i];
			to_equiv_bits[gate_signal[i]] = equiv_signal[i];
			added_equiv_cells.insert(equiv_cell);
		}

		for (auto cell : module->cells())
		for (auto conn : cell->connections())
			if (!added_equiv_cells.count(cell) && cell->input(conn.first)) {
				SigSpec new_sig;
				for (auto bit : conn.second)
					if (to_equiv_bits.count(sigmap(bit)))
						new_sig.append(to_equiv_bits.at(sigmap(bit)));
					else
						 new_sig.append(bit);
				if (conn.second != new_sig)
					cell->setPort(conn.first, new_sig);
			}
	}
} EquivAddPass;

PRIVATE_NAMESPACE_END
