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
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_add [-try] gold_sig gate_sig\n");
		log("\n");
		log("This command adds an $equiv cell for the specified signals.\n");
		log("\n");
		log("\n");
		log("    equiv_add [-try] -cell gold_cell gate_cell\n");
		log("\n");
		log("This command adds $equiv cells for the ports of the specified cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, Design *design) YS_OVERRIDE
	{
		bool try_mode = false;

		if (design->selected_active_module.empty())
			log_cmd_error("This command must be executed in module context!\n");

		Module *module = design->module(design->selected_active_module);
		log_assert(module != nullptr);

		if (GetSize(args) > 1 && args[1] == "-try") {
			args.erase(args.begin() + 1);
			try_mode = true;
		}

		if (GetSize(args) == 4 && args[1] == "-cell")
		{
			Cell *gold_cell = module->cell(RTLIL::escape_id(args[2]));
			Cell *gate_cell = module->cell(RTLIL::escape_id(args[3]));

			if (gold_cell == nullptr) {
				if (try_mode) {
					log_warning("Can't find gold cell '%s'.\n", args[2].c_str());
					return;
				}
				log_cmd_error("Can't find gold cell '%s'.\n", args[2].c_str());
			}

			if (gate_cell == nullptr) {
				if (try_mode) {
					log_warning("Can't find gate cell '%s'.\n", args[3].c_str());
					return;
				}
				log_cmd_error("Can't find gate cell '%s'.\n", args[3].c_str());
			}

			for (auto conn : gold_cell->connections())
			{
				auto port = conn.first;
				SigSpec gold_sig = gold_cell->getPort(port);
				SigSpec gate_sig = gate_cell->getPort(port);
				int width = min(GetSize(gold_sig), GetSize(gate_sig));

				if (gold_cell->input(port) && gate_cell->input(port))
				{
					SigSpec combined_sig = module->addWire(NEW_ID, width);

					for (int i = 0; i < width; i++) {
						module->addEquiv(NEW_ID, gold_sig[i], gate_sig[i], combined_sig[i]);
						gold_sig[i] = gate_sig[i] = combined_sig[i];
					}

					gold_cell->setPort(port, gold_sig);
					gate_cell->setPort(port, gate_sig);
					continue;
				}

				if (gold_cell->output(port) && gate_cell->output(port))
				{
					SigSpec new_gold_wire = module->addWire(NEW_ID, width);
					SigSpec new_gate_wire = module->addWire(NEW_ID, width);
					SigSig gg_conn;

					for (int i = 0; i < width; i++) {
						module->addEquiv(NEW_ID, new_gold_wire[i], new_gold_wire[i], gold_sig[i]);
						gg_conn.first.append(gate_sig[i]);
						gg_conn.second.append(gold_sig[i]);
						gold_sig[i] = new_gold_wire[i];
						gate_sig[i] = new_gate_wire[i];
					}

					module->connect(gg_conn);
					gold_cell->setPort(port, gold_sig);
					gate_cell->setPort(port, gate_sig);
					continue;
				}
			}
		}
		else
		{
			if (GetSize(args) != 3)
				 cmd_error(args, GetSize(args)-1, "Invalid number of arguments.");

			SigSpec gold_signal, gate_signal;

			if (!SigSpec::parse(gate_signal, module, args[2])) {
				if (try_mode) {
					log_warning("Error in gate signal: %s\n", args[2].c_str());
					return;
				}
				log_cmd_error("Error in gate signal: %s\n", args[2].c_str());
			}

			if (!SigSpec::parse_rhs(gate_signal, gold_signal, module, args[1])) {
				if (try_mode) {
					log_warning("Error in gold signal: %s\n", args[1].c_str());
					return;
				}
				log_cmd_error("Error in gold signal: %s\n", args[1].c_str());
			}

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
	}
} EquivAddPass;

PRIVATE_NAMESPACE_END
