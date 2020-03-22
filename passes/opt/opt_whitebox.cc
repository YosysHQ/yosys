/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Wolf <claire@symbioticeda.com>
 *  Copyright (C) 2020  David Shah <dave@ds0.me>
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
#include "kernel/consteval.h"
#include "kernel/celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptWhiteboxWorker {
	Design *design;
	CellTypes ct_all;
	OptWhiteboxWorker(Design *design) : design(design) {};

	struct OptimisedTable {
		static OptimisedTable constant(bool value)
		{
			OptimisedTable result;
			result.is_constant = true;
			result.constval = value;
			return result;
		}
		static OptimisedTable wire(int input)
		{
			OptimisedTable result;
			result.is_wire = true;
			result.wire_input = input;
			return result;
		}
		static OptimisedTable none()
		{
			return {};
		}
		bool is_constant = false, constval = false;
		bool is_wire = false;
		int wire_input = -1;
	};

	struct TruthTable
	{
		int input_count;
		std::vector<bool> table;
		bool found_undef = false;
		OptimisedTable optimise()
		{
			bool all_one = true, all_zero = true;
			std::vector<bool> is_wire(input_count, true);
			for (int i = 0; i < GetSize(table); i++)
			{
				if (table[i])
					all_zero = false;
				if (!table[i])
					all_one = false;
				for (int j = 0; j < input_count; j++)
					if (table[i] != ((i >> j) & 0x1))
						is_wire[j] = false;
			}
			if (all_zero)
				return OptimisedTable::constant(false);
			if (all_one)
				return OptimisedTable::constant(true);
			for (int i = 0; i < GetSize(is_wire); i++)
				if (is_wire[i])
					return OptimisedTable::wire(i);
			return OptimisedTable::none();
		}
	};

	void disconnect_port_bit(Cell *cell, SigMap &sigmap, IdString port, int bit)
	{
		auto orig = sigmap(cell->getPort(port));
		SigSpec rewritten;
		for (int i = 0; i < GetSize(orig); i++) {
			if (i == bit) {
				RTLIL::Wire *dummy_wire = cell->module->addWire(NEW_ID, 1);
				rewritten.append_bit(SigBit(dummy_wire, 0));
			} else {
				rewritten.append_bit(orig[i]);
			}
		}
		cell->setPort(port, rewritten);
	}

	void operator()() {
		pool<IdString> processed_derivations;
		ct_all.setup(design);
		for (auto module : design->selected_modules())
		{
			log("Optimizing whiteboxes in %s.\n", log_id(module));
			bool did_something = true;
			while (did_something) {
				SigMap module_sigmap(module);
				did_something = false;
				std::vector<Cell *> remove_cells;
				pool<SigBit> used_sigbits;
				for (auto wire : module->wires()) {
					if (wire->port_output || wire->get_bool_attribute(ID::keep)) {
						for (auto bit : SigSpec(wire))
							used_sigbits.insert(module_sigmap(bit));
					}
				}

				for (auto cell : module->cells()) {
					for (auto &c : cell->connections()) {
						if (ct_all.cell_known(cell->type) && !ct_all.cell_input(cell->type, c.first))
							continue;
						for (auto bit : module_sigmap(c.second))
							used_sigbits.insert(bit);
					}
				}
				// Find boxes
				for (auto cell : module->selected_cells()) {
					if (cell->get_bool_attribute(ID::keep))
						continue;
					RTLIL::Module* orig_box_module = module->design->module(cell->type);
					if (!orig_box_module || !orig_box_module->get_bool_attribute(ID(whitebox)))
						continue;
					IdString derived_name = orig_box_module->derive(module->design, cell->parameters);
					RTLIL::Module* box = module->design->module(derived_name);
					if (!processed_derivations.count(derived_name)) {
						Pass::call_on_module(box->design, box, "proc");
						processed_derivations.insert(derived_name);
					}
					log("  Processing box %s: %s\n", log_id(cell), log_id(cell->module));
					SigMap box_sigmap(box);

					// Inputs externally driven by a constant
					dict<SigBit, bool> const_inputs;
					// Set of non-constant inputs, and all outputs
					std::vector<SigBit> input_vec, output_vec;
					// Input/output signals from the module perspective
					std::vector<SigBit> input_mod_vec, output_mod_vec;
					// Map module to box inputs to detect duplicates
					dict<SigBit, SigBit> mod_to_box_inp;
					dict<SigBit, std::vector<SigBit>> input_dups;

					std::vector<std::pair<IdString, int>> box_output_bits;
					auto conn = cell->connections();

					for (auto wire : box->wires()) {
						if (wire->port_output) {
							for (int i = 0; i < wire->width; i++) {
								auto pc = conn.find(wire->name);
								if (pc == conn.end() || i >= GetSize(pc->second))
									continue;
								auto modbit = module_sigmap(pc->second[i]);
								if (!used_sigbits.count(modbit))
									continue;
								output_mod_vec.push_back(pc->second[i]);
								output_vec.push_back(box_sigmap(SigBit(wire, i)));
								box_output_bits.emplace_back(wire->name, i);
							}
						}
						if (wire->port_input) {
							for (int i = 0; i < wire->width; i++) {
								auto pc = conn.find(wire->name);
								if (pc != conn.end() && (i < GetSize(pc->second))) {
									if (pc->second[i] == State::S0) {
										const_inputs[box_sigmap(SigBit(wire, i))] = false;
										continue;
									}
									if (pc->second[i] == State::S1) {
										const_inputs[box_sigmap(SigBit(wire, i))] = true;
										continue;
									}
									auto modbit = module_sigmap(pc->second[i]);
									auto fnd = mod_to_box_inp.find(modbit);
									if (fnd != mod_to_box_inp.end()) {
										// Two whitebox inputs connected together
										input_dups[fnd->second].push_back(box_sigmap(SigBit(wire, i)));
										continue;
									}
									input_mod_vec.push_back(pc->second[i]);
									mod_to_box_inp[modbit] = box_sigmap(SigBit(wire, i));
								} else {
									input_mod_vec.emplace_back(State::Sx);
								}
								input_vec.push_back(box_sigmap(SigBit(wire, i)));
							}
						}
					}
					int output_count = GetSize(output_vec);
					if (GetSize(input_vec) > 12 || GetSize(output_vec) > 12) {
						// Truth tables become unviable, skip
						log("      box has too many ports, skipping.\n");
						continue;
					}
					std::vector<TruthTable> tables(output_vec.size());
					for (size_t i = 0; i < output_vec.size(); i++) {
						tables.at(i).input_count = GetSize(input_vec);
						tables.at(i).table.resize(1 << GetSize(input_vec));
					}
					// Create truth table
					ConstEval ce(box);
					for (auto c : const_inputs)
						ce.set(c.first, c.second ? State::S1 : State::S0);
					for (int eval = 0; eval < (1 << GetSize(input_vec)); eval++) {
						ce.push();
						for (int i = 0; i < GetSize(input_vec); i++) {
							bool bit = (eval >> i) & 1;
							ce.set(input_vec.at(i), bit ? State::S1 : State::S0);
							auto dups = input_dups.find(input_vec.at(i));
							if (dups != input_dups.end()) {
								for (auto dup : dups->second)
									ce.set(dup, bit ? State::S1 : State::S0);
							}
						}
						for (int i = 0; i < GetSize(output_vec); i++) {
							if (tables.at(i).found_undef)
								continue;
							SigSpec result(output_vec.at(i));
							if (ce.eval(result)) {
								if (result == State::S1)
									tables.at(i).table.at(eval) = true;
								else if (result == State::S0)
									tables.at(i).table.at(eval) = false;
								else
									tables.at(i).found_undef = true;
							} else {
								tables.at(i).found_undef = true;
							}
						}
						ce.pop();
					}
					for (int i = 0; i < GetSize(output_vec); i++) {
						auto &tab = tables.at(i);
						if (tab.found_undef)
							continue;
						auto opt = tab.optimise();
						if (opt.is_constant) {
							log("      output '%s' is constant %d\n", log_signal(output_vec.at(i)), opt.constval);
							disconnect_port_bit(cell, module_sigmap, box_output_bits.at(i).first, box_output_bits.at(i).second);
							module->connect(output_mod_vec.at(i), opt.constval ? State::S1 : State::S0);
							--output_count;
							continue;
						}
						if (opt.is_wire) {
							log("      output '%s' equivalent to input '%s'\n", log_signal(output_vec.at(i)), log_signal(input_vec.at(opt.wire_input)));
							disconnect_port_bit(cell, module_sigmap, box_output_bits.at(i).first, box_output_bits.at(i).second);
							module->connect(output_mod_vec.at(i), input_mod_vec.at(opt.wire_input));
							--output_count;
							continue;
						}
					}
					if (output_count == 0) {
						// Cell is redundant, add to list of cells to remove
						remove_cells.push_back(cell);
					}
				}
				// Trim redundant cells
				for (auto cell : remove_cells)
					module->remove(cell);
				if (did_something)
					design->scratchpad_set_bool("opt.did_something", true);
			}
		}
	}
};

struct OptWhiteboxPass : public Pass {
	OptWhiteboxPass() : Pass("opt_whitebox", "Replace whiteboxes with constants or wires") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_whitebox [selection]\n");
		log("\n");
		log("This pass optimises whitebox outputs that can be replaced by a constant driver\n");
		log("or wire.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing OPT_WHITEBOX pass (whitebox optimisations).\n");
		string techname;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			break;
		}
		extra_args(args, argidx, design);
		OptWhiteboxWorker worker(design);
		worker();

	}
} OptWhiteboxPass;

PRIVATE_NAMESPACE_END
