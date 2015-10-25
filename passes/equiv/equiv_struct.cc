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

struct EquivStructWorker
{
	Module *module;
	SigMap sigmap;
	SigMap equiv_bits;
	bool mode_icells;
	int merge_count;

	dict<IdString, pool<IdString>> cells_by_type;

	void handle_cell_pair(Cell *cell_a, Cell *cell_b)
	{
		if (cell_a->parameters != cell_b->parameters)
			return;

		bool merge_this_cells = false;
		bool found_diff_inputs = false;
		vector<SigSpec> inputs_a, inputs_b;

		for (auto &port_a : cell_a->connections())
		{
			SigSpec bits_a = equiv_bits(port_a.second);
			SigSpec bits_b = equiv_bits(cell_b->getPort(port_a.first));

			if (GetSize(bits_a) != GetSize(bits_b))
				return;

			if (cell_a->output(port_a.first)) {
				for (int i = 0; i < GetSize(bits_a); i++)
					if (bits_a[i] == bits_b[i])
						merge_this_cells = true;
			} else {
				SigSpec diff_bits_a, diff_bits_b;
				for (int i = 0; i < GetSize(bits_a); i++)
					if (bits_a[i] != bits_b[i]) {
						diff_bits_a.append(bits_a[i]);
						diff_bits_b.append(bits_b[i]);
					}
				if (!diff_bits_a.empty()) {
					inputs_a.push_back(diff_bits_a);
					inputs_b.push_back(diff_bits_b);
					found_diff_inputs = true;
				}
			}
		}

		if (!found_diff_inputs)
			merge_this_cells = true;

		if (merge_this_cells)
		{
			SigMap merged_map;

			log("      Merging cells %s and %s.\n", log_id(cell_a),  log_id(cell_b));
			merge_count++;

			for (int i = 0; i < GetSize(inputs_a); i++) {
				SigSpec &sig_a = inputs_a[i], &sig_b = inputs_b[i];
				SigSpec sig_y = module->addWire(NEW_ID, GetSize(sig_a));
				log("        A: %s, B: %s, Y: %s\n", log_signal(sig_a),  log_signal(sig_b), log_signal(sig_y));
				module->addEquiv(NEW_ID, sig_a, sig_b, sig_y);
				merged_map.add(sig_a, sig_y);
				merged_map.add(sig_b, sig_y);
			}

			std::vector<IdString> outport_names, inport_names;

			for (auto &port_a : cell_a->connections())
				if (cell_a->output(port_a.first))
					outport_names.push_back(port_a.first);
				else
					inport_names.push_back(port_a.first);

			for (auto &pn : inport_names)
				cell_a->setPort(pn, merged_map(equiv_bits(cell_a->getPort(pn))));

			for (auto &pn : outport_names) {
				SigSpec sig_a = cell_a->getPort(pn);
				SigSpec sig_b = cell_b->getPort(pn);
				module->connect(sig_b, sig_a);
				sigmap.add(sig_b, sig_a);
				equiv_bits.add(sig_b, sig_a);
			}

			auto merged_attr = cell_b->get_strpool_attribute("\\equiv_merged");
			merged_attr.insert(log_id(cell_b));
			cell_a->add_strpool_attribute("\\equiv_merged", merged_attr);
			module->remove(cell_b);
		}
	}

	EquivStructWorker(Module *module, bool mode_icells) :
			module(module), sigmap(module), equiv_bits(module), mode_icells(mode_icells), merge_count(0)
	{
		log("  Starting new iteration.\n");

		pool<SigBit> equiv_inputs;

		for (auto cell : module->selected_cells())
			if (cell->type == "$equiv") {
				SigBit sig_a = sigmap(cell->getPort("\\A").as_bit());
				SigBit sig_b = sigmap(cell->getPort("\\B").as_bit());
				equiv_bits.add(sig_b, sig_a);
				equiv_inputs.insert(sig_a);
				equiv_inputs.insert(sig_b);
				cells_by_type[cell->type].insert(cell->name);
			} else
			if (module->design->selected(module, cell)) {
				if (mode_icells || module->design->module(cell->type))
					cells_by_type[cell->type].insert(cell->name);
			}

		for (auto cell_name : cells_by_type["$equiv"]) {
			Cell *cell = module->cell(cell_name);
			SigBit sig_a = sigmap(cell->getPort("\\A").as_bit());
			SigBit sig_b = sigmap(cell->getPort("\\B").as_bit());
			SigBit sig_y = sigmap(cell->getPort("\\Y").as_bit());
			if (sig_a == sig_b && equiv_inputs.count(sig_y)) {
				log("    Purging redundant $equiv cell %s.\n", log_id(cell));
				module->remove(cell);
				merge_count++;
			}
		}

		if (merge_count > 0)
			return;

		for (auto &it : cells_by_type)
		{
			if (it.second.size() <= 1)
				continue;

			log("    Merging %s cells..\n", log_id(it.first));

			// FIXME: O(n^2)
			for (auto cell_name_a : it.second)
			for (auto cell_name_b : it.second)
				if (cell_name_a < cell_name_b) {
					Cell *cell_a = module->cell(cell_name_a);
					Cell *cell_b = module->cell(cell_name_b);
					if (cell_a && cell_b)
						handle_cell_pair(cell_a, cell_b);
				}
		}
	}
};

struct EquivStructPass : public Pass {
	EquivStructPass() : Pass("equiv_struct", "structural equivalence checking") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    equiv_struct [options] [selection]\n");
		log("\n");
		log("This command adds additional $equiv cells based on the assumption that the\n");
		log("gold and gate circuit are structurally equivalent. Note that this can introduce\n");
		log("bad $equiv cells in cases where the netlists are not structurally equivalent,\n");
		log("for example when analyzing circuits with cells with commutative inputs. This\n");
		log("command will also de-duplicate gates.\n");
		log("\n");
		log("    -icells\n");
		log("        by default, the internal RTL and gate cell types are ignored. add\n");
		log("        this option to also process those cell types with this command.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, Design *design)
	{
		bool mode_icells = false;

		log_header("Executing EQUIV_STRUCT pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-icells") {
				mode_icells = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			log("Running equiv_struct on module %s:", log_id(module));
			while (1) {
				EquivStructWorker worker(module, mode_icells);
				if (worker.merge_count == 0)
					break;
			}
		}
	}
} EquivStructPass;

PRIVATE_NAMESPACE_END
