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
	bool mode_fwd;
	bool mode_icells;
	int merge_count;

	const pool<IdString> &fwonly_cells;

	struct merge_key_t
	{
		IdString type;
		vector<pair<IdString, Const>> parameters;
		vector<pair<IdString, int>> port_sizes;
		vector<tuple<IdString, int, SigBit>> connections;

		bool operator==(const merge_key_t &other) const {
			return type == other.type && connections == other.connections &&
					parameters == other.parameters && port_sizes == other.port_sizes;
		}

		unsigned int hash() const {
			unsigned int h = mkhash_init;
			h = mkhash(h, mkhash(type));
			h = mkhash(h, mkhash(parameters));
			h = mkhash(h, mkhash(connections));
			return h;
		}
	};

	dict<merge_key_t, pool<IdString>> merge_cache;
	pool<merge_key_t> fwd_merge_cache, bwd_merge_cache;

	void merge_cell_pair(Cell *cell_a, Cell *cell_b)
	{
		SigMap merged_map;
		merge_count++;

		SigSpec inputs_a, inputs_b;
		vector<string> input_names;

		for (auto &port_a : cell_a->connections())
		{
			SigSpec bits_a = sigmap(port_a.second);
			SigSpec bits_b = sigmap(cell_b->getPort(port_a.first));

			log_assert(GetSize(bits_a) == GetSize(bits_b));

			if (!cell_a->output(port_a.first))
				for (int i = 0; i < GetSize(bits_a); i++)
					if (bits_a[i] != bits_b[i]) {
						inputs_a.append(bits_a[i]);
						inputs_b.append(bits_b[i]);
						input_names.push_back(GetSize(bits_a) == 1 ? port_a.first.str() :
								stringf("%s[%d]", log_id(port_a.first), i));
					}
		}

		for (int i = 0; i < GetSize(inputs_a); i++) {
			SigBit bit_a = inputs_a[i], bit_b = inputs_b[i];
			SigBit bit_y = module->addWire(NEW_ID);
			log("        New $equiv for input %s: A: %s, B: %s, Y: %s\n",
					input_names[i].c_str(), log_signal(bit_a), log_signal(bit_b), log_signal(bit_y));
			module->addEquiv(NEW_ID, bit_a, bit_b, bit_y);
			merged_map.add(bit_a, bit_y);
			merged_map.add(bit_b, bit_y);
		}

		std::vector<IdString> outport_names, inport_names;

		for (auto &port_a : cell_a->connections())
			if (cell_a->output(port_a.first))
				outport_names.push_back(port_a.first);
			else
				inport_names.push_back(port_a.first);

		for (auto &pn : inport_names)
			cell_a->setPort(pn, merged_map(sigmap(cell_a->getPort(pn))));

		for (auto &pn : outport_names) {
			SigSpec sig_a = cell_a->getPort(pn);
			SigSpec sig_b = cell_b->getPort(pn);
			module->connect(sig_b, sig_a);
		}

		auto merged_attr = cell_b->get_strpool_attribute("\\equiv_merged");
		merged_attr.insert(log_id(cell_b));
		cell_a->add_strpool_attribute("\\equiv_merged", merged_attr);
		module->remove(cell_b);
	}

	EquivStructWorker(Module *module, bool mode_fwd, bool mode_icells, const pool<IdString> &fwonly_cells, int iter_num) :
			module(module), sigmap(module), equiv_bits(module),
			mode_fwd(mode_fwd), mode_icells(mode_icells), merge_count(0), fwonly_cells(fwonly_cells)
	{
		log("  Starting iteration %d.\n", iter_num);

		pool<SigBit> equiv_inputs;
		pool<IdString> cells;

		for (auto cell : module->selected_cells())
			if (cell->type == "$equiv") {
				SigBit sig_a = sigmap(cell->getPort("\\A").as_bit());
				SigBit sig_b = sigmap(cell->getPort("\\B").as_bit());
				equiv_bits.add(sig_b, sig_a);
				equiv_inputs.insert(sig_a);
				equiv_inputs.insert(sig_b);
				cells.insert(cell->name);
			} else {
				if (mode_icells || module->design->module(cell->type))
					cells.insert(cell->name);
			}

		for (auto cell : module->selected_cells())
			if (cell->type == "$equiv") {
				SigBit sig_a = sigmap(cell->getPort("\\A").as_bit());
				SigBit sig_b = sigmap(cell->getPort("\\B").as_bit());
				SigBit sig_y = sigmap(cell->getPort("\\Y").as_bit());
				if (sig_a == sig_b && equiv_inputs.count(sig_y)) {
					log("    Purging redundant $equiv cell %s.\n", log_id(cell));
					module->connect(sig_y, sig_a);
					module->remove(cell);
					merge_count++;
				}
			}

		if (merge_count > 0)
			return;

		for (auto cell_name : cells)
		{
			merge_key_t key;
			vector<tuple<IdString, int, SigBit>> fwd_connections;

			Cell *cell = module->cell(cell_name);
			key.type = cell->type;

			for (auto &it : cell->parameters)
				key.parameters.push_back(it);
			std::sort(key.parameters.begin(), key.parameters.end());

			for (auto &it : cell->connections())
				key.port_sizes.push_back(make_pair(it.first, GetSize(it.second)));
			std::sort(key.port_sizes.begin(), key.port_sizes.end());

			for (auto &conn : cell->connections())
			{
				if (cell->input(conn.first)) {
					SigSpec sig = sigmap(conn.second);
					for (int i = 0; i < GetSize(sig); i++)
						fwd_connections.push_back(make_tuple(conn.first, i, sig[i]));
				}

				if (cell->output(conn.first)) {
					SigSpec sig = equiv_bits(conn.second);
					for (int i = 0; i < GetSize(sig); i++) {
						key.connections.clear();
						key.connections.push_back(make_tuple(conn.first, i, sig[i]));

						if (merge_cache.count(key))
							bwd_merge_cache.insert(key);
						merge_cache[key].insert(cell_name);
					}
				}
			}

			std::sort(fwd_connections.begin(), fwd_connections.end());
			key.connections.swap(fwd_connections);

			if (merge_cache.count(key))
				fwd_merge_cache.insert(key);
			merge_cache[key].insert(cell_name);
		}

		for (int phase = 0; phase < 2; phase++)
		{
			auto &queue = phase ? bwd_merge_cache : fwd_merge_cache;

			for (auto &key : queue)
			{
				const char *strategy = nullptr;
				vector<Cell*> gold_cells, gate_cells, other_cells;
				vector<pair<Cell*, Cell*>> cell_pairs;
				IdString cells_type;

				for (auto cell_name : merge_cache[key]) {
					Cell *c = module->cell(cell_name);
					if (c != nullptr) {
						string n = cell_name.str();
						cells_type = c->type;
						if (GetSize(n) > 5 && n.substr(GetSize(n)-5) == "_gold")
							gold_cells.push_back(c);
						else if (GetSize(n) > 5 && n.substr(GetSize(n)-5) == "_gate")
							gate_cells.push_back(c);
						else
							other_cells.push_back(c);
					}
				}

				if (phase && fwonly_cells.count(cells_type))
					continue;

				if (GetSize(gold_cells) > 1 || GetSize(gate_cells) > 1 || GetSize(other_cells) > 1)
				{
					strategy = "deduplicate";
					for (int i = 0; i+1 < GetSize(gold_cells); i += 2)
						cell_pairs.push_back(make_pair(gold_cells[i], gold_cells[i+1]));
					for (int i = 0; i+1 < GetSize(gate_cells); i += 2)
						cell_pairs.push_back(make_pair(gate_cells[i], gate_cells[i+1]));
					for (int i = 0; i+1 < GetSize(other_cells); i += 2)
						cell_pairs.push_back(make_pair(other_cells[i], other_cells[i+1]));
					goto run_strategy;
				}

				if (GetSize(gold_cells) == 1 && GetSize(gate_cells) == 1)
				{
					strategy = "gold-gate-pairs";
					cell_pairs.push_back(make_pair(gold_cells[0], gate_cells[0]));
					goto run_strategy;
				}

				if (GetSize(gold_cells) == 1 && GetSize(other_cells) == 1)
				{
					strategy = "gold-guess";
					cell_pairs.push_back(make_pair(gold_cells[0], other_cells[0]));
					goto run_strategy;
				}

				if (GetSize(other_cells) == 1 && GetSize(gate_cells) == 1)
				{
					strategy = "gate-guess";
					cell_pairs.push_back(make_pair(other_cells[0], gate_cells[0]));
					goto run_strategy;
				}

				log_assert(GetSize(gold_cells) + GetSize(gate_cells) + GetSize(other_cells) < 2);
				continue;

			run_strategy:
				int total_group_size = GetSize(gold_cells) + GetSize(gate_cells) + GetSize(other_cells);
				log("    %s merging %d %s cells (from group of %d) using strategy %s:\n", phase ? "Bwd" : "Fwd",
						2*GetSize(cell_pairs), log_id(cells_type), total_group_size, strategy);
				for (auto it : cell_pairs) {
					log("      Merging cells %s and %s.\n", log_id(it.first),  log_id(it.second));
					merge_cell_pair(it.first, it.second);
				}
			}

			if (merge_count > 0)
				return;
		}

		log("    Nothing to merge.\n");
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
		log("    -fwd\n");
		log("        by default this command performans forward sweeps until nothing can\n");
		log("        be merged by forwards sweeps, then backward sweeps until forward\n");
		log("        sweeps are effective again. with this option set only forward sweeps\n");
		log("        are performed.\n");
		log("\n");
		log("    -fwonly <cell_type>\n");
		log("        add the specified cell type to the list of cell types that are only\n");
		log("        merged in forward sweeps and never in backward sweeps. $equiv is in\n");
		log("        this list automatically.\n");
		log("\n");
		log("    -icells\n");
		log("        by default, the internal RTL and gate cell types are ignored. add\n");
		log("        this option to also process those cell types with this command.\n");
		log("\n");
		log("    -maxiter <N>\n");
		log("        maximum number of iterations to run before aborting\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, Design *design)
	{
		pool<IdString> fwonly_cells({ "$equiv" });
		bool mode_icells = false;
		bool mode_fwd = false;
		int max_iter = -1;

		log_header(design, "Executing EQUIV_STRUCT pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-fwd") {
				mode_fwd = true;
				continue;
			}
			if (args[argidx] == "-icells") {
				mode_icells = true;
				continue;
			}
			if (args[argidx] == "-fwonly" && argidx+1 < args.size()) {
				fwonly_cells.insert(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-maxiter" && argidx+1 < args.size()) {
				max_iter = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
			int module_merge_count = 0;
			log("Running equiv_struct on module %s:\n", log_id(module));
			for (int iter = 0;; iter++) {
				if (iter == max_iter) {
					log("  Reached iteration limit of %d.\n", iter);
					break;
				}
				EquivStructWorker worker(module, mode_fwd, mode_icells, fwonly_cells, iter+1);
				if (worker.merge_count == 0)
					break;
				module_merge_count += worker.merge_count;
			}
			if (module_merge_count)
				log("  Performed a total of %d merges in module %s.\n", module_merge_count, log_id(module));
		}
	}
} EquivStructPass;

PRIVATE_NAMESPACE_END
