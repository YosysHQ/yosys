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

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/celltypes.h"
#include "fsmdata.h"
#include <string.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct FsmExpand
{
	RTLIL::Module *module;
	RTLIL::Cell *fsm_cell;
	bool full_mode;

	SigMap assign_map;
	SigSet<RTLIL::Cell*, RTLIL::sort_by_name_id<RTLIL::Cell>> sig2driver, sig2user;
	CellTypes ct;

	std::set<RTLIL::Cell*, RTLIL::sort_by_name_id<RTLIL::Cell>> merged_set;
	std::set<RTLIL::Cell*, RTLIL::sort_by_name_id<RTLIL::Cell>> current_set;
	std::set<RTLIL::Cell*, RTLIL::sort_by_name_id<RTLIL::Cell>> no_candidate_set;

	bool already_optimized;
	int limit_transitions;

	bool is_cell_merge_candidate(RTLIL::Cell *cell)
	{
		if (full_mode || cell->type == "$_MUX_")
			return true;

		if (cell->type == "$mux" || cell->type == "$pmux")
			if (cell->getPort("\\A").size() < 2)
				return true;

		RTLIL::SigSpec new_signals;
		if (cell->hasPort("\\A"))
			new_signals.append(assign_map(cell->getPort("\\A")));
		if (cell->hasPort("\\B"))
			new_signals.append(assign_map(cell->getPort("\\B")));
		if (cell->hasPort("\\S"))
			new_signals.append(assign_map(cell->getPort("\\S")));
		if (cell->hasPort("\\Y"))
			new_signals.append(assign_map(cell->getPort("\\Y")));

		new_signals.sort_and_unify();
		new_signals.remove_const();

		new_signals.remove(assign_map(fsm_cell->getPort("\\CTRL_IN")));
		new_signals.remove(assign_map(fsm_cell->getPort("\\CTRL_OUT")));

		if (new_signals.size() > 3)
			return false;

		return true;
	}

	void create_current_set()
	{
		std::vector<RTLIL::Cell*> cell_list;

		for (auto c : sig2driver.find(assign_map(fsm_cell->getPort("\\CTRL_IN"))))
			cell_list.push_back(c);

		for (auto c : sig2user.find(assign_map(fsm_cell->getPort("\\CTRL_OUT"))))
			cell_list.push_back(c);

		current_set.clear();
		for (auto c : cell_list)
		{
			if (merged_set.count(c) > 0 || current_set.count(c) > 0 || no_candidate_set.count(c) > 0)
				continue;
			for (auto &p : c->connections()) {
				if (p.first != "\\A" && p.first != "\\B" && p.first != "\\S" && p.first != "\\Y")
					goto next_cell;
			}
			if (!is_cell_merge_candidate(c)) {
				no_candidate_set.insert(c);
				continue;
			}
			current_set.insert(c);
		next_cell:;
		}
	}

	void optimze_as_needed()
	{
		if (already_optimized)
			return;

		int trans_num = fsm_cell->parameters["\\TRANS_NUM"].as_int();
		if (trans_num > limit_transitions)
		{
			log("  grown transition table to %d entries -> optimize.\n", trans_num);
			FsmData::optimize_fsm(fsm_cell, module);
			already_optimized = true;

			trans_num = fsm_cell->parameters["\\TRANS_NUM"].as_int();
			log("  transition table size after optimizaton: %d\n", trans_num);
			limit_transitions = 16 * trans_num;
		}
	}

	void merge_cell_into_fsm(RTLIL::Cell *cell)
	{
		optimze_as_needed();

		log("  merging %s cell %s.\n", cell->type.c_str(), cell->name.c_str());
		merged_set.insert(cell);
		already_optimized = false;

		RTLIL::SigSpec input_sig, output_sig;

		for (auto &p : cell->connections())
			if (ct.cell_output(cell->type, p.first))
				output_sig.append(assign_map(p.second));
			else
				input_sig.append(assign_map(p.second));
		input_sig.sort_and_unify();
		input_sig.remove_const();

		std::vector<RTLIL::Const> truth_tab;

		for (int i = 0; i < (1 << input_sig.size()); i++) {
			RTLIL::Const in_val(i, input_sig.size());
			RTLIL::SigSpec A, B, S;
			if (cell->hasPort("\\A"))
				A = assign_map(cell->getPort("\\A"));
			if (cell->hasPort("\\B"))
				B = assign_map(cell->getPort("\\B"));
			if (cell->hasPort("\\S"))
				S = assign_map(cell->getPort("\\S"));
			A.replace(input_sig, RTLIL::SigSpec(in_val));
			B.replace(input_sig, RTLIL::SigSpec(in_val));
			S.replace(input_sig, RTLIL::SigSpec(in_val));
			log_assert(A.is_fully_const());
			log_assert(B.is_fully_const());
			log_assert(S.is_fully_const());
			truth_tab.push_back(ct.eval(cell, A.as_const(), B.as_const(), S.as_const()));
		}

		FsmData fsm_data;
		fsm_data.copy_from_cell(fsm_cell);

		fsm_data.num_inputs += input_sig.size();
		RTLIL::SigSpec new_ctrl_in = fsm_cell->getPort("\\CTRL_IN");
		new_ctrl_in.append(input_sig);
		fsm_cell->setPort("\\CTRL_IN", new_ctrl_in);

		fsm_data.num_outputs += output_sig.size();
		RTLIL::SigSpec new_ctrl_out = fsm_cell->getPort("\\CTRL_OUT");
		new_ctrl_out.append(output_sig);
		fsm_cell->setPort("\\CTRL_OUT", new_ctrl_out);

		std::vector<FsmData::transition_t> new_transition_table;
		for (auto &tr : fsm_data.transition_table) {
			for (int i = 0; i < (1 << input_sig.size()); i++) {
				FsmData::transition_t new_tr = tr;
				RTLIL::Const in_val(i, input_sig.size());
				RTLIL::Const out_val = truth_tab[i];
				RTLIL::SigSpec ctrl_in = new_tr.ctrl_in;
				RTLIL::SigSpec ctrl_out = new_tr.ctrl_out;
				ctrl_in.append(in_val);
				ctrl_out.append(out_val);
				new_tr.ctrl_in = ctrl_in.as_const();
				new_tr.ctrl_out = ctrl_out.as_const();
				new_transition_table.push_back(new_tr);
			}
		}
		fsm_data.transition_table.swap(new_transition_table);
		new_transition_table.clear();

		fsm_data.copy_to_cell(fsm_cell);
	}

	FsmExpand(RTLIL::Cell *cell, RTLIL::Design *design, RTLIL::Module *mod, bool full)
	{
		module = mod;
		fsm_cell = cell;
		full_mode = full;

		assign_map.set(module);
		ct.setup_internals();
		ct.setup_stdcells();

		for (auto &cell_it : module->cells_) {
			RTLIL::Cell *c = cell_it.second;
			if (ct.cell_known(c->type) && design->selected(mod, c))
				for (auto &p : c->connections()) {
					if (ct.cell_output(c->type, p.first))
						sig2driver.insert(assign_map(p.second), c);
					else
						sig2user.insert(assign_map(p.second), c);
				}
		}
	}

	void execute()
	{
		log("\n");
		log("Expanding FSM `%s' from module `%s':\n", fsm_cell->name.c_str(), module->name.c_str());

		already_optimized = false;
		limit_transitions =  16 * fsm_cell->parameters["\\TRANS_NUM"].as_int();

		for (create_current_set(); current_set.size() > 0; create_current_set()) {
			for (auto c : current_set)
				merge_cell_into_fsm(c);
		}

		for (auto c : merged_set)
			module->remove(c);

		if (merged_set.size() > 0 && !already_optimized)
			FsmData::optimize_fsm(fsm_cell, module);

		log("  merged %d cells into FSM.\n", GetSize(merged_set));
	}
};

struct FsmExpandPass : public Pass {
	FsmExpandPass() : Pass("fsm_expand", "expand FSM cells by merging logic into it") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fsm_expand [-full] [selection]\n");
		log("\n");
		log("The fsm_extract pass is conservative about the cells that belong to a finite\n");
		log("state machine. This pass can be used to merge additional auxiliary gates into\n");
		log("the finite state machine.\n");
		log("\n");
		log("By default, fsm_expand is still a bit conservative regarding merging larger\n");
		log("word-wide cells. Call with -full to consider all cells for merging.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool full_mode = false;

		log_header(design, "Executing FSM_EXPAND pass (merging auxiliary logic into FSMs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-full") {
				full_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules_) {
			if (!design->selected(mod_it.second))
				continue;
			std::vector<RTLIL::Cell*> fsm_cells;
			for (auto &cell_it : mod_it.second->cells_)
				if (cell_it.second->type == "$fsm" && design->selected(mod_it.second, cell_it.second))
					fsm_cells.push_back(cell_it.second);
			for (auto c : fsm_cells) {
				FsmExpand fsm_expand(c, design, mod_it.second, full_mode);
				fsm_expand.execute();
			}
		}
	}
} FsmExpandPass;

PRIVATE_NAMESPACE_END
