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
#include "kernel/celltypes.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Dff2dffeWorker
{
	RTLIL::Module *module;
	SigMap sigmap;
	CellTypes ct;

	typedef std::pair<RTLIL::Cell*, int> cell_int_t;
	std::map<RTLIL::SigBit, cell_int_t> bit2mux;
	std::vector<RTLIL::Cell*> dff_cells;
	std::map<RTLIL::SigBit, int> bitusers;

	typedef std::map<RTLIL::SigBit, bool> pattern_t;
	typedef std::set<pattern_t> patterns_t;

	Dff2dffeWorker(RTLIL::Module *module) : module(module), sigmap(module), ct(module->design)
	{
		for (auto wire : module->wires()) {
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					bitusers[bit]++;
		}

		for (auto cell : module->cells()) {
			if (cell->type == "$mux" || cell->type == "$pmux") {
				RTLIL::SigSpec sig_y = sigmap(cell->getPort("\\Y"));
				for (int i = 0; i < GetSize(sig_y); i++)
					bit2mux[sig_y[i]] = cell_int_t(cell, i);
			}
			if (cell->type == "$dff")
				dff_cells.push_back(cell);
			for (auto conn : cell->connections()) {
				if (ct.cell_output(cell->type, conn.first))
					continue;
				for (auto bit : sigmap(conn.second))
					bitusers[bit]++;
			}
		}
	}

	patterns_t find_muxtree_feedback_patterns(RTLIL::SigBit d, RTLIL::SigBit q, pattern_t path)
	{
		patterns_t ret;

		if (d == q) {
			ret.insert(path);
			return ret;
		}

		if (bit2mux.count(d) == 0 || bitusers[d] > 1)
			return ret;

		cell_int_t mux_cell_int = bit2mux.at(d);
		RTLIL::SigSpec sig_a = sigmap(mux_cell_int.first->getPort("\\A"));
		RTLIL::SigSpec sig_b = sigmap(mux_cell_int.first->getPort("\\B"));
		RTLIL::SigSpec sig_s = sigmap(mux_cell_int.first->getPort("\\S"));
		int width = GetSize(sig_a), index = mux_cell_int.second;

		for (int i = 0; i < GetSize(sig_s); i++)
			if (path.count(sig_s[i]) && path.at(sig_s[i]))
			{
				ret = find_muxtree_feedback_patterns(sig_b[i*width + index], q, path);

				if (sig_b[i*width + index] == q) {
					RTLIL::SigSpec s = mux_cell_int.first->getPort("\\B");
					s[i*width + index] = RTLIL::Sx;
					mux_cell_int.first->setPort("\\B", s);
				}

				return ret;
			}

		pattern_t path_else = path;

		for (int i = 0; i < GetSize(sig_s); i++)
		{
			if (path.count(sig_s[i]))
				continue;

			pattern_t path_this = path;
			path_else[sig_s[i]] = false;
			path_this[sig_s[i]] = true;

			for (auto &pat : find_muxtree_feedback_patterns(sig_b[i*width + index], q, path_this))
				ret.insert(pat);

			if (sig_b[i*width + index] == q) {
				RTLIL::SigSpec s = mux_cell_int.first->getPort("\\B");
				s[i*width + index] = RTLIL::Sx;
				mux_cell_int.first->setPort("\\B", s);
			}
		}

		for (auto &pat : find_muxtree_feedback_patterns(sig_a[index], q, path_else))
			ret.insert(pat);

		if (sig_a[index] == q) {
			RTLIL::SigSpec s = mux_cell_int.first->getPort("\\A");
			s[index] = RTLIL::Sx;
			mux_cell_int.first->setPort("\\A", s);
		}

		return ret;
	}

	void simplify_patterns(patterns_t&)
	{
		// TBD
	}

	RTLIL::SigSpec make_patterns_logic(patterns_t patterns)
	{
		RTLIL::SigSpec or_input;
		for (auto pat : patterns) {
			RTLIL::SigSpec s1, s2;
			for (auto it : pat) {
				s1.append(it.first);
				s2.append(it.second);
			}
			or_input.append(module->Ne(NEW_ID, s1, s2));
		}
		if (GetSize(or_input) == 0)
			return RTLIL::S1;
		if (GetSize(or_input) == 1)
			return or_input;
		return module->ReduceOr(NEW_ID, or_input);
	}

	void handle_dff_cell(RTLIL::Cell *dff_cell)
	{
		RTLIL::SigSpec sig_d = sigmap(dff_cell->getPort("\\D"));
		RTLIL::SigSpec sig_q = sigmap(dff_cell->getPort("\\Q"));

		std::map<patterns_t, std::set<int>> grouped_patterns;
		std::set<int> remaining_indices;

		for (int i = 0 ; i < GetSize(sig_d); i++) {
			patterns_t patterns = find_muxtree_feedback_patterns(sig_d[i], sig_q[i], pattern_t());
			if (!patterns.empty()) {
				simplify_patterns(patterns);
				grouped_patterns[patterns].insert(i);
			} else
				remaining_indices.insert(i);
		}

		for (auto &it : grouped_patterns) {
			RTLIL::SigSpec new_sig_d, new_sig_q;
			for (int i : it.second) {
				new_sig_d.append(sig_d[i]);
				new_sig_q.append(sig_q[i]);
			}
			RTLIL::Cell *new_cell = module->addDffe(NEW_ID, dff_cell->getPort("\\CLK"), make_patterns_logic(it.first),
					new_sig_d, new_sig_q, dff_cell->getParam("\\CLK_POLARITY").as_bool(), true);
			log("  created $dffe cell %s for %s -> %s.\n", log_id(new_cell), log_signal(new_sig_d), log_signal(new_sig_q));
		}

		if (remaining_indices.empty()) {
			log("  removing now obsolete cell %s.\n", log_id(dff_cell));
			module->remove(dff_cell);
		} else if (GetSize(remaining_indices) != GetSize(sig_d)) {
			log("  removing %d now obsolete bits from cell %s.\n", GetSize(sig_d) - GetSize(remaining_indices), log_id(dff_cell));
			RTLIL::SigSpec new_sig_d, new_sig_q;
			for (int i : remaining_indices) {
				new_sig_d.append(sig_d[i]);
				new_sig_q.append(sig_q[i]);
			}
			dff_cell->setPort("\\D", new_sig_d);
			dff_cell->setPort("\\Q", new_sig_q);
			dff_cell->setParam("\\WIDTH", GetSize(remaining_indices));
		}
	}

	void run()
	{
		log("Transforming $dff to $dffe cells in module %s:\n", log_id(module));
		for (auto dff_cell : dff_cells)
			handle_dff_cell(dff_cell);
	}
};

struct Dff2dffePass : public Pass {
	Dff2dffePass() : Pass("dff2dffe", "transform $dff cells to $dffe cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dff2dffe [selection]\n");
		log("\n");
		log("This pass transforms $dff cells driven by a tree of multiplexers with one or\n");
		log("more feedback paths to $dffe cells.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing DFF2DFFE pass (transform $dff to $dffe where applicable).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			// if (args[argidx] == "-foobar") {
			// 	foobar_mode = true;
			// 	continue;
			// }
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules())
			if (!mod->has_processes_warn()) {
				Dff2dffeWorker worker(mod);
				worker.run();
			}
	}
} Dff2dffePass;
 
PRIVATE_NAMESPACE_END
