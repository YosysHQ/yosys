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
#include "passes/techmap/simplemap.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Dff2dffeWorker
{
	const dict<IdString, IdString> &direct_dict;

	RTLIL::Module *module;
	SigMap sigmap;
	CellTypes ct;

	typedef std::pair<RTLIL::Cell*, int> cell_int_t;
	std::map<RTLIL::SigBit, cell_int_t> bit2mux;
	std::vector<RTLIL::Cell*> dff_cells;
	std::map<RTLIL::SigBit, int> bitusers;

	typedef std::map<RTLIL::SigBit, bool> pattern_t;
	typedef std::set<pattern_t> patterns_t;


	Dff2dffeWorker(RTLIL::Module *module, const dict<IdString, IdString> &direct_dict) :
			direct_dict(direct_dict), module(module), sigmap(module), ct(module->design)
	{
		for (auto wire : module->wires()) {
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					bitusers[bit]++;
		}

		for (auto cell : module->cells()) {
			if (cell->type == "$mux" || cell->type == "$pmux" || cell->type == "$_MUX_") {
				RTLIL::SigSpec sig_y = sigmap(cell->getPort("\\Y"));
				for (int i = 0; i < GetSize(sig_y); i++)
					bit2mux[sig_y[i]] = cell_int_t(cell, i);
			}
			if (direct_dict.empty()) {
				if (cell->type == "$dff" || cell->type == "$_DFF_N_" || cell->type == "$_DFF_P_")
					dff_cells.push_back(cell);
			} else {
				if (direct_dict.count(cell->type))
					dff_cells.push_back(cell);
			}
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

	RTLIL::SigSpec make_patterns_logic(patterns_t patterns, bool make_gates)
	{
		RTLIL::SigSpec or_input;

		for (auto pat : patterns)
		{
			RTLIL::SigSpec s1, s2;
			for (auto it : pat) {
				s1.append(it.first);
				s2.append(it.second);
			}

			RTLIL::SigSpec y = module->addWire(NEW_ID);
			RTLIL::Cell *c = module->addNe(NEW_ID, s1, s2, y);

			if (make_gates) {
				simplemap(module, c);
				module->remove(c);
			}

			or_input.append(y);
		}

		if (GetSize(or_input) == 0)
			return RTLIL::S1;

		if (GetSize(or_input) == 1)
			return or_input;

		RTLIL::SigSpec y = module->addWire(NEW_ID);
		RTLIL::Cell *c = module->addReduceAnd(NEW_ID, or_input, y);

		if (make_gates) {
			simplemap(module, c);
			module->remove(c);
		}

		return y;
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
			if (!direct_dict.empty()) {
				log("  converting %s cell %s to %s for %s -> %s.\n", log_id(dff_cell->type), log_id(dff_cell), log_id(direct_dict.at(dff_cell->type)), log_signal(new_sig_d), log_signal(new_sig_q));
				dff_cell->setPort("\\E", make_patterns_logic(it.first, true));
				dff_cell->type = direct_dict.at(dff_cell->type);
			} else
			if (dff_cell->type == "$dff") {
				RTLIL::Cell *new_cell = module->addDffe(NEW_ID, dff_cell->getPort("\\CLK"), make_patterns_logic(it.first, false),
						new_sig_d, new_sig_q, dff_cell->getParam("\\CLK_POLARITY").as_bool(), true);
				log("  created $dffe cell %s for %s -> %s.\n", log_id(new_cell), log_signal(new_sig_d), log_signal(new_sig_q));
			} else {
				RTLIL::Cell *new_cell = module->addDffeGate(NEW_ID, dff_cell->getPort("\\C"), make_patterns_logic(it.first, true),
						new_sig_d, new_sig_q, dff_cell->type == "$_DFF_P_", true);
				log("  created %s cell %s for %s -> %s.\n", log_id(new_cell->type), log_id(new_cell), log_signal(new_sig_d), log_signal(new_sig_q));
			}
		}

		if (!direct_dict.empty())
			return;

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
		log("Transforming FF to FF+Enable cells in module %s:\n", log_id(module));
		for (auto dff_cell : dff_cells) {
			// log("Handling candidate %s:\n", log_id(dff_cell));
			handle_dff_cell(dff_cell);
		}
	}
};

struct Dff2dffePass : public Pass {
	Dff2dffePass() : Pass("dff2dffe", "transform $dff cells to $dffe cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    dff2dffe [options] [selection]\n");
		log("\n");
		log("This pass transforms $dff cells driven by a tree of multiplexers with one or\n");
		log("more feedback paths to $dffe cells. It also works on gate-level cells such as\n");
		log("$_DFF_P_, $_DFF_N_ and $_MUX_.\n");
		log("\n");
		log("    -unmap\n");
		log("        operate in the opposite direction: replace $dffe cells with combinations\n");
		log("        of $dff and $mux cells. the options below are ignore in unmap mode.\n");
		log("\n");
		log("    -direct <internal_gate_type> <external_gate_type>\n");
		log("        map directly to external gate type. <internal_gate_type> can\n");
		log("        be any internal gate-level FF cell (except $_DFFE_??_). the\n");
		log("        <external_gate_type> is the cell type name for a cell with an\n");
		log("        identical interface to the <internal_gate_type>, except it\n");
		log("        also has an high-active enable port 'E'.\n");
		log("          Usually <external_gate_type> is an intermediate cell type\n");
		log("        that is then translated to the final type using 'techmap'.\n");
		log("\n");
		log("    -direct-match <pattern>\n");
		log("        like -direct for all DFF cell types matching the expression.\n");
		log("        this will use $__DFFE_* as <external_gate_type> matching the\n");
		log("        internal gate type $_DFF_*_, except for $_DFF_[NP]_, which is\n");
		log("        converted to $_DFFE_[NP]_.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing DFF2DFFE pass (transform $dff to $dffe where applicable).\n");

		bool unmap_mode = false;
		dict<IdString, IdString> direct_dict;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-unmap") {
				unmap_mode = true;
				continue;
			}
			if (args[argidx] == "-direct" && argidx + 2 < args.size()) {
				string direct_from = RTLIL::escape_id(args[++argidx]);
				string direct_to = RTLIL::escape_id(args[++argidx]);
				direct_dict[direct_from] = direct_to;
				continue;
			}
			if (args[argidx] == "-direct-match" && argidx + 1 < args.size()) {
				bool found_match = false;
				const char *pattern = args[++argidx].c_str();
				if (patmatch(pattern, "$_DFF_P_"  )) found_match = true, direct_dict["$_DFF_P_"  ] = "$_DFFE_PP_";
				if (patmatch(pattern, "$_DFF_N_"  )) found_match = true, direct_dict["$_DFF_N_"  ] = "$_DFFE_NP_";
				if (patmatch(pattern, "$_DFF_NN0_")) found_match = true, direct_dict["$_DFF_NN0_"] = "$__DFFE_NN0";
				if (patmatch(pattern, "$_DFF_NN1_")) found_match = true, direct_dict["$_DFF_NN1_"] = "$__DFFE_NN1";
				if (patmatch(pattern, "$_DFF_NP0_")) found_match = true, direct_dict["$_DFF_NP0_"] = "$__DFFE_NP0";
				if (patmatch(pattern, "$_DFF_NP1_")) found_match = true, direct_dict["$_DFF_NP1_"] = "$__DFFE_NP1";
				if (patmatch(pattern, "$_DFF_PN0_")) found_match = true, direct_dict["$_DFF_PN0_"] = "$__DFFE_PN0";
				if (patmatch(pattern, "$_DFF_PN1_")) found_match = true, direct_dict["$_DFF_PN1_"] = "$__DFFE_PN1";
				if (patmatch(pattern, "$_DFF_PP0_")) found_match = true, direct_dict["$_DFF_PP0_"] = "$__DFFE_PP0";
				if (patmatch(pattern, "$_DFF_PP1_")) found_match = true, direct_dict["$_DFF_PP1_"] = "$__DFFE_PP1";
				if (!found_match)
					log_cmd_error("No cell types matched pattern '%s'.\n", pattern);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!direct_dict.empty()) {
			log("Selected cell types for direct conversion:\n");
			for (auto &it : direct_dict)
				log("  %s -> %s\n", log_id(it.first), log_id(it.second));
		}

		for (auto mod : design->selected_modules())
			if (!mod->has_processes_warn())
			{
				if (unmap_mode) {
					for (auto cell : mod->selected_cells()) {
						if (cell->type == "$dffe") {
							RTLIL::SigSpec tmp = mod->addWire(NEW_ID, GetSize(cell->getPort("\\D")));
							mod->addDff(NEW_ID, cell->getPort("\\CLK"), tmp, cell->getPort("\\Q"), cell->getParam("\\CLK_POLARITY").as_bool());
							if (cell->getParam("\\EN_POLARITY").as_bool())
								mod->addMux(NEW_ID, cell->getPort("\\Q"), cell->getPort("\\D"), cell->getPort("\\EN"), tmp);
							else
								mod->addMux(NEW_ID, cell->getPort("\\D"), cell->getPort("\\Q"), cell->getPort("\\EN"), tmp);
							mod->remove(cell);
							continue;
						}
						if (cell->type.substr(0, 7) == "$_DFFE_") {
							bool clk_pol = cell->type.substr(7, 1) == "P";
							bool en_pol = cell->type.substr(8, 1) == "P";
							RTLIL::SigSpec tmp = mod->addWire(NEW_ID);
							mod->addDff(NEW_ID, cell->getPort("\\C"), tmp, cell->getPort("\\Q"), clk_pol);
							if (en_pol)
								mod->addMux(NEW_ID, cell->getPort("\\Q"), cell->getPort("\\D"), cell->getPort("\\E"), tmp);
							else
								mod->addMux(NEW_ID, cell->getPort("\\D"), cell->getPort("\\Q"), cell->getPort("\\E"), tmp);
							mod->remove(cell);
							continue;
						}
					}
					continue;
				}

				Dff2dffeWorker worker(mod, direct_dict);
				worker.run();
			}
	}
} Dff2dffePass;

PRIVATE_NAMESPACE_END
