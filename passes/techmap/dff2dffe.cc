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
			if (cell->type.in(ID($mux), ID($pmux), ID($_MUX_))) {
				RTLIL::SigSpec sig_y = sigmap(cell->getPort(ID::Y));
				for (int i = 0; i < GetSize(sig_y); i++)
					bit2mux[sig_y[i]] = cell_int_t(cell, i);
			}
			if (direct_dict.empty()) {
				if (cell->type.in(ID($dff), ID($_DFF_N_), ID($_DFF_P_)))
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
		RTLIL::SigSpec sig_a = sigmap(mux_cell_int.first->getPort(ID::A));
		RTLIL::SigSpec sig_b = sigmap(mux_cell_int.first->getPort(ID::B));
		RTLIL::SigSpec sig_s = sigmap(mux_cell_int.first->getPort(ID(S)));
		int width = GetSize(sig_a), index = mux_cell_int.second;

		for (int i = 0; i < GetSize(sig_s); i++)
			if (path.count(sig_s[i]) && path.at(sig_s[i]))
			{
				ret = find_muxtree_feedback_patterns(sig_b[i*width + index], q, path);

				if (sig_b[i*width + index] == q) {
					RTLIL::SigSpec s = mux_cell_int.first->getPort(ID::B);
					s[i*width + index] = RTLIL::Sx;
					mux_cell_int.first->setPort(ID::B, s);
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
				RTLIL::SigSpec s = mux_cell_int.first->getPort(ID::B);
				s[i*width + index] = RTLIL::Sx;
				mux_cell_int.first->setPort(ID::B, s);
			}
		}

		for (auto &pat : find_muxtree_feedback_patterns(sig_a[index], q, path_else))
			ret.insert(pat);

		if (sig_a[index] == q) {
			RTLIL::SigSpec s = mux_cell_int.first->getPort(ID::A);
			s[index] = RTLIL::Sx;
			mux_cell_int.first->setPort(ID::A, s);
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
			return State::S1;

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
		RTLIL::SigSpec sig_d = sigmap(dff_cell->getPort(ID(D)));
		RTLIL::SigSpec sig_q = sigmap(dff_cell->getPort(ID(Q)));

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
				dff_cell->setPort(ID(E), make_patterns_logic(it.first, true));
				dff_cell->type = direct_dict.at(dff_cell->type);
			} else
			if (dff_cell->type == ID($dff)) {
				RTLIL::Cell *new_cell = module->addDffe(NEW_ID, dff_cell->getPort(ID(CLK)), make_patterns_logic(it.first, false),
						new_sig_d, new_sig_q, dff_cell->getParam(ID(CLK_POLARITY)).as_bool(), true);
				log("  created $dffe cell %s for %s -> %s.\n", log_id(new_cell), log_signal(new_sig_d), log_signal(new_sig_q));
			} else {
				RTLIL::Cell *new_cell = module->addDffeGate(NEW_ID, dff_cell->getPort(ID(C)), make_patterns_logic(it.first, true),
						new_sig_d, new_sig_q, dff_cell->type == ID($_DFF_P_), true);
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
			dff_cell->setPort(ID(D), new_sig_d);
			dff_cell->setPort(ID(Q), new_sig_q);
			dff_cell->setParam(ID(WIDTH), GetSize(remaining_indices));
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
	void help() YS_OVERRIDE
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
		log("        of $dff and $mux cells. the options below are ignored in unmap mode.\n");
		log("\n");
		log("    -unmap-mince N\n");
		log("        Same as -unmap but only unmap $dffe where the clock enable port\n");
		log("        signal is used by less $dffe than the specified number\n");
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
		log("        internal gate type $_DFF_*_, and $__DFFSE_* for those matching\n");
		log("        $_DFFS_*_, except for $_DFF_[NP]_, which is converted to \n");
		log("        $_DFFE_[NP]_.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing DFF2DFFE pass (transform $dff to $dffe where applicable).\n");

		bool unmap_mode = false;
		int min_ce_use = -1;
		dict<IdString, IdString> direct_dict;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-unmap") {
				unmap_mode = true;
				continue;
			}
			if (args[argidx] == "-unmap-mince" && argidx + 1 < args.size()) {
				unmap_mode = true;
				min_ce_use = atoi(args[++argidx].c_str());
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
				if (patmatch(pattern, "$_DFF_P_"  )) found_match = true, direct_dict[ID($_DFF_P_)  ] = ID($_DFFE_PP_);
				if (patmatch(pattern, "$_DFF_N_"  )) found_match = true, direct_dict[ID($_DFF_N_)  ] = ID($_DFFE_NP_);
				if (patmatch(pattern, "$_DFF_NN0_")) found_match = true, direct_dict[ID($_DFF_NN0_)] = ID($__DFFE_NN0);
				if (patmatch(pattern, "$_DFF_NN1_")) found_match = true, direct_dict[ID($_DFF_NN1_)] = ID($__DFFE_NN1);
				if (patmatch(pattern, "$_DFF_NP0_")) found_match = true, direct_dict[ID($_DFF_NP0_)] = ID($__DFFE_NP0);
				if (patmatch(pattern, "$_DFF_NP1_")) found_match = true, direct_dict[ID($_DFF_NP1_)] = ID($__DFFE_NP1);
				if (patmatch(pattern, "$_DFF_PN0_")) found_match = true, direct_dict[ID($_DFF_PN0_)] = ID($__DFFE_PN0);
				if (patmatch(pattern, "$_DFF_PN1_")) found_match = true, direct_dict[ID($_DFF_PN1_)] = ID($__DFFE_PN1);
				if (patmatch(pattern, "$_DFF_PP0_")) found_match = true, direct_dict[ID($_DFF_PP0_)] = ID($__DFFE_PP0);
				if (patmatch(pattern, "$_DFF_PP1_")) found_match = true, direct_dict[ID($_DFF_PP1_)] = ID($__DFFE_PP1);

				if (patmatch(pattern, "$__DFFS_NN0_")) found_match = true, direct_dict[ID($__DFFS_NN0_)] = ID($__DFFSE_NN0);
				if (patmatch(pattern, "$__DFFS_NN1_")) found_match = true, direct_dict[ID($__DFFS_NN1_)] = ID($__DFFSE_NN1);
				if (patmatch(pattern, "$__DFFS_NP0_")) found_match = true, direct_dict[ID($__DFFS_NP0_)] = ID($__DFFSE_NP0);
				if (patmatch(pattern, "$__DFFS_NP1_")) found_match = true, direct_dict[ID($__DFFS_NP1_)] = ID($__DFFSE_NP1);
				if (patmatch(pattern, "$__DFFS_PN0_")) found_match = true, direct_dict[ID($__DFFS_PN0_)] = ID($__DFFSE_PN0);
				if (patmatch(pattern, "$__DFFS_PN1_")) found_match = true, direct_dict[ID($__DFFS_PN1_)] = ID($__DFFSE_PN1);
				if (patmatch(pattern, "$__DFFS_PP0_")) found_match = true, direct_dict[ID($__DFFS_PP0_)] = ID($__DFFSE_PP0);
				if (patmatch(pattern, "$__DFFS_PP1_")) found_match = true, direct_dict[ID($__DFFS_PP1_)] = ID($__DFFSE_PP1);
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
					SigMap sigmap(mod);
					for (auto cell : mod->selected_cells()) {
						if (cell->type == ID($dffe)) {
							if (min_ce_use >= 0) {
								int ce_use = 0;
								for (auto cell_other : mod->selected_cells()) {
									if (cell_other->type != cell->type)
										continue;
									if (sigmap(cell->getPort(ID(EN))) == sigmap(cell_other->getPort(ID(EN))))
										ce_use++;
								}
								if (ce_use >= min_ce_use)
									continue;
							}

							RTLIL::SigSpec tmp = mod->addWire(NEW_ID, GetSize(cell->getPort(ID(D))));
							mod->addDff(NEW_ID, cell->getPort(ID(CLK)), tmp, cell->getPort(ID(Q)), cell->getParam(ID(CLK_POLARITY)).as_bool());
							if (cell->getParam(ID(EN_POLARITY)).as_bool())
								mod->addMux(NEW_ID, cell->getPort(ID(Q)), cell->getPort(ID(D)), cell->getPort(ID(EN)), tmp);
							else
								mod->addMux(NEW_ID, cell->getPort(ID(D)), cell->getPort(ID(Q)), cell->getPort(ID(EN)), tmp);
							mod->remove(cell);
							continue;
						}
						if (cell->type.begins_with("$_DFFE_")) {
							if (min_ce_use >= 0) {
								int ce_use = 0;
								for (auto cell_other : mod->selected_cells()) {
									if (cell_other->type != cell->type)
										continue;
									if (sigmap(cell->getPort(ID(E))) == sigmap(cell_other->getPort(ID(E))))
										ce_use++;
								}
								if (ce_use >= min_ce_use)
									continue;
							}

							bool clk_pol = cell->type.compare(7, 1, "P") == 0;
							bool en_pol = cell->type.compare(8, 1, "P") == 0;
							RTLIL::SigSpec tmp = mod->addWire(NEW_ID);
							mod->addDff(NEW_ID, cell->getPort(ID(C)), tmp, cell->getPort(ID(Q)), clk_pol);
							if (en_pol)
								mod->addMux(NEW_ID, cell->getPort(ID(Q)), cell->getPort(ID(D)), cell->getPort(ID(E)), tmp);
							else
								mod->addMux(NEW_ID, cell->getPort(ID(D)), cell->getPort(ID(Q)), cell->getPort(ID(E)), tmp);
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
