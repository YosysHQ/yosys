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
#include "kernel/satgen.h"
#include "kernel/sigtools.h"
#include "kernel/modtools.h"

PRIVATE_NAMESPACE_BEGIN

struct ShareWorkerConfig
{
	bool opt_force;
	bool opt_aggressive;
	bool opt_fast;
	std::set<RTLIL::IdString> generic_uni_ops, generic_bin_ops, generic_cbin_ops;
};

struct ShareWorker
{
	ShareWorkerConfig config;
	std::set<RTLIL::IdString> generic_ops;

	RTLIL::Design *design;
	RTLIL::Module *module;

	CellTypes fwd_ct, cone_ct;
	ModWalker modwalker;

	std::set<RTLIL::Cell*> cells_to_remove;
	std::set<RTLIL::Cell*> recursion_state;


	// ------------------------------------------------------------------------------
	// Find terminal bits -- i.e. bits that do not (exclusively) feed into a mux tree
	// ------------------------------------------------------------------------------

	std::set<RTLIL::SigBit> terminal_bits;

	void find_terminal_bits()
	{
		std::set<RTLIL::SigBit> queue_bits;
		std::set<RTLIL::Cell*> visited_cells;

		queue_bits.insert(modwalker.signal_outputs.begin(), modwalker.signal_outputs.end());

		for (auto &it : module->cells_)
			if (!fwd_ct.cell_known(it.second->type)) {
				std::set<RTLIL::SigBit> &bits = modwalker.cell_inputs[it.second];
				queue_bits.insert(bits.begin(), bits.end());
			}

		terminal_bits.insert(queue_bits.begin(), queue_bits.end());

		while (!queue_bits.empty())
		{
			std::set<ModWalker::PortBit> portbits;
			modwalker.get_drivers(portbits, queue_bits);
			queue_bits.clear();

			for (auto &pbit : portbits) {
				if (pbit.cell->type == "$mux" || pbit.cell->type == "$pmux") {
					std::set<RTLIL::SigBit> bits = modwalker.sigmap(pbit.cell->getPort("\\S")).to_sigbit_set();
					terminal_bits.insert(bits.begin(), bits.end());
					queue_bits.insert(bits.begin(), bits.end());
					visited_cells.insert(pbit.cell);
				}
				if (fwd_ct.cell_known(pbit.cell->type) && visited_cells.count(pbit.cell) == 0) {
					std::set<RTLIL::SigBit> &bits = modwalker.cell_inputs[pbit.cell];
					terminal_bits.insert(bits.begin(), bits.end());
					queue_bits.insert(bits.begin(), bits.end());
					visited_cells.insert(pbit.cell);
				}
			}
		}
	}


	// ---------------------------------------------------
	// Find shareable cells and compatible groups of cells
	// ---------------------------------------------------

	std::set<RTLIL::Cell*> shareable_cells;

	void find_shareable_cells()
	{
		for (auto &it : module->cells_)
		{
			RTLIL::Cell *cell = it.second;

			if (!design->selected(module, cell) || !modwalker.ct.cell_known(cell->type))
				continue;

			for (auto &bit : modwalker.cell_outputs[cell])
				if (terminal_bits.count(bit))
					goto not_a_muxed_cell;

			if (0)
		not_a_muxed_cell:
				continue;

			if (config.opt_force) {
				shareable_cells.insert(cell);
				continue;
			}

			if (cell->type == "$memrd") {
				if (!cell->parameters.at("\\CLK_ENABLE").as_bool())
					shareable_cells.insert(cell);
				continue;
			}

			if (cell->type == "$mul" || cell->type == "$div" || cell->type == "$mod") {
				if (config.opt_aggressive || cell->parameters.at("\\Y_WIDTH").as_int() >= 4)
					shareable_cells.insert(cell);
				continue;
			}

			if (cell->type == "$shl" || cell->type == "$shr" || cell->type == "$sshl" || cell->type == "$sshr") {
				if (config.opt_aggressive || cell->parameters.at("\\Y_WIDTH").as_int() >= 8)
					shareable_cells.insert(cell);
				continue;
			}

			if (generic_ops.count(cell->type)) {
				if (config.opt_aggressive || cell->parameters.at("\\Y_WIDTH").as_int() >= 10)
					shareable_cells.insert(cell);
				continue;
			}
		}
	}

	bool is_shareable_pair(RTLIL::Cell *c1, RTLIL::Cell *c2)
	{
		if (c1->type != c2->type)
			return false;

		if (c1->type == "$memrd")
		{
			if (c1->parameters.at("\\MEMID").decode_string() != c2->parameters.at("\\MEMID").decode_string())
				return false;

			return true;
		}

		if (config.generic_uni_ops.count(c1->type))
		{
			if (!config.opt_aggressive)
			{
				int a1_width = c1->parameters.at("\\A_WIDTH").as_int();
				int y1_width = c1->parameters.at("\\Y_WIDTH").as_int();

				int a2_width = c2->parameters.at("\\A_WIDTH").as_int();
				int y2_width = c2->parameters.at("\\Y_WIDTH").as_int();

				if (std::max(a1_width, a2_width) > 2 * std::min(a1_width, a2_width)) return false;
				if (std::max(y1_width, y2_width) > 2 * std::min(y1_width, y2_width)) return false;
			}

			return true;
		}

		if (config.generic_bin_ops.count(c1->type))
		{
			if (!config.opt_aggressive)
			{
				int a1_width = c1->parameters.at("\\A_WIDTH").as_int();
				int b1_width = c1->parameters.at("\\B_WIDTH").as_int();
				int y1_width = c1->parameters.at("\\Y_WIDTH").as_int();

				int a2_width = c2->parameters.at("\\A_WIDTH").as_int();
				int b2_width = c2->parameters.at("\\B_WIDTH").as_int();
				int y2_width = c2->parameters.at("\\Y_WIDTH").as_int();

				if (std::max(a1_width, a2_width) > 2 * std::min(a1_width, a2_width)) return false;
				if (std::max(b1_width, b2_width) > 2 * std::min(b1_width, b2_width)) return false;
				if (std::max(y1_width, y2_width) > 2 * std::min(y1_width, y2_width)) return false;
			}

			return true;
		}

		if (config.generic_cbin_ops.count(c1->type))
		{
			if (!config.opt_aggressive)
			{
				int a1_width = c1->parameters.at("\\A_WIDTH").as_int();
				int b1_width = c1->parameters.at("\\B_WIDTH").as_int();
				int y1_width = c1->parameters.at("\\Y_WIDTH").as_int();

				int a2_width = c2->parameters.at("\\A_WIDTH").as_int();
				int b2_width = c2->parameters.at("\\B_WIDTH").as_int();
				int y2_width = c2->parameters.at("\\Y_WIDTH").as_int();

				int min1_width = std::min(a1_width, b1_width);
				int max1_width = std::max(a1_width, b1_width);

				int min2_width = std::min(a2_width, b2_width);
				int max2_width = std::max(a2_width, b2_width);

				if (std::max(min1_width, min2_width) > 2 * std::min(min1_width, min2_width)) return false;
				if (std::max(max1_width, max2_width) > 2 * std::min(max1_width, max2_width)) return false;
				if (std::max(y1_width, y2_width) > 2 * std::min(y1_width, y2_width)) return false;
			}

			return true;
		}

		for (auto &it : c1->parameters)
			if (c2->parameters.count(it.first) == 0 || c2->parameters.at(it.first) != it.second)
				return false;

		for (auto &it : c2->parameters)
			if (c1->parameters.count(it.first) == 0 || c1->parameters.at(it.first) != it.second)
				return false;

		return true;
	}

	void find_shareable_partners(std::vector<RTLIL::Cell*> &results, RTLIL::Cell *cell)
	{
		results.clear();
		for (auto c : shareable_cells)
			if (c != cell && is_shareable_pair(c, cell))
				results.push_back(c);
	}


	// -----------------------
	// Create replacement cell
	// -----------------------

	RTLIL::Cell *make_supercell(RTLIL::Cell *c1, RTLIL::Cell *c2, RTLIL::SigSpec act)
	{
		log_assert(c1->type == c2->type);

		if (config.generic_uni_ops.count(c1->type))
		{
			if (c1->parameters.at("\\A_SIGNED").as_bool() != c2->parameters.at("\\A_SIGNED").as_bool())
			{
				RTLIL::Cell *unsigned_cell = c1->parameters.at("\\A_SIGNED").as_bool() ? c2 : c1;
				if (unsigned_cell->getPort("\\A").to_sigbit_vector().back() != RTLIL::State::S0) {
					unsigned_cell->parameters.at("\\A_WIDTH") = unsigned_cell->parameters.at("\\A_WIDTH").as_int() + 1;
					RTLIL::SigSpec new_a = unsigned_cell->getPort("\\A");
					new_a.append_bit(RTLIL::State::S0);
					unsigned_cell->setPort("\\A", new_a);
				}
				unsigned_cell->parameters.at("\\A_SIGNED") = true;
				unsigned_cell->check();
			}

			bool a_signed = c1->parameters.at("\\A_SIGNED").as_bool();
			log_assert(a_signed == c2->parameters.at("\\A_SIGNED").as_bool());

			RTLIL::SigSpec a1 = c1->getPort("\\A");
			RTLIL::SigSpec y1 = c1->getPort("\\Y");

			RTLIL::SigSpec a2 = c2->getPort("\\A");
			RTLIL::SigSpec y2 = c2->getPort("\\Y");

			int a_width = std::max(a1.size(), a2.size());
			int y_width = std::max(y1.size(), y2.size());

			if (a1.size() != a_width) a1 = module->addPos(NEW_ID, a1, module->addWire(NEW_ID, a_width), a_signed)->getPort("\\Y");
			if (a2.size() != a_width) a2 = module->addPos(NEW_ID, a2, module->addWire(NEW_ID, a_width), a_signed)->getPort("\\Y");

			RTLIL::SigSpec a = module->Mux(NEW_ID, a2, a1, act);
			RTLIL::Wire *y = module->addWire(NEW_ID, y_width);

			RTLIL::Cell *supercell = module->addCell(NEW_ID, c1->type);
			supercell->parameters["\\A_SIGNED"] = a_signed;
			supercell->parameters["\\A_WIDTH"] = a_width;
			supercell->parameters["\\Y_WIDTH"] = y_width;
			supercell->setPort("\\A", a);
			supercell->setPort("\\Y", y);

			RTLIL::SigSpec new_y1(y, 0, y1.size());
			RTLIL::SigSpec new_y2(y, 0, y2.size());

			module->connect(RTLIL::SigSig(y1, new_y1));
			module->connect(RTLIL::SigSig(y2, new_y2));

			return supercell;
		}

		if (config.generic_bin_ops.count(c1->type) || config.generic_cbin_ops.count(c1->type))
		{
			bool modified_src_cells = false;

			if (config.generic_cbin_ops.count(c1->type))
			{
				int score_unflipped = std::max(c1->parameters.at("\\A_WIDTH").as_int(), c2->parameters.at("\\A_WIDTH").as_int()) +
						std::max(c1->parameters.at("\\B_WIDTH").as_int(), c2->parameters.at("\\B_WIDTH").as_int());

				int score_flipped = std::max(c1->parameters.at("\\A_WIDTH").as_int(), c2->parameters.at("\\B_WIDTH").as_int()) +
						std::max(c1->parameters.at("\\B_WIDTH").as_int(), c2->parameters.at("\\A_WIDTH").as_int());

				if (score_flipped < score_unflipped)
				{
					RTLIL::SigSpec tmp = c2->getPort("\\A");
					c2->setPort("\\A", c2->getPort("\\B"));
					c2->setPort("\\B", tmp);

					std::swap(c2->parameters.at("\\A_WIDTH"), c2->parameters.at("\\B_WIDTH"));
					std::swap(c2->parameters.at("\\A_SIGNED"), c2->parameters.at("\\B_SIGNED"));
					modified_src_cells = true;
				}
			}

			if (c1->parameters.at("\\A_SIGNED").as_bool() != c2->parameters.at("\\A_SIGNED").as_bool())

			{
				RTLIL::Cell *unsigned_cell = c1->parameters.at("\\A_SIGNED").as_bool() ? c2 : c1;
				if (unsigned_cell->getPort("\\A").to_sigbit_vector().back() != RTLIL::State::S0) {
					unsigned_cell->parameters.at("\\A_WIDTH") = unsigned_cell->parameters.at("\\A_WIDTH").as_int() + 1;
					RTLIL::SigSpec new_a = unsigned_cell->getPort("\\A");
					new_a.append_bit(RTLIL::State::S0);
					unsigned_cell->setPort("\\A", new_a);
				}
				unsigned_cell->parameters.at("\\A_SIGNED") = true;
				modified_src_cells = true;
			}

			if (c1->parameters.at("\\B_SIGNED").as_bool() != c2->parameters.at("\\B_SIGNED").as_bool())
			{
				RTLIL::Cell *unsigned_cell = c1->parameters.at("\\B_SIGNED").as_bool() ? c2 : c1;
				if (unsigned_cell->getPort("\\B").to_sigbit_vector().back() != RTLIL::State::S0) {
					unsigned_cell->parameters.at("\\B_WIDTH") = unsigned_cell->parameters.at("\\B_WIDTH").as_int() + 1;
					RTLIL::SigSpec new_b = unsigned_cell->getPort("\\B");
					new_b.append_bit(RTLIL::State::S0);
					unsigned_cell->setPort("\\B", new_b);
				}
				unsigned_cell->parameters.at("\\B_SIGNED") = true;
				modified_src_cells = true;
			}

			if (modified_src_cells) {
				c1->check();
				c2->check();
			}

			bool a_signed = c1->parameters.at("\\A_SIGNED").as_bool();
			bool b_signed = c1->parameters.at("\\B_SIGNED").as_bool();

			log_assert(a_signed == c2->parameters.at("\\A_SIGNED").as_bool());
			log_assert(b_signed == c2->parameters.at("\\B_SIGNED").as_bool());

			if (c1->type == "$shl" || c1->type == "$shr" || c1->type == "$sshl" || c1->type == "$sshr")
				b_signed = false;

			RTLIL::SigSpec a1 = c1->getPort("\\A");
			RTLIL::SigSpec b1 = c1->getPort("\\B");
			RTLIL::SigSpec y1 = c1->getPort("\\Y");

			RTLIL::SigSpec a2 = c2->getPort("\\A");
			RTLIL::SigSpec b2 = c2->getPort("\\B");
			RTLIL::SigSpec y2 = c2->getPort("\\Y");

			int a_width = std::max(a1.size(), a2.size());
			int b_width = std::max(b1.size(), b2.size());
			int y_width = std::max(y1.size(), y2.size());

			if (c1->type == "$shr" && a_signed)
			{
				a_width = std::max(y_width, a_width);

				if (a1.size() < y1.size()) a1 = module->addPos(NEW_ID, a1, module->addWire(NEW_ID, y1.size()), true)->getPort("\\Y");
				if (a2.size() < y2.size()) a2 = module->addPos(NEW_ID, a2, module->addWire(NEW_ID, y2.size()), true)->getPort("\\Y");

				if (a1.size() != a_width) a1 = module->addPos(NEW_ID, a1, module->addWire(NEW_ID, a_width), false)->getPort("\\Y");
				if (a2.size() != a_width) a2 = module->addPos(NEW_ID, a2, module->addWire(NEW_ID, a_width), false)->getPort("\\Y");
			}
			else
			{
				if (a1.size() != a_width) a1 = module->addPos(NEW_ID, a1, module->addWire(NEW_ID, a_width), a_signed)->getPort("\\Y");
				if (a2.size() != a_width) a2 = module->addPos(NEW_ID, a2, module->addWire(NEW_ID, a_width), a_signed)->getPort("\\Y");
			}

			if (b1.size() != b_width) b1 = module->addPos(NEW_ID, b1, module->addWire(NEW_ID, b_width), b_signed)->getPort("\\Y");
			if (b2.size() != b_width) b2 = module->addPos(NEW_ID, b2, module->addWire(NEW_ID, b_width), b_signed)->getPort("\\Y");

			RTLIL::SigSpec a = module->Mux(NEW_ID, a2, a1, act);
			RTLIL::SigSpec b = module->Mux(NEW_ID, b2, b1, act);
			RTLIL::Wire *y = module->addWire(NEW_ID, y_width);

			RTLIL::Cell *supercell = module->addCell(NEW_ID, c1->type);
			supercell->parameters["\\A_SIGNED"] = a_signed;
			supercell->parameters["\\B_SIGNED"] = b_signed;
			supercell->parameters["\\A_WIDTH"] = a_width;
			supercell->parameters["\\B_WIDTH"] = b_width;
			supercell->parameters["\\Y_WIDTH"] = y_width;
			supercell->setPort("\\A", a);
			supercell->setPort("\\B", b);
			supercell->setPort("\\Y", y);
			supercell->check();

			RTLIL::SigSpec new_y1(y, 0, y1.size());
			RTLIL::SigSpec new_y2(y, 0, y2.size());

			module->connect(RTLIL::SigSig(y1, new_y1));
			module->connect(RTLIL::SigSig(y2, new_y2));

			return supercell;
		}

		if (c1->type == "$memrd")
		{
			RTLIL::Cell *supercell = module->addCell(NEW_ID, c1);
			module->connect(c2->getPort("\\DATA"), supercell->getPort("\\DATA"));
			return supercell;
		}

		log_abort();
	}


	// -------------------------------------------
	// Finding forbidden control inputs for a cell
	// -------------------------------------------

	std::map<RTLIL::Cell*, std::set<RTLIL::SigBit>> forbidden_controls_cache;

	const std::set<RTLIL::SigBit> &find_forbidden_controls(RTLIL::Cell *cell)
	{
		if (recursion_state.count(cell)) {
			static std::set<RTLIL::SigBit> empty_controls_set;
			return empty_controls_set;
		}

		if (forbidden_controls_cache.count(cell))
			return forbidden_controls_cache.at(cell);

		std::set<ModWalker::PortBit> pbits;
		std::set<RTLIL::Cell*> consumer_cells;

		modwalker.get_consumers(pbits, modwalker.cell_outputs[cell]);

		for (auto &bit : pbits) {
			if ((bit.cell->type == "$mux" || bit.cell->type == "$pmux") && bit.port == "\\S")
				forbidden_controls_cache[cell].insert(bit.cell->getPort("\\S").extract(bit.offset, 1));
			consumer_cells.insert(bit.cell);
		}

		recursion_state.insert(cell);

		for (auto c : consumer_cells)
			if (fwd_ct.cell_known(c->type)) {
				const std::set<RTLIL::SigBit> &bits = find_forbidden_controls(c);
				forbidden_controls_cache[cell].insert(bits.begin(), bits.end());
			}

		log_assert(recursion_state.count(cell));
		recursion_state.erase(cell);

		return forbidden_controls_cache[cell];
	}


	// --------------------------------------------------------
	// Finding control inputs and activation pattern for a cell
	// --------------------------------------------------------

	std::map<RTLIL::Cell*, std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>>> activation_patterns_cache;

	bool sort_check_activation_pattern(std::pair<RTLIL::SigSpec, RTLIL::Const> &p)
	{
		std::map<RTLIL::SigBit, RTLIL::State> p_bits;

		std::vector<RTLIL::SigBit> p_first_bits = p.first;
		for (int i = 0; i < SIZE(p_first_bits); i++) {
			RTLIL::SigBit b = p_first_bits[i];
			RTLIL::State v = p.second.bits[i];
			if (p_bits.count(b) && p_bits.at(b) != v)
				return false;
			p_bits[b] = v;
		}

		p.first = RTLIL::SigSpec();
		p.second.bits.clear();

		for (auto &it : p_bits) {
			p.first.append_bit(it.first);
			p.second.bits.push_back(it.second);
		}

		return true;
	}

	void optimize_activation_patterns(std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> & /* patterns */)
	{
		// TODO: Remove patterns that are contained in other patterns
		// TODO: Consolidate pairs of patterns that only differ in the value for one signal bit
	}

	const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &find_cell_activation_patterns(RTLIL::Cell *cell, const char *indent)
	{
		if (recursion_state.count(cell)) {
			static std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> empty_patterns_set;
			return empty_patterns_set;
		}

		if (activation_patterns_cache.count(cell))
			return activation_patterns_cache.at(cell);

		const std::set<RTLIL::SigBit> &cell_out_bits = modwalker.cell_outputs[cell];
		std::set<RTLIL::Cell*> driven_cells, driven_data_muxes;

		for (auto &bit : cell_out_bits)
		{
			if (terminal_bits.count(bit)) {
				// Terminal cells are always active: unconditional activation pattern
				activation_patterns_cache[cell].insert(std::pair<RTLIL::SigSpec, RTLIL::Const>());
				return activation_patterns_cache.at(cell);
			}
			for (auto &pbit : modwalker.signal_consumers[bit]) {
				log_assert(fwd_ct.cell_known(pbit.cell->type));
				if ((pbit.cell->type == "$mux" || pbit.cell->type == "$pmux") && (pbit.port == "\\A" || pbit.port == "\\B"))
					driven_data_muxes.insert(pbit.cell);
				else
					driven_cells.insert(pbit.cell);
			}
		}

		recursion_state.insert(cell);

		for (auto c : driven_data_muxes)
		{
			const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &c_patterns = find_cell_activation_patterns(c, indent);

			bool used_in_a = false;
			std::set<int> used_in_b_parts;

			int width = c->parameters.at("\\WIDTH").as_int();
			std::vector<RTLIL::SigBit> sig_a = modwalker.sigmap(c->getPort("\\A"));
			std::vector<RTLIL::SigBit> sig_b = modwalker.sigmap(c->getPort("\\B"));
			std::vector<RTLIL::SigBit> sig_s = modwalker.sigmap(c->getPort("\\S"));

			for (auto &bit : sig_a)
				if (cell_out_bits.count(bit))
					used_in_a = true;

			for (int i = 0; i < SIZE(sig_b); i++)
				if (cell_out_bits.count(sig_b[i]))
					used_in_b_parts.insert(i / width);

			if (used_in_a)
				for (auto p : c_patterns) {
					for (int i = 0; i < SIZE(sig_s); i++)
						p.first.append_bit(sig_s[i]), p.second.bits.push_back(RTLIL::State::S0);
					if (sort_check_activation_pattern(p))
						activation_patterns_cache[cell].insert(p);
				}

			for (int idx : used_in_b_parts)
				for (auto p : c_patterns) {
					p.first.append_bit(sig_s[idx]), p.second.bits.push_back(RTLIL::State::S1);
					if (sort_check_activation_pattern(p))
						activation_patterns_cache[cell].insert(p);
				}
		}

		for (auto c : driven_cells) {
			const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &c_patterns = find_cell_activation_patterns(c, indent);
			activation_patterns_cache[cell].insert(c_patterns.begin(), c_patterns.end());
		}

		log_assert(recursion_state.count(cell));
		recursion_state.erase(cell);

		optimize_activation_patterns(activation_patterns_cache[cell]);
		if (activation_patterns_cache[cell].empty()) {
			log("%sFound cell that is never activated: %s\n", indent, log_id(cell));
			RTLIL::SigSpec cell_outputs = modwalker.cell_outputs[cell];
			module->connect(RTLIL::SigSig(cell_outputs, RTLIL::SigSpec(RTLIL::State::Sx, cell_outputs.size())));
			cells_to_remove.insert(cell);
		}

		return activation_patterns_cache[cell];
	}

	RTLIL::SigSpec bits_from_activation_patterns(const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &activation_patterns)
	{
		std::set<RTLIL::SigBit> all_bits;
		for (auto &it : activation_patterns) {
			std::vector<RTLIL::SigBit> bits = it.first;
			all_bits.insert(bits.begin(), bits.end());
		}

		RTLIL::SigSpec signal;
		for (auto &bit : all_bits)
			signal.append_bit(bit);

		return signal;
	}

	void filter_activation_patterns(std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &out,
			const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &in, const std::set<RTLIL::SigBit> &filter_bits)
	{
		for (auto &p : in)
		{
			std::vector<RTLIL::SigBit> p_first = p.first;
			std::pair<RTLIL::SigSpec, RTLIL::Const> new_p;

			for (int i = 0; i < SIZE(p_first); i++)
				if (filter_bits.count(p_first[i]) == 0) {
					new_p.first.append_bit(p_first[i]);
					new_p.second.bits.push_back(p.second.bits.at(i));
				}

			out.insert(new_p);
		}
	}

	RTLIL::SigSpec make_cell_activation_logic(const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &activation_patterns)
	{
		RTLIL::Wire *all_cases_wire = module->addWire(NEW_ID, 0);
		for (auto &p : activation_patterns) {
			all_cases_wire->width++;
			module->addEq(NEW_ID, p.first, p.second, RTLIL::SigSpec(all_cases_wire, all_cases_wire->width - 1));
		}
		if (all_cases_wire->width == 1)
			return all_cases_wire;
		return module->ReduceOr(NEW_ID, all_cases_wire);
	}


	// -------------
	// Setup and run
	// -------------

	ShareWorker(ShareWorkerConfig config, RTLIL::Design *design, RTLIL::Module *module) :
			config(config), design(design), module(module)
	{
		generic_ops.insert(config.generic_uni_ops.begin(), config.generic_uni_ops.end());
		generic_ops.insert(config.generic_bin_ops.begin(), config.generic_bin_ops.end());
		generic_ops.insert(config.generic_cbin_ops.begin(), config.generic_cbin_ops.end());

		fwd_ct.setup_internals();

		cone_ct.setup_internals();
		cone_ct.cell_types.erase("$mul");
		cone_ct.cell_types.erase("$mod");
		cone_ct.cell_types.erase("$div");
		cone_ct.cell_types.erase("$pow");
		cone_ct.cell_types.erase("$shl");
		cone_ct.cell_types.erase("$shr");
		cone_ct.cell_types.erase("$sshl");
		cone_ct.cell_types.erase("$sshr");

		modwalker.setup(design, module);

		find_terminal_bits();
		find_shareable_cells();

		if (shareable_cells.size() < 2)
			return;

		log("Found %d cells in module %s that may be considered for resource sharing.\n",
				SIZE(shareable_cells), log_id(module));

		while (!shareable_cells.empty())
		{
			RTLIL::Cell *cell = *shareable_cells.begin();
			shareable_cells.erase(cell);

			log("  Analyzing resource sharing options for %s:\n", log_id(cell));

			const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &cell_activation_patterns = find_cell_activation_patterns(cell, "    ");
			RTLIL::SigSpec cell_activation_signals = bits_from_activation_patterns(cell_activation_patterns);

			if (cell_activation_patterns.empty()) {
				log("    Cell is never active. Sharing is pointless, we simply remove it.\n");
				cells_to_remove.insert(cell);
				continue;
			}

			if (cell_activation_patterns.count(std::pair<RTLIL::SigSpec, RTLIL::Const>())) {
				log("    Cell is always active. Therefore no sharing is possible.\n");
				continue;
			}

			log("    Found %d activation_patterns using ctrl signal %s.\n", SIZE(cell_activation_patterns), log_signal(cell_activation_signals));

			std::vector<RTLIL::Cell*> candidates;
			find_shareable_partners(candidates, cell);

			if (candidates.empty()) {
				log("    No candidates found.\n");
				continue;
			}

			log("    Found %d candidates:", SIZE(candidates));
			for (auto c : candidates)
				log(" %s", log_id(c));
			log("\n");

			for (auto other_cell : candidates)
			{
				log("    Analyzing resource sharing with %s:\n", log_id(other_cell));

				const std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> &other_cell_activation_patterns = find_cell_activation_patterns(other_cell, "      ");
				RTLIL::SigSpec other_cell_activation_signals = bits_from_activation_patterns(other_cell_activation_patterns);

				if (other_cell_activation_patterns.empty()) {
					log("      Cell is never active. Sharing is pointless, we simply remove it.\n");
					shareable_cells.erase(other_cell);
					cells_to_remove.insert(other_cell);
					continue;
				}

				if (other_cell_activation_patterns.count(std::pair<RTLIL::SigSpec, RTLIL::Const>())) {
					log("      Cell is always active. Therefore no sharing is possible.\n");
					shareable_cells.erase(other_cell);
					continue;
				}

				log("      Found %d activation_patterns using ctrl signal %s.\n",
						SIZE(other_cell_activation_patterns), log_signal(other_cell_activation_signals));

				const std::set<RTLIL::SigBit> &cell_forbidden_controls = find_forbidden_controls(cell);
				const std::set<RTLIL::SigBit> &other_cell_forbidden_controls = find_forbidden_controls(other_cell);

				std::set<RTLIL::SigBit> union_forbidden_controls;
				union_forbidden_controls.insert(cell_forbidden_controls.begin(), cell_forbidden_controls.end());
				union_forbidden_controls.insert(other_cell_forbidden_controls.begin(), other_cell_forbidden_controls.end());

				if (!union_forbidden_controls.empty())
					log("      Forbidden control signals for this pair of cells: %s\n", log_signal(union_forbidden_controls));

				std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> filtered_cell_activation_patterns;
				std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> filtered_other_cell_activation_patterns;

				filter_activation_patterns(filtered_cell_activation_patterns, cell_activation_patterns, union_forbidden_controls);
				filter_activation_patterns(filtered_other_cell_activation_patterns, other_cell_activation_patterns, union_forbidden_controls);

				optimize_activation_patterns(filtered_cell_activation_patterns);
				optimize_activation_patterns(filtered_other_cell_activation_patterns);

				ezDefaultSAT ez;
				SatGen satgen(&ez, &modwalker.sigmap);

				std::set<RTLIL::Cell*> sat_cells;
				std::set<RTLIL::SigBit> bits_queue;

				std::vector<int> cell_active, other_cell_active;
				RTLIL::SigSpec all_ctrl_signals;

				for (auto &p : filtered_cell_activation_patterns) {
					log("      Activation pattern for cell %s: %s = %s\n", log_id(cell), log_signal(p.first), log_signal(p.second));
					cell_active.push_back(ez.vec_eq(satgen.importSigSpec(p.first), satgen.importSigSpec(p.second)));
					all_ctrl_signals.append(p.first);
				}

				for (auto &p : filtered_other_cell_activation_patterns) {
					log("      Activation pattern for cell %s: %s = %s\n", log_id(other_cell), log_signal(p.first), log_signal(p.second));
					other_cell_active.push_back(ez.vec_eq(satgen.importSigSpec(p.first), satgen.importSigSpec(p.second)));
					all_ctrl_signals.append(p.first);
				}

				for (auto &bit : cell_activation_signals.to_sigbit_vector())
					bits_queue.insert(bit);

				for (auto &bit : other_cell_activation_signals.to_sigbit_vector())
					bits_queue.insert(bit);

				while (!bits_queue.empty())
				{
					std::set<ModWalker::PortBit> portbits;
					modwalker.get_drivers(portbits, bits_queue);
					bits_queue.clear();

					for (auto &pbit : portbits)
						if (sat_cells.count(pbit.cell) == 0 && cone_ct.cell_known(pbit.cell->type)) {
							if (config.opt_fast && modwalker.cell_outputs[pbit.cell].size() >= 4)
								continue;
							// log("      Adding cell %s (%s) to SAT problem.\n", log_id(pbit.cell), log_id(pbit.cell->type));
							bits_queue.insert(modwalker.cell_inputs[pbit.cell].begin(), modwalker.cell_inputs[pbit.cell].end());
							satgen.importCell(pbit.cell);
							sat_cells.insert(pbit.cell);
						}

					if (config.opt_fast && sat_cells.size() > 100)
						break;
				}

				if (!ez.solve(ez.expression(ez.OpOr, cell_active))) {
					log("      According to the SAT solver the cell %s is never active. Sharing is pointless, we simply remove it.\n", log_id(cell));
					cells_to_remove.insert(cell);
					break;
				}

				if (!ez.solve(ez.expression(ez.OpOr, other_cell_active))) {
					log("      According to the SAT solver the cell %s is never active. Sharing is pointless, we simply remove it.\n", log_id(other_cell));
					cells_to_remove.insert(other_cell);
					shareable_cells.erase(other_cell);
					continue;
				}

				ez.non_incremental();

				all_ctrl_signals.sort_and_unify();
				std::vector<int> sat_model = satgen.importSigSpec(all_ctrl_signals);
				std::vector<bool> sat_model_values;

				ez.assume(ez.AND(ez.expression(ez.OpOr, cell_active), ez.expression(ez.OpOr, other_cell_active)));

				log("      Size of SAT problem: %d cells, %d variables, %d clauses\n",
						SIZE(sat_cells), ez.numCnfVariables(), ez.numCnfClauses());

				if (ez.solve(sat_model, sat_model_values)) {
					log("      According to the SAT solver this pair of cells can not be shared.\n");
					log("      Model from SAT solver: %s = %d'", log_signal(all_ctrl_signals), SIZE(sat_model_values));
					for (int i = SIZE(sat_model_values)-1; i >= 0; i--)
						log("%c", sat_model_values[i] ? '1' : '0');
					log("\n");
					continue;
				}

				log("      According to the SAT solver this pair of cells can be shared.\n");
				shareable_cells.erase(other_cell);

				int cell_select_score = 0;
				int other_cell_select_score = 0;

				for (auto &p : filtered_cell_activation_patterns)
					cell_select_score += p.first.size();

				for (auto &p : filtered_other_cell_activation_patterns)
					other_cell_select_score += p.first.size();

				RTLIL::Cell *supercell;
				if (cell_select_score <= other_cell_select_score) {
					RTLIL::SigSpec act = make_cell_activation_logic(filtered_cell_activation_patterns);
					supercell = make_supercell(cell, other_cell, act);
					log("      Activation signal for %s: %s\n", log_id(cell), log_signal(act));
				} else {
					RTLIL::SigSpec act = make_cell_activation_logic(filtered_other_cell_activation_patterns);
					supercell = make_supercell(other_cell, cell, act);
					log("      Activation signal for %s: %s\n", log_id(other_cell), log_signal(act));
				}

				log("      New cell: %s (%s)\n", log_id(supercell), log_id(supercell->type));

				std::set<std::pair<RTLIL::SigSpec, RTLIL::Const>> supercell_activation_patterns;
				supercell_activation_patterns.insert(filtered_cell_activation_patterns.begin(), filtered_cell_activation_patterns.end());
				supercell_activation_patterns.insert(filtered_other_cell_activation_patterns.begin(), filtered_other_cell_activation_patterns.end());
				optimize_activation_patterns(supercell_activation_patterns);
				activation_patterns_cache[supercell] = supercell_activation_patterns;
				shareable_cells.insert(supercell);

				cells_to_remove.insert(cell);
				cells_to_remove.insert(other_cell);
				break;
			}
		}

		if (!cells_to_remove.empty()) {
			log("Removing %d cells in module %s:\n", SIZE(cells_to_remove), log_id(module));
			for (auto c : cells_to_remove) {
				log("  Removing cell %s (%s).\n", log_id(c), log_id(c->type));
				module->remove(c);
			}
		}

		log_assert(recursion_state.empty());
	}
};

struct SharePass : public Pass {
	SharePass() : Pass("share", "perform sat-based resource sharing") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    share [options] [selection]\n");
		log("\n");
		log("This pass merges shareable resources into a single resource. A SAT solver\n");
		log("is used to determine if two resources are share-able.\n");
		log("\n");
		log("  -force\n");
		log("    Per default the selection of cells that is considered for sharing is\n");
		log("    narrowed using a list of cell types. With this option all selected\n");
		log("    cells are considered for resource sharing.\n");
		log("\n");
		log("    IMPORTANT NOTE: If the -all option is used then no cells with internal\n");
		log("    state must be selected!\n");
		log("\n");
		log("  -aggressive\n");
		log("    Per default some heuristics are used to reduce the number of cells\n");
		log("    considered for resource sharing to only large resources. This options\n");
		log("    turns this heuristics off, resulting in much more cells being considered\n");
		log("    for resource sharing.\n");
		log("\n");
		log("  -fast\n");
		log("    Only consider the simple part of the control logic in SAT solving, resulting\n");
		log("    in much easier SAT problems at the cost of maybe missing some oportunities\n");
		log("    for resource sharing.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		ShareWorkerConfig config;

		config.opt_force = false;
		config.opt_aggressive = false;
		config.opt_fast = false;

		config.generic_uni_ops.insert("$not");
		// config.generic_uni_ops.insert("$pos");
		config.generic_uni_ops.insert("$neg");

		config.generic_cbin_ops.insert("$and");
		config.generic_cbin_ops.insert("$or");
		config.generic_cbin_ops.insert("$xor");
		config.generic_cbin_ops.insert("$xnor");

		config.generic_bin_ops.insert("$shl");
		config.generic_bin_ops.insert("$shr");
		config.generic_bin_ops.insert("$sshl");
		config.generic_bin_ops.insert("$sshr");

		config.generic_bin_ops.insert("$lt");
		config.generic_bin_ops.insert("$le");
		config.generic_bin_ops.insert("$eq");
		config.generic_bin_ops.insert("$ne");
		config.generic_bin_ops.insert("$eqx");
		config.generic_bin_ops.insert("$nex");
		config.generic_bin_ops.insert("$ge");
		config.generic_bin_ops.insert("$gt");

		config.generic_cbin_ops.insert("$add");
		config.generic_cbin_ops.insert("$mul");

		config.generic_bin_ops.insert("$sub");
		config.generic_bin_ops.insert("$div");
		config.generic_bin_ops.insert("$mod");
		// config.generic_bin_ops.insert("$pow");

		config.generic_uni_ops.insert("$logic_not");
		config.generic_cbin_ops.insert("$logic_and");
		config.generic_cbin_ops.insert("$logic_or");

		log_header("Executing SHARE pass (SAT-based resource sharing).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-force") {
				config.opt_force = true;
				continue;
			}
			if (args[argidx] == "-aggressive") {
				config.opt_aggressive = true;
				continue;
			}
			if (args[argidx] == "-fast") {
				config.opt_fast = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules_)
			if (design->selected(mod_it.second))
				ShareWorker(config, design, mod_it.second);
	}
} SharePass;

PRIVATE_NAMESPACE_END

