/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHERWISE, ARISING OUT OF OR IN
 *  CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct OptAndOrPmuxWorker
{
	struct DriverBit {
		Cell *cell = nullptr;
		IdString port;
		int index = -1;
	};

	struct ConsumerBit {
		Cell *cell = nullptr;
		IdString port;
		int index = -1;
	};

	struct EqInfo {
		SigSpec select;
		Const value;
		SigBit bit;
	};

	struct DataExpr {
		std::vector<SigBit> factors;
	};

	struct Contribution {
		EqInfo eq;
		DataExpr data;
	};

	enum TermResult {
		TERM_FAIL,
		TERM_ZERO,
		TERM_OK,
	};

	struct Arm {
		Const value;
		SigBit select_bit;
		std::vector<std::vector<DataExpr>> bits;
	};

	struct BitContribs {
		int bit_idx = -1;
		SigSpec select;
		std::vector<Contribution> contribs;
	};

	struct SelectGroup {
		SigSpec select;
		std::vector<BitContribs> bits;
	};

	Module *module;
	SigMap sigmap;

	dict<SigBit, DriverBit> bit_drivers;
	dict<SigBit, std::vector<ConsumerBit>> bit_consumers;
	pool<SigBit> observable_bits;
	pool<Cell*> removed_cells;

	int converted_count = 0;
	static const int max_cone_bits = 100000;
	static const int min_pmux_bits = 8;

	OptAndOrPmuxWorker(Module *module) : module(module), sigmap(module)
	{
		run();
	}

	void build_maps()
	{
		bit_drivers.clear();
		bit_consumers.clear();
		observable_bits.clear();

		for (auto cell : module->cells())
		{
			for (auto &conn : cell->connections())
			{
				SigSpec sig = sigmap(conn.second);

				if (cell->output(conn.first)) {
					for (int i = 0; i < GetSize(sig); i++) {
						SigBit bit = sig[i];
						if (bit.wire == nullptr)
							continue;
						if (bit_drivers.count(bit))
							bit_drivers[bit].cell = nullptr;
						else
							bit_drivers[bit] = {cell, conn.first, i};
					}
				}

				if (cell->input(conn.first)) {
					for (int i = 0; i < GetSize(sig); i++) {
						SigBit bit = sig[i];
						if (bit.wire == nullptr)
							continue;
						bit_consumers[bit].push_back({cell, conn.first, i});
					}
				}
			}
		}

		for (auto &conn : module->connections())
		{
			SigSpec lhs = conn.first;
			SigSpec rhs = sigmap(conn.second);
			for (int i = 0; i < std::min(GetSize(lhs), GetSize(rhs)); i++) {
				SigBit lhs_bit = lhs[i];
				SigBit rhs_bit = rhs[i];
				if (lhs_bit.wire == nullptr)
					continue;
				if (lhs_bit.wire->port_output || lhs_bit.wire->get_bool_attribute(ID::keep)) {
					observable_bits.insert(lhs_bit);
					observable_bits.insert(rhs_bit);
				}
			}
		}
	}

	bool get_driver(SigBit bit, DriverBit &driver) const
	{
		bit = sigmap(bit);
		auto it = bit_drivers.find(bit);
		if (it == bit_drivers.end() || it->second.cell == nullptr)
			return false;
		if (removed_cells.count(it->second.cell))
			return false;
		driver = it->second;
		return true;
	}

	bool get_input_bit(Cell *cell, IdString port, int index, SigBit &bit) const
	{
		SigSpec sig = sigmap(cell->getPort(port));
		if (index < 0 || index >= GetSize(sig))
			return false;
		bit = sig[index];
		return true;
	}

	bool bit_has_observable_output(SigBit bit) const
	{
		bit = sigmap(bit);
		if (bit.wire == nullptr)
			return false;
		if (bit.wire->port_output || bit.wire->get_bool_attribute(ID::keep))
			return true;
		if (observable_bits.count(bit))
			return true;
		auto it = bit_consumers.find(bit);
		if (it != bit_consumers.end())
			for (auto &consumer : it->second)
				if (!removed_cells.count(consumer.cell))
					return true;
		return false;
	}

	bool match_eq(SigBit bit, EqInfo &eq) const
	{
		DriverBit driver;
		if (!get_driver(bit, driver))
			return false;

		Cell *cell = driver.cell;
		if (driver.port != ID::Y || driver.index != 0 || cell->type != ID($eq))
			return false;

		SigSpec nonconst_sig = sigmap(cell->getPort(ID::A));
		SigSpec const_sig = sigmap(cell->getPort(ID::B));

		if (!const_sig.is_fully_const()) {
			if (!nonconst_sig.is_fully_const())
				return false;
			std::swap(nonconst_sig, const_sig);
		}

		if (nonconst_sig.empty() || const_sig.empty() || nonconst_sig.is_fully_const())
			return false;

		eq.select = nonconst_sig;
		eq.value = const_sig.as_const();
		eq.bit = sigmap(bit);
		return true;
	}

	bool collect_or_terms(SigBit bit, std::vector<SigBit> &terms, pool<SigBit> &seen, int &budget) const
	{
		if (--budget < 0)
			return false;

		bit = sigmap(bit);

		if (bit == State::S0 || bit == State::Sx || bit == State::Sz)
			return true;
		if (bit == State::S1)
			return false;

		if (!seen.insert(bit).second)
			return false;

		DriverBit driver;
		if (get_driver(bit, driver) && driver.port == ID::Y && driver.cell->type == ID($or)) {
			SigBit a, b;
			if (!get_input_bit(driver.cell, ID::A, driver.index, a))
				return false;
			if (!get_input_bit(driver.cell, ID::B, driver.index, b))
				return false;
			return collect_or_terms(a, terms, seen, budget) && collect_or_terms(b, terms, seen, budget);
		}

		terms.push_back(bit);
		return true;
	}

	bool collect_and_factors(SigBit bit, std::vector<SigBit> &factors, pool<SigBit> &seen, int &budget) const
	{
		if (--budget < 0)
			return false;

		bit = sigmap(bit);

		if (bit == State::S0 || bit == State::S1 || bit == State::Sx || bit == State::Sz) {
			factors.push_back(bit);
			return true;
		}

		if (!seen.insert(bit).second)
			return false;

		DriverBit driver;
		if (get_driver(bit, driver) && driver.port == ID::Y && driver.cell->type == ID($and)) {
			SigBit a, b;
			if (!get_input_bit(driver.cell, ID::A, driver.index, a))
				return false;
			if (!get_input_bit(driver.cell, ID::B, driver.index, b))
				return false;
			return collect_and_factors(a, factors, seen, budget) && collect_and_factors(b, factors, seen, budget);
		}

		factors.push_back(bit);
		return true;
	}

	TermResult parse_term(SigBit bit, Contribution &contrib) const
	{
		EqInfo direct_eq;
		if (match_eq(bit, direct_eq)) {
			contrib.eq = direct_eq;
			contrib.data.factors.clear();
			return TERM_OK;
		}

		std::vector<SigBit> factors;
		pool<SigBit> seen;
		int budget = max_cone_bits;
		if (!collect_and_factors(bit, factors, seen, budget))
			return TERM_FAIL;

		bool have_eq = false;
		for (auto factor : factors)
		{
			factor = sigmap(factor);
			if (factor == State::S0)
				return TERM_ZERO;
			if (factor == State::Sx || factor == State::Sz)
				return TERM_FAIL;
			if (factor == State::S1)
				continue;

			EqInfo eq;
			if (match_eq(factor, eq)) {
				if (!have_eq) {
					contrib.eq = eq;
					have_eq = true;
				} else if (contrib.eq.select != eq.select || contrib.eq.value != eq.value) {
					return TERM_FAIL;
				}
				continue;
			}

			contrib.data.factors.push_back(factor);
		}

		return have_eq ? TERM_OK : TERM_FAIL;
	}

	SigBit make_and_tree(Cell *cell, const std::vector<SigBit> &factors, const std::string &src)
	{
		SigBit result = State::S1;

		for (auto factor : factors)
		{
			factor = sigmap(factor);
			if (factor == State::S0 || factor == State::Sx || factor == State::Sz)
				return State::S0;
			if (factor == State::S1)
				continue;
			if (result == State::S1) {
				result = factor;
				continue;
			}

			Wire *wire = module->addWire(NEW_ID2_SUFFIX("andor_pmux_data_and"), 1);
			module->addAnd(NEW_ID2_SUFFIX("andor_pmux_data_and"), result, factor, SigBit(wire), false, src);
			result = SigBit(wire);
		}

		return result;
	}

	SigBit make_or_tree(Cell *cell, const std::vector<SigBit> &terms, const std::string &src)
	{
		SigBit result = State::S0;

		for (auto term : terms)
		{
			term = sigmap(term);
			if (term == State::S1)
				return State::S1;
			if (term == State::S0 || term == State::Sx || term == State::Sz)
				continue;
			if (result == State::S0) {
				result = term;
				continue;
			}

			Wire *wire = module->addWire(NEW_ID2_SUFFIX("andor_pmux_data_or"), 1);
			module->addOr(NEW_ID2_SUFFIX("andor_pmux_data_or"), result, term, SigBit(wire), false, src);
			result = SigBit(wire);
		}

		return result;
	}

	SigBit emit_data_bit(Cell *cell, const std::vector<DataExpr> &exprs, const std::string &src)
	{
		std::vector<SigBit> terms;
		for (auto &expr : exprs) {
			SigBit term = make_and_tree(cell, expr.factors, src);
			if (term == State::S1)
				return State::S1;
			if (term != State::S0 && term != State::Sx && term != State::Sz)
				terms.push_back(term);
		}
		return make_or_tree(cell, terms, src);
	}

	bool collect_bit_contribs(Cell *cell, int bit_idx, BitContribs &bit_contribs) const
	{
		SigSpec y = sigmap(cell->getPort(ID::Y));
		SigBit y_bit = y[bit_idx];

		if (!bit_has_observable_output(y_bit))
			return false;

		std::vector<SigBit> terms;
		pool<SigBit> seen;
		int budget = max_cone_bits;
		if (!collect_or_terms(y_bit, terms, seen, budget))
			return false;

		bit_contribs.bit_idx = bit_idx;
		for (auto term : terms)
		{
			Contribution contrib;
			TermResult result = parse_term(term, contrib);
			if (result == TERM_ZERO)
				continue;
			if (result == TERM_FAIL)
				return false;

			if (bit_contribs.select.empty())
				bit_contribs.select = contrib.eq.select;
			else if (bit_contribs.select != contrib.eq.select)
				return false;

			bit_contribs.contribs.push_back(contrib);
		}

		return !bit_contribs.contribs.empty();
	}

	bool convert_group(Cell *cell, const SelectGroup &group, pool<int> &converted_bits)
	{
		SigSpec y = sigmap(cell->getPort(ID::Y));
		int width = GetSize(group.bits);
		if (width == 0)
			return false;

		std::vector<Arm> arms;
		dict<Const, int> arm_index;

		for (int group_bit_idx = 0; group_bit_idx < width; group_bit_idx++)
		{
			const BitContribs &bit_contribs = group.bits[group_bit_idx];
			for (auto &contrib : bit_contribs.contribs)
			{
				int arm_idx;
				auto it = arm_index.find(contrib.eq.value);
				if (it == arm_index.end()) {
					arm_idx = GetSize(arms);
					arms.push_back({contrib.eq.value, contrib.eq.bit, std::vector<std::vector<DataExpr>>(width)});
					arm_index[contrib.eq.value] = arm_idx;
				} else {
					arm_idx = it->second;
				}

				arms[arm_idx].bits[group_bit_idx].push_back(contrib.data);
			}
		}

		if (GetSize(arms) < 2 || GetSize(arms) * width < min_pmux_bits)
			return false;

		SigSpec pmux_y, pmux_s, pmux_b;
		std::string src = cell->get_src_attribute();

		for (auto &bit_contribs : group.bits)
			pmux_y.append(y[bit_contribs.bit_idx]);

		for (auto &arm : arms)
		{
			SigSpec data;
			for (int bit_idx = 0; bit_idx < width; bit_idx++)
				data.append(emit_data_bit(cell, arm.bits[bit_idx], src));

			pmux_b.append(data);
			pmux_s.append(arm.select_bit);
		}

		log("Converting AND/OR mux %s.%s to a $pmux with %d cases and width %d.\n",
				log_id(module), log_id(cell), GetSize(arms), width);

		module->addPmux(NEW_ID2_SUFFIX("andor_pmux"), Const(State::S0, width), pmux_b, pmux_s, pmux_y, src);
		for (auto &bit_contribs : group.bits)
			converted_bits.insert(bit_contribs.bit_idx);
		converted_count++;
		return true;
	}

	bool try_convert(Cell *cell)
	{
		if (removed_cells.count(cell))
			return false;
		if (cell->type != ID($or) || cell->get_bool_attribute(ID::keep))
			return false;

		SigSpec y = sigmap(cell->getPort(ID::Y));
		SigSpec a = sigmap(cell->getPort(ID::A));
		SigSpec b = sigmap(cell->getPort(ID::B));
		int width = GetSize(y);
		if (width == 0)
			return false;

		std::vector<SelectGroup> groups;

		for (int bit_idx = 0; bit_idx < width; bit_idx++)
		{
			BitContribs bit_contribs;
			if (!collect_bit_contribs(cell, bit_idx, bit_contribs))
				continue;

			bool found = false;
			for (auto &group : groups) {
				if (group.select == bit_contribs.select) {
					group.bits.push_back(bit_contribs);
					found = true;
					break;
				}
			}
			if (!found)
				groups.push_back({bit_contribs.select, {bit_contribs}});
		}

		pool<int> converted_bits;
		for (auto &group : groups)
			convert_group(cell, group, converted_bits);

		if (converted_bits.empty())
			return false;

		SigSpec keep_a, keep_b, keep_y;
		for (int bit_idx = 0; bit_idx < width; bit_idx++) {
			if (converted_bits.count(bit_idx))
				continue;
			keep_a.append(a[bit_idx]);
			keep_b.append(b[bit_idx]);
			keep_y.append(y[bit_idx]);
		}

		std::string src = cell->get_src_attribute();
		if (!keep_y.empty())
			module->addOr(NEW_ID2_SUFFIX("andor_pmux_keep_or"), keep_a, keep_b, keep_y, false, src);
		removed_cells.insert(cell);
		module->remove(cell);

		return true;
	}

	void run()
	{
		build_maps();

		std::vector<Cell*> cells;
		for (auto cell : module->selected_cells())
			cells.push_back(cell);

		for (auto cell : cells)
			if (try_convert(cell))
				build_maps();
	}
};

struct OptAndOrPmuxPass : public Pass {
	OptAndOrPmuxPass() : Pass("opt_andor_pmux", "convert equality-decoded AND/OR muxes to $pmux") { }

	void help() override
	{
		log("\n");
		log("    opt_andor_pmux [selection]\n");
		log("\n");
		log("This pass converts logic of the form:\n");
		log("\n");
		log("    (sel == C0 & D0) | (sel == C1 & D1) | ...\n");
		log("\n");
		log("into $pmux cells. It only rewrites terms whose select conditions are\n");
		log("equality comparisons against distinct constants of the same select signal.\n");
		log("Very small conversions are ignored to avoid replacing tiny boolean cones.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing OPT_ANDOR_PMUX pass (AND/OR muxes to $pmux).\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		int total_converted = 0;
		for (auto module : design->selected_modules()) {
			OptAndOrPmuxWorker worker(module);
			total_converted += worker.converted_count;
		}

		if (total_converted)
			design->scratchpad_set_bool("opt.did_something", true);

		log("Converted %d AND/OR muxes to $pmux cells.\n", total_converted);
	}
} OptAndOrPmuxPass;

PRIVATE_NAMESPACE_END
