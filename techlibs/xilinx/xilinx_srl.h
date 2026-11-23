#ifndef XILINX_SRL_H
#define XILINX_SRL_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

struct XilinxSrlFixedMatch
{
	IdString clk_port = {};
	IdString en_port = {};
	Cell *first = nullptr;
	Cell *next = nullptr;
};

struct XilinxSrlFixed : MatchPattern<XilinxSrlFixed, XilinxSrlFixedMatch>
{
	vector<Cell*> chain = {};
	vector<Cell*> longest_chain = {};
	pool<Cell*> non_first_cells = {};
	int minlen = {};

	vector<Cell*> first_cells = {};
	MatchIndex<std::tuple<IdString, SigBit>> next_index = {};

	XilinxSrlFixed(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &XilinxSrlFixed::start)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_), ID::FDRE, ID::FDRE_1) &&
					!cell->has_keep_attr() &&
					(!cell->type.in(ID::FDRE) || !param(cell, ID::IS_R_INVERTED).as_bool()) &&
					(!cell->type.in(ID::FDRE) || !param(cell, ID::IS_D_INVERTED).as_bool()) &&
					(!cell->type.in(ID::FDRE, ID::FDRE_1) || port(cell, ID::R, State::S0).is_fully_zero()))
				first_cells.push_back(cell);
			if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_), ID::FDRE, ID::FDRE_1) &&
					!cell->has_keep_attr() &&
					port(cell, ID::D)[0].wire && !port(cell, ID::D)[0].wire->get_bool_attribute(ID::keep) &&
					nusers(port(cell, ID::Q)) == 2)
				next_index.add({cell->type, SigBit(port(cell, ID::Q))}, cell);
		}
	}

	static void assign_ports(Match &n)
	{
		if (n.first->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_), ID::FDRE, ID::FDRE_1))
			n.clk_port = ID::C;
		else log_abort();
		if (n.first->type.in(ID($_DFF_N_), ID($_DFF_P_)))
			n.en_port = IdString::Null;
		else if (n.first->type.in(ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
			n.en_port = ID::E;
		else if (n.first->type.in(ID::FDRE, ID::FDRE_1))
			n.en_port = ID::CE;
		else log_abort();
	}

	bool next_compatible(const Match &m, Cell *next) const
	{
		return port(next, m.clk_port) == port(m.first, m.clk_port) &&
				(m.en_port == IdString::Null || port(next, m.en_port) == port(m.first, m.en_port)) &&
				(!m.first->type.in(ID::FDRE) || param(next, ID::IS_C_INVERTED).as_bool() == param(m.first, ID::IS_C_INVERTED).as_bool()) &&
				(!m.first->type.in(ID::FDRE) || param(next, ID::IS_D_INVERTED).as_bool() == param(m.first, ID::IS_D_INVERTED).as_bool()) &&
				(!m.first->type.in(ID::FDRE) || param(next, ID::IS_R_INVERTED).as_bool() == param(m.first, ID::IS_R_INVERTED).as_bool()) &&
				(!m.first->type.in(ID::FDRE, ID::FDRE_1) || port(next, ID::R, State::S0).is_fully_zero());
	}

	void start(const Match &m)
	{
		non_first_cells.clear();
		setup(m);
		if (unwinding())
			return;
		match_first(m);
	}

	void match_first(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *first : first_cells) {
			if (blacklisted(first))
				continue;
			if (non_first_cells.count(first))
				continue;
			found_any_match = true;
			Match n = m;
			n.first = first;
			frame.enter(first);
			code_chain(n);
			if (frame.leave())
				return;
		}

		if (should_generate(found_any_match, 100, 0)) {
			SigSpec C = module->addWire(NEW_ID);
			SigSpec D = module->addWire(NEW_ID);
			SigSpec Q = module->addWire(NEW_ID);
			auto r = rng(8);
			Cell* cell = nullptr;
			switch (r)
			{
			case 0:
			case 1:
				cell = module->addCell(NEW_ID, ID::FDRE);
				cell->setPort(ID::C, C);
				cell->setPort(ID::D, D);
				cell->setPort(ID::Q, Q);
				cell->setPort(ID::CE, module->addWire(NEW_ID));
				if (r & 1)
					cell->setPort(ID::R, module->addWire(NEW_ID));
				else {
					if (rng(2) == 0)
						cell->setPort(ID::R, State::S0);
				}
				break;
			case 2:
			case 3:
				cell = module->addDffGate(NEW_ID, C, D, Q, r & 1);
				break;
			case 4:
			case 5:
			case 6:
			case 7:
				cell = module->addDffeGate(NEW_ID, C, module->addWire(NEW_ID), D, Q, r & 1, r & 2);
				break;
			default: log_abort();
			}
		}
	}

	void code_chain(const Match &m)
	{
		Match n = m;
		assign_ports(n);

		longest_chain.clear();
		chain.push_back(n.first);
		tail(n);
		chain.pop_back();
		log_assert(chain.empty());
		if (GetSize(longest_chain) >= minlen)
			accept(n);
	}

	void setup(const Match &m)
	{
		match_each(m, first_cells, &Match::first, &XilinxSrlFixed::setup_code_ports);
	}

	void setup_code_ports(const Match &m)
	{
		Match n = m;
		assign_ports(n);
		setup_match_next(n);
	}

	void setup_match_next(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *next : next_index.find({m.first->type, SigBit(port(m.first, ID::D))})) {
			if (blacklisted(next))
				continue;
			if (!next_compatible(m, next))
				continue;
			Match n = m;
			n.next = next;
			frame.enter(next);
			setup_code_mark(n);
			if (frame.leave())
				return;
		}
	}

	void setup_code_mark(const Match &m)
	{
		non_first_cells.insert(m.next);
	}

	void tail(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *next : next_index.find({chain.back()->type, SigBit(port(chain.back(), ID::D))})) {
			if (blacklisted(next))
				continue;
			if (!next_compatible(m, next))
				continue;
			found_any_match = true;
			Match n = m;
			n.next = next;
			frame.enter(next);
			tail_code_extend(n);
			if (frame.leave())
				return;
		}

		if (!found_any_match) {
			Match n = m;
			n.next = nullptr;
			tail_code_extend(n);
		}

		if (should_generate(found_any_match, 100, 0)) {
			Cell *cell = module->addCell(NEW_ID, chain.back()->type);
			cell->setPort(ID::C, chain.back()->getPort(ID::C));
			cell->setPort(ID::D, module->addWire(NEW_ID));
			cell->setPort(ID::Q, chain.back()->getPort(ID::D));
			if (cell->type == ID::FDRE) {
				if (rng(2) == 0)
					cell->setPort(ID::R, port(chain.back(), ID::R, State::S0));
				cell->setPort(ID::CE, chain.back()->getPort(ID::CE));
			}
			else if (cell->type.begins_with("$_DFFE_"))
				cell->setPort(ID::E, chain.back()->getPort(ID::E));
		}
	}

	void tail_code_extend(const Match &m)
	{
		if (m.next) {
			chain.push_back(m.next);
			tail(m);
			chain.pop_back();
		} else {
			if (GetSize(chain) > GetSize(longest_chain))
				longest_chain = chain;
		}
	}
};

struct XilinxSrlVariableMatch
{
	IdString clk_port = {};
	IdString en_port = {};
	int shiftx_width = {};
	int slice = {};
	Cell *shiftx = nullptr;
	Cell *first = nullptr;
	Cell *next = nullptr;
};

struct XilinxSrlVariable : MatchPattern<XilinxSrlVariable, XilinxSrlVariableMatch>
{
	struct FfSlice {
		Cell *cell = nullptr;
		int idx = {};
	};

	int minlen = {};
	vector<pair<Cell*,int>> chain = {};
	pool<SigBit> chain_bits = {};

	vector<Cell*> shiftx_cells = {};
	MatchIndex<SigBit, FfSlice> first_index = {};
	MatchIndex<std::tuple<IdString, SigBit, SigBit>, FfSlice> next_index = {};

	XilinxSrlVariable(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &XilinxSrlVariable::start)
	{
		for (auto cell : cells) {
			if (cell->type.in(ID($shiftx)) &&
					!cell->has_keep_attr() &&
					param(cell, ID::Y_WIDTH).as_int() == 1)
				shiftx_cells.push_back(cell);
			if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_), ID($dff), ID($dffe)) &&
					!cell->has_keep_attr() &&
					port(cell, ID::Q)[0].wire && !port(cell, ID::Q)[0].wire->get_bool_attribute(ID::keep))
				for (int idx = 0; idx < GetSize(port(cell, ID::Q)); idx++)
					if (nusers(port(cell, ID::Q)[idx]) <= 2)
						first_index.add(port(cell, ID::Q)[idx], {cell, idx});
			if (cell->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_), ID($dff), ID($dffe)) &&
					!cell->has_keep_attr() &&
					port(cell, ID::D)[0].wire && !port(cell, ID::D)[0].wire->get_bool_attribute(ID::keep))
				for (int idx = 0; idx < GetSize(port(cell, ID::Q)); idx++)
					if (nusers(port(cell, ID::Q)[idx]) <= 3)
						next_index.add({cell->type, port(cell, ID::Q)[idx], port(cell, ID::Q)[idx]}, {cell, idx});
		}
	}

	void start(const Match &m)
	{
		chain_bits.clear();
		match_shiftx(m);
	}

	void match_shiftx(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (Cell *shiftx : shiftx_cells) {
			if (blacklisted(shiftx))
				continue;
			if (param(shiftx, ID::A_WIDTH).as_int() < minlen)
				continue;
			found_any_match = true;
			Match n = m;
			n.shiftx = shiftx;
			frame.enter(shiftx);
			code_shiftx_width(n);
			if (frame.leave())
				return;
		}

		if (should_generate(found_any_match, 100, 0)) {
			minlen = 3;
			module->addShiftx(NEW_ID, module->addWire(NEW_ID, rng(6)+minlen), module->addWire(NEW_ID, 3), module->addWire(NEW_ID));
		}
	}

	void code_shiftx_width(const Match &m)
	{
		Match n = m;
		n.shiftx_width = param(n.shiftx, ID::A_WIDTH).as_int();
		match_first(n);
	}

	void match_first(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (auto &[first, idx] : first_index.find(port(m.shiftx, ID::A)[m.shiftx_width-1])) {
			if (blacklisted(first))
				continue;
			found_any_match = true;
			Match n = m;
			n.first = first;
			n.slice = idx;
			frame.enter(first);
			code_chain(n);
			if (frame.leave())
				return;
		}

		if (should_generate(found_any_match, 100, 0)) {
			SigSpec C = module->addWire(NEW_ID);
			auto WIDTH = rng(3)+1;
			SigSpec D = module->addWire(NEW_ID, WIDTH);
			SigSpec Q = module->addWire(NEW_ID, WIDTH);
			auto r = rng(8);
			Cell *cell = nullptr;
			switch (r)
			{
			case 0:
			case 1:
				cell = module->addDff(NEW_ID, C, D, Q, r & 1);
				break;
			case 2:
			case 3:
			case 4:
			case 5:
				//cell = module->addDffe(NEW_ID, C, module->addWire(NEW_ID), D, Q, r & 1, r & 4);
				//break;
			case 6:
			case 7:
				WIDTH = 1;
				cell = module->addDffGate(NEW_ID, C, D[0], Q[0], r & 1);
				break;
			default: log_abort();
			}
			m.shiftx->connections_.at(ID::A)[m.shiftx_width-1] = port(cell, ID::Q)[rng(WIDTH)];
		}
	}

	void code_chain(const Match &m)
	{
		Match n = m;
		if (n.first->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
			n.clk_port = ID::C;
		else if (n.first->type.in(ID($dff), ID($dffe)))
			n.clk_port = ID::CLK;
		else log_abort();
		if (n.first->type.in(ID($_DFF_N_), ID($_DFF_P_), ID($dff)))
			n.en_port = IdString::Null;
		else if (n.first->type.in(ID($_DFFE_NN_), ID($_DFFE_NP_), ID($_DFFE_PN_), ID($_DFFE_PP_)))
			n.en_port = ID::E;
		else if (n.first->type.in(ID($dffe)))
			n.en_port = ID::EN;
		else log_abort();

		chain_bits.insert(port(n.first, ID::Q)[n.slice]);
		chain.emplace_back(n.first, n.slice);
		tail(n);
		if (GetSize(chain) == n.shiftx_width)
			accept(n);
		chain.clear();
	}

	void tail(const Match &m)
	{
		bool found_any_match = false;
		MatchFrame frame(ctx);
		for (auto &[next, idx] : next_index.find({chain.back().first->type, port(chain.back().first, ID::D)[chain.back().second], port(m.shiftx, ID::A)[m.shiftx_width-1-GetSize(chain)]})) {
			if (blacklisted(next))
				continue;
			if (port(next, m.clk_port) != port(m.first, m.clk_port))
				continue;
			if (m.en_port != IdString::Null && port(next, m.en_port) != port(m.first, m.en_port))
				continue;
			if (next->type.in(ID($dff), ID($dffe)) && param(next, ID::CLK_POLARITY).as_bool() != param(m.first, ID::CLK_POLARITY).as_bool())
				continue;
			if (next->type.in(ID($dffe)) && param(next, ID::EN_POLARITY).as_bool() != param(m.first, ID::EN_POLARITY).as_bool())
				continue;
			if (chain_bits.count(port(next, ID::D)[idx]))
				continue;
			found_any_match = true;
			Match n = m;
			n.next = next;
			n.slice = idx;
			frame.enter(next);
			tail_code_extend(n);
			if (frame.leave())
				return;
		}

		if (!found_any_match) {
			Match n = m;
			n.next = nullptr;
			tail_code_extend(n);
		}

		if (should_generate(found_any_match, 100, 0)) {
			if (GetSize(chain) < m.shiftx_width) {
				auto back = chain.back().first;
				auto slice = chain.back().second;
				if (back->type.in(ID($dff), ID($dffe))) {
					auto WIDTH = GetSize(port(back, ID::D));
					if (rng(2) == 0 && slice < WIDTH-1) {
						auto new_slice = slice + rng(WIDTH-1-slice);
						back->connections_.at(ID::D)[slice] = port(back, ID::Q)[new_slice];
					}
					else {
						auto D = module->addWire(NEW_ID, WIDTH);
						if (back->type == ID($dff))
							module->addDff(NEW_ID, port(back, ID::CLK), D, port(back, ID::D), param(back, ID::CLK_POLARITY).as_bool());
						else if (back->type == ID($dffe))
							module->addDffe(NEW_ID, port(back, ID::CLK), port(back, ID::EN), D, port(back, ID::D), param(back, ID::CLK_POLARITY).as_bool(), param(back, ID::EN_POLARITY).as_bool());
						else
							log_abort();
					}
				}
				else if (back->type.begins_with("$_DFF_")) {
					Cell *cell = module->addCell(NEW_ID, back->type);
					cell->setPort(ID::C, back->getPort(ID::C));
					cell->setPort(ID::D, module->addWire(NEW_ID));
					cell->setPort(ID::Q, back->getPort(ID::D));
				}
				else
					log_abort();
				m.shiftx->connections_.at(ID::A)[m.shiftx_width-1-GetSize(chain)] = port(back, ID::D)[slice];
			}
		}
	}

	void tail_code_extend(const Match &m)
	{
		if (m.next) {
			chain_bits.insert(port(m.next, ID::Q)[m.slice]);
			chain.emplace_back(m.next, m.slice);
			if (GetSize(chain) < m.shiftx_width)
				tail(m);
		}
	}
};

YOSYS_NAMESPACE_END

#endif
