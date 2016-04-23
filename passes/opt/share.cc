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
#include "kernel/utils.h"
#include "kernel/macc.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

typedef RTLIL::IdString::compare_ptr_by_name<RTLIL::Cell> cell_ptr_cmp;
typedef std::pair<RTLIL::SigSpec, RTLIL::Const> ssc_pair_t;

struct ShareWorkerConfig
{
	int limit;
	bool opt_force;
	bool opt_aggressive;
	bool opt_fast;
	pool<RTLIL::IdString> generic_uni_ops, generic_bin_ops, generic_cbin_ops, generic_other_ops;
};

struct ShareWorker
{
	ShareWorkerConfig config;
	pool<RTLIL::IdString> generic_ops;

	RTLIL::Design *design;
	RTLIL::Module *module;

	CellTypes fwd_ct, cone_ct;
	ModWalker modwalker;
	ModIndex mi;

	pool<RTLIL::Cell*> cells_to_remove;
	pool<RTLIL::Cell*> recursion_state;

	SigMap topo_sigmap;
	std::map<RTLIL::Cell*, std::set<RTLIL::Cell*, cell_ptr_cmp>, cell_ptr_cmp> topo_cell_drivers;
	std::map<RTLIL::SigBit, std::set<RTLIL::Cell*, cell_ptr_cmp>> topo_bit_drivers;

	std::vector<std::pair<RTLIL::SigBit, RTLIL::SigBit>> exclusive_ctrls;


	// ------------------------------------------------------------------------------
	// Find terminal bits -- i.e. bits that do not (exclusively) feed into a mux tree
	// ------------------------------------------------------------------------------

	pool<RTLIL::SigBit> terminal_bits;

	void find_terminal_bits()
	{
		pool<RTLIL::SigBit> queue_bits;
		pool<RTLIL::Cell*> visited_cells;

		queue_bits.insert(modwalker.signal_outputs.begin(), modwalker.signal_outputs.end());

		for (auto &it : module->cells_)
			if (!fwd_ct.cell_known(it.second->type)) {
				pool<RTLIL::SigBit> &bits = modwalker.cell_inputs[it.second];
				queue_bits.insert(bits.begin(), bits.end());
			}

		terminal_bits.insert(queue_bits.begin(), queue_bits.end());

		while (!queue_bits.empty())
		{
			pool<ModWalker::PortBit> portbits;
			modwalker.get_drivers(portbits, queue_bits);
			queue_bits.clear();

			for (auto &pbit : portbits) {
				if (pbit.cell->type == "$mux" || pbit.cell->type == "$pmux") {
					pool<RTLIL::SigBit> bits = modwalker.sigmap(pbit.cell->getPort("\\S")).to_sigbit_pool();
					terminal_bits.insert(bits.begin(), bits.end());
					queue_bits.insert(bits.begin(), bits.end());
					visited_cells.insert(pbit.cell);
				}
				if (fwd_ct.cell_known(pbit.cell->type) && visited_cells.count(pbit.cell) == 0) {
					pool<RTLIL::SigBit> &bits = modwalker.cell_inputs[pbit.cell];
					terminal_bits.insert(bits.begin(), bits.end());
					queue_bits.insert(bits.begin(), bits.end());
					visited_cells.insert(pbit.cell);
				}
			}
		}
	}


	// ---------------------------------------------------
	// Code for sharing and comparing MACC cells
	// ---------------------------------------------------

	static int bits_macc_port(const Macc::port_t &p, int width)
	{
		if (GetSize(p.in_a) == 0 || GetSize(p.in_b) == 0)
			return min(max(GetSize(p.in_a), GetSize(p.in_b)), width);
		return min(GetSize(p.in_a), width) * min(GetSize(p.in_b), width) / 2;
	}

	static int bits_macc(const Macc &m, int width)
	{
		int bits = GetSize(m.bit_ports);
		for (auto &p : m.ports)
			bits += bits_macc_port(p, width);
		return bits;
	}

	static int bits_macc(RTLIL::Cell *c)
	{
		Macc m(c);
		int width = GetSize(c->getPort("\\Y"));
		return bits_macc(m, width);
	}

	static bool cmp_macc_ports(const Macc::port_t &p1, const Macc::port_t &p2)
	{
		bool mul1 = GetSize(p1.in_a) && GetSize(p1.in_b);
		bool mul2 = GetSize(p2.in_a) && GetSize(p2.in_b);

		int w1 = mul1 ? GetSize(p1.in_a) * GetSize(p1.in_b) : GetSize(p1.in_a) + GetSize(p1.in_b);
		int w2 = mul2 ? GetSize(p2.in_a) * GetSize(p2.in_b) : GetSize(p2.in_a) + GetSize(p2.in_b);

		if (mul1 != mul2)
			return mul1;

		if (w1 != w2)
			return w1 > w2;

		if (p1.is_signed != p2.is_signed)
			return p1.is_signed < p2.is_signed;

		if (p1.do_subtract != p2.do_subtract)
			return p1.do_subtract < p2.do_subtract;

		if (p1.in_a != p2.in_a)
			return p1.in_a < p2.in_a;

		if (p1.in_b != p2.in_b)
			return p1.in_b < p2.in_b;

		return false;
	}

	int share_macc_ports(Macc::port_t &p1, Macc::port_t &p2, int w1, int w2,
			RTLIL::SigSpec act = RTLIL::SigSpec(), Macc *supermacc = nullptr, pool<RTLIL::Cell*> *supercell_aux = nullptr)
	{
		if (p1.do_subtract != p2.do_subtract)
			return -1;

		bool mul1 = GetSize(p1.in_a) && GetSize(p1.in_b);
		bool mul2 = GetSize(p2.in_a) && GetSize(p2.in_b);

		if (mul1 != mul2)
			return -1;

		bool force_signed = false, force_not_signed = false;

		if ((GetSize(p1.in_a) && GetSize(p1.in_a) < w1) || (GetSize(p1.in_b) && GetSize(p1.in_b) < w1)) {
			if (p1.is_signed)
				force_signed = true;
			else
				force_not_signed = true;
		}

		if ((GetSize(p2.in_a) && GetSize(p2.in_a) < w2) || (GetSize(p2.in_b) && GetSize(p2.in_b) < w2)) {
			if (p2.is_signed)
				force_signed = true;
			else
				force_not_signed = true;
		}

		if (force_signed && force_not_signed)
			return -1;

		if (supermacc)
		{
			RTLIL::SigSpec sig_a1 = p1.in_a, sig_b1 = p1.in_b;
			RTLIL::SigSpec sig_a2 = p2.in_a, sig_b2 = p2.in_b;

			RTLIL::SigSpec sig_a = GetSize(sig_a1) > GetSize(sig_a2) ? sig_a1 : sig_a2;
			RTLIL::SigSpec sig_b = GetSize(sig_b1) > GetSize(sig_b2) ? sig_b1 : sig_b2;

			sig_a1.extend_u0(GetSize(sig_a), p1.is_signed);
			sig_b1.extend_u0(GetSize(sig_b), p1.is_signed);

			sig_a2.extend_u0(GetSize(sig_a), p2.is_signed);
			sig_b2.extend_u0(GetSize(sig_b), p2.is_signed);

			if (supercell_aux && GetSize(sig_a)) {
				sig_a = module->addWire(NEW_ID, GetSize(sig_a));
				supercell_aux->insert(module->addMux(NEW_ID, sig_a2, sig_a1, act, sig_a));
			}

			if (supercell_aux && GetSize(sig_b)) {
				sig_b = module->addWire(NEW_ID, GetSize(sig_b));
				supercell_aux->insert(module->addMux(NEW_ID, sig_b2, sig_b1, act, sig_b));
			}

			Macc::port_t p;
			p.in_a = sig_a;
			p.in_b = sig_b;
			p.is_signed = force_signed;
			p.do_subtract = p1.do_subtract;
			supermacc->ports.push_back(p);
		}

		int score = 1000 + abs(GetSize(p1.in_a) - GetSize(p2.in_a)) * max(abs(GetSize(p1.in_b) - GetSize(p2.in_b)), 1);

		for (int i = 0; i < min(GetSize(p1.in_a), GetSize(p2.in_a)); i++)
			if (p1.in_a[i] == p2.in_a[i] && score > 0)
				score--;

		for (int i = 0; i < min(GetSize(p1.in_b), GetSize(p2.in_b)); i++)
			if (p1.in_b[i] == p2.in_b[i] && score > 0)
				score--;

		return score;
	}

	int share_macc(RTLIL::Cell *c1, RTLIL::Cell *c2,
			RTLIL::SigSpec act = RTLIL::SigSpec(), RTLIL::Cell *supercell = nullptr, pool<RTLIL::Cell*> *supercell_aux = nullptr)
	{
		Macc m1(c1), m2(c2), supermacc;

		int w1 = GetSize(c1->getPort("\\Y")), w2 = GetSize(c2->getPort("\\Y"));
		int width = max(w1, w2);

		m1.optimize(w1);
		m2.optimize(w2);

		std::sort(m1.ports.begin(), m1.ports.end(), cmp_macc_ports);
		std::sort(m2.ports.begin(), m2.ports.end(), cmp_macc_ports);

		std::set<int> m1_unmapped, m2_unmapped;

		for (int i = 0; i < GetSize(m1.ports); i++)
			m1_unmapped.insert(i);

		for (int i = 0; i < GetSize(m2.ports); i++)
			m2_unmapped.insert(i);

		while (1)
		{
			int best_i = -1, best_j = -1, best_score = 0;

			for (int i : m1_unmapped)
			for (int j : m2_unmapped) {
				int score = share_macc_ports(m1.ports[i], m2.ports[j], w1, w2);
				if (score >= 0 && (best_i < 0 || best_score > score))
					best_i = i, best_j = j, best_score = score;
			}

			if (best_i >= 0) {
				m1_unmapped.erase(best_i);
				m2_unmapped.erase(best_j);
				share_macc_ports(m1.ports[best_i], m2.ports[best_j], w1, w2, act, &supermacc, supercell_aux);
			} else
				break;
		}

		for (int i : m1_unmapped)
		{
			RTLIL::SigSpec sig_a = m1.ports[i].in_a;
			RTLIL::SigSpec sig_b = m1.ports[i].in_b;

			if (supercell_aux && GetSize(sig_a)) {
				sig_a = module->addWire(NEW_ID, GetSize(sig_a));
				supercell_aux->insert(module->addMux(NEW_ID, RTLIL::SigSpec(0, GetSize(sig_a)), m1.ports[i].in_a, act, sig_a));
			}

			if (supercell_aux && GetSize(sig_b)) {
				sig_b = module->addWire(NEW_ID, GetSize(sig_b));
				supercell_aux->insert(module->addMux(NEW_ID, RTLIL::SigSpec(0, GetSize(sig_b)), m1.ports[i].in_b, act, sig_b));
			}

			Macc::port_t p;
			p.in_a = sig_a;
			p.in_b = sig_b;
			p.is_signed = m1.ports[i].is_signed;
			p.do_subtract = m1.ports[i].do_subtract;
			supermacc.ports.push_back(p);
		}

		for (int i : m2_unmapped)
		{
			RTLIL::SigSpec sig_a = m2.ports[i].in_a;
			RTLIL::SigSpec sig_b = m2.ports[i].in_b;

			if (supercell_aux && GetSize(sig_a)) {
				sig_a = module->addWire(NEW_ID, GetSize(sig_a));
				supercell_aux->insert(module->addMux(NEW_ID, m2.ports[i].in_a, RTLIL::SigSpec(0, GetSize(sig_a)), act, sig_a));
			}

			if (supercell_aux && GetSize(sig_b)) {
				sig_b = module->addWire(NEW_ID, GetSize(sig_b));
				supercell_aux->insert(module->addMux(NEW_ID, m2.ports[i].in_b, RTLIL::SigSpec(0, GetSize(sig_b)), act, sig_b));
			}

			Macc::port_t p;
			p.in_a = sig_a;
			p.in_b = sig_b;
			p.is_signed = m2.ports[i].is_signed;
			p.do_subtract = m2.ports[i].do_subtract;
			supermacc.ports.push_back(p);
		}

		if (supercell)
		{
			RTLIL::SigSpec sig_y = module->addWire(NEW_ID, width);

			supercell_aux->insert(module->addPos(NEW_ID, sig_y, c1->getPort("\\Y")));
			supercell_aux->insert(module->addPos(NEW_ID, sig_y, c2->getPort("\\Y")));

			supercell->setParam("\\Y_WIDTH", width);
			supercell->setPort("\\Y", sig_y);

			supermacc.optimize(width);
			supermacc.to_cell(supercell);
		}

		return bits_macc(supermacc, width);
	}


	// ---------------------------------------------------
	// Find shareable cells and compatible groups of cells
	// ---------------------------------------------------

	pool<RTLIL::Cell*> shareable_cells;

	void find_shareable_cells()
	{
		for (auto cell : module->cells())
		{
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
				if (cell->parameters.at("\\CLK_ENABLE").as_bool())
					continue;
				if (config.opt_aggressive || !modwalker.sigmap(cell->getPort("\\ADDR")).is_fully_const())
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
				if (config.opt_aggressive)
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

				if (max(a1_width, a2_width) > 2 * min(a1_width, a2_width)) return false;
				if (max(y1_width, y2_width) > 2 * min(y1_width, y2_width)) return false;
			}

			return true;
		}

		if (config.generic_bin_ops.count(c1->type) || c1->type == "$alu")
		{
			if (!config.opt_aggressive)
			{
				int a1_width = c1->parameters.at("\\A_WIDTH").as_int();
				int b1_width = c1->parameters.at("\\B_WIDTH").as_int();
				int y1_width = c1->parameters.at("\\Y_WIDTH").as_int();

				int a2_width = c2->parameters.at("\\A_WIDTH").as_int();
				int b2_width = c2->parameters.at("\\B_WIDTH").as_int();
				int y2_width = c2->parameters.at("\\Y_WIDTH").as_int();

				if (max(a1_width, a2_width) > 2 * min(a1_width, a2_width)) return false;
				if (max(b1_width, b2_width) > 2 * min(b1_width, b2_width)) return false;
				if (max(y1_width, y2_width) > 2 * min(y1_width, y2_width)) return false;
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

				int min1_width = min(a1_width, b1_width);
				int max1_width = max(a1_width, b1_width);

				int min2_width = min(a2_width, b2_width);
				int max2_width = max(a2_width, b2_width);

				if (max(min1_width, min2_width) > 2 * min(min1_width, min2_width)) return false;
				if (max(max1_width, max2_width) > 2 * min(max1_width, max2_width)) return false;
				if (max(y1_width, y2_width) > 2 * min(y1_width, y2_width)) return false;
			}

			return true;
		}

		if (c1->type == "$macc")
		{
			if (!config.opt_aggressive)
				if (share_macc(c1, c2) > 2 * min(bits_macc(c1), bits_macc(c2))) return false;

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

	RTLIL::Cell *make_supercell(RTLIL::Cell *c1, RTLIL::Cell *c2, RTLIL::SigSpec act, pool<RTLIL::Cell*> &supercell_aux)
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

			int a_width = max(a1.size(), a2.size());
			int y_width = max(y1.size(), y2.size());

			a1.extend_u0(a_width, a_signed);
			a2.extend_u0(a_width, a_signed);

			RTLIL::SigSpec a = module->addWire(NEW_ID, a_width);
			supercell_aux.insert(module->addMux(NEW_ID, a2, a1, act, a));

			RTLIL::Wire *y = module->addWire(NEW_ID, y_width);

			RTLIL::Cell *supercell = module->addCell(NEW_ID, c1->type);
			supercell->parameters["\\A_SIGNED"] = a_signed;
			supercell->parameters["\\A_WIDTH"] = a_width;
			supercell->parameters["\\Y_WIDTH"] = y_width;
			supercell->setPort("\\A", a);
			supercell->setPort("\\Y", y);

			supercell_aux.insert(module->addPos(NEW_ID, y, y1));
			supercell_aux.insert(module->addPos(NEW_ID, y, y2));

			supercell_aux.insert(supercell);
			return supercell;
		}

		if (config.generic_bin_ops.count(c1->type) || config.generic_cbin_ops.count(c1->type) || c1->type == "$alu")
		{
			bool modified_src_cells = false;

			if (config.generic_cbin_ops.count(c1->type))
			{
				int score_unflipped = max(c1->parameters.at("\\A_WIDTH").as_int(), c2->parameters.at("\\A_WIDTH").as_int()) +
						max(c1->parameters.at("\\B_WIDTH").as_int(), c2->parameters.at("\\B_WIDTH").as_int());

				int score_flipped = max(c1->parameters.at("\\A_WIDTH").as_int(), c2->parameters.at("\\B_WIDTH").as_int()) +
						max(c1->parameters.at("\\B_WIDTH").as_int(), c2->parameters.at("\\A_WIDTH").as_int());

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

			int a_width = max(a1.size(), a2.size());
			int b_width = max(b1.size(), b2.size());
			int y_width = max(y1.size(), y2.size());

			if (c1->type == "$shr" && a_signed)
			{
				a_width = max(y_width, a_width);

				if (a1.size() < y1.size()) a1.extend_u0(y1.size(), true);
				if (a2.size() < y2.size()) a2.extend_u0(y2.size(), true);

				a1.extend_u0(a_width, false);
				a2.extend_u0(a_width, false);
			}
			else
			{
				a1.extend_u0(a_width, a_signed);
				a2.extend_u0(a_width, a_signed);
			}

			b1.extend_u0(b_width, b_signed);
			b2.extend_u0(b_width, b_signed);

			RTLIL::SigSpec a = module->addWire(NEW_ID, a_width);
			RTLIL::SigSpec b = module->addWire(NEW_ID, b_width);

			supercell_aux.insert(module->addMux(NEW_ID, a2, a1, act, a));
			supercell_aux.insert(module->addMux(NEW_ID, b2, b1, act, b));

			RTLIL::Wire *y = module->addWire(NEW_ID, y_width);
			RTLIL::Wire *x = c1->type == "$alu" ? module->addWire(NEW_ID, y_width) : nullptr;
			RTLIL::Wire *co = c1->type == "$alu" ? module->addWire(NEW_ID, y_width) : nullptr;

			RTLIL::Cell *supercell = module->addCell(NEW_ID, c1->type);
			supercell->parameters["\\A_SIGNED"] = a_signed;
			supercell->parameters["\\B_SIGNED"] = b_signed;
			supercell->parameters["\\A_WIDTH"] = a_width;
			supercell->parameters["\\B_WIDTH"] = b_width;
			supercell->parameters["\\Y_WIDTH"] = y_width;
			supercell->setPort("\\A", a);
			supercell->setPort("\\B", b);
			supercell->setPort("\\Y", y);
			if (c1->type == "$alu") {
				RTLIL::Wire *ci = module->addWire(NEW_ID), *bi = module->addWire(NEW_ID);
				supercell_aux.insert(module->addMux(NEW_ID, c2->getPort("\\CI"), c1->getPort("\\CI"), act, ci));
				supercell_aux.insert(module->addMux(NEW_ID, c2->getPort("\\BI"), c1->getPort("\\BI"), act, bi));
				supercell->setPort("\\CI", ci);
				supercell->setPort("\\BI", bi);
				supercell->setPort("\\CO", co);
				supercell->setPort("\\X", x);
			}
			supercell->check();

			supercell_aux.insert(module->addPos(NEW_ID, y, y1));
			supercell_aux.insert(module->addPos(NEW_ID, y, y2));
			if (c1->type == "$alu") {
				supercell_aux.insert(module->addPos(NEW_ID, co, c1->getPort("\\CO")));
				supercell_aux.insert(module->addPos(NEW_ID, co, c2->getPort("\\CO")));
				supercell_aux.insert(module->addPos(NEW_ID, x, c1->getPort("\\X")));
				supercell_aux.insert(module->addPos(NEW_ID, x, c2->getPort("\\X")));
			}

			supercell_aux.insert(supercell);
			return supercell;
		}

		if (c1->type == "$macc")
		{
			RTLIL::Cell *supercell = module->addCell(NEW_ID, c1->type);
			supercell_aux.insert(supercell);
			share_macc(c1, c2, act, supercell, &supercell_aux);
			supercell->check();
			return supercell;
		}

		if (c1->type == "$memrd")
		{
			RTLIL::Cell *supercell = module->addCell(NEW_ID, c1);
			RTLIL::SigSpec addr1 = c1->getPort("\\ADDR");
			RTLIL::SigSpec addr2 = c2->getPort("\\ADDR");
			if (addr1 != addr2)
				supercell->setPort("\\ADDR", module->Mux(NEW_ID, addr2, addr1, act));
			supercell_aux.insert(module->addPos(NEW_ID, supercell->getPort("\\DATA"), c2->getPort("\\DATA")));
			supercell_aux.insert(supercell);
			return supercell;
		}

		log_abort();
	}


	// -------------------------------------------
	// Finding forbidden control inputs for a cell
	// -------------------------------------------

	std::map<RTLIL::Cell*, pool<RTLIL::SigBit>, cell_ptr_cmp> forbidden_controls_cache;

	const pool<RTLIL::SigBit> &find_forbidden_controls(RTLIL::Cell *cell)
	{
		if (recursion_state.count(cell)) {
			static pool<RTLIL::SigBit> empty_controls_set;
			return empty_controls_set;
		}

		if (forbidden_controls_cache.count(cell))
			return forbidden_controls_cache.at(cell);

		pool<ModWalker::PortBit> pbits;
		pool<RTLIL::Cell*> consumer_cells;

		modwalker.get_consumers(pbits, modwalker.cell_outputs[cell]);

		for (auto &bit : pbits) {
			if ((bit.cell->type == "$mux" || bit.cell->type == "$pmux") && bit.port == "\\S")
				forbidden_controls_cache[cell].insert(bit.cell->getPort("\\S").extract(bit.offset, 1));
			consumer_cells.insert(bit.cell);
		}

		recursion_state.insert(cell);

		for (auto c : consumer_cells)
			if (fwd_ct.cell_known(c->type)) {
				const pool<RTLIL::SigBit> &bits = find_forbidden_controls(c);
				forbidden_controls_cache[cell].insert(bits.begin(), bits.end());
			}

		log_assert(recursion_state.count(cell) != 0);
		recursion_state.erase(cell);

		return forbidden_controls_cache[cell];
	}


	// --------------------------------------------------------
	// Finding control inputs and activation pattern for a cell
	// --------------------------------------------------------

	std::map<RTLIL::Cell*, pool<ssc_pair_t>, cell_ptr_cmp> activation_patterns_cache;

	bool sort_check_activation_pattern(ssc_pair_t &p)
	{
		std::map<RTLIL::SigBit, RTLIL::State> p_bits;

		std::vector<RTLIL::SigBit> p_first_bits = p.first;
		for (int i = 0; i < GetSize(p_first_bits); i++) {
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

	void optimize_activation_patterns(pool<ssc_pair_t> &patterns)
	{
		// TODO: Remove patterns that are contained in other patterns

		dict<SigSpec, pool<Const>> db;
		bool did_something = false;

		for (auto const &p : patterns)
		{
			auto &sig = p.first;
			auto &val = p.second;
			int len = GetSize(sig);

			for (int i = 0; i < len; i++)
			{
				auto otherval = val;

				if (otherval.bits[i] == State::S0)
					otherval.bits[i] = State::S1;
				else if (otherval.bits[i] == State::S1)
					otherval.bits[i] = State::S0;
				else
					continue;

				if (db[sig].count(otherval))
				{
					auto newsig = sig;
					newsig.remove(i);

					auto newval = val;
					newval.bits.erase(newval.bits.begin() + i);

					db[newsig].insert(newval);
					db[sig].erase(otherval);

					did_something = true;
					goto next_pattern;
				}
			}

			db[sig].insert(val);
		next_pattern:;
		}

		if (!did_something)
			return;

		patterns.clear();
		for (auto &it : db)
		for (auto &val : it.second)
			patterns.insert(make_pair(it.first, val));

		optimize_activation_patterns(patterns);
	}

	const pool<ssc_pair_t> &find_cell_activation_patterns(RTLIL::Cell *cell, const char *indent)
	{
		if (recursion_state.count(cell)) {
			static pool<ssc_pair_t> empty_patterns_set;
			return empty_patterns_set;
		}

		if (activation_patterns_cache.count(cell))
			return activation_patterns_cache.at(cell);

		const pool<RTLIL::SigBit> &cell_out_bits = modwalker.cell_outputs[cell];
		pool<RTLIL::Cell*> driven_cells, driven_data_muxes;

		for (auto &bit : cell_out_bits)
		{
			if (terminal_bits.count(bit)) {
				// Terminal cells are always active: unconditional activation pattern
				activation_patterns_cache[cell].insert(ssc_pair_t());
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
			const pool<ssc_pair_t> &c_patterns = find_cell_activation_patterns(c, indent);

			bool used_in_a = false;
			std::set<int> used_in_b_parts;

			int width = c->parameters.at("\\WIDTH").as_int();
			std::vector<RTLIL::SigBit> sig_a = modwalker.sigmap(c->getPort("\\A"));
			std::vector<RTLIL::SigBit> sig_b = modwalker.sigmap(c->getPort("\\B"));
			std::vector<RTLIL::SigBit> sig_s = modwalker.sigmap(c->getPort("\\S"));

			for (auto &bit : sig_a)
				if (cell_out_bits.count(bit))
					used_in_a = true;

			for (int i = 0; i < GetSize(sig_b); i++)
				if (cell_out_bits.count(sig_b[i]))
					used_in_b_parts.insert(i / width);

			if (used_in_a)
				for (auto p : c_patterns) {
					for (int i = 0; i < GetSize(sig_s); i++)
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
			const pool<ssc_pair_t> &c_patterns = find_cell_activation_patterns(c, indent);
			activation_patterns_cache[cell].insert(c_patterns.begin(), c_patterns.end());
		}

		log_assert(recursion_state.count(cell) != 0);
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

	RTLIL::SigSpec bits_from_activation_patterns(const pool<ssc_pair_t> &activation_patterns)
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

	void filter_activation_patterns(pool<ssc_pair_t> &out,
			const pool<ssc_pair_t> &in, const std::set<RTLIL::SigBit> &filter_bits)
	{
		for (auto &p : in)
		{
			std::vector<RTLIL::SigBit> p_first = p.first;
			ssc_pair_t new_p;

			for (int i = 0; i < GetSize(p_first); i++)
				if (filter_bits.count(p_first[i]) == 0) {
					new_p.first.append_bit(p_first[i]);
					new_p.second.bits.push_back(p.second.bits.at(i));
				}

			out.insert(new_p);
		}
	}

	RTLIL::SigSpec make_cell_activation_logic(const pool<ssc_pair_t> &activation_patterns, pool<RTLIL::Cell*> &supercell_aux)
	{
		RTLIL::Wire *all_cases_wire = module->addWire(NEW_ID, 0);

		for (auto &p : activation_patterns) {
			all_cases_wire->width++;
			supercell_aux.insert(module->addEq(NEW_ID, p.first, p.second, RTLIL::SigSpec(all_cases_wire, all_cases_wire->width - 1)));
		}

		if (all_cases_wire->width == 1)
			return all_cases_wire;

		RTLIL::Wire *result_wire = module->addWire(NEW_ID);
		supercell_aux.insert(module->addReduceOr(NEW_ID, all_cases_wire, result_wire));
		return result_wire;
	}


	// -------------------------------------------------------------------------------------
	// Helper functions used to make sure that this pass does not introduce new logic loops.
	// -------------------------------------------------------------------------------------

	bool module_has_scc()
	{
		CellTypes ct;
		ct.setup_internals();
		ct.setup_stdcells();

		TopoSort<RTLIL::Cell*, cell_ptr_cmp> toposort;
		toposort.analyze_loops = false;

		topo_sigmap.set(module);
		topo_bit_drivers.clear();

		dict<RTLIL::Cell*, pool<RTLIL::SigBit>> cell_to_bits;
		dict<RTLIL::SigBit, pool<RTLIL::Cell*>> bit_to_cells;

		for (auto cell : module->cells())
			if (ct.cell_known(cell->type))
				for (auto &conn : cell->connections()) {
					if (ct.cell_output(cell->type, conn.first))
						for (auto bit : topo_sigmap(conn.second)) {
							cell_to_bits[cell].insert(bit);
							topo_bit_drivers[bit].insert(cell);
						}
					else
						for (auto bit : topo_sigmap(conn.second))
							bit_to_cells[bit].insert(cell);
				}

		for (auto &it : cell_to_bits)
		{
			RTLIL::Cell *c1 = it.first;

			for (auto bit : it.second)
			for (auto c2 : bit_to_cells[bit])
				toposort.edge(c1, c2);
		}

		bool found_scc = !toposort.sort();
		topo_cell_drivers = std::move(toposort.database);

		if (found_scc && toposort.analyze_loops)
			for (auto &loop : toposort.loops) {
				log("### loop ###\n");
				for (auto &c : loop)
					log("%s (%s)\n", log_id(c), log_id(c->type));
			}

		return found_scc;
	}

	bool find_in_input_cone_worker(RTLIL::Cell *root, RTLIL::Cell *needle, pool<RTLIL::Cell*> &stop)
	{
		if (root == needle)
			return true;

		if (stop.count(root))
			return false;

		stop.insert(root);

		for (auto c : topo_cell_drivers[root])
			if (find_in_input_cone_worker(c, needle, stop))
				return true;
		return false;
	}

	bool find_in_input_cone(RTLIL::Cell *root, RTLIL::Cell *needle)
	{
		pool<RTLIL::Cell*> stop;
		return find_in_input_cone_worker(root, needle, stop);
	}

	bool is_part_of_scc(RTLIL::Cell *cell)
	{
		CellTypes ct;
		ct.setup_internals();
		ct.setup_stdcells();

		pool<RTLIL::Cell*> queue, covered;
		queue.insert(cell);

		while (!queue.empty())
		{
			pool<RTLIL::Cell*> new_queue;

			for (auto c : queue) {
				if (!ct.cell_known(c->type))
					continue;
				for (auto &conn : c->connections())
					if (ct.cell_input(c->type, conn.first))
						for (auto bit : conn.second)
							for (auto &pi : mi.query_ports(bit))
								if (ct.cell_known(pi.cell->type) && ct.cell_output(pi.cell->type, pi.port))
									new_queue.insert(pi.cell);
				covered.insert(c);
			}

			queue.clear();
			for (auto c : new_queue) {
				if (cells_to_remove.count(c))
					continue;
				if (c == cell)
					return true;
				if (!covered.count(c))
					queue.insert(c);
			}
		}

		return false;
	}


	// -------------
	// Setup and run
	// -------------

	void remove_cell(Cell *cell)
	{
		shareable_cells.erase(cell);
		forbidden_controls_cache.erase(cell);
		activation_patterns_cache.erase(cell);
		module->remove(cell);
	}

	ShareWorker(ShareWorkerConfig config, RTLIL::Design *design, RTLIL::Module *module) :
			config(config), design(design), module(module), mi(module)
	{
	#ifndef NDEBUG
		bool before_scc = module_has_scc();
	#endif

		generic_ops.insert(config.generic_uni_ops.begin(), config.generic_uni_ops.end());
		generic_ops.insert(config.generic_bin_ops.begin(), config.generic_bin_ops.end());
		generic_ops.insert(config.generic_cbin_ops.begin(), config.generic_cbin_ops.end());
		generic_ops.insert(config.generic_other_ops.begin(), config.generic_other_ops.end());

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
				GetSize(shareable_cells), log_id(module));

		for (auto cell : module->cells())
			if (cell->type == "$pmux")
				for (auto bit : cell->getPort("\\S"))
				for (auto other_bit : cell->getPort("\\S"))
					if (bit < other_bit)
						exclusive_ctrls.push_back(std::pair<RTLIL::SigBit, RTLIL::SigBit>(bit, other_bit));

		while (!shareable_cells.empty() && config.limit != 0)
		{
			RTLIL::Cell *cell = *shareable_cells.begin();
			shareable_cells.erase(cell);

			log("  Analyzing resource sharing options for %s (%s):\n", log_id(cell), log_id(cell->type));

			const pool<ssc_pair_t> &cell_activation_patterns = find_cell_activation_patterns(cell, "    ");
			RTLIL::SigSpec cell_activation_signals = bits_from_activation_patterns(cell_activation_patterns);

			if (cell_activation_patterns.empty()) {
				log("    Cell is never active. Sharing is pointless, we simply remove it.\n");
				cells_to_remove.insert(cell);
				continue;
			}

			if (cell_activation_patterns.count(ssc_pair_t())) {
				log("    Cell is always active. Therefore no sharing is possible.\n");
				continue;
			}

			log("    Found %d activation_patterns using ctrl signal %s.\n", GetSize(cell_activation_patterns), log_signal(cell_activation_signals));

			std::vector<RTLIL::Cell*> candidates;
			find_shareable_partners(candidates, cell);

			if (candidates.empty()) {
				log("    No candidates found.\n");
				continue;
			}

			log("    Found %d candidates:", GetSize(candidates));
			for (auto c : candidates)
				log(" %s", log_id(c));
			log("\n");

			for (auto other_cell : candidates)
			{
				log("    Analyzing resource sharing with %s (%s):\n", log_id(other_cell), log_id(other_cell->type));

				const pool<ssc_pair_t> &other_cell_activation_patterns = find_cell_activation_patterns(other_cell, "      ");
				RTLIL::SigSpec other_cell_activation_signals = bits_from_activation_patterns(other_cell_activation_patterns);

				if (other_cell_activation_patterns.empty()) {
					log("      Cell is never active. Sharing is pointless, we simply remove it.\n");
					shareable_cells.erase(other_cell);
					cells_to_remove.insert(other_cell);
					continue;
				}

				if (other_cell_activation_patterns.count(ssc_pair_t())) {
					log("      Cell is always active. Therefore no sharing is possible.\n");
					shareable_cells.erase(other_cell);
					continue;
				}

				log("      Found %d activation_patterns using ctrl signal %s.\n",
						GetSize(other_cell_activation_patterns), log_signal(other_cell_activation_signals));

				const pool<RTLIL::SigBit> &cell_forbidden_controls = find_forbidden_controls(cell);
				const pool<RTLIL::SigBit> &other_cell_forbidden_controls = find_forbidden_controls(other_cell);

				std::set<RTLIL::SigBit> union_forbidden_controls;
				union_forbidden_controls.insert(cell_forbidden_controls.begin(), cell_forbidden_controls.end());
				union_forbidden_controls.insert(other_cell_forbidden_controls.begin(), other_cell_forbidden_controls.end());

				if (!union_forbidden_controls.empty())
					log("      Forbidden control signals for this pair of cells: %s\n", log_signal(union_forbidden_controls));

				pool<ssc_pair_t> filtered_cell_activation_patterns;
				pool<ssc_pair_t> filtered_other_cell_activation_patterns;

				filter_activation_patterns(filtered_cell_activation_patterns, cell_activation_patterns, union_forbidden_controls);
				filter_activation_patterns(filtered_other_cell_activation_patterns, other_cell_activation_patterns, union_forbidden_controls);

				optimize_activation_patterns(filtered_cell_activation_patterns);
				optimize_activation_patterns(filtered_other_cell_activation_patterns);

				ezSatPtr ez;
				SatGen satgen(ez.get(), &modwalker.sigmap);

				pool<RTLIL::Cell*> sat_cells;
				std::set<RTLIL::SigBit> bits_queue;

				std::vector<int> cell_active, other_cell_active;
				RTLIL::SigSpec all_ctrl_signals;

				for (auto &p : filtered_cell_activation_patterns) {
					log("      Activation pattern for cell %s: %s = %s\n", log_id(cell), log_signal(p.first), log_signal(p.second));
					cell_active.push_back(ez->vec_eq(satgen.importSigSpec(p.first), satgen.importSigSpec(p.second)));
					all_ctrl_signals.append(p.first);
				}

				for (auto &p : filtered_other_cell_activation_patterns) {
					log("      Activation pattern for cell %s: %s = %s\n", log_id(other_cell), log_signal(p.first), log_signal(p.second));
					other_cell_active.push_back(ez->vec_eq(satgen.importSigSpec(p.first), satgen.importSigSpec(p.second)));
					all_ctrl_signals.append(p.first);
				}

				for (auto &bit : cell_activation_signals.to_sigbit_vector())
					bits_queue.insert(bit);

				for (auto &bit : other_cell_activation_signals.to_sigbit_vector())
					bits_queue.insert(bit);

				while (!bits_queue.empty())
				{
					pool<ModWalker::PortBit> portbits;
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

				for (auto it : exclusive_ctrls)
					if (satgen.importedSigBit(it.first) && satgen.importedSigBit(it.second)) {
						log("      Adding exclusive control bits: %s vs. %s\n", log_signal(it.first), log_signal(it.second));
						int sub1 = satgen.importSigBit(it.first);
						int sub2 = satgen.importSigBit(it.second);
						ez->assume(ez->NOT(ez->AND(sub1, sub2)));
					}

				if (!ez->solve(ez->expression(ez->OpOr, cell_active))) {
					log("      According to the SAT solver the cell %s is never active. Sharing is pointless, we simply remove it.\n", log_id(cell));
					cells_to_remove.insert(cell);
					break;
				}

				if (!ez->solve(ez->expression(ez->OpOr, other_cell_active))) {
					log("      According to the SAT solver the cell %s is never active. Sharing is pointless, we simply remove it.\n", log_id(other_cell));
					cells_to_remove.insert(other_cell);
					shareable_cells.erase(other_cell);
					continue;
				}

				ez->non_incremental();

				all_ctrl_signals.sort_and_unify();
				std::vector<int> sat_model = satgen.importSigSpec(all_ctrl_signals);
				std::vector<bool> sat_model_values;

				int sub1 = ez->expression(ez->OpOr, cell_active);
				int sub2 = ez->expression(ez->OpOr, other_cell_active);
				ez->assume(ez->AND(sub1, sub2));

				log("      Size of SAT problem: %d cells, %d variables, %d clauses\n",
						GetSize(sat_cells), ez->numCnfVariables(), ez->numCnfClauses());

				if (ez->solve(sat_model, sat_model_values)) {
					log("      According to the SAT solver this pair of cells can not be shared.\n");
					log("      Model from SAT solver: %s = %d'", log_signal(all_ctrl_signals), GetSize(sat_model_values));
					for (int i = GetSize(sat_model_values)-1; i >= 0; i--)
						log("%c", sat_model_values[i] ? '1' : '0');
					log("\n");
					continue;
				}

				log("      According to the SAT solver this pair of cells can be shared.\n");

				if (find_in_input_cone(cell, other_cell)) {
					log("      Sharing not possible: %s is in input cone of %s.\n", log_id(other_cell), log_id(cell));
					continue;
				}

				if (find_in_input_cone(other_cell, cell)) {
					log("      Sharing not possible: %s is in input cone of %s.\n", log_id(cell), log_id(other_cell));
					continue;
				}

				shareable_cells.erase(other_cell);

				int cell_select_score = 0;
				int other_cell_select_score = 0;

				for (auto &p : filtered_cell_activation_patterns)
					cell_select_score += p.first.size();

				for (auto &p : filtered_other_cell_activation_patterns)
					other_cell_select_score += p.first.size();

				RTLIL::Cell *supercell;
				pool<RTLIL::Cell*> supercell_aux;
				if (cell_select_score <= other_cell_select_score) {
					RTLIL::SigSpec act = make_cell_activation_logic(filtered_cell_activation_patterns, supercell_aux);
					supercell = make_supercell(cell, other_cell, act, supercell_aux);
					log("      Activation signal for %s: %s\n", log_id(cell), log_signal(act));
				} else {
					RTLIL::SigSpec act = make_cell_activation_logic(filtered_other_cell_activation_patterns, supercell_aux);
					supercell = make_supercell(other_cell, cell, act, supercell_aux);
					log("      Activation signal for %s: %s\n", log_id(other_cell), log_signal(act));
				}

				log("      New cell: %s (%s)\n", log_id(supercell), log_id(supercell->type));

				cells_to_remove.insert(cell);
				cells_to_remove.insert(other_cell);

				for (auto c : supercell_aux)
					if (is_part_of_scc(c))
						goto do_rollback;

				if (0) {
			do_rollback:
					log("      New topology contains loops! Rolling back..\n");
					cells_to_remove.erase(cell);
					cells_to_remove.erase(other_cell);
					shareable_cells.insert(other_cell);
					for (auto cc : supercell_aux)
						remove_cell(cc);
					continue;
				}

				pool<ssc_pair_t> supercell_activation_patterns;
				supercell_activation_patterns.insert(filtered_cell_activation_patterns.begin(), filtered_cell_activation_patterns.end());
				supercell_activation_patterns.insert(filtered_other_cell_activation_patterns.begin(), filtered_other_cell_activation_patterns.end());
				optimize_activation_patterns(supercell_activation_patterns);
				activation_patterns_cache[supercell] = supercell_activation_patterns;
				shareable_cells.insert(supercell);

				for (auto bit : topo_sigmap(all_ctrl_signals))
					for (auto c : topo_bit_drivers[bit])
						topo_cell_drivers[supercell].insert(c);

				topo_cell_drivers[supercell].insert(topo_cell_drivers[cell].begin(), topo_cell_drivers[cell].end());
				topo_cell_drivers[supercell].insert(topo_cell_drivers[other_cell].begin(), topo_cell_drivers[other_cell].end());

				topo_cell_drivers[cell] = { supercell };
				topo_cell_drivers[other_cell] = { supercell };

				if (config.limit > 0)
					config.limit--;

				break;
			}
		}

		if (!cells_to_remove.empty()) {
			log("Removing %d cells in module %s:\n", GetSize(cells_to_remove), log_id(module));
			for (auto c : cells_to_remove) {
				log("  Removing cell %s (%s).\n", log_id(c), log_id(c->type));
				remove_cell(c);
			}
		}

		log_assert(recursion_state.empty());

	#ifndef NDEBUG
		bool after_scc = before_scc || module_has_scc();
		log_assert(before_scc == after_scc);
	#endif
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
		log("    in much easier SAT problems at the cost of maybe missing some opportunities\n");
		log("    for resource sharing.\n");
		log("\n");
		log("  -limit N\n");
		log("    Only perform the first N merges, then stop. This is useful for debugging.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		ShareWorkerConfig config;

		config.limit = -1;
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

		config.generic_other_ops.insert("$alu");
		config.generic_other_ops.insert("$macc");

		log_header(design, "Executing SHARE pass (SAT-based resource sharing).\n");

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
			if (args[argidx] == "-limit" && argidx+1 < args.size()) {
				config.limit = atoi(args[++argidx].c_str());
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
