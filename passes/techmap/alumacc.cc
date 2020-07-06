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
#include "kernel/macc.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct AlumaccWorker
{
	RTLIL::Module *module;
	SigMap sigmap;

	struct maccnode_t {
		Macc macc;
		RTLIL::Cell *cell;
		RTLIL::SigSpec y;
		int users;
	};

	struct alunode_t
	{
		std::vector<RTLIL::Cell*> cells;
		RTLIL::SigSpec a, b, c, y;
		std::vector<tuple<bool, bool, bool, bool, RTLIL::SigSpec>> cmp;
		bool is_signed, invert_b;

		RTLIL::Cell *alu_cell;
		RTLIL::SigSpec cached_lt, cached_gt, cached_eq, cached_ne;
		RTLIL::SigSpec cached_cf, cached_of, cached_sf;

		RTLIL::SigSpec get_lt() {
			if (GetSize(cached_lt) == 0) {
				if (is_signed) {
					get_of();
					get_sf();
					cached_lt = alu_cell->module->Xor(NEW_ID, cached_of, cached_sf);
				}
				else
					cached_lt = get_cf();
			}
			return cached_lt;
		}

		RTLIL::SigSpec get_gt() {
			if (GetSize(cached_gt) == 0) {
				get_lt();
				get_eq();
				SigSpec Or = alu_cell->module->Or(NEW_ID, cached_lt, cached_eq);
				cached_gt = alu_cell->module->Not(NEW_ID, Or, false, alu_cell->get_src_attribute());
			}
			return cached_gt;
		}

		RTLIL::SigSpec get_eq() {
			if (GetSize(cached_eq) == 0)
				cached_eq = alu_cell->module->ReduceAnd(NEW_ID, alu_cell->getPort(ID(X)), false, alu_cell->get_src_attribute());
			return cached_eq;
		}

		RTLIL::SigSpec get_ne() {
			if (GetSize(cached_ne) == 0)
				cached_ne = alu_cell->module->Not(NEW_ID, get_eq(), false, alu_cell->get_src_attribute());
			return cached_ne;
		}

		RTLIL::SigSpec get_cf() {
			if (GetSize(cached_cf) == 0) {
				cached_cf = alu_cell->getPort(ID(CO));
				log_assert(GetSize(cached_cf) >= 1);
				cached_cf = alu_cell->module->Not(NEW_ID, cached_cf[GetSize(cached_cf)-1], false, alu_cell->get_src_attribute());
			}
			return cached_cf;
		}

		RTLIL::SigSpec get_of() {
			if (GetSize(cached_of) == 0) {
				cached_of = {alu_cell->getPort(ID(CO)), alu_cell->getPort(ID(CI))};
				log_assert(GetSize(cached_of) >= 2);
				cached_of = alu_cell->module->Xor(NEW_ID, cached_of[GetSize(cached_of)-1], cached_of[GetSize(cached_of)-2]);
			}
			return cached_of;
		}

		RTLIL::SigSpec get_sf() {
			if (GetSize(cached_sf) == 0) {
				cached_sf = alu_cell->getPort(ID::Y);
				cached_sf = cached_sf[GetSize(cached_sf)-1];
			}
			return cached_sf;
		}
	};

	dict<RTLIL::SigBit, int> bit_users;
	dict<RTLIL::SigSpec, maccnode_t*> sig_macc;
	dict<RTLIL::SigSig, pool<alunode_t*, hash_ptr_ops>> sig_alu;
	int macc_counter, alu_counter;

	AlumaccWorker(RTLIL::Module *module) : module(module), sigmap(module)
	{
		macc_counter = 0;
		alu_counter = 0;
	}

	void count_bit_users()
	{
		for (auto port : module->ports)
			for (auto bit : sigmap(module->wire(port)))
				bit_users[bit]++;

		for (auto cell : module->cells())
		for (auto &conn : cell->connections())
			for (auto bit : sigmap(conn.second))
				bit_users[bit]++;
	}

	void extract_macc()
	{
		for (auto cell : module->selected_cells())
		{
			if (!cell->type.in(ID($pos), ID($neg), ID($add), ID($sub), ID($mul)))
				continue;

			log("  creating $macc model for %s (%s).\n", log_id(cell), log_id(cell->type));

			maccnode_t *n = new maccnode_t;
			Macc::port_t new_port;

			n->cell = cell;
			n->y = sigmap(cell->getPort(ID::Y));
			n->users = 0;

			for (auto bit : n->y)
				n->users = max(n->users, bit_users.at(bit) - 1);

			if (cell->type.in(ID($pos), ID($neg)))
			{
				new_port.in_a = sigmap(cell->getPort(ID::A));
				new_port.is_signed = cell->getParam(ID(A_SIGNED)).as_bool();
				new_port.do_subtract = cell->type == ID($neg);
				n->macc.ports.push_back(new_port);
			}

			if (cell->type.in(ID($add), ID($sub)))
			{
				new_port.in_a = sigmap(cell->getPort(ID::A));
				new_port.is_signed = cell->getParam(ID(A_SIGNED)).as_bool();
				new_port.do_subtract = false;
				n->macc.ports.push_back(new_port);

				new_port.in_a = sigmap(cell->getPort(ID::B));
				new_port.is_signed = cell->getParam(ID(B_SIGNED)).as_bool();
				new_port.do_subtract = cell->type == ID($sub);
				n->macc.ports.push_back(new_port);
			}

			if (cell->type.in(ID($mul)))
			{
				new_port.in_a = sigmap(cell->getPort(ID::A));
				new_port.in_b = sigmap(cell->getPort(ID::B));
				new_port.is_signed = cell->getParam(ID(A_SIGNED)).as_bool();
				new_port.do_subtract = false;
				n->macc.ports.push_back(new_port);
			}

			log_assert(sig_macc.count(n->y) == 0);
			sig_macc[n->y] = n;
		}
	}

	static bool macc_may_overflow(Macc &macc, int width, bool is_signed)
	{
		std::vector<int> port_sizes;

		for (auto &port : macc.ports) {
			if (port.is_signed != is_signed)
				return true;
			if (!port.is_signed && port.do_subtract)
				return true;
			if (GetSize(port.in_b))
				port_sizes.push_back(GetSize(port.in_a) + GetSize(port.in_b));
			else
				port_sizes.push_back(GetSize(port.in_a));
		}

		std::sort(port_sizes.begin(), port_sizes.end());

		int acc_sum = 0, acc_shift = 0;
		for (int sz : port_sizes) {
			while ((sz - acc_shift) > 20) {
				if (acc_sum & 1)
					acc_sum++;
				acc_sum = acc_sum >> 1;
				acc_shift++;
			}
			acc_sum += (1 << (sz - acc_shift)) - 1;
		}

		while (acc_sum) {
			acc_sum = acc_sum >> 1;
			acc_shift++;
		}

		return acc_shift > width;
	}

	void merge_macc()
	{
		while (1)
		{
			pool<maccnode_t*, hash_ptr_ops> delete_nodes;

			for (auto &it : sig_macc)
			{
				auto n = it.second;

				if (delete_nodes.count(n))
					continue;

				for (int i = 0; i < GetSize(n->macc.ports); i++)
				{
					auto &port = n->macc.ports[i];

					if (GetSize(port.in_b) > 0 || sig_macc.count(port.in_a) == 0)
						continue;

					auto other_n = sig_macc.at(port.in_a);

					if (other_n->users > 1)
						continue;

					if (GetSize(other_n->y) != GetSize(n->y) && macc_may_overflow(other_n->macc, GetSize(other_n->y), port.is_signed))
						continue;

					log("  merging $macc model for %s into %s.\n", log_id(other_n->cell), log_id(n->cell));

					bool do_subtract = port.do_subtract;
					for (int j = 0; j < GetSize(other_n->macc.ports); j++) {
						if (do_subtract)
							other_n->macc.ports[j].do_subtract = !other_n->macc.ports[j].do_subtract;
						if (j == 0)
							n->macc.ports[i--] = other_n->macc.ports[j];
						else
							n->macc.ports.push_back(other_n->macc.ports[j]);
					}

					delete_nodes.insert(other_n);
				}
			}

			if (delete_nodes.empty())
				break;

			for (auto n : delete_nodes) {
				sig_macc.erase(n->y);
				delete n;
			}
		}
	}

	void macc_to_alu()
	{
		pool<maccnode_t*, hash_ptr_ops> delete_nodes;

		for (auto &it : sig_macc)
		{
			auto n = it.second;
			RTLIL::SigSpec A, B, C = n->macc.bit_ports;
			bool a_signed = false, b_signed = false;
			bool subtract_b = false;
			alunode_t *alunode;

			for (auto &port : n->macc.ports)
				if (GetSize(port.in_b) > 0) {
					goto next_macc;
				} else if (GetSize(port.in_a) == 1 && !port.is_signed && !port.do_subtract) {
					C.append(port.in_a);
				} else if (GetSize(A) || port.do_subtract) {
					if (GetSize(B))
						goto next_macc;
					B = port.in_a;
					b_signed = port.is_signed;
					subtract_b = port.do_subtract;
				} else {
					if (GetSize(A))
						goto next_macc;
					A = port.in_a;
					a_signed = port.is_signed;
				}

			if (!a_signed || !b_signed) {
				if (GetSize(A) == GetSize(n->y))
					a_signed = false;
				if (GetSize(B) == GetSize(n->y))
					b_signed = false;
				if (a_signed != b_signed)
					goto next_macc;
			}

			if (GetSize(A) == 0 && GetSize(C) > 0) {
				A = C[0];
				C.remove(0);
			}

			if (GetSize(B) == 0 && GetSize(C) > 0) {
				B = C[0];
				C.remove(0);
			}

			if (subtract_b)
				C.append(State::S1);

			if (GetSize(C) > 1)
				goto next_macc;

			if (!subtract_b && B < A && GetSize(B))
				std::swap(A, B);

			log("  creating $alu model for $macc %s.\n", log_id(n->cell));

			alunode = new alunode_t;
			alunode->cells.push_back(n->cell);
			alunode->is_signed = a_signed;
			alunode->invert_b = subtract_b;

			alunode->a = A;
			alunode->b = B;
			alunode->c = C;
			alunode->y = n->y;

			sig_alu[RTLIL::SigSig(A, B)].insert(alunode);
			delete_nodes.insert(n);
		next_macc:;
		}

		for (auto n : delete_nodes) {
			sig_macc.erase(n->y);
			delete n;
		}
	}

	void replace_macc()
	{
		for (auto &it : sig_macc)
		{
			auto n = it.second;
			auto cell = module->addCell(NEW_ID, ID($macc));

			macc_counter++;

			log("  creating $macc cell for %s: %s\n", log_id(n->cell), log_id(cell));

			cell->set_src_attribute(n->cell->get_src_attribute());

			n->macc.optimize(GetSize(n->y));
			n->macc.to_cell(cell);
			cell->setPort(ID::Y, n->y);
			cell->fixup_parameters();
			module->remove(n->cell);
			delete n;
		}

		sig_macc.clear();
	}

	void extract_cmp_alu()
	{
		std::vector<RTLIL::Cell*> lge_cells, eq_cells;

		for (auto cell : module->selected_cells())
		{
			if (cell->type.in(ID($lt), ID($le), ID($ge), ID($gt)))
				lge_cells.push_back(cell);
			if (cell->type.in(ID($eq), ID($eqx), ID($ne), ID($nex)))
				eq_cells.push_back(cell);
		}

		for (auto cell : lge_cells)
		{
			log("  creating $alu model for %s (%s):", log_id(cell), log_id(cell->type));

			bool cmp_less = cell->type.in(ID($lt), ID($le));
			bool cmp_equal = cell->type.in(ID($le), ID($ge));
			bool is_signed = cell->getParam(ID(A_SIGNED)).as_bool();

			RTLIL::SigSpec A = sigmap(cell->getPort(ID::A));
			RTLIL::SigSpec B = sigmap(cell->getPort(ID::B));
			RTLIL::SigSpec Y = sigmap(cell->getPort(ID::Y));

			if (B < A && GetSize(B)) {
				cmp_less = !cmp_less;
				std::swap(A, B);
			}

			alunode_t *n = nullptr;

			for (auto node : sig_alu[RTLIL::SigSig(A, B)])
				if (node->is_signed == is_signed && node->invert_b && node->c == State::S1) {
					n = node;
					break;
				}

			if (n == nullptr) {
				n = new alunode_t;
				n->a = A;
				n->b = B;
				n->c = State::S1;
				n->y = module->addWire(NEW_ID, max(GetSize(A), GetSize(B)));
				n->is_signed = is_signed;
				n->invert_b = true;
				sig_alu[RTLIL::SigSig(A, B)].insert(n);
				log(" new $alu\n");
			} else {
				log(" merged with %s.\n", log_id(n->cells.front()));
			}

			n->cells.push_back(cell);
			n->cmp.push_back(std::make_tuple(cmp_less, !cmp_less, cmp_equal, false, Y));
		}

		for (auto cell : eq_cells)
		{
			bool cmp_equal = cell->type.in(ID($eq), ID($eqx));
			bool is_signed = cell->getParam(ID(A_SIGNED)).as_bool();

			RTLIL::SigSpec A = sigmap(cell->getPort(ID::A));
			RTLIL::SigSpec B = sigmap(cell->getPort(ID::B));
			RTLIL::SigSpec Y = sigmap(cell->getPort(ID::Y));

			if (B < A && GetSize(B))
				std::swap(A, B);

			alunode_t *n = nullptr;

			for (auto node : sig_alu[RTLIL::SigSig(A, B)])
				if (node->is_signed == is_signed && node->invert_b && node->c == State::S1) {
					n = node;
					break;
				}

			if (n != nullptr) {
				log("  creating $alu model for %s (%s): merged with %s.\n", log_id(cell), log_id(cell->type), log_id(n->cells.front()));
				n->cells.push_back(cell);
				n->cmp.push_back(std::make_tuple(false, false, cmp_equal, !cmp_equal, Y));
			}
		}
	}

	void replace_alu()
	{
		std::string src("");
		for (auto &it1 : sig_alu)
		for (auto n : it1.second)
		{
			if (GetSize(n->b) == 0 && GetSize(n->c) == 0 && GetSize(n->cmp) == 0)
			{
				n->alu_cell = module->addPos(NEW_ID, n->a, n->y, n->is_signed);

				log("  creating $pos cell for ");
				for (int i = 0; i < GetSize(n->cells); i++)
					log("%s%s", i ? ", ": "", log_id(n->cells[i]));
				log(": %s\n", log_id(n->alu_cell));

				goto delete_node;
			}

			n->alu_cell = module->addCell(NEW_ID, ID($alu));
			alu_counter++;

			log("  creating $alu cell for ");
			for (int i = 0; i < GetSize(n->cells); i++)
				log("%s%s", i ? ", ": "", log_id(n->cells[i]));
			log(": %s\n", log_id(n->alu_cell));

			if (n->cells.size() > 0)
				n->alu_cell->set_src_attribute(n->cells[0]->get_src_attribute());

			n->alu_cell->setPort(ID::A, n->a);
			n->alu_cell->setPort(ID::B, n->b);
			n->alu_cell->setPort(ID(CI), GetSize(n->c) ? n->c : State::S0);
			n->alu_cell->setPort(ID(BI), n->invert_b ? State::S1 : State::S0);
			n->alu_cell->setPort(ID::Y, n->y);
			n->alu_cell->setPort(ID(X), module->addWire(NEW_ID, GetSize(n->y)));
			n->alu_cell->setPort(ID(CO), module->addWire(NEW_ID, GetSize(n->y)));
			n->alu_cell->fixup_parameters(n->is_signed, n->is_signed);

			for (auto &it : n->cmp)
			{
				bool cmp_lt = std::get<0>(it);
				bool cmp_gt = std::get<1>(it);
				bool cmp_eq = std::get<2>(it);
				bool cmp_ne = std::get<3>(it);
				RTLIL::SigSpec cmp_y = std::get<4>(it);

				RTLIL::SigSpec sig;
				if (cmp_lt) sig.append(n->get_lt());
				if (cmp_gt) sig.append(n->get_gt());
				if (cmp_eq) sig.append(n->get_eq());
				if (cmp_ne) sig.append(n->get_ne());

				if (GetSize(sig) > 1)
					sig = module->ReduceOr(NEW_ID, sig);

				sig.extend_u0(GetSize(cmp_y));
				module->connect(cmp_y, sig);
			}

		delete_node:
			for (auto c : n->cells)
				module->remove(c);
			delete n;
		}

		sig_alu.clear();
	}

	void run()
	{
		log("Extracting $alu and $macc cells in module %s:\n", log_id(module));

		count_bit_users();
		extract_macc();
		merge_macc();
		macc_to_alu();
		replace_macc();
		extract_cmp_alu();
		replace_alu();

		log("  created %d $alu and %d $macc cells.\n", alu_counter, macc_counter);
	}
};

struct AlumaccPass : public Pass {
	AlumaccPass() : Pass("alumacc", "extract ALU and MACC cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    alumacc [selection]\n");
		log("\n");
		log("This pass translates arithmetic operations like $add, $mul, $lt, etc. to $alu\n");
		log("and $macc cells.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ALUMACC pass (create $alu and $macc cells).\n");

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
				AlumaccWorker worker(mod);
				worker.run();
			}
	}
} AlumaccPass;

PRIVATE_NAMESPACE_END
