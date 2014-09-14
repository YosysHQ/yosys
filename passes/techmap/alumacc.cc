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

	std::map<RTLIL::SigBit, int> bit_users;
	std::map<RTLIL::SigSpec, maccnode_t*> sig_macc;

	AlumaccWorker(RTLIL::Module *module) : module(module), sigmap(module) { }

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
			if (!cell->type.in("$pos", "$neg", "$add", "$sub", "$mul"))
				continue;

			log("  creating $macc model for %s (%s).\n", log_id(cell), log_id(cell->type));

			maccnode_t *n = new maccnode_t;
			Macc::port_t new_port;

			n->cell = cell;
			n->y = sigmap(cell->getPort("\\Y"));
			n->users = 0;

			for (auto bit : n->y)
				n->users = std::max(n->users, bit_users.at(bit) - 1);

			if (cell->type.in("$pos", "$neg"))
			{
				new_port.in_a = sigmap(cell->getPort("\\A"));
				new_port.is_signed = cell->getParam("\\A_SIGNED").as_bool();
				new_port.do_subtract = cell->type == "$neg";
				n->macc.ports.push_back(new_port);
			}

			if (cell->type.in("$add", "$sub"))
			{
				new_port.in_a = sigmap(cell->getPort("\\A"));
				new_port.is_signed = cell->getParam("\\A_SIGNED").as_bool();
				new_port.do_subtract = false;
				n->macc.ports.push_back(new_port);

				new_port.in_a = sigmap(cell->getPort("\\B"));
				new_port.is_signed = cell->getParam("\\B_SIGNED").as_bool();
				new_port.do_subtract = cell->type == "$sub";
				n->macc.ports.push_back(new_port);
			}

			if (cell->type.in("$mul"))
			{
				new_port.in_a = sigmap(cell->getPort("\\A"));
				new_port.in_b = sigmap(cell->getPort("\\B"));
				new_port.is_signed = cell->getParam("\\A_SIGNED").as_bool();
				new_port.do_subtract = false;
				n->macc.ports.push_back(new_port);
			}

			log_assert(sig_macc.count(n->y) == 0);
			sig_macc[n->y] = n;
		}
	}

	void merge_macc()
	{
		while (1)
		{
			std::set<maccnode_t*> delete_nodes;

			for (auto &it : sig_macc)
			{
				auto n = it.second;

				if (delete_nodes.count(n))
					continue;

				for (int i = 0; i < SIZE(n->macc.ports); i++)
				{
					auto &port = n->macc.ports[i];

					if (SIZE(port.in_b) > 0 || sig_macc.count(port.in_a) == 0)
						continue;

					auto other_n = sig_macc.at(port.in_a);

					if (other_n->users > 1)
						continue;

					if (SIZE(other_n->y) != SIZE(n->y))
						continue;

					log("  merging $macc model for %s into %s.\n", log_id(other_n->cell), log_id(n->cell));

					bool do_subtract = port.do_subtract;
					for (int j = 0; j < SIZE(other_n->macc.ports); j++) {
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

	void replace_macc()
	{
		for (auto &it : sig_macc)
		{
			auto n = it.second;
			auto cell = module->addCell(NEW_ID, "$macc");
			n->macc.to_cell(cell);
			cell->setPort("\\Y", n->y);
			cell->fixup_parameters();
			module->remove(n->cell);
			delete n;
		}

		sig_macc.clear();
	}

	void run()
	{
		log("Extracting $alu and $macc cells in module %s:\n", log_id(module));

		count_bit_users();
		extract_macc();
		merge_macc();
		replace_macc();
	}
};

struct AlumaccPass : public Pass {
	AlumaccPass() : Pass("alumacc", "extract ALU and MACC cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    alumacc [selection]\n");
		log("\n");
		log("This pass translates arithmetic operations $add, $mul, $lt, etc. to $alu and\n");
		log("$macc cells.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing ALUMACC pass (create $alu and $macc cells).\n");

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
 
