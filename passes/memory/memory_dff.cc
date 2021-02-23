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

#include <algorithm>
#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/ffinit.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryDffWorker
{
	Module *module;
	SigMap sigmap;

	vector<Cell*> dff_cells;
	dict<SigBit, SigBit> invbits;
	dict<SigBit, int> sigbit_users_count;
	FfInitVals initvals;

	MemoryDffWorker(Module *module) : module(module), sigmap(module)
	{
		initvals.set(&sigmap, module);
	}

	bool find_sig_before_dff(RTLIL::SigSpec &sig, RTLIL::SigSpec &clk, bool &clk_polarity)
	{
		sigmap.apply(sig);

		dict<SigBit, SigBit> cache;

		for (auto &bit : sig)
		{
			if (cache.count(bit)) {
				bit = cache[bit];
				continue;
			}

			if (bit.wire == NULL)
				continue;

			if (initvals(bit) != State::Sx)
				return false;

			for (auto cell : dff_cells)
			{
				SigSpec this_clk = cell->getPort(ID::CLK);
				bool this_clk_polarity = cell->parameters[ID::CLK_POLARITY].as_bool();

				if (invbits.count(this_clk)) {
					this_clk = invbits.at(this_clk);
					this_clk_polarity = !this_clk_polarity;
				}

				if (clk != RTLIL::SigSpec(RTLIL::State::Sx)) {
					if (this_clk != clk)
						continue;
					if (this_clk_polarity != clk_polarity)
						continue;
				}

				RTLIL::SigSpec q_norm = cell->getPort(ID::Q);
				sigmap.apply(q_norm);

				RTLIL::SigSpec d = q_norm.extract(bit, &cell->getPort(ID::D));
				if (d.size() != 1)
					continue;

				if (cell->type == ID($sdffce)) {
					SigSpec rval = cell->parameters[ID::SRST_VALUE];
					SigSpec rbit = q_norm.extract(bit, &rval);
					if (cell->parameters[ID::SRST_POLARITY].as_bool())
						d = module->Mux(NEW_ID, d, rbit, cell->getPort(ID::SRST));
					else
						d = module->Mux(NEW_ID, rbit, d, cell->getPort(ID::SRST));
				}

				if (cell->type.in(ID($dffe), ID($sdffe), ID($sdffce))) {
					if (cell->parameters[ID::EN_POLARITY].as_bool())
						d = module->Mux(NEW_ID, bit, d, cell->getPort(ID::EN));
					else
						d = module->Mux(NEW_ID, d, bit, cell->getPort(ID::EN));
				}

				if (cell->type.in(ID($sdff), ID($sdffe))) {
					SigSpec rval = cell->parameters[ID::SRST_VALUE];
					SigSpec rbit = q_norm.extract(bit, &rval);
					if (cell->parameters[ID::SRST_POLARITY].as_bool())
						d = module->Mux(NEW_ID, d, rbit, cell->getPort(ID::SRST));
					else
						d = module->Mux(NEW_ID, rbit, d, cell->getPort(ID::SRST));
				}

				cache[bit] = d;
				bit = d;
				clk = this_clk;
				clk_polarity = this_clk_polarity;
				goto replaced_this_bit;
			}

			return false;
		replaced_this_bit:;
		}

		return true;
	}

	bool find_sig_after_dffe(RTLIL::SigSpec &sig, RTLIL::SigSpec &clk, bool &clk_polarity, RTLIL::SigSpec &en, bool &en_polarity)
	{
		sigmap.apply(sig);

		for (auto &bit : sig)
		{
			if (bit.wire == NULL)
				continue;

			for (auto cell : dff_cells)
			{
				if (!cell->type.in(ID($dff), ID($dffe)))
					continue;

				SigSpec this_clk = cell->getPort(ID::CLK);
				bool this_clk_polarity = cell->parameters[ID::CLK_POLARITY].as_bool();
				SigSpec this_en = State::S1;
				bool this_en_polarity = true;

				if (cell->type == ID($dffe)) {
					this_en = cell->getPort(ID::EN);
					this_en_polarity = cell->parameters[ID::EN_POLARITY].as_bool();
				}

				if (invbits.count(this_clk)) {
					this_clk = invbits.at(this_clk);
					this_clk_polarity = !this_clk_polarity;
				}

				if (invbits.count(this_en)) {
					this_en = invbits.at(this_en);
					this_en_polarity = !this_en_polarity;
				}

				if (clk != RTLIL::SigSpec(RTLIL::State::Sx)) {
					if (this_clk != clk)
						continue;
					if (this_clk_polarity != clk_polarity)
						continue;
					if (this_en != en)
						continue;
					if (this_en_polarity != en_polarity)
						continue;
				}

				RTLIL::SigSpec q_norm = cell->getPort(ID::D);
				sigmap.apply(q_norm);

				RTLIL::SigSpec d = q_norm.extract(bit, &cell->getPort(ID::Q));
				if (d.size() != 1)
					continue;

				if (initvals(d) != State::Sx)
					return false;

				bit = d;
				clk = this_clk;
				clk_polarity = this_clk_polarity;
				en = this_en;
				en_polarity = this_en_polarity;
				goto replaced_this_bit;
			}

			return false;
		replaced_this_bit:;
		}

		return true;
	}

	void disconnect_dff(RTLIL::SigSpec sig)
	{
		sigmap.apply(sig);
		sig.sort_and_unify();

		std::stringstream sstr;
		sstr << "$memory_dff_disconnected$" << (autoidx++);

		RTLIL::SigSpec new_sig = module->addWire(sstr.str(), sig.size());

		for (auto cell : module->cells())
			if (cell->type.in(ID($dff), ID($dffe))) {
				RTLIL::SigSpec new_q = cell->getPort(ID::Q);
				new_q.replace(sig, new_sig);
				cell->setPort(ID::Q, new_q);
			}
	}

	void handle_rd_cell(RTLIL::Cell *cell)
	{
		log("Checking cell `%s' in module `%s': ", cell->name.c_str(), module->name.c_str());

		bool clk_polarity = 0;
		bool en_polarity = 0;

		RTLIL::SigSpec clk_data = RTLIL::SigSpec(RTLIL::State::Sx);
		RTLIL::SigSpec en_data;
		RTLIL::SigSpec sig_data = cell->getPort(ID::DATA);

		for (auto bit : sigmap(sig_data))
			if (sigbit_users_count[bit] > 1)
				goto skip_ff_after_read_merging;

		if (find_sig_after_dffe(sig_data, clk_data, clk_polarity, en_data, en_polarity) && clk_data != RTLIL::SigSpec(RTLIL::State::Sx))
		{
			if (!en_polarity)
				en_data = module->LogicNot(NEW_ID, en_data);
			disconnect_dff(sig_data);
			cell->setPort(ID::CLK, clk_data);
			cell->setPort(ID::EN, en_data);
			cell->setPort(ID::DATA, sig_data);
			cell->parameters[ID::CLK_ENABLE] = RTLIL::Const(1);
			cell->parameters[ID::CLK_POLARITY] = RTLIL::Const(clk_polarity);
			cell->parameters[ID::TRANSPARENT] = RTLIL::Const(0);
			log("merged data $dff to cell.\n");
			return;
		}

	skip_ff_after_read_merging:;
		RTLIL::SigSpec clk_addr = RTLIL::SigSpec(RTLIL::State::Sx);
		RTLIL::SigSpec sig_addr = cell->getPort(ID::ADDR);
		if (find_sig_before_dff(sig_addr, clk_addr, clk_polarity) &&
				clk_addr != RTLIL::SigSpec(RTLIL::State::Sx))
		{
			cell->setPort(ID::CLK, clk_addr);
			cell->setPort(ID::EN, State::S1);
			cell->setPort(ID::ADDR, sig_addr);
			cell->parameters[ID::CLK_ENABLE] = RTLIL::Const(1);
			cell->parameters[ID::CLK_POLARITY] = RTLIL::Const(clk_polarity);
			cell->parameters[ID::TRANSPARENT] = RTLIL::Const(1);
			log("merged address $dff to cell.\n");
			return;
		}

		log("no (compatible) $dff found.\n");
	}

	void run()
	{
		for (auto wire : module->wires()) {
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					sigbit_users_count[bit]++;
		}

		for (auto cell : module->cells()) {
			if (cell->type.in(ID($dff), ID($dffe), ID($sdff), ID($sdffe), ID($sdffce)))
				dff_cells.push_back(cell);
			if (cell->type.in(ID($not), ID($_NOT_)) || (cell->type == ID($logic_not) && GetSize(cell->getPort(ID::A)) == 1)) {
				SigSpec sig_a = cell->getPort(ID::A);
				SigSpec sig_y = cell->getPort(ID::Y);
				if (cell->type == ID($not))
					sig_a.extend_u0(GetSize(sig_y), cell->getParam(ID::A_SIGNED).as_bool());
				if (cell->type == ID($logic_not))
					sig_y.extend_u0(1);
				for (int i = 0; i < GetSize(sig_y); i++)
					invbits[sig_y[i]] = sig_a[i];
			}
			for (auto &conn : cell->connections())
				if (!cell->known() || cell->input(conn.first))
					for (auto bit : sigmap(conn.second))
						sigbit_users_count[bit]++;
		}

		for (auto cell : module->selected_cells())
			if (cell->type == ID($memrd) && !cell->parameters[ID::CLK_ENABLE].as_bool())
				handle_rd_cell(cell);
	}
};

struct MemoryDffPass : public Pass {
	MemoryDffPass() : Pass("memory_dff", "merge input/output DFFs into memory read ports") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_dff [options] [selection]\n");
		log("\n");
		log("This pass detects DFFs at memory read ports and merges them into the memory port.\n");
		log("I.e. it consumes an asynchronous memory port and the flip-flops at its\n");
		log("interface and yields a synchronous memory port.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing MEMORY_DFF pass (merging $dff cells to $memrd).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			MemoryDffWorker worker(mod);
			worker.run();
		}
	}
} MemoryDffPass;

PRIVATE_NAMESPACE_END
