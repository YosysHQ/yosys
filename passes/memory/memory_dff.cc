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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryDffWorker
{
	Module *module;
	SigMap sigmap;

	vector<Cell*> dff_cells;
	dict<SigBit, SigBit> invbits;
	dict<SigBit, int> sigbit_users_count;
	dict<SigSpec, Cell*> mux_cells_a, mux_cells_b;
	pool<Cell*> forward_merged_dffs, candidate_dffs;

	MemoryDffWorker(Module *module) : module(module), sigmap(module) { }

	bool find_sig_before_dff(RTLIL::SigSpec &sig, RTLIL::SigSpec &clk, bool &clk_polarity, bool after = false)
	{
		sigmap.apply(sig);

		for (auto &bit : sig)
		{
			if (bit.wire == NULL)
				continue;

			for (auto cell : dff_cells)
			{
				if (after && forward_merged_dffs.count(cell))
					continue;

				SigSpec this_clk = cell->getPort("\\CLK");
				bool this_clk_polarity = cell->parameters["\\CLK_POLARITY"].as_bool();

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

				RTLIL::SigSpec q_norm = cell->getPort(after ? "\\D" : "\\Q");
				sigmap.apply(q_norm);

				RTLIL::SigSpec d = q_norm.extract(bit, &cell->getPort(after ? "\\Q" : "\\D"));
				if (d.size() != 1)
					continue;

				bit = d;
				clk = this_clk;
				clk_polarity = this_clk_polarity;
				candidate_dffs.insert(cell);
				goto replaced_this_bit;
			}

			return false;
		replaced_this_bit:;
		}

		return true;
	}

	void handle_wr_cell(RTLIL::Cell *cell)
	{
		log("Checking cell `%s' in module `%s': ", cell->name.c_str(), module->name.c_str());

		RTLIL::SigSpec clk = RTLIL::SigSpec(RTLIL::State::Sx);
		bool clk_polarity = 0;
		candidate_dffs.clear();

		RTLIL::SigSpec sig_addr = cell->getPort("\\ADDR");
		if (!find_sig_before_dff(sig_addr, clk, clk_polarity)) {
			log("no (compatible) $dff for address input found.\n");
			return;
		}

		RTLIL::SigSpec sig_data = cell->getPort("\\DATA");
		if (!find_sig_before_dff(sig_data, clk, clk_polarity)) {
			log("no (compatible) $dff for data input found.\n");
			return;
		}

		RTLIL::SigSpec sig_en = cell->getPort("\\EN");
		if (!find_sig_before_dff(sig_en, clk, clk_polarity)) {
			log("no (compatible) $dff for enable input found.\n");
			return;
		}

		if (clk != RTLIL::SigSpec(RTLIL::State::Sx))
		{
			for (auto cell : candidate_dffs)
				forward_merged_dffs.insert(cell);

			cell->setPort("\\CLK", clk);
			cell->setPort("\\ADDR", sig_addr);
			cell->setPort("\\DATA", sig_data);
			cell->setPort("\\EN", sig_en);
			cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(1);
			cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity);

			log("merged $dff to cell.\n");
			return;
		}

		log("no (compatible) $dff found.\n");
	}

	void disconnect_dff(RTLIL::SigSpec sig)
	{
		sigmap.apply(sig);
		sig.sort_and_unify();

		std::stringstream sstr;
		sstr << "$memory_dff_disconnected$" << (autoidx++);

		RTLIL::SigSpec new_sig = module->addWire(sstr.str(), sig.size());

		for (auto cell : module->cells())
			if (cell->type == "$dff") {
				RTLIL::SigSpec new_q = cell->getPort("\\Q");
				new_q.replace(sig, new_sig);
				cell->setPort("\\Q", new_q);
			}
	}

	void handle_rd_cell(RTLIL::Cell *cell)
	{
		log("Checking cell `%s' in module `%s': ", cell->name.c_str(), module->name.c_str());

		bool clk_polarity = 0;

		RTLIL::SigSpec clk_data = RTLIL::SigSpec(RTLIL::State::Sx);
		RTLIL::SigSpec sig_data = cell->getPort("\\DATA");

		for (auto bit : sigmap(sig_data))
			if (sigbit_users_count[bit] > 1)
				goto skip_ff_after_read_merging;

		if (mux_cells_a.count(sig_data) || mux_cells_b.count(sig_data))
		{
			bool enable_invert = mux_cells_a.count(sig_data) != 0;
			Cell *mux = enable_invert ? mux_cells_a.at(sig_data) : mux_cells_b.at(sig_data);
			SigSpec check_q = sigmap(mux->getPort(enable_invert ? "\\B" : "\\A"));

			sig_data = sigmap(mux->getPort("\\Y"));
			for (auto bit : sig_data)
				if (sigbit_users_count[bit] > 1)
					goto skip_ff_after_read_merging;

			if (find_sig_before_dff(sig_data, clk_data, clk_polarity, true) && clk_data != RTLIL::SigSpec(RTLIL::State::Sx) && sig_data == check_q)
			{
				disconnect_dff(sig_data);
				cell->setPort("\\CLK", clk_data);
				cell->setPort("\\EN", enable_invert ? module->LogicNot(NEW_ID, mux->getPort("\\S")) : mux->getPort("\\S"));
				cell->setPort("\\DATA", sig_data);
				cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(1);
				cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity);
				cell->parameters["\\TRANSPARENT"] = RTLIL::Const(0);
				log("merged data $dff with rd enable to cell.\n");
				return;
			}
		}
		else
		{
			if (find_sig_before_dff(sig_data, clk_data, clk_polarity, true) && clk_data != RTLIL::SigSpec(RTLIL::State::Sx))
			{
				disconnect_dff(sig_data);
				cell->setPort("\\CLK", clk_data);
				cell->setPort("\\EN", State::S1);
				cell->setPort("\\DATA", sig_data);
				cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(1);
				cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity);
				cell->parameters["\\TRANSPARENT"] = RTLIL::Const(0);
				log("merged data $dff to cell.\n");
				return;
			}
		}

	skip_ff_after_read_merging:;
		RTLIL::SigSpec clk_addr = RTLIL::SigSpec(RTLIL::State::Sx);
		RTLIL::SigSpec sig_addr = cell->getPort("\\ADDR");
		if (find_sig_before_dff(sig_addr, clk_addr, clk_polarity) &&
				clk_addr != RTLIL::SigSpec(RTLIL::State::Sx))
		{
			cell->setPort("\\CLK", clk_addr);
			cell->setPort("\\EN", State::S1);
			cell->setPort("\\ADDR", sig_addr);
			cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(1);
			cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity);
			cell->parameters["\\TRANSPARENT"] = RTLIL::Const(1);
			log("merged address $dff to cell.\n");
			return;
		}

		log("no (compatible) $dff found.\n");
	}

	void run(bool flag_wr_only)
	{
		for (auto wire : module->wires()) {
			if (wire->port_output)
				for (auto bit : sigmap(wire))
					sigbit_users_count[bit]++;
		}

		for (auto cell : module->cells()) {
			if (cell->type == "$dff")
				dff_cells.push_back(cell);
			if (cell->type == "$mux") {
				mux_cells_a[sigmap(cell->getPort("\\A"))] = cell;
				mux_cells_b[sigmap(cell->getPort("\\B"))] = cell;
			}
			if (cell->type == "$not" || cell->type == "$_NOT_" || (cell->type == "$logic_not" && GetSize(cell->getPort("\\A")) == 1)) {
				SigSpec sig_a = cell->getPort("\\A");
				SigSpec sig_y = cell->getPort("\\Y");
				if (cell->type == "$not")
					sig_a.extend_u0(GetSize(sig_y), cell->getParam("\\A_SIGNED").as_bool());
				if (cell->type == "$logic_not")
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
			if (cell->type == "$memwr" && !cell->parameters["\\CLK_ENABLE"].as_bool())
				handle_wr_cell(cell);

		if (!flag_wr_only)
			for (auto cell : module->selected_cells())
				if (cell->type == "$memrd" && !cell->parameters["\\CLK_ENABLE"].as_bool())
					handle_rd_cell(cell);
	}
};

struct MemoryDffPass : public Pass {
	MemoryDffPass() : Pass("memory_dff", "merge input/output DFFs into memories") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_dff [options] [selection]\n");
		log("\n");
		log("This pass detects DFFs at memory ports and merges them into the memory port.\n");
		log("I.e. it consumes an asynchronous memory port and the flip-flops at its\n");
		log("interface and yields a synchronous memory port.\n");
		log("\n");
		log("    -nordfff\n");
		log("        do not merge registers on read ports\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_wr_only = false;

		log_header(design, "Executing MEMORY_DFF pass (merging $dff cells to $memrd and $memwr).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-nordff" || args[argidx] == "-wr_only") {
				flag_wr_only = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			MemoryDffWorker worker(mod);
			worker.run(flag_wr_only);
		}
	}
} MemoryDffPass;

PRIVATE_NAMESPACE_END
