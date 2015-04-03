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

#include "kernel/register.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <sstream>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void normalize_sig(RTLIL::Module *module, RTLIL::SigSpec &sig)
{
	for (auto &conn : module->connections())
		sig.replace(conn.first, conn.second);
}

bool find_sig_before_dff(RTLIL::Module *module, std::vector<RTLIL::Cell*> &dff_cells, RTLIL::SigSpec &sig, RTLIL::SigSpec &clk, bool &clk_polarity, bool after = false)
{
	normalize_sig(module, sig);

	for (auto &bit : sig)
	{
		if (bit.wire == NULL)
			continue;

		for (auto cell : dff_cells)
		{
			if (clk != RTLIL::SigSpec(RTLIL::State::Sx)) {
				if (cell->getPort("\\CLK") != clk)
					continue;
				if (cell->parameters["\\CLK_POLARITY"].as_bool() != clk_polarity)
					continue;
			}

			RTLIL::SigSpec q_norm = cell->getPort(after ? "\\D" : "\\Q");
			normalize_sig(module, q_norm);

			RTLIL::SigSpec d = q_norm.extract(bit, &cell->getPort(after ? "\\Q" : "\\D"));
			if (d.size() != 1)
				continue;

			bit = d;
			clk = cell->getPort("\\CLK");
			clk_polarity = cell->parameters["\\CLK_POLARITY"].as_bool();
			goto replaced_this_bit;
		}

		return false;
	replaced_this_bit:;
	}

	return true;
}

void handle_wr_cell(RTLIL::Module *module, std::vector<RTLIL::Cell*> &dff_cells, RTLIL::Cell *cell)
{
	log("Checking cell `%s' in module `%s': ", cell->name.c_str(), module->name.c_str());

	RTLIL::SigSpec clk = RTLIL::SigSpec(RTLIL::State::Sx);
	bool clk_polarity = 0;

	RTLIL::SigSpec sig_addr = cell->getPort("\\ADDR");
	if (!find_sig_before_dff(module, dff_cells, sig_addr, clk, clk_polarity)) {
		log("no (compatible) $dff for address input found.\n");
		return;
	}

	RTLIL::SigSpec sig_data = cell->getPort("\\DATA");
	if (!find_sig_before_dff(module, dff_cells, sig_data, clk, clk_polarity)) {
		log("no (compatible) $dff for data input found.\n");
		return;
	}

	RTLIL::SigSpec sig_en = cell->getPort("\\EN");
	if (!find_sig_before_dff(module, dff_cells, sig_en, clk, clk_polarity)) {
		log("no (compatible) $dff for enable input found.\n");
		return;
	}

	if (clk != RTLIL::SigSpec(RTLIL::State::Sx)) {
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

void disconnect_dff(RTLIL::Module *module, RTLIL::SigSpec sig)
{
	normalize_sig(module, sig);
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

void handle_rd_cell(RTLIL::Module *module, std::vector<RTLIL::Cell*> &dff_cells, RTLIL::Cell *cell)
{
	log("Checking cell `%s' in module `%s': ", cell->name.c_str(), module->name.c_str());

	bool clk_polarity = 0;

	RTLIL::SigSpec clk_data = RTLIL::SigSpec(RTLIL::State::Sx);
	RTLIL::SigSpec sig_data = cell->getPort("\\DATA");
	if (find_sig_before_dff(module, dff_cells, sig_data, clk_data, clk_polarity, true) &&
			clk_data != RTLIL::SigSpec(RTLIL::State::Sx))
	{
		disconnect_dff(module, sig_data);
		cell->setPort("\\CLK", clk_data);
		cell->setPort("\\DATA", sig_data);
		cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(1);
		cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity);
		cell->parameters["\\TRANSPARENT"] = RTLIL::Const(0);
		log("merged data $dff to cell.\n");
		return;
	}

	RTLIL::SigSpec clk_addr = RTLIL::SigSpec(RTLIL::State::Sx);
	RTLIL::SigSpec sig_addr = cell->getPort("\\ADDR");
	if (find_sig_before_dff(module, dff_cells, sig_addr, clk_addr, clk_polarity) &&
			clk_addr != RTLIL::SigSpec(RTLIL::State::Sx))
	{
		cell->setPort("\\CLK", clk_addr);
		cell->setPort("\\ADDR", sig_addr);
		cell->parameters["\\CLK_ENABLE"] = RTLIL::Const(1);
		cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(clk_polarity);
		cell->parameters["\\TRANSPARENT"] = RTLIL::Const(1);
		log("merged address $dff to cell.\n");
		return;
	}

	log("no (compatible) $dff found.\n");
}

void handle_module(RTLIL::Module *module, bool flag_wr_only)
{
	std::vector<RTLIL::Cell*> dff_cells;

	for (auto cell : module->cells())
		if (cell->type == "$dff")
			dff_cells.push_back(cell);

	for (auto cell : module->selected_cells())
		if (cell->type == "$memwr" && !cell->parameters["\\CLK_ENABLE"].as_bool())
			handle_wr_cell(module, dff_cells, cell);

	if (!flag_wr_only)
		for (auto cell : module->selected_cells())
			if (cell->type == "$memrd" && !cell->parameters["\\CLK_ENABLE"].as_bool())
				handle_rd_cell(module, dff_cells, cell);
}

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
		log("    -wr_only\n");
		log("        do not merge registers on read ports\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_wr_only = false;

		log_header("Executing MEMORY_DFF pass (merging $dff cells to $memrd and $memwr).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-wr_only") {
				flag_wr_only = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules())
			handle_module(mod, flag_wr_only);
	}
} MemoryDffPass;
 
PRIVATE_NAMESPACE_END
