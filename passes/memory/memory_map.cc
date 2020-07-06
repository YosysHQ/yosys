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
#include <sstream>
#include <set>
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryMapWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;

	std::map<std::pair<RTLIL::SigSpec, RTLIL::SigSpec>, RTLIL::SigBit> decoder_cache;

	std::string genid(RTLIL::IdString name, std::string token1 = "", int i = -1, std::string token2 = "", int j = -1, std::string token3 = "", int k = -1, std::string token4 = "")
	{
		std::stringstream sstr;
		sstr << "$memory" << name.str() << token1;

		if (i >= 0)
			sstr << "[" << i << "]";

		sstr << token2;

		if (j >= 0)
			sstr << "[" << j << "]";

		sstr << token3;

		if (k >= 0)
			sstr << "[" << k << "]";

		sstr << token4 << "$" << (autoidx++);
		return sstr.str();
	}

	RTLIL::Wire *addr_decode(RTLIL::SigSpec addr_sig, RTLIL::SigSpec addr_val)
	{
		std::pair<RTLIL::SigSpec, RTLIL::SigSpec> key(addr_sig, addr_val);
		log_assert(GetSize(addr_sig) == GetSize(addr_val));

		if (decoder_cache.count(key) == 0) {
			if (GetSize(addr_sig) < 2) {
				decoder_cache[key] = module->Eq(NEW_ID, addr_sig, addr_val);
			} else {
				int split_at = GetSize(addr_sig) / 2;
				RTLIL::SigBit left_eq = addr_decode(addr_sig.extract(0, split_at), addr_val.extract(0, split_at));
				RTLIL::SigBit right_eq = addr_decode(addr_sig.extract(split_at, GetSize(addr_sig) - split_at), addr_val.extract(split_at, GetSize(addr_val) - split_at));
				decoder_cache[key] = module->And(NEW_ID, left_eq, right_eq);
			}
		}

		RTLIL::SigBit bit = decoder_cache.at(key);
		log_assert(bit.wire != nullptr && GetSize(bit.wire) == 1);
		return bit.wire;
	}

	void handle_cell(RTLIL::Cell *cell)
	{
		std::set<int> static_ports;
		std::map<int, RTLIL::SigSpec> static_cells_map;

		int wr_ports = cell->parameters["\\WR_PORTS"].as_int();
		int rd_ports = cell->parameters["\\RD_PORTS"].as_int();

		int mem_size = cell->parameters["\\SIZE"].as_int();
		int mem_width = cell->parameters["\\WIDTH"].as_int();
		int mem_offset = cell->parameters["\\OFFSET"].as_int();
		int mem_abits = cell->parameters["\\ABITS"].as_int();

		SigSpec init_data = cell->getParam("\\INIT");
		init_data.extend_u0(mem_size*mem_width, true);

		// delete unused memory cell
		if (wr_ports == 0 && rd_ports == 0) {
			module->remove(cell);
			return;
		}

		// all write ports must share the same clock
		RTLIL::SigSpec clocks = cell->getPort("\\WR_CLK");
		RTLIL::Const clocks_pol = cell->parameters["\\WR_CLK_POLARITY"];
		RTLIL::Const clocks_en = cell->parameters["\\WR_CLK_ENABLE"];
		clocks_pol.bits.resize(wr_ports);
		clocks_en.bits.resize(wr_ports);
		RTLIL::SigSpec refclock;
		RTLIL::State refclock_pol = RTLIL::State::Sx;
		for (int i = 0; i < clocks.size(); i++) {
			RTLIL::SigSpec wr_en = cell->getPort("\\WR_EN").extract(i * mem_width, mem_width);
			if (wr_en.is_fully_const() && !wr_en.as_bool()) {
				static_ports.insert(i);
				continue;
			}
			if (clocks_en.bits[i] != RTLIL::State::S1) {
				RTLIL::SigSpec wr_addr = cell->getPort("\\WR_ADDR").extract(i*mem_abits, mem_abits);
				RTLIL::SigSpec wr_data = cell->getPort("\\WR_DATA").extract(i*mem_width, mem_width);
				if (wr_addr.is_fully_const()) {
					// FIXME: Actually we should check for wr_en.is_fully_const() also and
					// create a $adff cell with this ports wr_en input as reset pin when wr_en
					// is not a simple static 1.
					static_cells_map[wr_addr.as_int() - mem_offset] = wr_data;
					static_ports.insert(i);
					continue;
				}
				log("Not mapping memory cell %s in module %s (write port %d has no clock).\n",
						cell->name.c_str(), module->name.c_str(), i);
				return;
			}
			if (refclock.size() == 0) {
				refclock = clocks.extract(i, 1);
				refclock_pol = clocks_pol.bits[i];
			}
			if (clocks.extract(i, 1) != refclock || clocks_pol.bits[i] != refclock_pol) {
				log("Not mapping memory cell %s in module %s (write clock %d is incompatible with other clocks).\n",
						cell->name.c_str(), module->name.c_str(), i);
				return;
			}
		}

		log("Mapping memory cell %s in module %s:\n", cell->name.c_str(), module->name.c_str());

		std::vector<RTLIL::SigSpec> data_reg_in;
		std::vector<RTLIL::SigSpec> data_reg_out;

		int count_static = 0;

		for (int i = 0; i < mem_size; i++)
		{
			if (static_cells_map.count(i) > 0)
			{
				data_reg_in.push_back(RTLIL::SigSpec(RTLIL::State::Sz, mem_width));
				data_reg_out.push_back(static_cells_map[i]);
				count_static++;
			}
			else
			{
				RTLIL::Cell *c = module->addCell(genid(cell->name, "", i), "$dff");
				c->parameters["\\WIDTH"] = cell->parameters["\\WIDTH"];
				if (clocks_pol.bits.size() > 0) {
					c->parameters["\\CLK_POLARITY"] = RTLIL::Const(clocks_pol.bits[0]);
					c->setPort("\\CLK", clocks.extract(0, 1));
				} else {
					c->parameters["\\CLK_POLARITY"] = RTLIL::Const(RTLIL::State::S1);
					c->setPort("\\CLK", RTLIL::SigSpec(RTLIL::State::S0));
				}

				RTLIL::Wire *w_in = module->addWire(genid(cell->name, "", i, "$d"), mem_width);
				data_reg_in.push_back(RTLIL::SigSpec(w_in));
				c->setPort("\\D", data_reg_in.back());

				std::string w_out_name = stringf("%s[%d]", cell->parameters["\\MEMID"].decode_string().c_str(), i);
				if (module->wires_.count(w_out_name) > 0)
					w_out_name = genid(cell->name, "", i, "$q");

				RTLIL::Wire *w_out = module->addWire(w_out_name, mem_width);
				SigSpec w_init = init_data.extract(i*mem_width, mem_width);

				if (!w_init.is_fully_undef())
					w_out->attributes["\\init"] = w_init.as_const();

				data_reg_out.push_back(RTLIL::SigSpec(w_out));
				c->setPort("\\Q", data_reg_out.back());
			}
		}

		log("  created %d $dff cells and %d static cells of width %d.\n", mem_size-count_static, count_static, mem_width);

		int count_dff = 0, count_mux = 0, count_wrmux = 0;

		for (int i = 0; i < cell->parameters["\\RD_PORTS"].as_int(); i++)
		{
			RTLIL::SigSpec rd_addr = cell->getPort("\\RD_ADDR").extract(i*mem_abits, mem_abits);

			if (mem_offset)
				rd_addr = module->Sub(NEW_ID, rd_addr, SigSpec(mem_offset, GetSize(rd_addr)));

			std::vector<RTLIL::SigSpec> rd_signals;
			rd_signals.push_back(cell->getPort("\\RD_DATA").extract(i*mem_width, mem_width));

			if (cell->parameters["\\RD_CLK_ENABLE"].bits[i] == RTLIL::State::S1)
			{
				RTLIL::Cell *dff_cell = nullptr;

				if (cell->parameters["\\RD_TRANSPARENT"].bits[i] == RTLIL::State::S1)
				{
					dff_cell = module->addCell(genid(cell->name, "$rdreg", i), "$dff");
					dff_cell->parameters["\\WIDTH"] = RTLIL::Const(mem_abits);
					dff_cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(cell->parameters["\\RD_CLK_POLARITY"].bits[i]);
					dff_cell->setPort("\\CLK", cell->getPort("\\RD_CLK").extract(i, 1));
					dff_cell->setPort("\\D", rd_addr);
					count_dff++;

					RTLIL::Wire *w = module->addWire(genid(cell->name, "$rdreg", i, "$q"), mem_abits);

					dff_cell->setPort("\\Q", RTLIL::SigSpec(w));
					rd_addr = RTLIL::SigSpec(w);
				}
				else
				{
					dff_cell = module->addCell(genid(cell->name, "$rdreg", i), "$dff");
					dff_cell->parameters["\\WIDTH"] = cell->parameters["\\WIDTH"];
					dff_cell->parameters["\\CLK_POLARITY"] = RTLIL::Const(cell->parameters["\\RD_CLK_POLARITY"].bits[i]);
					dff_cell->setPort("\\CLK", cell->getPort("\\RD_CLK").extract(i, 1));
					dff_cell->setPort("\\Q", rd_signals.back());
					count_dff++;

					RTLIL::Wire *w = module->addWire(genid(cell->name, "$rdreg", i, "$d"), mem_width);

					rd_signals.clear();
					rd_signals.push_back(RTLIL::SigSpec(w));
					dff_cell->setPort("\\D", rd_signals.back());
				}

				SigBit en_bit = cell->getPort("\\RD_EN").extract(i);
				if (en_bit != State::S1) {
					SigSpec new_d = module->Mux(genid(cell->name, "$rdenmux", i),
							dff_cell->getPort("\\Q"), dff_cell->getPort("\\D"), en_bit);
					dff_cell->setPort("\\D", new_d);
				}
			}

			for (int j = 0; j < mem_abits; j++)
			{
				std::vector<RTLIL::SigSpec> next_rd_signals;

				for (size_t k = 0; k < rd_signals.size(); k++)
				{
					RTLIL::Cell *c = module->addCell(genid(cell->name, "$rdmux", i, "", j, "", k), "$mux");
					c->parameters["\\WIDTH"] = cell->parameters["\\WIDTH"];
					c->setPort("\\Y", rd_signals[k]);
					c->setPort("\\S", rd_addr.extract(mem_abits-j-1, 1));
					count_mux++;

					c->setPort("\\A", module->addWire(genid(cell->name, "$rdmux", i, "", j, "", k, "$a"), mem_width));
					c->setPort("\\B", module->addWire(genid(cell->name, "$rdmux", i, "", j, "", k, "$b"), mem_width));

					next_rd_signals.push_back(c->getPort("\\A"));
					next_rd_signals.push_back(c->getPort("\\B"));
				}

				next_rd_signals.swap(rd_signals);
			}

			for (int j = 0; j < mem_size; j++)
				module->connect(RTLIL::SigSig(rd_signals[j], data_reg_out[j]));
		}

		log("  read interface: %d $dff and %d $mux cells.\n", count_dff, count_mux);

		for (int i = 0; i < mem_size; i++)
		{
			if (static_cells_map.count(i) > 0)
				continue;

			RTLIL::SigSpec sig = data_reg_out[i];

			for (int j = 0; j < cell->parameters["\\WR_PORTS"].as_int(); j++)
			{
				RTLIL::SigSpec wr_addr = cell->getPort("\\WR_ADDR").extract(j*mem_abits, mem_abits);
				RTLIL::SigSpec wr_data = cell->getPort("\\WR_DATA").extract(j*mem_width, mem_width);
				RTLIL::SigSpec wr_en = cell->getPort("\\WR_EN").extract(j*mem_width, mem_width);

				if (mem_offset)
					wr_addr = module->Sub(NEW_ID, wr_addr, SigSpec(mem_offset, GetSize(wr_addr)));

				RTLIL::Wire *w_seladdr = addr_decode(wr_addr, RTLIL::SigSpec(i, mem_abits));

				int wr_offset = 0;
				while (wr_offset < wr_en.size())
				{
					int wr_width = 1;
					RTLIL::SigSpec wr_bit = wr_en.extract(wr_offset, 1);

					while (wr_offset + wr_width < wr_en.size()) {
						RTLIL::SigSpec next_wr_bit = wr_en.extract(wr_offset + wr_width, 1);
						if (next_wr_bit != wr_bit)
							break;
						wr_width++;
					}

					RTLIL::Wire *w = w_seladdr;

					if (wr_bit != State::S1)
					{
						RTLIL::Cell *c = module->addCell(genid(cell->name, "$wren", i, "", j, "", wr_offset), "$and");
						c->parameters["\\A_SIGNED"] = RTLIL::Const(0);
						c->parameters["\\B_SIGNED"] = RTLIL::Const(0);
						c->parameters["\\A_WIDTH"] = RTLIL::Const(1);
						c->parameters["\\B_WIDTH"] = RTLIL::Const(1);
						c->parameters["\\Y_WIDTH"] = RTLIL::Const(1);
						c->setPort("\\A", w);
						c->setPort("\\B", wr_bit);

						w = module->addWire(genid(cell->name, "$wren", i, "", j, "", wr_offset, "$y"));
						c->setPort("\\Y", RTLIL::SigSpec(w));
					}

					RTLIL::Cell *c = module->addCell(genid(cell->name, "$wrmux", i, "", j, "", wr_offset), "$mux");
					c->parameters["\\WIDTH"] = wr_width;
					c->setPort("\\A", sig.extract(wr_offset, wr_width));
					c->setPort("\\B", wr_data.extract(wr_offset, wr_width));
					c->setPort("\\S", RTLIL::SigSpec(w));

					w = module->addWire(genid(cell->name, "$wrmux", i, "", j, "", wr_offset, "$y"), wr_width);
					c->setPort("\\Y", w);

					sig.replace(wr_offset, w);
					wr_offset += wr_width;
					count_wrmux++;
				}
			}

			module->connect(RTLIL::SigSig(data_reg_in[i], sig));
		}

		log("  write interface: %d write mux blocks.\n", count_wrmux);

		module->remove(cell);
	}

	MemoryMapWorker(RTLIL::Design *design, RTLIL::Module *module) : design(design), module(module)
	{
		std::vector<RTLIL::Cell*> cells;
		for (auto cell : module->selected_cells())
			if (cell->type == "$mem" && design->selected(module, cell))
				cells.push_back(cell);
		for (auto cell : cells)
			handle_cell(cell);
	}
};

struct MemoryMapPass : public Pass {
	MemoryMapPass() : Pass("memory_map", "translate multiport memories to basic cells") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_map [selection]\n");
		log("\n");
		log("This pass converts multiport memory cells as generated by the memory_collect\n");
		log("pass to word-wide DFFs and address decoders.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE {
		log_header(design, "Executing MEMORY_MAP pass (converting $mem cells to logic and flip-flops).\n");
		extra_args(args, 1, design);
		for (auto mod : design->selected_modules())
			MemoryMapWorker(design, mod);
	}
} MemoryMapPass;

PRIVATE_NAMESPACE_END
