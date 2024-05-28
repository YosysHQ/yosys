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
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/register.h"
#include "kernel/log.h"
#include "kernel/mem.h"
#include <sstream>
#include <set>
#include <stdlib.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryMapWorker
{
	bool attr_icase = false;
	bool rom_only = false;
	bool keepdc = false;
	bool formal = false;
	dict<RTLIL::IdString, std::vector<RTLIL::Const>> attributes;

	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap;
	FfInitVals initvals;

	std::map<std::pair<RTLIL::SigSpec, RTLIL::SigSpec>, RTLIL::SigBit> decoder_cache;

	MemoryMapWorker(RTLIL::Design *design, RTLIL::Module *module) : design(design), module(module), sigmap(module), initvals(&sigmap, module) {}

	std::string map_case(std::string value) const
	{
		if (attr_icase) {
			for (char &c : value)
				c = tolower(c);
		}
		return value;
	}

	RTLIL::Const map_case(RTLIL::Const value) const
	{
		if (value.flags & RTLIL::CONST_FLAG_STRING)
			return map_case(value.decode_string());
		return value;
	}

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

	void handle_memory(Mem &mem)
	{
		std::set<int> static_ports;
		std::map<int, RTLIL::SigSpec> static_cells_map;

		SigSpec init_data = mem.get_init_data();

		if (!mem.wr_ports.empty() && rom_only)
			return;

		// check if attributes allow us to infer FFRAM for this memory
		for (const auto &attr : attributes) {
			if (mem.attributes.count(attr.first)) {
				const auto &cell_attr = mem.attributes[attr.first];
				if (attr.second.empty()) {
					log("Not mapping memory %s in module %s (attribute %s is set).\n",
							mem.memid.c_str(), module->name.c_str(), attr.first.c_str());
					return;
				}

				bool found = false;
				for (auto &value : attr.second) {
					if (map_case(cell_attr) == map_case(value)) {
						found = true;
						break;
					}
				}
				if (!found) {
					if (cell_attr.flags & RTLIL::CONST_FLAG_STRING) {
						log("Not mapping memory %s in module %s (attribute %s is set to \"%s\").\n",
								mem.memid.c_str(), module->name.c_str(), attr.first.c_str(), cell_attr.decode_string().c_str());
					} else {
						log("Not mapping memory %s in module %s (attribute %s is set to %d).\n",
								mem.memid.c_str(), module->name.c_str(), attr.first.c_str(), cell_attr.as_int());
					}
					return;
				}
			}
		}

		// delete unused memory cell
		if (mem.rd_ports.empty()) {
			mem.remove();
			return;
		}

		// all write ports must share the same clock
		RTLIL::SigSpec refclock;
		bool refclock_pol = false;
		bool async_wr = false;
		bool static_only = true;
		for (int i = 0; i < GetSize(mem.wr_ports); i++) {
			auto &port = mem.wr_ports[i];
			if (port.en.is_fully_const() && !port.en.as_bool()) {
				static_ports.insert(i);
				continue;
			}
			if (!port.clk_enable) {
				if (port.addr.is_fully_const() && port.en.is_fully_ones()) {
					for (int sub = 0; sub < (1 << port.wide_log2); sub++)
						static_cells_map[port.addr.as_int() + sub] = port.data.extract(sub * mem.width, mem.width);
					static_ports.insert(i);
					continue;
				}
				static_only = false;
				if (GetSize(refclock) != 0)
					log("Not mapping memory %s in module %s (mixed clocked and async write ports).\n",
							mem.memid.c_str(), module->name.c_str());
				if (!formal)
					log("Not mapping memory %s in module %s (write port %d has no clock).\n",
								mem.memid.c_str(), module->name.c_str(), i);
				async_wr = true;
				continue;
			}
			static_only = false;
			if (async_wr)
				log("Not mapping memory %s in module %s (mixed clocked and async write ports).\n",
						mem.memid.c_str(), module->name.c_str());
			if (refclock.size() == 0) {
				refclock = port.clk;
				refclock_pol = port.clk_polarity;
			}
			if (port.clk != refclock || port.clk_polarity != refclock_pol) {
				log("Not mapping memory %s in module %s (write clock %d is incompatible with other clocks).\n",
						mem.memid.c_str(), module->name.c_str(), i);
				return;
			}
		}

		log("Mapping memory %s in module %s:\n", mem.memid.c_str(), module->name.c_str());

		int abits = ceil_log2(mem.size);
		std::vector<RTLIL::SigSpec> data_reg_in(1 << abits);
		std::vector<RTLIL::SigSpec> data_reg_out(1 << abits);

		std::vector<RTLIL::SigSpec> &data_read = async_wr ? data_reg_in : data_reg_out;

		int count_static = 0;

		for (int i = 0; i < mem.size; i++)
		{
			int addr = i + mem.start_offset;
			int idx = addr & ((1 << abits) - 1);
			SigSpec w_init = init_data.extract(i*mem.width, mem.width);
			if (static_cells_map.count(addr) > 0)
			{
				data_read[idx] = static_cells_map[addr];
				count_static++;
			}
			else if (static_only && (!keepdc || w_init.is_fully_def()))
			{
				data_read[idx] = w_init;
			}
			else
			{
				RTLIL::Cell *c;
				auto ff_id = genid(mem.memid, "", addr);

				if (static_only) {
					// non-static part is a ROM, we only reach this with keepdc
					if (formal) {
						c = module->addCell(ff_id, ID($ff));
					} else {
						c = module->addCell(ff_id, ID($dff));
						c->parameters[ID::CLK_POLARITY] = RTLIL::Const(RTLIL::State::S1);
						c->setPort(ID::CLK, RTLIL::SigSpec(RTLIL::State::S0));
					}
				} else if (async_wr) {
					log_assert(formal); // General async write not implemented yet, checked against above
					c = module->addCell(ff_id, ID($ff));
				} else {
					c = module->addCell(ff_id, ID($dff));
					c->parameters[ID::CLK_POLARITY] = RTLIL::Const(refclock_pol);
					c->setPort(ID::CLK, refclock);
				}
				c->parameters[ID::WIDTH] = mem.width;

				RTLIL::Wire *w_in = module->addWire(genid(mem.memid, "", addr, "$d"), mem.width);
				data_reg_in[idx] = w_in;
				c->setPort(ID::D, w_in);

				std::string w_out_name = stringf("%s[%d]", mem.memid.c_str(), addr);
				if (module->wires_.count(w_out_name) > 0)
					w_out_name = genid(mem.memid, "", addr, "$q");

				RTLIL::Wire *w_out = module->addWire(w_out_name, mem.width);

				if (formal && mem.packed && mem.cell->name.c_str()[0] == '\\') {
					auto hdlname = mem.cell->get_hdlname_attribute();
					if (hdlname.empty())
						hdlname.push_back(mem.cell->name.c_str() + 1);
					hdlname.push_back(stringf("[%d]", addr));
					w_out->set_hdlname_attribute(hdlname);
				}

				if (!w_init.is_fully_undef())
					w_out->attributes[ID::init] = w_init.as_const();

				data_reg_out[idx] = w_out;
				c->setPort(ID::Q, w_out);

				if (static_only)
					module->connect(RTLIL::SigSig(w_in, w_out));
			}
		}

		log("  created %d %s cells and %d static cells of width %d.\n",
				mem.size-count_static, formal && (static_only || async_wr) ? "$ff" : "$dff", count_static, mem.width);

		int count_dff = 0, count_mux = 0, count_wrmux = 0;

		for (int i = 0; i < GetSize(mem.rd_ports); i++)
		{
			auto &port = mem.rd_ports[i];
			if (mem.extract_rdff(i, &initvals))
				count_dff++;
			RTLIL::SigSpec rd_addr = port.addr;
			rd_addr.extend_u0(abits, false);

			std::vector<RTLIL::SigSpec> rd_signals;
			rd_signals.push_back(port.data);

			for (int j = 0; j < abits - port.wide_log2; j++)
			{
				std::vector<RTLIL::SigSpec> next_rd_signals;

				for (size_t k = 0; k < rd_signals.size(); k++)
				{
					RTLIL::Cell *c = module->addCell(genid(mem.memid, "$rdmux", i, "", j, "", k), ID($mux));
					c->parameters[ID::WIDTH] = GetSize(port.data);
					c->setPort(ID::Y, rd_signals[k]);
					c->setPort(ID::S, rd_addr.extract(abits-j-1, 1));
					count_mux++;

					c->setPort(ID::A, module->addWire(genid(mem.memid, "$rdmux", i, "", j, "", k, "$a"), GetSize(port.data)));
					c->setPort(ID::B, module->addWire(genid(mem.memid, "$rdmux", i, "", j, "", k, "$b"), GetSize(port.data)));

					next_rd_signals.push_back(c->getPort(ID::A));
					next_rd_signals.push_back(c->getPort(ID::B));
				}

				next_rd_signals.swap(rd_signals);
			}

			for (int j = 0; j < (1 << abits); j++)
				if (data_read[j] != SigSpec())
					module->connect(RTLIL::SigSig(rd_signals[j >> port.wide_log2].extract((j & ((1 << port.wide_log2) - 1)) * mem.width, mem.width), data_read[j]));
		}

		log("  read interface: %d $dff and %d $mux cells.\n", count_dff, count_mux);

		if (!static_only)
		{
			for (int i = 0; i < mem.size; i++)
			{
				int addr = i + mem.start_offset;
				int idx = addr & ((1 << abits) - 1);
				if (static_cells_map.count(addr) > 0)
					continue;

				RTLIL::SigSpec sig = data_reg_out[idx];

				for (int j = 0; j < GetSize(mem.wr_ports); j++)
				{
					auto &port = mem.wr_ports[j];
					RTLIL::SigSpec wr_addr = port.addr.extract_end(port.wide_log2);
					RTLIL::Wire *w_seladdr = addr_decode(wr_addr, RTLIL::SigSpec(addr >> port.wide_log2, GetSize(wr_addr)));

					int sub = addr & ((1 << port.wide_log2) - 1);

					int wr_offset = 0;
					while (wr_offset < mem.width)
					{
						int wr_width = 1;
						RTLIL::SigSpec wr_bit = port.en.extract(wr_offset + sub * mem.width, 1);

						while (wr_offset + wr_width < mem.width) {
							RTLIL::SigSpec next_wr_bit = port.en.extract(wr_offset + wr_width + sub * mem.width, 1);
							if (next_wr_bit != wr_bit)
								break;
							wr_width++;
						}

						RTLIL::Wire *w = w_seladdr;

						if (wr_bit != State::S1)
						{
							RTLIL::Cell *c = module->addCell(genid(mem.memid, "$wren", addr, "", j, "", wr_offset), ID($and));
							c->parameters[ID::A_SIGNED] = RTLIL::Const(0);
							c->parameters[ID::B_SIGNED] = RTLIL::Const(0);
							c->parameters[ID::A_WIDTH] = RTLIL::Const(1);
							c->parameters[ID::B_WIDTH] = RTLIL::Const(1);
							c->parameters[ID::Y_WIDTH] = RTLIL::Const(1);
							c->setPort(ID::A, w);
							c->setPort(ID::B, wr_bit);

							w = module->addWire(genid(mem.memid, "$wren", addr, "", j, "", wr_offset, "$y"));
							c->setPort(ID::Y, RTLIL::SigSpec(w));
						}

						RTLIL::Cell *c = module->addCell(genid(mem.memid, "$wrmux", addr, "", j, "", wr_offset), ID($mux));
						c->parameters[ID::WIDTH] = wr_width;
						c->setPort(ID::A, sig.extract(wr_offset, wr_width));
						c->setPort(ID::B, port.data.extract(wr_offset + sub * mem.width, wr_width));
						c->setPort(ID::S, RTLIL::SigSpec(w));

						w = module->addWire(genid(mem.memid, "$wrmux", addr, "", j, "", wr_offset, "$y"), wr_width);
						c->setPort(ID::Y, w);

						sig.replace(wr_offset, w);
						wr_offset += wr_width;
						count_wrmux++;
					}
				}

				module->connect(RTLIL::SigSig(data_reg_in[idx], sig));
			}
		}

		log("  write interface: %d write mux blocks.\n", count_wrmux);

		mem.remove();
	}

	void run()
	{
		for (auto &mem : Mem::get_selected_memories(module))
			handle_memory(mem);
	}
};

struct MemoryMapPass : public Pass {
	MemoryMapPass() : Pass("memory_map", "translate multiport memories to basic cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_map [options] [selection]\n");
		log("\n");
		log("This pass converts multiport memory cells as generated by the memory_collect\n");
		log("pass to word-wide DFFs and address decoders.\n");
		log("\n");
		log("    -attr !<name>\n");
		log("        do not map memories that have attribute <name> set.\n");
		log("\n");
		log("    -attr <name>[=<value>]\n");
		log("        for memories that have attribute <name> set, only map them if its value\n");
		log("        is a string <value> (if specified), or an integer 1 (otherwise). if this\n");
		log("        option is specified multiple times, map the memory if the attribute is\n");
		log("        to any of the values.\n");
		log("\n");
		log("    -iattr\n");
		log("        for -attr, suppress case sensitivity in matching of <value>.\n");
		log("\n");
		log("    -rom-only\n");
		log("        only perform conversion for ROMs (memories with no write ports).\n");
		log("\n");
		log("    -keepdc\n");
		log("        when mapping ROMs, keep x-bits shared across read ports.\n");
		log("\n");
		log("    -formal\n");
		log("        map memories for a global clock based formal verification flow.\n");
		log("        This implies -keepdc, uses $ff cells for ROMs and sets hdlname\n");
		log("        attributes. It also has limited support for async write ports\n");
		log("        as generated by clk2fflogic.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool attr_icase = false;
		bool rom_only = false;
		bool keepdc = false;
		bool formal = false;
		dict<RTLIL::IdString, std::vector<RTLIL::Const>> attributes;

		log_header(design, "Executing MEMORY_MAP pass (converting memories to logic and flip-flops).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-attr" && argidx + 1 < args.size())
			{
				std::string attr_arg = args[++argidx];
				std::string name;
				RTLIL::Const value;
				size_t eq_at = attr_arg.find('=');
				if (eq_at != std::string::npos) {
					name  = attr_arg.substr(0, eq_at);
					value = attr_arg.substr(eq_at + 1);
				} else {
					name  = attr_arg;
					value = RTLIL::Const(1);
				}
				if (attr_arg.size() > 1 && attr_arg[0] == '!') {
					if (value != RTLIL::Const(1)) {
						--argidx;
						break; // we don't support -attr !<name>=<value>
					}
					attributes[RTLIL::escape_id(name.substr(1))].clear();
				} else {
					attributes[RTLIL::escape_id(name)].push_back(value);
				}
				continue;
			}
			if (args[argidx] == "-iattr")
			{
				attr_icase = true;
				continue;
			}
			if (args[argidx] == "-rom-only")
			{
				rom_only = true;
				continue;
			}
			if (args[argidx] == "-keepdc")
			{
				keepdc = true;
				continue;
			}
			if (args[argidx] == "-formal")
			{
				formal = true;
				keepdc = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			if (mod->has_processes_warn())
				continue;

			MemoryMapWorker worker(design, mod);
			worker.attr_icase = attr_icase;
			worker.attributes = attributes;
			worker.rom_only = rom_only;
			worker.keepdc = keepdc;
			worker.formal = formal;
			worker.run();
		}
	}
} MemoryMapPass;

PRIVATE_NAMESPACE_END
