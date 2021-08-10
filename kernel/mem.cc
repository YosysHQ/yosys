/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Marcelina Kościelnicka <mwk@0x04.net>
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

#include "kernel/mem.h"
#include "kernel/ff.h"

USING_YOSYS_NAMESPACE

void Mem::remove() {
	if (cell) {
		module->remove(cell);
		cell = nullptr;
	}
	if (mem) {
		module->memories.erase(mem->name);
		delete mem;
		mem = nullptr;
	}
	for (auto &port : rd_ports) {
		if (port.cell) {
			module->remove(port.cell);
			port.cell = nullptr;
		}
	}
	for (auto &port : wr_ports) {
		if (port.cell) {
			module->remove(port.cell);
			port.cell = nullptr;
		}
	}
	for (auto &init : inits) {
		if (init.cell) {
			module->remove(init.cell);
			init.cell = nullptr;
		}
	}
}

void Mem::emit() {
	check();
	std::vector<int> rd_left;
	for (int i = 0; i < GetSize(rd_ports); i++) {
		auto &port = rd_ports[i];
		if (port.removed) {
			if (port.cell) {
				module->remove(port.cell);
			}
		} else {
			rd_left.push_back(i);
		}
	}
	std::vector<int> wr_left;
	for (int i = 0; i < GetSize(wr_ports); i++) {
		auto &port = wr_ports[i];
		if (port.removed) {
			if (port.cell) {
				module->remove(port.cell);
			}
		} else {
			wr_left.push_back(i);
		}
	}
	std::vector<int> init_left;
	for (int i = 0; i < GetSize(inits); i++) {
		auto &init = inits[i];
		if (init.removed) {
			if (init.cell) {
				module->remove(init.cell);
			}
		} else {
			init_left.push_back(i);
		}
	}
	for (int i = 0; i < GetSize(rd_left); i++)
		if (i != rd_left[i])
			std::swap(rd_ports[i], rd_ports[rd_left[i]]);
	rd_ports.resize(GetSize(rd_left));
	for (int i = 0; i < GetSize(wr_left); i++)
		if (i != wr_left[i])
			std::swap(wr_ports[i], wr_ports[wr_left[i]]);
	wr_ports.resize(GetSize(wr_left));
	for (int i = 0; i < GetSize(init_left); i++)
		if (i != init_left[i])
			std::swap(inits[i], inits[init_left[i]]);
	inits.resize(GetSize(init_left));

	for (auto &port : rd_ports) {
		for (int i = 0; i < GetSize(wr_left); i++) {
			port.transparency_mask[i] = port.transparency_mask[wr_left[i]];
			port.collision_x_mask[i] = port.collision_x_mask[wr_left[i]];
		}
		port.transparency_mask.resize(GetSize(wr_left));
		port.collision_x_mask.resize(GetSize(wr_left));
	}
	for (auto &port : wr_ports) {
		for (int i = 0; i < GetSize(wr_left); i++)
			port.priority_mask[i] = port.priority_mask[wr_left[i]];
		port.priority_mask.resize(GetSize(wr_left));
	}

	if (packed) {
		if (mem) {
			module->memories.erase(mem->name);
			delete mem;
			mem = nullptr;
		}
		if (!cell) {
			if (memid.empty())
				memid = NEW_ID;
			cell = module->addCell(memid, ID($mem));
		}
		cell->attributes = attributes;
		cell->parameters[ID::MEMID] = Const(memid.str());
		cell->parameters[ID::WIDTH] = Const(width);
		cell->parameters[ID::OFFSET] = Const(start_offset);
		cell->parameters[ID::SIZE] = Const(size);
		Const rd_wide_continuation, rd_clk_enable, rd_clk_polarity, rd_transparent;
		Const wr_wide_continuation, wr_clk_enable, wr_clk_polarity;
		SigSpec rd_clk, rd_en, rd_addr, rd_data;
		SigSpec wr_clk, wr_en, wr_addr, wr_data;
		int abits = 0;
		for (auto &port : rd_ports)
			abits = std::max(abits, GetSize(port.addr));
		for (auto &port : wr_ports)
			abits = std::max(abits, GetSize(port.addr));
		cell->parameters[ID::ABITS] = Const(abits);
		for (auto &port : rd_ports) {
			// TODO: remove
			log_assert(port.arst == State::S0);
			log_assert(port.srst == State::S0);
			log_assert(port.init_value == Const(State::Sx, width << port.wide_log2));
			bool transparent = false;
			bool non_transparent = false;
			if (port.clk_enable) {
				for (int i = 0; i < GetSize(wr_ports); i++) {
					auto &oport = wr_ports[i];
					if (oport.clk_enable && oport.clk == port.clk && oport.clk_polarity == port.clk_polarity) {
						if (port.transparency_mask[i])
							transparent = true;
						else if (!port.collision_x_mask[i])
							non_transparent = true;
					}
				}
				log_assert(!transparent || !non_transparent);
			}
			if (port.cell) {
				module->remove(port.cell);
				port.cell = nullptr;
			}
			for (int sub = 0; sub < (1 << port.wide_log2); sub++)
			{
				rd_wide_continuation.bits.push_back(State(sub != 0));
				rd_clk_enable.bits.push_back(State(port.clk_enable));
				rd_clk_polarity.bits.push_back(State(port.clk_polarity));
				rd_transparent.bits.push_back(State(transparent));
				rd_clk.append(port.clk);
				rd_en.append(port.en);
				SigSpec addr = port.sub_addr(sub);
				addr.extend_u0(abits, false);
				rd_addr.append(addr);
				log_assert(GetSize(addr) == abits);
			}
			rd_data.append(port.data);
		}
		if (rd_ports.empty()) {
			rd_wide_continuation = State::S0;
			rd_clk_enable = State::S0;
			rd_clk_polarity = State::S0;
			rd_transparent = State::S0;
		}
		cell->parameters[ID::RD_PORTS] = Const(GetSize(rd_clk));
		cell->parameters[ID::RD_CLK_ENABLE] = rd_clk_enable;
		cell->parameters[ID::RD_CLK_POLARITY] = rd_clk_polarity;
		cell->parameters[ID::RD_TRANSPARENT] = rd_transparent;
		cell->setPort(ID::RD_CLK, rd_clk);
		cell->setPort(ID::RD_EN, rd_en);
		cell->setPort(ID::RD_ADDR, rd_addr);
		cell->setPort(ID::RD_DATA, rd_data);
		for (auto &port : wr_ports) {
			if (port.cell) {
				module->remove(port.cell);
				port.cell = nullptr;
			}
			for (int sub = 0; sub < (1 << port.wide_log2); sub++)
			{
				wr_wide_continuation.bits.push_back(State(sub != 0));
				wr_clk_enable.bits.push_back(State(port.clk_enable));
				wr_clk_polarity.bits.push_back(State(port.clk_polarity));
				wr_clk.append(port.clk);
				SigSpec addr = port.sub_addr(sub);
				addr.extend_u0(abits, false);
				wr_addr.append(addr);
				log_assert(GetSize(addr) == abits);
			}
			wr_en.append(port.en);
			wr_data.append(port.data);
		}
		if (wr_ports.empty()) {
			wr_wide_continuation = State::S0;
			wr_clk_enable = State::S0;
			wr_clk_polarity = State::S0;
		}
		cell->parameters[ID::WR_PORTS] = Const(GetSize(wr_clk));
		cell->parameters[ID::WR_CLK_ENABLE] = wr_clk_enable;
		cell->parameters[ID::WR_CLK_POLARITY] = wr_clk_polarity;
		cell->setPort(ID::WR_CLK, wr_clk);
		cell->setPort(ID::WR_EN, wr_en);
		cell->setPort(ID::WR_ADDR, wr_addr);
		cell->setPort(ID::WR_DATA, wr_data);
		for (auto &init : inits) {
			if (init.cell) {
				module->remove(init.cell);
				init.cell = nullptr;
			}
		}
		cell->parameters[ID::INIT] = get_init_data();
	} else {
		if (cell) {
			module->remove(cell);
			cell = nullptr;
		}
		if (!mem) {
			if (memid.empty())
				memid = NEW_ID;
			mem = new RTLIL::Memory;
			mem->name = memid;
			module->memories[memid] = mem;
		}
		mem->width = width;
		mem->start_offset = start_offset;
		mem->size = size;
		mem->attributes = attributes;
		for (auto &port : rd_ports) {
			// TODO: remove
			log_assert(port.arst == State::S0);
			log_assert(port.srst == State::S0);
			log_assert(port.init_value == Const(State::Sx, width << port.wide_log2));
			bool transparent = false;
			bool non_transparent = false;
			if (port.clk_enable) {
				for (int i = 0; i < GetSize(wr_ports); i++) {
					auto &oport = wr_ports[i];
					if (oport.clk_enable && oport.clk == port.clk && oport.clk_polarity == port.clk_polarity) {
						if (port.transparency_mask[i])
							transparent = true;
						else if (!port.collision_x_mask[i])
							non_transparent = true;
					}
				}
				log_assert(!transparent || !non_transparent);
			}
			if (!port.cell)
				port.cell = module->addCell(NEW_ID, ID($memrd));
			port.cell->attributes = port.attributes;
			port.cell->parameters[ID::MEMID] = memid.str();
			port.cell->parameters[ID::ABITS] = GetSize(port.addr);
			port.cell->parameters[ID::WIDTH] = width << port.wide_log2;
			port.cell->parameters[ID::CLK_ENABLE] = port.clk_enable;
			port.cell->parameters[ID::CLK_POLARITY] = port.clk_polarity;
			port.cell->parameters[ID::TRANSPARENT] = transparent;
			port.cell->setPort(ID::CLK, port.clk);
			port.cell->setPort(ID::EN, port.en);
			port.cell->setPort(ID::ADDR, port.addr);
			port.cell->setPort(ID::DATA, port.data);
		}
		int idx = 0;
		for (auto &port : wr_ports) {
			if (!port.cell)
				port.cell = module->addCell(NEW_ID, ID($memwr));
			port.cell->attributes = port.attributes;
			port.cell->parameters[ID::MEMID] = memid.str();
			port.cell->parameters[ID::ABITS] = GetSize(port.addr);
			port.cell->parameters[ID::WIDTH] = width << port.wide_log2;
			port.cell->parameters[ID::CLK_ENABLE] = port.clk_enable;
			port.cell->parameters[ID::CLK_POLARITY] = port.clk_polarity;
			port.cell->parameters[ID::PRIORITY] = idx++;
			port.cell->setPort(ID::CLK, port.clk);
			port.cell->setPort(ID::EN, port.en);
			port.cell->setPort(ID::ADDR, port.addr);
			port.cell->setPort(ID::DATA, port.data);
		}
		idx = 0;
		for (auto &init : inits) {
			bool v2 = !init.en.is_fully_ones();
			if (!init.cell)
				init.cell = module->addCell(NEW_ID, v2 ? ID($meminit_v2) : ID($meminit));
			else
				init.cell->type = v2 ? ID($meminit_v2) : ID($meminit);
			init.cell->attributes = init.attributes;
			init.cell->parameters[ID::MEMID] = memid.str();
			init.cell->parameters[ID::ABITS] = GetSize(init.addr);
			init.cell->parameters[ID::WIDTH] = width;
			init.cell->parameters[ID::WORDS] = GetSize(init.data) / width;
			init.cell->parameters[ID::PRIORITY] = idx++;
			init.cell->setPort(ID::ADDR, init.addr);
			init.cell->setPort(ID::DATA, init.data);
			if (v2)
				init.cell->setPort(ID::EN, init.en);
			else
				init.cell->unsetPort(ID::EN);
		}
	}
}

void Mem::clear_inits() {
	for (auto &init : inits)
		init.removed = true;
}

void Mem::coalesce_inits() {
	// start address -> end address
	std::map<int, int> chunks;
	// Figure out chunk boundaries.
	for (auto &init : inits) {
		if (init.removed)
			continue;
		bool valid = false;
		for (auto bit : init.en)
			if (bit == State::S1)
				valid = true;
		if (!valid) {
			init.removed = true;
			continue;
		}
		int addr = init.addr.as_int();
		int addr_e = addr + GetSize(init.data) / width;
		auto it_e = chunks.upper_bound(addr_e);
		auto it = it_e;
		while (it != chunks.begin()) {
			--it;
			if (it->second < addr) {
				++it;
				break;
			}
		}
		if (it == it_e) {
			// No overlapping inits — add this one to index.
			chunks[addr] = addr_e;
		} else {
			// We have an overlap — all chunks in the [it, it_e)
			// range will be merged with this init.
			if (it->first < addr)
				addr = it->first;
			auto it_last = it_e;
			it_last--;
			if (it_last->second > addr_e)
				addr_e = it_last->second;
			chunks.erase(it, it_e);
			chunks[addr] = addr_e;
		}
	}
	// Group inits by the chunk they belong to.
	dict<int, std::vector<int>> inits_by_chunk;
	for (int i = 0; i < GetSize(inits); i++) {
		auto &init = inits[i];
		if (init.removed)
			continue;
		auto it = chunks.upper_bound(init.addr.as_int());
		--it;
		inits_by_chunk[it->first].push_back(i);
		int addr = init.addr.as_int();
		int addr_e = addr + GetSize(init.data) / width;
		log_assert(addr >= it->first && addr_e <= it->second);
	}
	// Process each chunk.
	for (auto &it : inits_by_chunk) {
		int caddr = it.first;
		int caddr_e = chunks[caddr];
		auto &chunk_inits = it.second;
		if (GetSize(chunk_inits) == 1) {
			auto &init = inits[chunk_inits[0]];
			if (!init.en.is_fully_ones()) {
				for (int i = 0; i < GetSize(init.data); i++)
					if (init.en[i % width] != State::S1)
						init.data[i] = State::Sx;
				init.en = Const(State::S1, width);
			}
			continue;
		}
		Const cdata(State::Sx, (caddr_e - caddr) * width);
		for (int idx : chunk_inits) {
			auto &init = inits[idx];
			int offset = (init.addr.as_int() - caddr) * width;
			log_assert(offset >= 0);
			log_assert(offset + GetSize(init.data) <= GetSize(cdata));
			for (int i = 0; i < GetSize(init.data); i++)
				if (init.en[i % width] == State::S1)
					cdata.bits[i+offset] = init.data.bits[i];
			init.removed = true;
		}
		MemInit new_init;
		new_init.addr = caddr;
		new_init.data = cdata;
		new_init.en = Const(State::S1, width);
		inits.push_back(new_init);
	}
}

Const Mem::get_init_data() const {
	Const init_data(State::Sx, width * size);
	for (auto &init : inits) {
		if (init.removed)
			continue;
		int offset = (init.addr.as_int() - start_offset) * width;
		for (int i = 0; i < GetSize(init.data); i++)
			if (0 <= i+offset && i+offset < GetSize(init_data) && init.en[i % width] == State::S1)
				init_data.bits[i+offset] = init.data.bits[i];
	}
	return init_data;
}

void Mem::check() {
	int max_wide_log2 = 0;
	for (auto &port : rd_ports) {
		if (port.removed)
			continue;
		log_assert(GetSize(port.clk) == 1);
		log_assert(GetSize(port.en) == 1);
		log_assert(GetSize(port.arst) == 1);
		log_assert(GetSize(port.srst) == 1);
		log_assert(GetSize(port.data) == (width << port.wide_log2));
		log_assert(GetSize(port.init_value) == (width << port.wide_log2));
		log_assert(GetSize(port.arst_value) == (width << port.wide_log2));
		log_assert(GetSize(port.srst_value) == (width << port.wide_log2));
		if (!port.clk_enable) {
			log_assert(port.en == State::S1);
			log_assert(port.arst == State::S0);
			log_assert(port.srst == State::S0);
		}
		for (int j = 0; j < port.wide_log2; j++) {
			log_assert(port.addr[j] == State::S0);
		}
		max_wide_log2 = std::max(max_wide_log2, port.wide_log2);
		log_assert(GetSize(port.transparency_mask) == GetSize(wr_ports));
		log_assert(GetSize(port.collision_x_mask) == GetSize(wr_ports));
		for (int j = 0; j < GetSize(wr_ports); j++) {
			auto &wport = wr_ports[j];
			if ((port.transparency_mask[j] || port.collision_x_mask[j]) && !wport.removed) {
				log_assert(port.clk_enable);
				log_assert(wport.clk_enable);
				log_assert(port.clk == wport.clk);
				log_assert(port.clk_polarity == wport.clk_polarity);
			}
			log_assert(!port.transparency_mask[j] || !port.collision_x_mask[j]);
		}
	}
	for (int i = 0; i < GetSize(wr_ports); i++) {
		auto &port = wr_ports[i];
		if (port.removed)
			continue;
		log_assert(GetSize(port.clk) == 1);
		log_assert(GetSize(port.en) == (width << port.wide_log2));
		log_assert(GetSize(port.data) == (width << port.wide_log2));
		for (int j = 0; j < port.wide_log2; j++) {
			log_assert(port.addr[j] == State::S0);
		}
		max_wide_log2 = std::max(max_wide_log2, port.wide_log2);
		log_assert(GetSize(port.priority_mask) == GetSize(wr_ports));
		for (int j = 0; j < GetSize(wr_ports); j++) {
			auto &wport = wr_ports[j];
			if (port.priority_mask[j] && !wport.removed) {
				log_assert(j < i);
				log_assert(port.clk_enable == wport.clk_enable);
				if (port.clk_enable) {
					log_assert(port.clk == wport.clk);
					log_assert(port.clk_polarity == wport.clk_polarity);
				}
			}
		}
	}
	int mask = (1 << max_wide_log2) - 1;
	log_assert(!(start_offset & mask));
	log_assert(!(size & mask));
}

namespace {

	struct MemIndex {
		dict<IdString, pool<Cell *>> rd_ports;
		dict<IdString, pool<Cell *>> wr_ports;
		dict<IdString, pool<Cell *>> inits;
		MemIndex (Module *module) {
			for (auto cell: module->cells()) {
				if (cell->type == ID($memwr))
					wr_ports[cell->parameters.at(ID::MEMID).decode_string()].insert(cell);
				else if (cell->type == ID($memrd))
					rd_ports[cell->parameters.at(ID::MEMID).decode_string()].insert(cell);
				else if (cell->type.in(ID($meminit), ID($meminit_v2)))
					inits[cell->parameters.at(ID::MEMID).decode_string()].insert(cell);
			}
		}
	};

	Mem mem_from_memory(Module *module, RTLIL::Memory *mem, const MemIndex &index) {
		Mem res(module, mem->name, mem->width, mem->start_offset, mem->size);
		res.packed = false;
		res.mem = mem;
		res.attributes = mem->attributes;
		std::vector<bool> rd_transparent;
		if (index.rd_ports.count(mem->name)) {
			for (auto cell : index.rd_ports.at(mem->name)) {
				MemRd mrd;
				mrd.cell = cell;
				mrd.attributes = cell->attributes;
				mrd.clk_enable = cell->parameters.at(ID::CLK_ENABLE).as_bool();
				mrd.clk_polarity = cell->parameters.at(ID::CLK_POLARITY).as_bool();
				bool transparent = cell->parameters.at(ID::TRANSPARENT).as_bool();
				mrd.clk = cell->getPort(ID::CLK);
				mrd.en = cell->getPort(ID::EN);
				mrd.addr = cell->getPort(ID::ADDR);
				mrd.data = cell->getPort(ID::DATA);
				mrd.wide_log2 = ceil_log2(GetSize(mrd.data) / mem->width);
				mrd.ce_over_srst = false;
				mrd.arst_value = Const(State::Sx, mem->width << mrd.wide_log2);
				mrd.srst_value = Const(State::Sx, mem->width << mrd.wide_log2);
				mrd.init_value = Const(State::Sx, mem->width << mrd.wide_log2);
				mrd.srst = State::S0;
				mrd.arst = State::S0;
				if (!mrd.clk_enable) {
					// Fix some patterns that we'll allow for backwards compatibility,
					// but don't want to see moving forwards: async transparent
					// ports (inherently meaningless) and async ports without
					// const 1 tied to EN bit (which may mean a latch in the future).
					transparent = false;
					if (mrd.en == State::Sx)
						mrd.en = State::S1;
				}
				res.rd_ports.push_back(mrd);
				rd_transparent.push_back(transparent);
			}
		}
		if (index.wr_ports.count(mem->name)) {
			std::vector<std::pair<int, MemWr>> ports;
			for (auto cell : index.wr_ports.at(mem->name)) {
				MemWr mwr;
				mwr.cell = cell;
				mwr.attributes = cell->attributes;
				mwr.clk_enable = cell->parameters.at(ID::CLK_ENABLE).as_bool();
				mwr.clk_polarity = cell->parameters.at(ID::CLK_POLARITY).as_bool();
				mwr.clk = cell->getPort(ID::CLK);
				mwr.en = cell->getPort(ID::EN);
				mwr.addr = cell->getPort(ID::ADDR);
				mwr.data = cell->getPort(ID::DATA);
				mwr.wide_log2 = ceil_log2(GetSize(mwr.data) / mem->width);
				ports.push_back(std::make_pair(cell->parameters.at(ID::PRIORITY).as_int(), mwr));
			}
			std::sort(ports.begin(), ports.end(), [](const std::pair<int, MemWr> &a, const std::pair<int, MemWr> &b) { return a.first < b.first; });
			for (auto &it : ports)
				res.wr_ports.push_back(it.second);
		}
		if (index.inits.count(mem->name)) {
			std::vector<std::pair<int, MemInit>> inits;
			for (auto cell : index.inits.at(mem->name)) {
				MemInit init;
				init.cell = cell;
				init.attributes = cell->attributes;
				auto addr = cell->getPort(ID::ADDR);
				auto data = cell->getPort(ID::DATA);
				if (!addr.is_fully_const())
					log_error("Non-constant address %s in memory initialization %s.\n", log_signal(addr), log_id(cell));
				if (!data.is_fully_const())
					log_error("Non-constant data %s in memory initialization %s.\n", log_signal(data), log_id(cell));
				init.addr = addr.as_const();
				init.data = data.as_const();
				if (cell->type == ID($meminit_v2)) {
					auto en = cell->getPort(ID::EN);
					if (!en.is_fully_const())
						log_error("Non-constant enable %s in memory initialization %s.\n", log_signal(en), log_id(cell));
					init.en = en.as_const();
				} else {
					init.en = RTLIL::Const(State::S1, mem->width);
				}
				inits.push_back(std::make_pair(cell->parameters.at(ID::PRIORITY).as_int(), init));
			}
			std::sort(inits.begin(), inits.end(), [](const std::pair<int, MemInit> &a, const std::pair<int, MemInit> &b) { return a.first < b.first; });
			for (auto &it : inits)
				res.inits.push_back(it.second);
		}
		for (int i = 0; i < GetSize(res.wr_ports); i++) {
			auto &port = res.wr_ports[i];
			port.priority_mask.resize(GetSize(res.wr_ports));
			for (int j = 0; j < i; j++) {
				auto &oport = res.wr_ports[j];
				if (port.clk_enable != oport.clk_enable)
					continue;
				if (port.clk_enable && port.clk != oport.clk)
					continue;
				if (port.clk_enable && port.clk_polarity != oport.clk_polarity)
					continue;
				port.priority_mask[j] = true;
			}
		}
		for (int i = 0; i < GetSize(res.rd_ports); i++) {
			auto &port = res.rd_ports[i];
			port.transparency_mask.resize(GetSize(res.wr_ports));
			port.collision_x_mask.resize(GetSize(res.wr_ports));
			if (!rd_transparent[i])
				continue;
			if (!port.clk_enable)
				continue;
			for (int j = 0; j < GetSize(res.wr_ports); j++) {
				auto &wport = res.wr_ports[j];
				if (!wport.clk_enable)
					continue;
				if (port.clk != wport.clk)
					continue;
				if (port.clk_polarity != wport.clk_polarity)
					continue;
				port.transparency_mask[j] = true;
			}
		}
		res.check();
		return res;
	}

	Mem mem_from_cell(Cell *cell) {
		Mem res(cell->module, cell->parameters.at(ID::MEMID).decode_string(),
			cell->parameters.at(ID::WIDTH).as_int(),
			cell->parameters.at(ID::OFFSET).as_int(),
			cell->parameters.at(ID::SIZE).as_int()
		);
		int abits = cell->parameters.at(ID::ABITS).as_int();
		res.packed = true;
		res.cell = cell;
		res.attributes = cell->attributes;
		Const &init = cell->parameters.at(ID::INIT);
		if (!init.is_fully_undef()) {
			int pos = 0;
			while (pos < res.size) {
				Const word = init.extract(pos * res.width, res.width, State::Sx);
				if (word.is_fully_undef()) {
					pos++;
				} else {
					int epos;
					for (epos = pos; epos < res.size; epos++) {
						Const eword = init.extract(epos * res.width, res.width, State::Sx);
						if (eword.is_fully_undef())
							break;
					}
					MemInit minit;
					minit.addr = res.start_offset + pos;
					minit.data = init.extract(pos * res.width, (epos - pos) * res.width, State::Sx);
					minit.en = RTLIL::Const(State::S1, res.width);
					res.inits.push_back(minit);
					pos = epos;
				}
			}
		}
		for (int i = 0; i < cell->parameters.at(ID::RD_PORTS).as_int(); i++) {
			MemRd mrd;
			mrd.wide_log2 = 0;
			mrd.clk_enable = cell->parameters.at(ID::RD_CLK_ENABLE).extract(i, 1).as_bool();
			mrd.clk_polarity = cell->parameters.at(ID::RD_CLK_POLARITY).extract(i, 1).as_bool();
			mrd.clk = cell->getPort(ID::RD_CLK).extract(i, 1);
			mrd.en = cell->getPort(ID::RD_EN).extract(i, 1);
			mrd.addr = cell->getPort(ID::RD_ADDR).extract(i * abits, abits);
			mrd.data = cell->getPort(ID::RD_DATA).extract(i * res.width, res.width);
			mrd.ce_over_srst = false;
			mrd.arst_value = Const(State::Sx, res.width << mrd.wide_log2);
			mrd.srst_value = Const(State::Sx, res.width << mrd.wide_log2);
			mrd.init_value = Const(State::Sx, res.width << mrd.wide_log2);
			mrd.srst = State::S0;
			mrd.arst = State::S0;
			res.rd_ports.push_back(mrd);
		}
		for (int i = 0; i < cell->parameters.at(ID::WR_PORTS).as_int(); i++) {
			MemWr mwr;
			mwr.wide_log2 = 0;
			mwr.clk_enable = cell->parameters.at(ID::WR_CLK_ENABLE).extract(i, 1).as_bool();
			mwr.clk_polarity = cell->parameters.at(ID::WR_CLK_POLARITY).extract(i, 1).as_bool();
			mwr.clk = cell->getPort(ID::WR_CLK).extract(i, 1);
			mwr.en = cell->getPort(ID::WR_EN).extract(i * res.width, res.width);
			mwr.addr = cell->getPort(ID::WR_ADDR).extract(i * abits, abits);
			mwr.data = cell->getPort(ID::WR_DATA).extract(i * res.width, res.width);
			res.wr_ports.push_back(mwr);
		}
		for (int i = 0; i < GetSize(res.wr_ports); i++) {
			auto &port = res.wr_ports[i];
			port.priority_mask.resize(GetSize(res.wr_ports));
			for (int j = 0; j < i; j++) {
				auto &oport = res.wr_ports[j];
				if (port.clk_enable != oport.clk_enable)
					continue;
				if (port.clk_enable && port.clk != oport.clk)
					continue;
				if (port.clk_enable && port.clk_polarity != oport.clk_polarity)
					continue;
				port.priority_mask[j] = true;
			}
		}
		for (int i = 0; i < GetSize(res.rd_ports); i++) {
			auto &port = res.rd_ports[i];
			port.transparency_mask.resize(GetSize(res.wr_ports));
			port.collision_x_mask.resize(GetSize(res.wr_ports));
			if (!cell->parameters.at(ID::RD_TRANSPARENT).extract(i, 1).as_bool())
				continue;
			if (!port.clk_enable)
				continue;
			for (int j = 0; j < GetSize(res.wr_ports); j++) {
				auto &wport = res.wr_ports[j];
				if (!wport.clk_enable)
					continue;
				if (port.clk != wport.clk)
					continue;
				if (port.clk_polarity != wport.clk_polarity)
					continue;
				port.transparency_mask[j] = true;
			}
		}
		res.check();
		return res;
	}

}

std::vector<Mem> Mem::get_all_memories(Module *module) {
	std::vector<Mem> res;
	MemIndex index(module);
	for (auto it: module->memories) {
		res.push_back(mem_from_memory(module, it.second, index));
	}
	for (auto cell: module->cells()) {
		if (cell->type == ID($mem))
			res.push_back(mem_from_cell(cell));
	}
	return res;
}

std::vector<Mem> Mem::get_selected_memories(Module *module) {
	std::vector<Mem> res;
	MemIndex index(module);
	for (auto it: module->memories) {
		if (module->design->selected(module, it.second))
			res.push_back(mem_from_memory(module, it.second, index));
	}
	for (auto cell: module->selected_cells()) {
		if (cell->type == ID($mem))
			res.push_back(mem_from_cell(cell));
	}
	return res;
}

Cell *Mem::extract_rdff(int idx, FfInitVals *initvals) {
	MemRd &port = rd_ports[idx];

	if (!port.clk_enable)
		return nullptr;

	Cell *c;

	// There are two ways to handle rdff extraction when transparency is involved:
	//
	// - if all of the following conditions are true, put the FF on address input:
	//
	//   - the port has no clock enable, no reset, and no initial value
	//   - the port is transparent wrt all write ports (implying they also share
	//     the clock domain)
	//
	// - otherwise, put the FF on the data output, and make bypass paths for
	//   all write ports wrt which this port is transparent
	bool trans_use_addr = true;
	for (int i = 0; i < GetSize(wr_ports); i++)
		if (!port.transparency_mask[i] && !wr_ports[i].removed)
			trans_use_addr = false;

	// If there are no write ports at all, we could possibly use either way; do data
	// FF in this case.
	if (GetSize(wr_ports) == 0)
		trans_use_addr = false;

	if (port.en != State::S1 || port.srst != State::S0 || port.arst != State::S0 || !port.init_value.is_fully_undef())
		trans_use_addr = false;

	if (trans_use_addr)
	{
		// Do not put a register in front of constant address bits — this is both
		// unnecessary and will break wide ports.
		int width = 0;
		for (int i = 0; i < GetSize(port.addr); i++)
			if (port.addr[i].wire)
				width++;

		if (width)
		{
			SigSpec sig_q = module->addWire(stringf("$%s$rdreg[%d]$q", memid.c_str(), idx), width);
			SigSpec sig_d;

			int pos = 0;
			for (int i = 0; i < GetSize(port.addr); i++)
				if (port.addr[i].wire) {
					sig_d.append(port.addr[i]);
					port.addr[i] = sig_q[pos++];
				}

			c = module->addDff(stringf("$%s$rdreg[%d]", memid.c_str(), idx), port.clk, sig_d, sig_q, port.clk_polarity);
		} else {
			c = nullptr;
		}
	}
	else
	{
		log_assert(port.arst == State::S0 || port.srst == State::S0);

		SigSpec async_d = module->addWire(stringf("$%s$rdreg[%d]$d", memid.c_str(), idx), GetSize(port.data));
		SigSpec sig_d = async_d;

		for (int i = 0; i < GetSize(wr_ports); i++) {
			auto &wport = wr_ports[i];
			if (wport.removed)
				continue;
			if (port.transparency_mask[i] || port.collision_x_mask[i]) {
				log_assert(wport.clk_enable);
				log_assert(wport.clk == port.clk);
				log_assert(wport.clk_enable == port.clk_enable);
				int min_wide_log2 = std::min(port.wide_log2, wport.wide_log2);
				int max_wide_log2 = std::max(port.wide_log2, wport.wide_log2);
				bool wide_write = wport.wide_log2 > port.wide_log2;
				for (int sub = 0; sub < (1 << max_wide_log2); sub += (1 << min_wide_log2)) {
					SigSpec raddr = port.addr;
					SigSpec waddr = wport.addr;
					if (wide_write)
						waddr = wport.sub_addr(sub);
					else
						raddr = port.sub_addr(sub);
					SigSpec addr_eq;
					if (raddr != waddr)
						addr_eq = module->Eq(stringf("$%s$rdtransen[%d][%d][%d]$d", memid.c_str(), idx, i, sub), raddr, waddr);
					int pos = 0;
					int ewidth = width << min_wide_log2;
					int wsub = wide_write ? sub : 0;
					int rsub = wide_write ? 0 : sub;
					while (pos < ewidth) {
						int epos = pos;
						while (epos < ewidth && wport.en[epos + wsub * width] == wport.en[pos + wsub * width])
							epos++;
						SigSpec cur = sig_d.extract(pos + rsub * width, epos-pos);
						SigSpec other = port.transparency_mask[i] ? wport.data.extract(pos + wsub * width, epos-pos) : Const(State::Sx, epos-pos);
						SigSpec cond;
						if (raddr != waddr)
							cond = module->And(stringf("$%s$rdtransgate[%d][%d][%d][%d]$d", memid.c_str(), idx, i, sub, pos), wport.en[pos + wsub * width], addr_eq);
						else
							cond = wport.en[pos + wsub * width];
						SigSpec merged = module->Mux(stringf("$%s$rdtransmux[%d][%d][%d][%d]$d", memid.c_str(), idx, i, sub, pos), cur, other, cond);
						sig_d.replace(pos + rsub * width, merged);
						pos = epos;
					}
				}
			}
		}

		IdString name = stringf("$%s$rdreg[%d]", memid.c_str(), idx);
		FfData ff(initvals);
		ff.width = GetSize(port.data);
		ff.has_clk = true;
		ff.sig_clk = port.clk;
		ff.pol_clk = port.clk_polarity;
		if (port.en != State::S1) {
			ff.has_en = true;
			ff.pol_en = true;
			ff.sig_en = port.en;
		}
		if (port.arst != State::S0) {
			ff.has_arst = true;
			ff.pol_arst = true;
			ff.sig_arst = port.arst;
			ff.val_arst = port.arst_value;
		}
		if (port.srst != State::S0) {
			ff.has_srst = true;
			ff.pol_srst = true;
			ff.sig_srst = port.srst;
			ff.val_srst = port.srst_value;
			ff.ce_over_srst = ff.has_en && port.ce_over_srst;
		}
		ff.sig_d = sig_d;
		ff.sig_q = port.data;
		ff.val_init = port.init_value;
		port.data = async_d;
		c = ff.emit(module, name);
	}

	log("Extracted %s FF from read port %d of %s.%s: %s\n", trans_use_addr ? "addr" : "data",
			idx, log_id(module), log_id(memid), log_id(c));

	port.en = State::S1;
	port.clk = State::S0;
	port.arst = State::S0;
	port.srst = State::S0;
	port.clk_enable = false;
	port.clk_polarity = true;
	port.ce_over_srst = false;
	port.arst_value = Const(State::Sx, GetSize(port.data));
	port.srst_value = Const(State::Sx, GetSize(port.data));
	port.init_value = Const(State::Sx, GetSize(port.data));

	for (int i = 0; i < GetSize(wr_ports); i++) {
		port.transparency_mask[i] = false;
		port.collision_x_mask[i] = false;
	}

	return c;
}

void Mem::narrow() {
	// NOTE: several passes depend on this function not modifying
	// the design at all until (and unless) emit() is called.
	// Be careful to preserve this.
	std::vector<MemRd> new_rd_ports;
	std::vector<MemWr> new_wr_ports;
	std::vector<std::pair<int, int>> new_rd_map;
	std::vector<std::pair<int, int>> new_wr_map;
	for (int i = 0; i < GetSize(rd_ports); i++) {
		auto &port = rd_ports[i];
		for (int sub = 0; sub < (1 << port.wide_log2); sub++) {
			new_rd_map.push_back(std::make_pair(i, sub));
		}
	}
	for (int i = 0; i < GetSize(wr_ports); i++) {
		auto &port = wr_ports[i];
		for (int sub = 0; sub < (1 << port.wide_log2); sub++) {
			new_wr_map.push_back(std::make_pair(i, sub));
		}
	}
	for (auto &it : new_rd_map) {
		MemRd &orig = rd_ports[it.first];
		MemRd port = orig;
		if (it.second != 0)
			port.cell = nullptr;
		if (port.wide_log2) {
			port.data = port.data.extract(it.second * width, width);
			port.init_value = port.init_value.extract(it.second * width, width);
			port.arst_value = port.arst_value.extract(it.second * width, width);
			port.srst_value = port.srst_value.extract(it.second * width, width);
			port.addr = port.sub_addr(it.second);
			port.wide_log2 = 0;
		}
		port.transparency_mask.clear();
		port.collision_x_mask.clear();
		for (auto &it2 : new_wr_map)
			port.transparency_mask.push_back(orig.transparency_mask[it2.first]);
		for (auto &it2 : new_wr_map)
			port.collision_x_mask.push_back(orig.collision_x_mask[it2.first]);
		new_rd_ports.push_back(port);
	}
	for (auto &it : new_wr_map) {
		MemWr &orig = wr_ports[it.first];
		MemWr port = orig;
		if (it.second != 0)
			port.cell = nullptr;
		if (port.wide_log2) {
			port.data = port.data.extract(it.second * width, width);
			port.en = port.en.extract(it.second * width, width);
			port.addr = port.sub_addr(it.second);
			port.wide_log2 = 0;
		}
		port.priority_mask.clear();
		for (auto &it2 : new_wr_map)
			port.priority_mask.push_back(orig.priority_mask[it2.first]);
		new_wr_ports.push_back(port);
	}
	std::swap(rd_ports, new_rd_ports);
	std::swap(wr_ports, new_wr_ports);
}

void Mem::emulate_priority(int idx1, int idx2, FfInitVals *initvals)
{
	auto &port1 = wr_ports[idx1];
	auto &port2 = wr_ports[idx2];
	if (!port2.priority_mask[idx1])
		return;
	for (int i = 0; i < GetSize(rd_ports); i++) {
		auto &rport = rd_ports[i];
		if (rport.removed)
			continue;
		if (rport.transparency_mask[idx1] && !(rport.transparency_mask[idx2] || rport.collision_x_mask[idx2]))
			emulate_transparency(idx1, i, initvals);
	}
	int min_wide_log2 = std::min(port1.wide_log2, port2.wide_log2);
	int max_wide_log2 = std::max(port1.wide_log2, port2.wide_log2);
	bool wide1 = port1.wide_log2 > port2.wide_log2;
	for (int sub = 0; sub < (1 << max_wide_log2); sub += (1 << min_wide_log2)) {
		SigSpec addr1 = port1.addr;
		SigSpec addr2 = port2.addr;
		if (wide1)
			addr1 = port1.sub_addr(sub);
		else
			addr2 = port2.sub_addr(sub);
		SigSpec addr_eq = module->Eq(NEW_ID, addr1, addr2);
		int ewidth = width << min_wide_log2;
		int sub1 = wide1 ? sub : 0;
		int sub2 = wide1 ? 0 : sub;
		dict<std::pair<SigBit, SigBit>, SigBit> cache;
		for (int pos = 0; pos < ewidth; pos++) {
			SigBit &en1 = port1.en[pos + sub1 * width];
			SigBit &en2 = port2.en[pos + sub2 * width];
			std::pair<SigBit, SigBit> key(en1, en2);
			if (cache.count(key)) {
				en1 = cache[key];
			} else {
				SigBit active2 = module->And(NEW_ID, addr_eq, en2);
				SigBit nactive2 = module->Not(NEW_ID, active2);
				en1 = cache[key] = module->And(NEW_ID, en1, nactive2);
			}
		}
	}
	port2.priority_mask[idx1] = false;
}

void Mem::emulate_transparency(int widx, int ridx, FfInitVals *initvals) {
	auto &wport = wr_ports[widx];
	auto &rport = rd_ports[ridx];
	log_assert(rport.transparency_mask[widx]);
	// If other write ports have priority over this one, emulate their transparency too.
	for (int i = GetSize(wr_ports) - 1; i > widx; i--) {
		if (wr_ports[i].removed)
			continue;
		if (rport.transparency_mask[i] && wr_ports[i].priority_mask[widx])
			emulate_transparency(i, ridx, initvals);
	}
	int min_wide_log2 = std::min(rport.wide_log2, wport.wide_log2);
	int max_wide_log2 = std::max(rport.wide_log2, wport.wide_log2);
	bool wide_write = wport.wide_log2 > rport.wide_log2;
	// The write data FF doesn't need full reset/init behavior, as it'll be masked by
	// the mux whenever this would be relevant.  It does, however, need to have the same
	// clock enable signal as the read port.
	SigSpec wdata_q = module->addWire(NEW_ID, GetSize(wport.data));
	module->addDffe(NEW_ID, rport.clk, rport.en, wport.data, wdata_q, rport.clk_polarity, true);
	for (int sub = 0; sub < (1 << max_wide_log2); sub += (1 << min_wide_log2)) {
		SigSpec raddr = rport.addr;
		SigSpec waddr = wport.addr;
		for (int j = min_wide_log2; j < max_wide_log2; j++)
			if (wide_write)
				waddr = wport.sub_addr(sub);
			else
				raddr = rport.sub_addr(sub);
		SigSpec addr_eq;
		if (raddr != waddr)
			addr_eq = module->Eq(NEW_ID, raddr, waddr);
		int pos = 0;
		int ewidth = width << min_wide_log2;
		int wsub = wide_write ? sub : 0;
		int rsub = wide_write ? 0 : sub;
		SigSpec rdata_a = module->addWire(NEW_ID, ewidth);
		while (pos < ewidth) {
			int epos = pos;
			while (epos < ewidth && wport.en[epos + wsub * width] == wport.en[pos + wsub * width])
				epos++;
			SigSpec cond;
			if (raddr != waddr)
				cond = module->And(NEW_ID, wport.en[pos + wsub * width], addr_eq);
			else
				cond = wport.en[pos + wsub * width];
			SigSpec cond_q = module->addWire(NEW_ID);
			// The FF for storing the bypass enable signal must be carefully
			// constructed to preserve the overall init/reset/enable behavior
			// of the whole port.
			FfData ff(initvals);
			ff.width = 1;
			ff.sig_q = cond_q;
			ff.has_d = true;
			ff.sig_d = cond;
			ff.has_clk = true;
			ff.sig_clk = rport.clk;
			ff.pol_clk = rport.clk_polarity;
			if (rport.en != State::S1) {
				ff.has_en = true;
				ff.sig_en = rport.en;
				ff.pol_en = true;
			}
			if (rport.arst != State::S0) {
				ff.has_arst = true;
				ff.sig_arst = rport.arst;
				ff.pol_arst = true;
				ff.val_arst = State::S0;
			}
			if (rport.srst != State::S0) {
				ff.has_srst = true;
				ff.sig_srst = rport.srst;
				ff.pol_srst = true;
				ff.val_srst = State::S0;
				ff.ce_over_srst = rport.ce_over_srst;
			}
			if (!rport.init_value.is_fully_undef())
				ff.val_init = State::S0;
			else
				ff.val_init = State::Sx;
			ff.emit(module, NEW_ID);
			// And the final bypass mux.
			SigSpec cur = rdata_a.extract(pos, epos-pos);
			SigSpec other = wdata_q.extract(pos + wsub * width, epos-pos);
			SigSpec dest = rport.data.extract(pos + rsub * width, epos-pos);
			module->addMux(NEW_ID, cur, other, cond_q, dest);
			pos = epos;
		}
		rport.data.replace(rsub * width, rdata_a);
	}
	rport.transparency_mask[widx] = false;
	rport.collision_x_mask[widx] = true;
}

void Mem::prepare_wr_merge(int idx1, int idx2, FfInitVals *initvals) {
	log_assert(idx1 < idx2);
	auto &port1 = wr_ports[idx1];
	auto &port2 = wr_ports[idx2];
	// If port 2 has priority over a port before port 1, make port 1 have priority too.
	for (int i = 0; i < idx1; i++)
		if (port2.priority_mask[i])
			port1.priority_mask[i] = true;
	// If port 2 has priority over a port after port 1, emulate it.
	for (int i = idx1 + 1; i < idx2; i++)
		if (port2.priority_mask[i] && !wr_ports[i].removed)
			emulate_priority(i, idx2, initvals);
	// If some port had priority over port 2, make it have priority over the merged port too.
	for (int i = idx2 + 1; i < GetSize(wr_ports); i++) {
		auto &oport = wr_ports[i];
		if (oport.priority_mask[idx2])
			oport.priority_mask[idx1] = true;
	}
	// Make sure all read ports have identical collision/transparency behavior wrt both
	// ports.
	for (int i = 0; i < GetSize(rd_ports); i++) {
		auto &rport = rd_ports[i];
		if (rport.removed)
			continue;
		// If collision already undefined with both ports, it's fine.
		if (rport.collision_x_mask[idx1] && rport.collision_x_mask[idx2])
			continue;
		// If one port has undefined collision, change it to the behavior
		// of the other port.
		if (rport.collision_x_mask[idx1]) {
			rport.collision_x_mask[idx1] = false;
			rport.transparency_mask[idx1] = rport.transparency_mask[idx2];
			continue;
		}
		if (rport.collision_x_mask[idx2]) {
			rport.collision_x_mask[idx2] = false;
			rport.transparency_mask[idx2] = rport.transparency_mask[idx1];
			continue;
		}
		// If transparent with both ports, also fine.
		if (rport.transparency_mask[idx1] && rport.transparency_mask[idx2])
			continue;
		// If transparent with only one, emulate it, and remove the collision-X
		// flag that emulate_transparency will set (to align with the other port).
		if (rport.transparency_mask[idx1]) {
			emulate_transparency(i, idx1, initvals);
			rport.collision_x_mask[idx1] = false;
			continue;
		}
		if (rport.transparency_mask[idx2]) {
			emulate_transparency(i, idx2, initvals);
			rport.collision_x_mask[idx2] = false;
			continue;
		}
		// If we got here, it's transparent with neither port, which is fine.
	}
}

void Mem::prepare_rd_merge(int idx1, int idx2, FfInitVals *initvals) {
	auto &port1 = rd_ports[idx1];
	auto &port2 = rd_ports[idx2];
	// Note that going through write ports in order is important, since
	// emulating transparency of a write port can change transparency
	// mask for higher-numbered ports (due to transitive transparency
	// emulation needed because of write port priority).
	for (int i = 0; i < GetSize(wr_ports); i++) {
		if (wr_ports[i].removed)
			continue;
		// Both ports undefined, OK.
		if (port1.collision_x_mask[i] && port2.collision_x_mask[i])
			continue;
		// Only one port undefined — change its behavior
		// to align with the other port.
		if (port1.collision_x_mask[i]) {
			port1.collision_x_mask[i] = false;
			port1.transparency_mask[i] = port2.transparency_mask[i];
			continue;
		}
		if (port2.collision_x_mask[i]) {
			port2.collision_x_mask[i] = false;
			port2.transparency_mask[i] = port1.transparency_mask[i];
			continue;
		}
		// Both ports transparent, OK.
		if (port1.transparency_mask[i] && port2.transparency_mask[i])
			continue;
		// Only one port transparent — emulate transparency
		// on the other.
		if (port1.transparency_mask[i]) {
			emulate_transparency(i, idx1, initvals);
			port1.collision_x_mask[i] = false;
			continue;
		}
		if (port2.transparency_mask[i]) {
			emulate_transparency(i, idx2, initvals);
			port2.collision_x_mask[i] = false;
			continue;
		}
		// No ports transparent, OK.
	}

}

void Mem::widen_prep(int wide_log2) {
	// Make sure start_offset and size are aligned to the port width,
	// adjust if necessary.
	int mask = ((1 << wide_log2) - 1);
	int delta = start_offset & mask;
	start_offset -= delta;
	size += delta;
	if (size & mask) {
		size |= mask;
		size++;
	}
}

void Mem::widen_wr_port(int idx, int wide_log2) {
	widen_prep(wide_log2);
	auto &port = wr_ports[idx];
	log_assert(port.wide_log2 <= wide_log2);
	if (port.wide_log2 < wide_log2) {
		SigSpec new_data, new_en;
		SigSpec addr_lo = port.addr.extract(0, wide_log2);
		for (int sub = 0; sub < (1 << wide_log2); sub += (1 << port.wide_log2))
		{
			Const cur_addr_lo(sub, wide_log2);
			if (addr_lo == cur_addr_lo) {
				// Always writes to this subword.
				new_data.append(port.data);
				new_en.append(port.en);
			} else if (addr_lo.is_fully_const()) {
				// Never writes to this subword.
				new_data.append(Const(State::Sx, GetSize(port.data)));
				new_en.append(Const(State::S0, GetSize(port.data)));
			} else {
				// May or may not write to this subword.
				new_data.append(port.data);
				SigSpec addr_eq = module->Eq(NEW_ID, addr_lo, cur_addr_lo);
				SigSpec en = module->Mux(NEW_ID, Const(State::S0, GetSize(port.data)), port.en, addr_eq);
				new_en.append(en);
			}
		}
		port.addr.replace(port.wide_log2, Const(State::S0, wide_log2 - port.wide_log2));
		port.data = new_data;
		port.en = new_en;
		port.wide_log2 = wide_log2;
	}
}
