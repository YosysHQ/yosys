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
			cell = module->addCell(memid, ID($mem_v2));
		}
		cell->type = ID($mem_v2);
		cell->attributes = attributes;
		cell->parameters[ID::MEMID] = Const(memid.str());
		cell->parameters[ID::WIDTH] = Const(width);
		cell->parameters[ID::OFFSET] = Const(start_offset);
		cell->parameters[ID::SIZE] = Const(size);
		Const rd_wide_continuation, rd_clk_enable, rd_clk_polarity, rd_transparency_mask, rd_collision_x_mask;
		Const wr_wide_continuation, wr_clk_enable, wr_clk_polarity, wr_priority_mask;
		Const rd_ce_over_srst, rd_arst_value, rd_srst_value, rd_init_value;
		SigSpec rd_clk, rd_en, rd_addr, rd_data;
		SigSpec wr_clk, wr_en, wr_addr, wr_data;
		SigSpec rd_arst, rd_srst;
		int abits = 0;
		for (auto &port : rd_ports)
			abits = std::max(abits, GetSize(port.addr));
		for (auto &port : wr_ports)
			abits = std::max(abits, GetSize(port.addr));
		cell->parameters[ID::ABITS] = Const(abits);
		std::vector<int> wr_port_xlat;
		for (int i = 0; i < GetSize(wr_ports); i++)
			for (int j = 0; j < (1 << wr_ports[i].wide_log2); j++)
				wr_port_xlat.push_back(i);
		for (auto &port : rd_ports) {
			for (auto attr: port.attributes)
				if (!cell->has_attribute(attr.first))
					cell->attributes.insert(attr);
			if (port.cell) {
				module->remove(port.cell);
				port.cell = nullptr;
			}
			for (int sub = 0; sub < (1 << port.wide_log2); sub++)
			{
				rd_wide_continuation.bits().push_back(State(sub != 0));
				rd_clk_enable.bits().push_back(State(port.clk_enable));
				rd_clk_polarity.bits().push_back(State(port.clk_polarity));
				rd_ce_over_srst.bits().push_back(State(port.ce_over_srst));
				rd_clk.append(port.clk);
				rd_arst.append(port.arst);
				rd_srst.append(port.srst);
				rd_en.append(port.en);
				SigSpec addr = port.sub_addr(sub);
				addr.extend_u0(abits, false);
				rd_addr.append(addr);
				log_assert(GetSize(addr) == abits);
				for (auto idx : wr_port_xlat) {
					rd_transparency_mask.bits().push_back(State(bool(port.transparency_mask[idx])));
					rd_collision_x_mask.bits().push_back(State(bool(port.collision_x_mask[idx])));
				}
			}
			rd_data.append(port.data);
			for (auto bit : port.arst_value)
				rd_arst_value.bits().push_back(bit);
			for (auto bit : port.srst_value)
				rd_srst_value.bits().push_back(bit);
			for (auto bit : port.init_value)
				rd_init_value.bits().push_back(bit);
		}
		if (rd_ports.empty()) {
			rd_wide_continuation = State::S0;
			rd_clk_enable = State::S0;
			rd_clk_polarity = State::S0;
			rd_ce_over_srst = State::S0;
			rd_arst_value = State::S0;
			rd_srst_value = State::S0;
			rd_init_value = State::S0;
		}
		if (rd_ports.empty() || wr_ports.empty()) {
			rd_transparency_mask = State::S0;
			rd_collision_x_mask = State::S0;
		}
		cell->parameters[ID::RD_PORTS] = Const(GetSize(rd_clk));
		cell->parameters[ID::RD_CLK_ENABLE] = rd_clk_enable;
		cell->parameters[ID::RD_CLK_POLARITY] = rd_clk_polarity;
		cell->parameters[ID::RD_TRANSPARENCY_MASK] = rd_transparency_mask;
		cell->parameters[ID::RD_COLLISION_X_MASK] = rd_collision_x_mask;
		cell->parameters[ID::RD_WIDE_CONTINUATION] = rd_wide_continuation;
		cell->parameters[ID::RD_CE_OVER_SRST] = rd_ce_over_srst;
		cell->parameters[ID::RD_ARST_VALUE] = rd_arst_value;
		cell->parameters[ID::RD_SRST_VALUE] = rd_srst_value;
		cell->parameters[ID::RD_INIT_VALUE] = rd_init_value;
		cell->parameters.erase(ID::RD_TRANSPARENT);
		cell->setPort(ID::RD_CLK, rd_clk);
		cell->setPort(ID::RD_EN, rd_en);
		cell->setPort(ID::RD_ARST, rd_arst);
		cell->setPort(ID::RD_SRST, rd_srst);
		cell->setPort(ID::RD_ADDR, rd_addr);
		cell->setPort(ID::RD_DATA, rd_data);
		for (auto &port : wr_ports) {
			for (auto attr: port.attributes)
				if (!cell->has_attribute(attr.first))
					cell->attributes.insert(attr);
			if (port.cell) {
				module->remove(port.cell);
				port.cell = nullptr;
			}
			for (int sub = 0; sub < (1 << port.wide_log2); sub++)
			{
				wr_wide_continuation.bits().push_back(State(sub != 0));
				wr_clk_enable.bits().push_back(State(port.clk_enable));
				wr_clk_polarity.bits().push_back(State(port.clk_polarity));
				wr_clk.append(port.clk);
				for (auto idx : wr_port_xlat)
					wr_priority_mask.bits().push_back(State(bool(port.priority_mask[idx])));
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
			wr_priority_mask = State::S0;
		}
		cell->parameters[ID::WR_PORTS] = Const(GetSize(wr_clk));
		cell->parameters[ID::WR_CLK_ENABLE] = wr_clk_enable;
		cell->parameters[ID::WR_CLK_POLARITY] = wr_clk_polarity;
		cell->parameters[ID::WR_PRIORITY_MASK] = wr_priority_mask;
		cell->parameters[ID::WR_WIDE_CONTINUATION] = wr_wide_continuation;
		cell->setPort(ID::WR_CLK, wr_clk);
		cell->setPort(ID::WR_EN, wr_en);
		cell->setPort(ID::WR_ADDR, wr_addr);
		cell->setPort(ID::WR_DATA, wr_data);
		for (auto &init : inits) {
			for (auto attr: init.attributes)
				if (!cell->has_attribute(attr.first))
					cell->attributes.insert(attr);
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
			if (!port.cell)
				port.cell = module->addCell(NEW_ID, ID($memrd_v2));
			port.cell->type = ID($memrd_v2);
			port.cell->attributes = port.attributes;
			port.cell->parameters[ID::MEMID] = memid.str();
			port.cell->parameters[ID::ABITS] = GetSize(port.addr);
			port.cell->parameters[ID::WIDTH] = width << port.wide_log2;
			port.cell->parameters[ID::CLK_ENABLE] = port.clk_enable;
			port.cell->parameters[ID::CLK_POLARITY] = port.clk_polarity;
			port.cell->parameters[ID::CE_OVER_SRST] = port.ce_over_srst;
			port.cell->parameters[ID::ARST_VALUE] = port.arst_value;
			port.cell->parameters[ID::SRST_VALUE] = port.srst_value;
			port.cell->parameters[ID::INIT_VALUE] = port.init_value;
			port.cell->parameters[ID::TRANSPARENCY_MASK] = port.transparency_mask;
			port.cell->parameters[ID::COLLISION_X_MASK] = port.collision_x_mask;
			port.cell->parameters.erase(ID::TRANSPARENT);
			port.cell->setPort(ID::CLK, port.clk);
			port.cell->setPort(ID::EN, port.en);
			port.cell->setPort(ID::ARST, port.arst);
			port.cell->setPort(ID::SRST, port.srst);
			port.cell->setPort(ID::ADDR, port.addr);
			port.cell->setPort(ID::DATA, port.data);
		}
		int idx = 0;
		for (auto &port : wr_ports) {
			if (!port.cell)
				port.cell = module->addCell(NEW_ID, ID($memwr_v2));
			port.cell->type = ID($memwr_v2);
			port.cell->attributes = port.attributes;
			if (port.cell->parameters.count(ID::PRIORITY))
				port.cell->parameters.erase(ID::PRIORITY);
			port.cell->parameters[ID::MEMID] = memid.str();
			port.cell->parameters[ID::ABITS] = GetSize(port.addr);
			port.cell->parameters[ID::WIDTH] = width << port.wide_log2;
			port.cell->parameters[ID::CLK_ENABLE] = port.clk_enable;
			port.cell->parameters[ID::CLK_POLARITY] = port.clk_polarity;
			port.cell->parameters[ID::PORTID] = idx++;
			port.cell->parameters[ID::PRIORITY_MASK] = port.priority_mask;
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
						init.data.bits()[i] = State::Sx;
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
					cdata.bits()[i+offset] = init.data[i];
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
				init_data.bits()[i+offset] = init.data[i];
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
		log_assert(GetSize(port.addr) >= port.wide_log2);
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
		log_assert(GetSize(port.addr) >= port.wide_log2);
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
	log_assert(width != 0);
}

namespace {

	struct MemIndex {
		dict<IdString, pool<Cell *>> rd_ports;
		dict<IdString, pool<Cell *>> wr_ports;
		dict<IdString, pool<Cell *>> inits;
		MemIndex (Module *module) {
			for (auto cell: module->cells()) {
				if (cell->type.in(ID($memwr), ID($memwr_v2)))
					wr_ports[cell->parameters.at(ID::MEMID).decode_string()].insert(cell);
				else if (cell->type.in(ID($memrd), ID($memrd_v2)))
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
		std::vector<int> wr_portid;
		if (index.rd_ports.count(mem->name)) {
			for (auto cell : index.rd_ports.at(mem->name)) {
				MemRd mrd;
				bool is_compat = cell->type == ID($memrd);
				mrd.cell = cell;
				mrd.attributes = cell->attributes;
				mrd.clk_enable = cell->parameters.at(ID::CLK_ENABLE).as_bool();
				mrd.clk_polarity = cell->parameters.at(ID::CLK_POLARITY).as_bool();
				mrd.clk = cell->getPort(ID::CLK);
				mrd.en = cell->getPort(ID::EN);
				mrd.addr = cell->getPort(ID::ADDR);
				mrd.data = cell->getPort(ID::DATA);
				mrd.wide_log2 = ceil_log2(GetSize(mrd.data) / mem->width);
				bool transparent = false;
				if (is_compat) {
					transparent = cell->parameters.at(ID::TRANSPARENT).as_bool();
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
				} else {
					mrd.ce_over_srst = cell->parameters.at(ID::CE_OVER_SRST).as_bool();
					mrd.arst_value = cell->parameters.at(ID::ARST_VALUE);
					mrd.srst_value = cell->parameters.at(ID::SRST_VALUE);
					mrd.init_value = cell->parameters.at(ID::INIT_VALUE);
					mrd.arst = cell->getPort(ID::ARST);
					mrd.srst = cell->getPort(ID::SRST);
				}
				res.rd_ports.push_back(mrd);
				rd_transparent.push_back(transparent);
			}
		}
		if (index.wr_ports.count(mem->name)) {
			std::vector<std::pair<int, MemWr>> ports;
			for (auto cell : index.wr_ports.at(mem->name)) {
				MemWr mwr;
				bool is_compat = cell->type == ID($memwr);
				mwr.cell = cell;
				mwr.attributes = cell->attributes;
				mwr.clk_enable = cell->parameters.at(ID::CLK_ENABLE).as_bool();
				mwr.clk_polarity = cell->parameters.at(ID::CLK_POLARITY).as_bool();
				mwr.clk = cell->getPort(ID::CLK);
				mwr.en = cell->getPort(ID::EN);
				mwr.addr = cell->getPort(ID::ADDR);
				mwr.data = cell->getPort(ID::DATA);
				mwr.wide_log2 = ceil_log2(GetSize(mwr.data) / mem->width);
				ports.push_back(std::make_pair(cell->parameters.at(is_compat ? ID::PRIORITY : ID::PORTID).as_int(), mwr));
			}
			std::sort(ports.begin(), ports.end(), [](const std::pair<int, MemWr> &a, const std::pair<int, MemWr> &b) { return a.first < b.first; });
			for (auto &it : ports) {
				res.wr_ports.push_back(it.second);
				wr_portid.push_back(it.first);
			}
			for (int i = 0; i < GetSize(res.wr_ports); i++) {
				auto &port = res.wr_ports[i];
				bool is_compat = port.cell->type == ID($memwr);
				if (is_compat) {
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
				} else {
					Const orig_prio_mask = port.cell->parameters.at(ID::PRIORITY_MASK);
					for (int orig_portid : wr_portid) {
						bool has_prio = orig_portid < GetSize(orig_prio_mask) && orig_prio_mask[orig_portid] == State::S1;
						port.priority_mask.push_back(has_prio);
					}
				}
			}
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
		for (int i = 0; i < GetSize(res.rd_ports); i++) {
			auto &port = res.rd_ports[i];
			bool is_compat = port.cell->type == ID($memrd);
			if (is_compat) {
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
			} else {
				Const orig_trans_mask = port.cell->parameters.at(ID::TRANSPARENCY_MASK);
				Const orig_cx_mask = port.cell->parameters.at(ID::COLLISION_X_MASK);
				for (int orig_portid : wr_portid) {
					port.transparency_mask.push_back(orig_portid < GetSize(orig_trans_mask) && orig_trans_mask[orig_portid] == State::S1);
					port.collision_x_mask.push_back(orig_portid < GetSize(orig_cx_mask) && orig_cx_mask[orig_portid] == State::S1);
				}
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
		bool is_compat = cell->type == ID($mem);
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
		int n_rd_ports = cell->parameters.at(ID::RD_PORTS).as_int();
		int n_wr_ports = cell->parameters.at(ID::WR_PORTS).as_int();
		Const rd_wide_continuation = is_compat ? Const(State::S0, n_rd_ports) : cell->parameters.at(ID::RD_WIDE_CONTINUATION);
		Const wr_wide_continuation = is_compat ? Const(State::S0, n_wr_ports) : cell->parameters.at(ID::WR_WIDE_CONTINUATION);
		for (int i = 0, ni; i < n_rd_ports; i = ni) {
			ni = i + 1;
			while (ni < n_rd_ports && rd_wide_continuation[ni] == State::S1)
				ni++;
			MemRd mrd;
			mrd.wide_log2 = ceil_log2(ni - i);
			log_assert(ni - i == (1 << mrd.wide_log2));
			mrd.clk_enable = cell->parameters.at(ID::RD_CLK_ENABLE).extract(i, 1).as_bool();
			mrd.clk_polarity = cell->parameters.at(ID::RD_CLK_POLARITY).extract(i, 1).as_bool();
			mrd.clk = cell->getPort(ID::RD_CLK).extract(i, 1);
			mrd.en = cell->getPort(ID::RD_EN).extract(i, 1);
			mrd.addr = cell->getPort(ID::RD_ADDR).extract(i * abits, abits);
			mrd.data = cell->getPort(ID::RD_DATA).extract(i * res.width, (ni - i) * res.width);
			if (is_compat) {
				mrd.ce_over_srst = false;
				mrd.arst_value = Const(State::Sx, res.width << mrd.wide_log2);
				mrd.srst_value = Const(State::Sx, res.width << mrd.wide_log2);
				mrd.init_value = Const(State::Sx, res.width << mrd.wide_log2);
				mrd.arst = State::S0;
				mrd.srst = State::S0;
			} else {
				mrd.ce_over_srst = cell->parameters.at(ID::RD_CE_OVER_SRST).extract(i, 1).as_bool();
				mrd.arst_value = cell->parameters.at(ID::RD_ARST_VALUE).extract(i * res.width, (ni - i) * res.width);
				mrd.srst_value = cell->parameters.at(ID::RD_SRST_VALUE).extract(i * res.width, (ni - i) * res.width);
				mrd.init_value = cell->parameters.at(ID::RD_INIT_VALUE).extract(i * res.width, (ni - i) * res.width);
				mrd.arst = cell->getPort(ID::RD_ARST).extract(i, 1);
				mrd.srst = cell->getPort(ID::RD_SRST).extract(i, 1);
			}
			if (!is_compat) {
				Const transparency_mask = cell->parameters.at(ID::RD_TRANSPARENCY_MASK).extract(i * n_wr_ports, n_wr_ports);
				Const collision_x_mask = cell->parameters.at(ID::RD_COLLISION_X_MASK).extract(i * n_wr_ports, n_wr_ports);
				for (int j = 0; j < n_wr_ports; j++)
					if (wr_wide_continuation[j] != State::S1) {
						mrd.transparency_mask.push_back(transparency_mask[j] == State::S1);
						mrd.collision_x_mask.push_back(collision_x_mask[j] == State::S1);
					}
			}
			res.rd_ports.push_back(mrd);
		}
		for (int i = 0, ni; i < n_wr_ports; i = ni) {
			ni = i + 1;
			while (ni < n_wr_ports && wr_wide_continuation[ni] == State::S1)
				ni++;
			MemWr mwr;
			mwr.wide_log2 = ceil_log2(ni - i);
			log_assert(ni - i == (1 << mwr.wide_log2));
			mwr.clk_enable = cell->parameters.at(ID::WR_CLK_ENABLE).extract(i, 1).as_bool();
			mwr.clk_polarity = cell->parameters.at(ID::WR_CLK_POLARITY).extract(i, 1).as_bool();
			mwr.clk = cell->getPort(ID::WR_CLK).extract(i, 1);
			mwr.en = cell->getPort(ID::WR_EN).extract(i * res.width, (ni - i) * res.width);
			mwr.addr = cell->getPort(ID::WR_ADDR).extract(i * abits, abits);
			mwr.data = cell->getPort(ID::WR_DATA).extract(i * res.width, (ni - i) * res.width);
			if (!is_compat) {
				Const priority_mask = cell->parameters.at(ID::WR_PRIORITY_MASK).extract(i * n_wr_ports, n_wr_ports);
				for (int j = 0; j < n_wr_ports; j++)
					if (wr_wide_continuation[j] != State::S1)
						mwr.priority_mask.push_back(priority_mask[j] == State::S1);
			}
			res.wr_ports.push_back(mwr);
		}
		if (is_compat) {
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
		if (cell->type.in(ID($mem), ID($mem_v2)))
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
		if (cell->type.in(ID($mem), ID($mem_v2)))
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
		FfData ff(module, initvals, name);
		ff.width = GetSize(port.data);
		ff.has_clk = true;
		ff.sig_clk = port.clk;
		ff.pol_clk = port.clk_polarity;
		if (port.en != State::S1) {
			ff.has_ce = true;
			ff.pol_ce = true;
			ff.sig_ce = port.en;
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
			ff.ce_over_srst = ff.has_ce && port.ce_over_srst;
		}
		ff.sig_d = sig_d;
		ff.sig_q = port.data;
		ff.val_init = port.init_value;
		port.data = async_d;
		c = ff.emit();
	}

	if (c)
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
			FfData ff(module, initvals, NEW_ID);
			ff.width = 1;
			ff.sig_q = cond_q;
			ff.sig_d = cond;
			ff.has_clk = true;
			ff.sig_clk = rport.clk;
			ff.pol_clk = rport.clk_polarity;
			if (rport.en != State::S1) {
				ff.has_ce = true;
				ff.sig_ce = rport.en;
				ff.pol_ce = true;
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
			ff.emit();
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
			emulate_transparency(idx1, i, initvals);
			rport.collision_x_mask[idx1] = false;
			continue;
		}
		if (rport.transparency_mask[idx2]) {
			emulate_transparency(idx2, i, initvals);
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

void Mem::emulate_rden(int idx, FfInitVals *initvals) {
	auto &port = rd_ports[idx];
	log_assert(port.clk_enable);
	emulate_rd_ce_over_srst(idx);
	Wire *new_data = module->addWire(NEW_ID, GetSize(port.data));
	Wire *prev_data = module->addWire(NEW_ID, GetSize(port.data));
	Wire *sel = module->addWire(NEW_ID);
	FfData ff_sel(module, initvals, NEW_ID);
	FfData ff_data(module, initvals, NEW_ID);
	ff_sel.width = 1;
	ff_sel.has_clk = true;
	ff_sel.sig_clk = port.clk;
	ff_sel.pol_clk = port.clk_polarity;
	ff_sel.sig_d = port.en;
	ff_sel.sig_q = sel;
	ff_data.width = GetSize(port.data);
	ff_data.has_clk = true;
	ff_data.sig_clk = port.clk;
	ff_data.pol_clk = port.clk_polarity;
	ff_data.sig_d = port.data;
	ff_data.sig_q = prev_data;
	if (!port.init_value.is_fully_undef()) {
		ff_sel.val_init = State::S0;
		ff_data.val_init = port.init_value;
		port.init_value = Const(State::Sx, GetSize(port.data));
	} else {
		ff_sel.val_init = State::Sx;
		ff_data.val_init = Const(State::Sx, GetSize(port.data));
	}
	if (port.arst != State::S0) {
		ff_sel.has_arst = true;
		ff_sel.val_arst = State::S0;
		ff_sel.sig_arst = port.arst;
		ff_sel.pol_arst = true;
		ff_data.has_arst = true;
		ff_data.val_arst = port.arst_value;
		ff_data.sig_arst = port.arst;
		ff_data.pol_arst = true;
		port.arst = State::S0;
	}
	if (port.srst != State::S0) {
		log_assert(!port.ce_over_srst);
		ff_sel.has_srst = true;
		ff_sel.val_srst = State::S0;
		ff_sel.sig_srst = port.srst;
		ff_sel.pol_srst = true;
		ff_sel.ce_over_srst = false;
		ff_data.has_srst = true;
		ff_data.val_srst = port.srst_value;
		ff_data.sig_srst = port.srst;
		ff_data.pol_srst = true;
		ff_data.ce_over_srst = false;
		port.srst = State::S0;
	}
	ff_sel.emit();
	ff_data.emit();
	module->addMux(NEW_ID, prev_data, new_data, sel, port.data);
	port.data = new_data;
	port.en = State::S1;
}

void Mem::emulate_reset(int idx, bool emu_init, bool emu_arst, bool emu_srst, FfInitVals *initvals) {
	auto &port = rd_ports[idx];
	if (emu_init && !port.init_value.is_fully_undef()) {
		Wire *sel = module->addWire(NEW_ID);
		FfData ff_sel(module, initvals, NEW_ID);
		Wire *new_data = module->addWire(NEW_ID, GetSize(port.data));
		ff_sel.width = 1;
		ff_sel.has_clk = true;
		ff_sel.sig_clk = port.clk;
		ff_sel.pol_clk = port.clk_polarity;
		ff_sel.sig_d = State::S1;
		ff_sel.sig_q = sel;
		ff_sel.val_init = State::S0;
		if (port.en != State::S1) {
			ff_sel.has_ce = true;
			ff_sel.sig_ce = port.en;
			ff_sel.pol_ce = true;
			ff_sel.ce_over_srst = port.ce_over_srst;
		}
		if (port.arst != State::S0) {
			ff_sel.has_arst = true;
			ff_sel.sig_arst = port.arst;
			ff_sel.pol_arst = true;
			if (emu_arst && port.arst_value == port.init_value) {
				// If we're going to emulate async reset anyway, and the reset
				// value is the same as init value, reuse the same mux.
				ff_sel.val_arst = State::S0;
				port.arst = State::S0;
			} else {
				ff_sel.val_arst = State::S1;
			}
		}
		if (port.srst != State::S0) {
			ff_sel.has_srst = true;
			ff_sel.sig_srst = port.srst;
			ff_sel.pol_srst = true;
			if (emu_srst && port.srst_value == port.init_value) {
				ff_sel.val_srst = State::S0;
				port.srst = State::S0;
			} else {
				ff_sel.val_srst = State::S1;
			}
		}
		ff_sel.emit();
		module->addMux(NEW_ID, port.init_value, new_data, sel, port.data);
		port.data = new_data;
		port.init_value = Const(State::Sx, GetSize(port.data));
	}
	if (emu_arst && port.arst != State::S0) {
		Wire *sel = module->addWire(NEW_ID);
		FfData ff_sel(module, initvals, NEW_ID);
		Wire *new_data = module->addWire(NEW_ID, GetSize(port.data));
		ff_sel.width = 1;
		ff_sel.has_clk = true;
		ff_sel.sig_clk = port.clk;
		ff_sel.pol_clk = port.clk_polarity;
		ff_sel.sig_d = State::S1;
		ff_sel.sig_q = sel;
		if (port.init_value.is_fully_undef())
			ff_sel.val_init = State::Sx;
		else
			ff_sel.val_init = State::S1;
		if (port.en != State::S1) {
			ff_sel.has_ce = true;
			ff_sel.sig_ce = port.en;
			ff_sel.pol_ce = true;
			ff_sel.ce_over_srst = port.ce_over_srst;
		}
		ff_sel.has_arst = true;
		ff_sel.sig_arst = port.arst;
		ff_sel.pol_arst = true;
		ff_sel.val_arst = State::S0;
		if (port.srst != State::S0) {
			ff_sel.has_srst = true;
			ff_sel.sig_srst = port.srst;
			ff_sel.pol_srst = true;
			if (emu_srst && port.srst_value == port.arst_value) {
				ff_sel.val_srst = State::S0;
				port.srst = State::S0;
			} else {
				ff_sel.val_srst = State::S1;
			}
		}
		ff_sel.emit();
		module->addMux(NEW_ID, port.arst_value, new_data, sel, port.data);
		port.data = new_data;
		port.arst = State::S0;
	}
	if (emu_srst && port.srst != State::S0) {
		Wire *sel = module->addWire(NEW_ID);
		FfData ff_sel(module, initvals, NEW_ID);
		Wire *new_data = module->addWire(NEW_ID, GetSize(port.data));
		ff_sel.width = 1;
		ff_sel.has_clk = true;
		ff_sel.sig_clk = port.clk;
		ff_sel.pol_clk = port.clk_polarity;
		ff_sel.sig_d = State::S1;
		ff_sel.sig_q = sel;
		if (port.init_value.is_fully_undef())
			ff_sel.val_init = State::Sx;
		else
			ff_sel.val_init = State::S1;
		if (port.en != State::S1) {
			ff_sel.has_ce = true;
			ff_sel.sig_ce = port.en;
			ff_sel.pol_ce = true;
			ff_sel.ce_over_srst = port.ce_over_srst;
		}
		ff_sel.has_srst = true;
		ff_sel.sig_srst = port.srst;
		ff_sel.pol_srst = true;
		ff_sel.val_srst = State::S0;
		if (port.arst != State::S0) {
			ff_sel.has_arst = true;
			ff_sel.sig_arst = port.arst;
			ff_sel.pol_arst = true;
			ff_sel.val_arst = State::S1;
		}
		ff_sel.emit();
		module->addMux(NEW_ID, port.srst_value, new_data, sel, port.data);
		port.data = new_data;
		port.srst = State::S0;
	}
}

void Mem::emulate_rd_ce_over_srst(int idx) {
	auto &port = rd_ports[idx];
	log_assert(port.clk_enable);
	if (port.en == State::S1 || port.srst == State::S0 || !port.ce_over_srst) {
		port.ce_over_srst = false;
		return;
	}
	port.ce_over_srst = false;
	port.srst = module->And(NEW_ID, port.en, port.srst);
}

void Mem::emulate_rd_srst_over_ce(int idx) {
	auto &port = rd_ports[idx];
	log_assert(port.clk_enable);
	if (port.en == State::S1 || port.srst == State::S0 || port.ce_over_srst) {
		port.ce_over_srst = true;
		return;
	}
	port.ce_over_srst = true;
	port.en = module->Or(NEW_ID, port.en, port.srst);
}

bool Mem::emulate_read_first_ok() {
	if (wr_ports.empty())
		return false;
	SigSpec clk = wr_ports[0].clk;
	bool clk_polarity = wr_ports[0].clk_polarity;
	for (auto &port: wr_ports) {
		if (!port.clk_enable)
			return false;
		if (port.clk != clk)
			return false;
		if (port.clk_polarity != clk_polarity)
			return false;
	}
	bool found_read_first = false;
	for (auto &port: rd_ports) {
		if (!port.clk_enable)
			return false;
		if (port.clk != clk)
			return false;
		if (port.clk_polarity != clk_polarity)
			return false;
		// No point doing this operation if there is no read-first relationship
		// in the first place.
		for (int j = 0; j < GetSize(wr_ports); j++)
			if (!port.transparency_mask[j] && !port.collision_x_mask[j])
				found_read_first = true;
	}
	return found_read_first;
}

void Mem::emulate_read_first(FfInitVals *initvals) {
	log_assert(emulate_read_first_ok());
	for (int i = 0; i < GetSize(rd_ports); i++)
		for (int j = 0; j < GetSize(wr_ports); j++)
			if (rd_ports[i].transparency_mask[j])
				emulate_transparency(j, i, initvals);
	for (int i = 0; i < GetSize(rd_ports); i++)
		for (int j = 0; j < GetSize(wr_ports); j++) {
			log_assert(!rd_ports[i].transparency_mask[j]);
			rd_ports[i].collision_x_mask[j] = false;
			rd_ports[i].transparency_mask[j] = true;
		}
	for (auto &port: wr_ports) {
		Wire *new_data = module->addWire(NEW_ID, GetSize(port.data));
		Wire *new_addr = module->addWire(NEW_ID, GetSize(port.addr));
		auto compressed = port.compress_en();
		Wire *new_en = module->addWire(NEW_ID, GetSize(compressed.first));
		FfData ff_data(module, initvals, NEW_ID);
		FfData ff_addr(module, initvals, NEW_ID);
		FfData ff_en(module, initvals, NEW_ID);
		ff_data.width = GetSize(port.data);
		ff_data.has_clk = true;
		ff_data.sig_clk = port.clk;
		ff_data.pol_clk = port.clk_polarity;
		ff_data.sig_d = port.data;
		ff_data.sig_q = new_data;;
		ff_data.val_init = Const(State::Sx, ff_data.width);
		ff_data.emit();
		ff_addr.width = GetSize(port.addr);
		ff_addr.has_clk = true;
		ff_addr.sig_clk = port.clk;
		ff_addr.pol_clk = port.clk_polarity;
		ff_addr.sig_d = port.addr;
		ff_addr.sig_q = new_addr;;
		ff_addr.val_init = Const(State::Sx, ff_addr.width);
		ff_addr.emit();
		ff_en.width = GetSize(compressed.first);
		ff_en.has_clk = true;
		ff_en.sig_clk = port.clk;
		ff_en.pol_clk = port.clk_polarity;
		ff_en.sig_d = compressed.first;
		ff_en.sig_q = new_en;;
		if (inits.empty())
			ff_en.val_init = Const(State::Sx, ff_en.width);
		else
			ff_en.val_init = Const(State::S0, ff_en.width);
		ff_en.emit();
		port.data = new_data;
		port.addr = new_addr;
		port.en = port.decompress_en(compressed.second, new_en);
	}
}

std::pair<SigSpec, std::vector<int>> MemWr::compress_en() {
	SigSpec sig = en[0];
	std::vector<int> swizzle;
	SigBit prev_bit = en[0];
	int idx = 0;
	for (auto &bit: en) {
		if (bit != prev_bit) {
			sig.append(bit);
			prev_bit = bit;
			idx++;
		}
		swizzle.push_back(idx);
	}
	log_assert(idx + 1 == GetSize(sig));
	return {sig, swizzle};
}

SigSpec MemWr::decompress_en(const std::vector<int> &swizzle, SigSpec sig) {
	SigSpec res;
	for (int i: swizzle)
		res.append(sig[i]);
	return res;
}

using addr_t = MemContents::addr_t;

MemContents::MemContents(Mem *mem) :
	MemContents(ceil_log2(mem->size), mem->width)
{
	for(const auto &init : mem->inits) {
		if(init.en.is_fully_zero()) continue;
		log_assert(init.en.size() == _data_width);
		if(init.en.is_fully_ones())
			insert_concatenated(init.addr.as_int(), init.data);
		else {
			// TODO: this case could be handled more efficiently by adding
			// a flag to reserve_range that tells it to preserve
			// previous contents
			addr_t addr = init.addr.as_int();
			addr_t words = init.data.size() / _data_width;
			RTLIL::Const data = init.data;
			log_assert(data.size() % _data_width == 0);
			for(addr_t i = 0; i < words; i++) {
				RTLIL::Const previous = (*this)[addr + i];
				for(int j = 0; j < _data_width; j++)
					if(init.en[j] != State::S1)
						data.bits()[_data_width * i + j] = previous[j];
			}
			insert_concatenated(init.addr.as_int(), data);
		}
	}
}

MemContents::iterator & MemContents::iterator::operator++() {
	auto it = _memory->_values.upper_bound(_addr);
	if(it == _memory->_values.end()) {
		_memory = nullptr;
		_addr = ~(addr_t) 0;
	} else
		_addr = it->first;
	return *this;
}

void MemContents::check() {
	log_assert(_addr_width > 0 && _addr_width < (int)sizeof(addr_t) * 8);
	log_assert(_data_width > 0);
	log_assert(_default_value.size() == _data_width);
	if(_values.empty()) return;
	auto it = _values.begin();
	for(;;) {
		log_assert(!it->second.empty());
		log_assert(it->second.size() % _data_width == 0);
		auto end1 = _range_end(it);
		log_assert(_range_begin(it) < (addr_t)(1<<_addr_width));
		log_assert(end1 <= (addr_t)(1<<_addr_width));
		if(++it == _values.end())
			break;
		// check that ranges neither overlap nor touch
		log_assert(_range_begin(it) > end1);
	}
}

bool MemContents::_range_contains(std::map<addr_t, RTLIL::Const>::iterator it, addr_t addr) const {
	// if addr < begin, the subtraction will overflow, and the comparison will always fail
	// (since we have an invariant that begin + size <= 2^(addr_t bits))
	return it != _values.end() && addr - _range_begin(it) < _range_size(it);
}


bool MemContents::_range_contains(std::map<addr_t, RTLIL::Const>::iterator it, addr_t begin_addr, addr_t end_addr) const {
	// note that we assume begin_addr <= end_addr
	return it != _values.end() && _range_begin(it) <= begin_addr && end_addr - _range_begin(it) <= _range_size(it);
}

bool MemContents::_range_overlaps(std::map<addr_t, RTLIL::Const>::iterator it, addr_t begin_addr, addr_t end_addr) const {
	if(it == _values.end() || begin_addr >= end_addr)
		return false;
	auto top1 = _range_end(it) - 1;
	auto top2 = end_addr - 1;
	return !(top1 < begin_addr || top2 < _range_begin(it));
}

std::map<addr_t, RTLIL::Const>::iterator MemContents::_range_at(addr_t addr) const {
	// allow addr == 1<<_addr_width (which will just return end())
	log_assert(addr <= (addr_t)(1<<_addr_width));
	// get the first range with base > addr
	// (we use const_cast since map::iterators are only passed around internally and not exposed to the user
	// and using map::iterator in both the const and non-const case simplifies the code a little,
	// at the cost of having to be a little careful when implementing const methods)
	auto it = const_cast<std::map<addr_t, RTLIL::Const> &>(_values).upper_bound(addr);
	// if we get the very first range, all ranges are past the addr, so return the first one
	if(it == _values.begin())
		return it;
	// otherwise, go back to the previous interval
	// this must be the last interval with base <= addr
	auto it_prev = std::next(it, -1);
	if(_range_contains(it_prev, addr))
		return it_prev;
	else
		return it;
}

RTLIL::Const MemContents::operator[](addr_t addr) const {
	auto it = _range_at(addr);
	if(_range_contains(it, addr))
		return it->second.extract(_range_offset(it, addr), _data_width);
	else
		return _default_value;
}

addr_t MemContents::count_range(addr_t begin_addr, addr_t end_addr) const {
	addr_t count = 0;
	for(auto it = _range_at(begin_addr); _range_overlaps(it, begin_addr, end_addr); it++) {
		auto first = std::max(_range_begin(it), begin_addr);
		auto last = std::min(_range_end(it), end_addr);
		count += last - first;
	}
	return count;
}

void MemContents::clear_range(addr_t begin_addr, addr_t end_addr) {
	if(begin_addr >= end_addr) return;
	// identify which ranges are affected by this operation
	// the first iterator affected is the first one containing any addr >= begin_addr
	auto begin_it = _range_at(begin_addr);
	// the first iterator *not* affected is the first one with base addr > end_addr - 1
	auto end_it = _values.upper_bound(end_addr - 1);
	if(begin_it == end_it)
		return; // nothing to do
	// the last iterator affected is one before the first one not affected
	auto last_it = std::next(end_it, -1);
	// the first and last range may need to be truncated, the rest can just be deleted
	// to handle the begin_it == last_it case correctly, do the end case first by inserting a new range past the end
	if(_range_contains(last_it, end_addr - 1)) {
		auto new_begin = end_addr;
		auto end = _range_end(last_it);
		// if there is data past the end address, preserve it by creating a new range
		if(new_begin != end)
			end_it = _values.emplace_hint(last_it, new_begin, last_it->second.extract(_range_offset(last_it, new_begin), (_range_end(last_it) - new_begin) * _data_width));
		// the original range will either be truncated in the next if() block or deleted in the erase, so we can leave it untruncated
	}
	if(_range_contains(begin_it, begin_addr)) {
		auto new_end = begin_addr;
		// if there is data before the start address, truncate but don't delete
		if(new_end != begin_it->first) {
			begin_it->second.extu(_range_offset(begin_it, new_end));
			++begin_it;
		}
		// else: begin_it will be deleted
	}
	_values.erase(begin_it, end_it);
}

std::map<addr_t, RTLIL::Const>::iterator MemContents::_reserve_range(addr_t begin_addr, addr_t end_addr) {
	if(begin_addr >= end_addr)
		return _values.end(); // need a dummy value to return, end() is cheap
	// find the first range containing any addr >= begin_addr - 1
	auto lower_it = begin_addr == 0 ? _values.begin() : _range_at(begin_addr - 1);
	// check if our range is already covered by a single range
	// note that since ranges are not allowed to touch, if any range contains begin_addr, lower_it equals that range
	if (_range_contains(lower_it, begin_addr, end_addr))
		return lower_it;
	// find the first range containing any addr >= end_addr
	auto upper_it = _range_at(end_addr);
	// check if either of the two ranges we just found touch our range
	bool lower_touch = begin_addr > 0 && _range_contains(lower_it, begin_addr - 1);
	bool upper_touch = _range_contains(upper_it, end_addr);
	if (lower_touch && upper_touch) {
		log_assert (lower_it != upper_it); // lower_it == upper_it should be excluded by the check above
		// we have two different ranges touching at either end, we need to merge them
		auto upper_end = _range_end(upper_it);
		// make range bigger (maybe reserve here instead of resize?)
		lower_it->second.bits().resize(_range_offset(lower_it, upper_end), State::Sx);
		// copy only the data beyond our range
		std::copy(_range_data(upper_it, end_addr), _range_data(upper_it, upper_end), _range_data(lower_it, end_addr));
		// keep lower_it, but delete upper_it
		_values.erase(std::next(lower_it), std::next(upper_it));
		return lower_it;
	} else if (lower_touch) {
		// we have a range to the left, just make it bigger and delete any other that may exist.
		lower_it->second.bits().resize(_range_offset(lower_it, end_addr), State::Sx);
		// keep lower_it and upper_it
		_values.erase(std::next(lower_it), upper_it);
		return lower_it;
	} else if (upper_touch) {
		// we have a range to the right, we need to expand it
		// since we need to erase and reinsert to a new address, steal the data
		RTLIL::Const data = std::move(upper_it->second);
		// note that begin_addr is not in upper_it, otherwise the whole range covered check would have tripped
		data.bits().insert(data.bits().begin(), (_range_begin(upper_it) - begin_addr) * _data_width, State::Sx);
		// delete lower_it and upper_it, then reinsert
		_values.erase(lower_it, std::next(upper_it));
		return _values.emplace(begin_addr, std::move(data)).first;
	} else {
		// no ranges are touching, so just delete all ranges in our range and allocate a new one
		// could try to resize an existing range but not sure if that actually helps
		_values.erase(lower_it, upper_it);
		return _values.emplace(begin_addr, RTLIL::Const(State::Sx, (end_addr - begin_addr) * _data_width)).first;
	}
}

void MemContents::insert_concatenated(addr_t addr, RTLIL::Const const &values) {
	addr_t words = (values.size() + _data_width - 1) / _data_width;
	log_assert(addr < (addr_t)(1<<_addr_width));
	log_assert(words <= (addr_t)(1<<_addr_width) - addr);
	auto it = _reserve_range(addr, addr + words);
	auto to_begin = _range_data(it, addr);
	std::copy(values.begin(), values.end(), to_begin);
	// if values is not word-aligned, fill any missing bits with 0
	std::fill(to_begin + values.size(), to_begin + words * _data_width, State::S0);
}

std::vector<State>::iterator MemContents::_range_write(std::vector<State>::iterator it, RTLIL::Const const &word) {
	auto from_end = word.size() <= _data_width ? word.end() : word.begin() + _data_width;
	auto to_end = std::copy(word.begin(), from_end, it);
	auto it_next = std::next(it, _data_width);
	std::fill(to_end, it_next, State::S0);
	return it_next;
}