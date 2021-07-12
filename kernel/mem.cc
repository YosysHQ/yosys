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

	// for future: handle transparency mask here

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
			if (port.cell) {
				module->remove(port.cell);
				port.cell = nullptr;
			}
			for (int sub = 0; sub < (1 << port.wide_log2); sub++)
			{
				rd_wide_continuation.bits.push_back(State(sub != 0));
				rd_clk_enable.bits.push_back(State(port.clk_enable));
				rd_clk_polarity.bits.push_back(State(port.clk_polarity));
				rd_transparent.bits.push_back(State(port.transparent));
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
			if (!port.cell)
				port.cell = module->addCell(NEW_ID, ID($memrd));
			port.cell->attributes = port.attributes;
			port.cell->parameters[ID::MEMID] = memid.str();
			port.cell->parameters[ID::ABITS] = GetSize(port.addr);
			port.cell->parameters[ID::WIDTH] = width << port.wide_log2;
			port.cell->parameters[ID::CLK_ENABLE] = port.clk_enable;
			port.cell->parameters[ID::CLK_POLARITY] = port.clk_polarity;
			port.cell->parameters[ID::TRANSPARENT] = port.transparent;
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
			if (!init.cell)
				init.cell = module->addCell(NEW_ID, ID($meminit));
			init.cell->attributes = init.attributes;
			init.cell->parameters[ID::MEMID] = memid.str();
			init.cell->parameters[ID::ABITS] = GetSize(init.addr);
			init.cell->parameters[ID::WIDTH] = width;
			init.cell->parameters[ID::WORDS] = GetSize(init.data) / width;
			init.cell->parameters[ID::PRIORITY] = idx++;
			init.cell->setPort(ID::ADDR, init.addr);
			init.cell->setPort(ID::DATA, init.data);
		}
	}
}

void Mem::clear_inits() {
	for (auto &init : inits)
		init.removed = true;
}

Const Mem::get_init_data() const {
	Const init_data(State::Sx, width * size);
	for (auto &init : inits) {
		if (init.removed)
			continue;
		int offset = (init.addr.as_int() - start_offset) * width;
		for (int i = 0; i < GetSize(init.data); i++)
			if (0 <= i+offset && i+offset < GetSize(init_data))
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
			log_assert(!port.transparent);
			log_assert(port.en == State::S1);
			log_assert(port.arst == State::S0);
			log_assert(port.srst == State::S0);
		}
		for (int j = 0; j < port.wide_log2; j++) {
			log_assert(port.addr[j] == State::S0);
		}
		max_wide_log2 = std::max(max_wide_log2, port.wide_log2);
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
				else if (cell->type == ID($meminit))
					inits[cell->parameters.at(ID::MEMID).decode_string()].insert(cell);
			}
		}
	};

	Mem mem_from_memory(Module *module, RTLIL::Memory *mem, const MemIndex &index) {
		Mem res(module, mem->name, mem->width, mem->start_offset, mem->size);
		res.packed = false;
		res.mem = mem;
		res.attributes = mem->attributes;
		if (index.rd_ports.count(mem->name)) {
			for (auto cell : index.rd_ports.at(mem->name)) {
				MemRd mrd;
				mrd.cell = cell;
				mrd.attributes = cell->attributes;
				mrd.clk_enable = cell->parameters.at(ID::CLK_ENABLE).as_bool();
				mrd.clk_polarity = cell->parameters.at(ID::CLK_POLARITY).as_bool();
				mrd.transparent = cell->parameters.at(ID::TRANSPARENT).as_bool();
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
					mrd.transparent = false;
					if (mrd.en == State::Sx)
						mrd.en = State::S1;
				}
				res.rd_ports.push_back(mrd);
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
			mrd.transparent = cell->parameters.at(ID::RD_TRANSPARENT).extract(i, 1).as_bool();
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
	bool trans_use_addr = port.transparent;

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
			if (port.transparent) {
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
						SigSpec other = wport.data.extract(pos + wsub * width, epos-pos);
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
	port.transparent = false;
	port.ce_over_srst = false;
	port.arst_value = Const(State::Sx, GetSize(port.data));
	port.srst_value = Const(State::Sx, GetSize(port.data));
	port.init_value = Const(State::Sx, GetSize(port.data));

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

void Mem::emulate_priority(int idx1, int idx2)
{
	auto &port1 = wr_ports[idx1];
	auto &port2 = wr_ports[idx2];
	if (!port2.priority_mask[idx1])
		return;
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

void Mem::prepare_wr_merge(int idx1, int idx2) {
	log_assert(idx1 < idx2);
	auto &port1 = wr_ports[idx1];
	auto &port2 = wr_ports[idx2];
	// If port 2 has priority over a port before port 1, make port 1 have priority too.
	for (int i = 0; i < idx1; i++)
		if (port2.priority_mask[i])
			port1.priority_mask[i] = true;
	// If port 2 has priority over a port after port 1, emulate it.
	for (int i = idx1 + 1; i < idx2; i++)
		if (port2.priority_mask[i])
			emulate_priority(i, idx2);
	// If some port had priority over port 2, make it have priority over the merged port too.
	for (int i = idx2 + 1; i < GetSize(wr_ports); i++) {
		auto &oport = wr_ports[i];
		if (oport.priority_mask[idx2])
			oport.priority_mask[idx1] = true;
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
