/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Marcelina Kościelnicka <mwk@0x04.net>
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

#include "memlib.h"

#include <ctype.h>

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/mem.h"
#include "kernel/qcsat.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using namespace MemLibrary;

#define FACTOR_MUX 0.5
#define FACTOR_DEMUX 0.5
#define FACTOR_EMU 2

struct PassOptions {
	bool no_auto_distributed;
	bool no_auto_block;
	bool no_auto_huge;
	double logic_cost_rom;
	double logic_cost_ram;
};

struct WrPortConfig {
	// Index of the read port this port is merged with, or -1 if none.
	int rd_port;
	// Index of the PortGroup in the Ram.
	int port_group;
	int port_variant;
	const PortVariant *def;
	// Emulate priority logic for this list of (source) write port indices.
	std::vector<int> emu_prio;
	// If true, this port needs to end up with uniform byte enables to work correctly.
	bool force_uniform;

	WrPortConfig() : rd_port(-1), force_uniform(false) {}
};

struct RdPortConfig {
	// Index of the write port this port is merged with, or -1 if none.
	int wr_port;
	// Index of the PortGroup in the Ram.
	int port_group;
	int port_variant;
	const PortVariant *def;
	// If true, this is a sync port mapped into async mem, make an output
	// register.  Mutually exclusive with the following options.
	bool emu_sync;
	// Emulate the EN / ARST / SRST / init value circuitry.
	bool emu_en;
	bool emu_arst;
	bool emu_srst;
	bool emu_init;
	// Emulate EN-SRST priority.
	bool emu_srst_en_prio;
	// If true, use clk_en as rd_en.
	bool rd_en_to_clk_en;
	// Emulate transparency logic for this list of (source) write port indices.
	std::vector<int> emu_trans;

	RdPortConfig() : wr_port(-1), emu_sync(false), emu_en(false), emu_arst(false), emu_srst(false), emu_init(false), emu_srst_en_prio(false), rd_en_to_clk_en(false) {}
};

// The named clock and clock polarity assignments.
struct SharedClockConfig {
	bool used;
	SigBit clk;
	// For anyedge clocks.
	bool polarity;
	// For non-anyedge clocks.
	bool invert;
};

struct MemConfig {
	// Reference to the library ram definition
	const Ram *def;
	// Port assignments, indexed by Mem port index.
	std::vector<WrPortConfig> wr_ports;
	std::vector<RdPortConfig> rd_ports;
	std::vector<SharedClockConfig> shared_clocks;
	// Emulate read-first write-read behavior using soft logic.
	bool emu_read_first;
	// This many low bits of (target) address are always-0 on all ports.
	int base_width_log2;
	int unit_width_log2;
	std::vector<int> swizzle;
	int hard_wide_mask;
	int emu_wide_mask;
	// How many times the base memory block will need to be duplicated to get more
	// data bits.
	int repl_d;
	// How many times the whole memory array will need to be duplicated to cover
	// all read ports required.
	int repl_port;
	// Emulation score — how much circuitry we need to add for priority / transparency /
	// reset / initial value emulation.
	int score_emu;
	// Mux score — how much circuitry we need to add to manually decode whatever address
	// bits are not decoded by the memory array itself, for reads.
	int score_mux;
	// Demux score — how much circuitry we need to add to manually decode whatever address
	// bits are not decoded by the memory array itself, for writes.
	int score_demux;
	double cost;
	MemConfig() : emu_read_first(false) {}
};

typedef std::vector<MemConfig> MemConfigs;

struct MapWorker {
	Module *module;
	ModWalker modwalker;
	SigMap sigmap;
	SigMap sigmap_xmux;
	FfInitVals initvals;

	MapWorker(Module *module) : module(module), modwalker(module->design, module), sigmap(module), sigmap_xmux(module), initvals(&sigmap, module) {
		for (auto cell : module->cells())
		{
			if (cell->type == ID($mux))
			{
				RTLIL::SigSpec sig_a = sigmap_xmux(cell->getPort(ID::A));
				RTLIL::SigSpec sig_b = sigmap_xmux(cell->getPort(ID::B));

				if (sig_a.is_fully_undef())
					sigmap_xmux.add(cell->getPort(ID::Y), sig_b);
				else if (sig_b.is_fully_undef())
					sigmap_xmux.add(cell->getPort(ID::Y), sig_a);
			}
		}
	}
};

struct SwizzleBit {
	bool valid;
	int mux_idx;
	int addr;
	int bit;
};

struct Swizzle {
	int addr_shift;
	int addr_start;
	int addr_end;
	std::vector<int> addr_mux_bits;
	std::vector<std::vector<SwizzleBit>> bits;
};

struct MemMapping {
	MapWorker &worker;
	QuickConeSat qcsat;
	Mem &mem;
	const Library &lib;
	const PassOptions &opts;
	std::vector<MemConfig> cfgs;
	bool logic_ok;
	double logic_cost;
	RamKind kind;
	std::string style;
	dict<int, int> wr_en_cache;
	dict<std::pair<int, int>, bool> wr_implies_rd_cache;
	dict<std::pair<int, int>, bool> wr_excludes_rd_cache;
	dict<std::pair<int, int>, bool> wr_excludes_srst_cache;
	std::string rejected_cfg_debug_msgs;

	MemMapping(MapWorker &worker, Mem &mem, const Library &lib, const PassOptions &opts) : worker(worker), qcsat(worker.modwalker), mem(mem), lib(lib), opts(opts) {
		determine_style();
		logic_ok = determine_logic_ok();
		if (GetSize(mem.wr_ports) == 0)
			logic_cost = mem.width * mem.size * opts.logic_cost_rom;
		else
			logic_cost = mem.width * mem.size * opts.logic_cost_ram;
		if (kind == RamKind::Logic)
			return;
		for (int i = 0; i < GetSize(lib.rams); i++) {
			auto &rdef = lib.rams[i];
			if (!check_ram_kind(rdef))
				continue;
			if (!check_ram_style(rdef))
				continue;
			if (!check_init(rdef))
				continue;
			if (rdef.prune_rom && mem.wr_ports.empty()) {
				log_debug("memory %s.%s: rejecting mapping to %s: ROM mapping disabled (prune_rom set)\n", log_id(mem.module->name), log_id(mem.memid), log_id(rdef.id));
				continue;
			}
			MemConfig cfg;
			cfg.def = &rdef;
			for (auto &cdef: rdef.shared_clocks) {
				(void)cdef;
				SharedClockConfig clk;
				clk.used = false;
				cfg.shared_clocks.push_back(clk);
			}
			cfgs.push_back(cfg);
		}
		assign_wr_ports();
		assign_rd_ports();
		handle_trans();
		// If we got this far, the memory is mappable.  The following two can require emulating
		// some functionality, but cannot cause the mapping to fail.
		handle_priority();
		handle_rd_rst();
		score_emu_ports();
		// Now it is just a matter of picking geometry.
		handle_geom();
		dump_configs(0);
		prune_post_geom();
		dump_configs(1);
	}

	bool addr_compatible(int wpidx, int rpidx) {
		auto &wport = mem.wr_ports[wpidx];
		auto &rport = mem.rd_ports[rpidx];
		int max_wide_log2 = std::max(rport.wide_log2, wport.wide_log2);
		SigSpec raddr = rport.addr.extract_end(max_wide_log2);
		SigSpec waddr = wport.addr.extract_end(max_wide_log2);
		int abits = std::max(GetSize(raddr), GetSize(waddr));
		raddr.extend_u0(abits);
		waddr.extend_u0(abits);
		return worker.sigmap_xmux(raddr) == worker.sigmap_xmux(waddr);
	}

	int get_wr_en(int wpidx) {
		auto it = wr_en_cache.find(wpidx);
		if (it != wr_en_cache.end())
			return it->second;
		int res = qcsat.ez->expression(qcsat.ez->OpOr, qcsat.importSig(mem.wr_ports[wpidx].en));
		wr_en_cache.insert({wpidx, res});
		return res;
	}

	bool get_wr_implies_rd(int wpidx, int rpidx) {
		auto key = std::make_pair(wpidx, rpidx);
		auto it = wr_implies_rd_cache.find(key);
		if (it != wr_implies_rd_cache.end())
			return it->second;
		int wr_en = get_wr_en(wpidx);
		int rd_en = qcsat.importSigBit(mem.rd_ports[rpidx].en[0]);
		qcsat.prepare();
		bool res = !qcsat.ez->solve(wr_en, qcsat.ez->NOT(rd_en));
		wr_implies_rd_cache.insert({key, res});
		return res;
	}

	bool get_wr_excludes_rd(int wpidx, int rpidx) {
		auto key = std::make_pair(wpidx, rpidx);
		auto it = wr_excludes_rd_cache.find(key);
		if (it != wr_excludes_rd_cache.end())
			return it->second;
		int wr_en = get_wr_en(wpidx);
		int rd_en = qcsat.importSigBit(mem.rd_ports[rpidx].en[0]);
		qcsat.prepare();
		bool res = !qcsat.ez->solve(wr_en, rd_en);
		wr_excludes_rd_cache.insert({key, res});
		return res;
	}

	bool get_wr_excludes_srst(int wpidx, int rpidx) {
		auto key = std::make_pair(wpidx, rpidx);
		auto it = wr_excludes_srst_cache.find(key);
		if (it != wr_excludes_srst_cache.end())
			return it->second;
		int wr_en = get_wr_en(wpidx);
		int srst = qcsat.importSigBit(mem.rd_ports[rpidx].srst);
		if (mem.rd_ports[rpidx].ce_over_srst) {
			int rd_en = qcsat.importSigBit(mem.rd_ports[rpidx].en[0]);
			srst = qcsat.ez->AND(srst, rd_en);
		}
		qcsat.prepare();
		bool res = !qcsat.ez->solve(wr_en, srst);
		wr_excludes_srst_cache.insert({key, res});
		return res;
	}

	void dump_configs(int stage);
	void dump_config(MemConfig &cfg);
	void determine_style();
	bool determine_logic_ok();
	bool check_ram_kind(const Ram &ram);
	bool check_ram_style(const Ram &ram);
	bool check_init(const Ram &ram);
	void assign_wr_ports();
	void assign_rd_ports();
	void handle_trans();
	void handle_priority();
	void handle_rd_rst();
	void score_emu_ports();
	void handle_geom();
	void prune_post_geom();
	void emit_port(const MemConfig &cfg, std::vector<Cell*> &cells, const PortVariant &pdef, const char *name, int wpidx, int rpidx, const std::vector<int> &hw_addr_swizzle);
	void emit(const MemConfig &cfg);

	void log_reject(std::string message){
		if(ys_debug(1)) {
			rejected_cfg_debug_msgs += message;
			rejected_cfg_debug_msgs += "\n";
		}
	}

	void log_reject(const Ram &ram, std::string message) {
		if(ys_debug(1)) {
			rejected_cfg_debug_msgs += stringf("can't map to to %s: ", log_id(ram.id));
			rejected_cfg_debug_msgs += message;
			rejected_cfg_debug_msgs += "\n";
		}
	}

	void log_reject(const Ram &ram, const PortGroup &pg, std::string message) {
		if(ys_debug(1)) {
			rejected_cfg_debug_msgs += stringf("can't map to port group [");
			bool first = true;
			for (std::string portname : pg.names){
				if (!first) rejected_cfg_debug_msgs += ", ";
				rejected_cfg_debug_msgs += portname;
				first = false;
			}
			rejected_cfg_debug_msgs += stringf("] of %s: ", log_id(ram.id));
			rejected_cfg_debug_msgs += message;
			rejected_cfg_debug_msgs += "\n";
		}
	}
	
	void log_reject(const Ram &ram, const PortGroup &pg, int pvi, std::string message) {
		if(ys_debug(1)) {
			rejected_cfg_debug_msgs += stringf("can't map to option selection [");
			bool first = true;
			for(auto opt : pg.variants[pvi].options){
				if (!first) rejected_cfg_debug_msgs += ", ";
				rejected_cfg_debug_msgs += opt.first;
				rejected_cfg_debug_msgs += stringf(" = %s", log_const(opt.second));
				first = false;
			}
			rejected_cfg_debug_msgs += "] of port group [";
			first = true;
			for (std::string portname : pg.names){
				if (!first) rejected_cfg_debug_msgs += ", ";
				rejected_cfg_debug_msgs += portname;
				first = false;
			}
			rejected_cfg_debug_msgs += stringf("] of %s: ", log_id(ram.id));
			rejected_cfg_debug_msgs += message;
			rejected_cfg_debug_msgs += "\n";
		}
	}
};

void MemMapping::dump_configs(int stage) {
	const char *stage_name;
	switch (stage) {
		case 0:
			stage_name = "post-geometry";
			break;
		case 1:
			stage_name = "after post-geometry prune";
			break;
		default:
			abort();
	}
	log_debug("Memory %s.%s mapping candidates (%s):\n", log_id(mem.module->name), log_id(mem.memid), stage_name);
	if (logic_ok) {
		log_debug("- logic fallback\n");
		log_debug("  - cost: %f\n", logic_cost);
	}
	for (auto &cfg: cfgs) {
		dump_config(cfg);
	}
}

void MemMapping::dump_config(MemConfig &cfg) {
	log_debug("- %s:\n", log_id(cfg.def->id));
	for (auto &it: cfg.def->options)
		log_debug("  - option %s %s\n", it.first.c_str(), log_const(it.second));
	log_debug("  - emulation score: %d\n", cfg.score_emu);
	log_debug("  - replicates (for ports): %d\n", cfg.repl_port);
	log_debug("  - replicates (for data): %d\n", cfg.repl_d);
	log_debug("  - mux score: %d\n", cfg.score_mux);
	log_debug("  - demux score: %d\n", cfg.score_demux);
	log_debug("  - cost: %f\n", cfg.cost);
	std::stringstream os;
	for (int x: cfg.def->dbits)
		os << " " << x;
	std::string dbits_s = os.str();
	log_debug("  - abits %d dbits%s\n", cfg.def->abits, dbits_s.c_str());
	if (cfg.def->byte != 0)
		log_debug("  - byte width %d\n", cfg.def->byte);
	log_debug("  - chosen base width %d\n", cfg.def->dbits[cfg.base_width_log2]);
	os.str("");
	for (int x: cfg.swizzle)
		if (x == -1)
			os << " -";
		else
			os << " " << x;
	std::string swizzle_s = os.str();
	log_debug("  - swizzle%s\n", swizzle_s.c_str());
	os.str("");
	for (int i = 0; (1 << i) <= cfg.hard_wide_mask; i++)
		if (cfg.hard_wide_mask & 1 << i)
			os << " " << i;
	std::string wide_s = os.str();
	if (cfg.hard_wide_mask)
		log_debug("  - hard wide bits%s\n", wide_s.c_str());
	if (cfg.emu_read_first)
		log_debug("  - emulate read-first behavior\n");
	for (int i = 0; i < GetSize(mem.wr_ports); i++) {
		auto &pcfg = cfg.wr_ports[i];
		if (pcfg.rd_port == -1)
			log_debug("  - write port %d: port group %s\n", i, cfg.def->port_groups[pcfg.port_group].names[0].c_str());
		else
			log_debug("  - write port %d: port group %s (shared with read port %d)\n", i, cfg.def->port_groups[pcfg.port_group].names[0].c_str(), pcfg.rd_port);

		for (auto &it: pcfg.def->options)
			log_debug("    - option %s %s\n", it.first.c_str(), log_const(it.second));
		if (cfg.def->width_mode == WidthMode::PerPort) {
			std::stringstream os;
			for (int i = pcfg.def->min_wr_wide_log2; i <= pcfg.def->max_wr_wide_log2; i++)
				os << " " << cfg.def->dbits[i];
			std::string widths_s = os.str();
			const char *note = "";
			if (pcfg.rd_port != -1)
				note = pcfg.def->width_tied ? " (tied)" : " (independent)";
			log_debug("    - widths%s%s\n", widths_s.c_str(), note);
		}
		for (auto i: pcfg.emu_prio)
			log_debug("    - emulate priority over write port %d\n", i);
	}
	for (int i = 0; i < GetSize(mem.rd_ports); i++) {
		auto &pcfg = cfg.rd_ports[i];
		if (pcfg.wr_port == -1)
			log_debug("  - read port %d: port group %s\n", i, cfg.def->port_groups[pcfg.port_group].names[0].c_str());
		else
			log_debug("  - read port %d: port group %s (shared with write port %d)\n", i, cfg.def->port_groups[pcfg.port_group].names[0].c_str(), pcfg.wr_port);
		for (auto &it: pcfg.def->options)
			log_debug("    - option %s %s\n", it.first.c_str(), log_const(it.second));
		if (cfg.def->width_mode == WidthMode::PerPort) {
			std::stringstream os;
			for (int i = pcfg.def->min_rd_wide_log2; i <= pcfg.def->max_rd_wide_log2; i++)
				os << " " << cfg.def->dbits[i];
			std::string widths_s = os.str();
			const char *note = "";
			if (pcfg.wr_port != -1)
				note = pcfg.def->width_tied ? " (tied)" : " (independent)";
			log_debug("    - widths%s%s\n", widths_s.c_str(), note);
		}
		if (pcfg.emu_sync)
			log_debug("    - emulate data register\n");
		if (pcfg.emu_en)
			log_debug("    - emulate clock enable\n");
		if (pcfg.emu_arst)
			log_debug("    - emulate async reset\n");
		if (pcfg.emu_srst)
			log_debug("    - emulate sync reset\n");
		if (pcfg.emu_init)
			log_debug("    - emulate init value\n");
		if (pcfg.emu_srst_en_prio)
			log_debug("    - emulate sync reset / enable priority\n");
		for (auto i: pcfg.emu_trans)
			log_debug("    - emulate transparency with write port %d\n", i);
	}
}

std::pair<bool, Const> search_for_attribute(Mem mem, IdString attr) {
	// priority of attributes:
	// 1. attributes on memory itself
	// 2. attributes on a read or write port
	// 3. attributes on data signal of a read or write port
	// 4. attributes on address signal of a read or write port

	if (mem.has_attribute(attr))
		return std::make_pair(true, mem.attributes.at(attr));

	for (auto &port: mem.rd_ports)
		if (port.has_attribute(attr))
			return std::make_pair(true, port.attributes.at(attr));
	for (auto &port: mem.wr_ports)
		if (port.has_attribute(attr))
			return std::make_pair(true, port.attributes.at(attr));

	for (auto &port: mem.rd_ports)
		for (SigBit bit: port.data)
			if (bit.is_wire() && bit.wire->has_attribute(attr))
				return std::make_pair(true, bit.wire->attributes.at(attr));
	for (auto &port: mem.wr_ports)
		for (SigBit bit: port.data)
			if (bit.is_wire() && bit.wire->has_attribute(attr))
				return std::make_pair(true, bit.wire->attributes.at(attr));

	for (auto &port: mem.rd_ports)
		for (SigBit bit: port.addr)
			if (bit.is_wire() && bit.wire->has_attribute(attr))
				return std::make_pair(true, bit.wire->attributes.at(attr));
	for (auto &port: mem.wr_ports)
		for (SigBit bit: port.addr)
			if (bit.is_wire() && bit.wire->has_attribute(attr))
				return std::make_pair(true, bit.wire->attributes.at(attr));
	
	return std::make_pair(false, Const());
}

// Go through memory attributes to determine user-requested mapping style.
void MemMapping::determine_style() {
	kind = RamKind::Auto;
	style = "";
	auto find_attr = search_for_attribute(mem, ID::lram);
	if (find_attr.first && find_attr.second.as_bool()) {
		kind = RamKind::Huge;
		log("found attribute 'lram' on memory %s.%s, forced mapping to huge RAM\n", log_id(mem.module->name), log_id(mem.memid));
		return;
	}
	for (auto attr: {ID::ram_block, ID::rom_block, ID::ram_style, ID::rom_style, ID::ramstyle, ID::romstyle, ID::syn_ramstyle, ID::syn_romstyle}) {
		find_attr = search_for_attribute(mem, attr);
		if (find_attr.first) {
			Const val = find_attr.second;
			if (val == 1) {
				kind = RamKind::NotLogic;
				log("found attribute '%s = 1' on memory %s.%s, disabled mapping to FF\n", log_id(attr), log_id(mem.module->name), log_id(mem.memid));
				return;
			}
			std::string val_s = val.decode_string();
			for (auto &c: val_s)
				c = std::tolower(c);
			// Handled in memory_dff.
			if (val_s == "no_rw_check")
				continue;
			if (val_s == "auto") {
				// Nothing.
			} else if (val_s == "logic" || val_s == "registers") {
				kind = RamKind::Logic;
				log("found attribute '%s = %s' on memory %s.%s, forced mapping to FF\n", log_id(attr), val_s.c_str(), log_id(mem.module->name), log_id(mem.memid));
			} else if (val_s == "distributed") {
				kind = RamKind::Distributed;
				log("found attribute '%s = %s' on memory %s.%s, forced mapping to distributed RAM\n", log_id(attr), val_s.c_str(), log_id(mem.module->name), log_id(mem.memid));
			} else if (val_s == "block" || val_s == "block_ram" || val_s == "ebr") {
				kind = RamKind::Block;
				log("found attribute '%s = %s' on memory %s.%s, forced mapping to block RAM\n", log_id(attr), val_s.c_str(), log_id(mem.module->name), log_id(mem.memid));
			} else if (val_s == "huge" || val_s == "ultra") {
				kind = RamKind::Huge;
				log("found attribute '%s = %s' on memory %s.%s, forced mapping to huge RAM\n", log_id(attr), val_s.c_str(), log_id(mem.module->name), log_id(mem.memid));
			} else {
				kind = RamKind::NotLogic;
				style = val_s;
				log("found attribute '%s = %s' on memory %s.%s, forced mapping to %s RAM\n", log_id(attr), val_s.c_str(), log_id(mem.module->name), log_id(mem.memid), val_s.c_str());
			}
			return;
		}
	}
	for (auto attr: {ID::logic_block, ID::no_ram}){
		find_attr = search_for_attribute(mem, attr);
		if (find_attr.first && find_attr.second.as_bool())
			kind = RamKind::Logic;
	}
}

// Determine whether the memory can be mapped entirely to soft logic.
bool MemMapping::determine_logic_ok() {
	if (kind != RamKind::Auto && kind != RamKind::Logic) {
		log_reject("can't map to logic: RAM kind conflicts with attribute");
		return false;
	}
	// Memory is mappable entirely to soft logic iff all its write ports are in the same clock domain.
	if (mem.wr_ports.empty())
		return true;
	for (auto &port: mem.wr_ports) {
		if (!port.clk_enable){
			log_reject("can't map to logic: unclocked port");
			return false;
		}
		if (port.clk != mem.wr_ports[0].clk) {
			log_reject("can't map to logic: ports have different write clock domains");
			return false;
		}
		if (port.clk_polarity != mem.wr_ports[0].clk_polarity) {
			log_reject("can't map to logic: ports have different write clock polarity");
			return false;
		}
	}
	return true;
}

// Apply RAM kind restrictions (logic/distributed/block/huge), if any.
bool MemMapping::check_ram_kind(const Ram &ram) {
	if (style != "")
		return true;
	if (ram.kind == kind)
		return true;
	if (kind == RamKind::Auto || kind == RamKind::NotLogic) {
		if (ram.kind == RamKind::Distributed && opts.no_auto_distributed) {
			log_reject(ram, "option -no-auto-distributed given");
			return false;
		}
		if (ram.kind == RamKind::Block && opts.no_auto_block) {
			log_reject(ram, "option -no-auto-block given");
			return false;
		}
		if (ram.kind == RamKind::Huge && opts.no_auto_huge) {
			log_reject(ram, "option -no-auto-huge given");
			return false;
		}
		return true;
	}
	log_reject(ram, "RAM kind conflicts with attribute");
	return false;
}

// Apply specific RAM style restrictions, if any.
bool MemMapping::check_ram_style(const Ram &ram) {
	if (style == "")
		return true;
	for (auto &s: ram.style)
		if (s == style)
			return true;
	log_reject(ram, "RAM style conflicts with attribute");
	return false;
}

// Handle memory initializer restrictions, if any.
bool MemMapping::check_init(const Ram &ram) {
	bool has_nonx = false;
	bool has_one = false;

	for (auto &init: mem.inits) {
		if (init.data.is_fully_undef())
			continue;
		has_nonx = true;
		for (auto bit: init.data)
			if (bit == State::S1)
				has_one = true;
	}

	switch (ram.init) {
		case MemoryInitKind::None:
			if(has_nonx) log_reject(ram, "does not support initialization");
			return !has_nonx;
		case MemoryInitKind::Zero:
			if(has_one) log_reject(ram, "does not support non-zero initialization");
			return !has_one;
		default:
			return true;
	}
}

bool apply_clock(MemConfig &cfg, const PortVariant &def, SigBit clk, bool clk_polarity) {
	if (def.clk_shared == -1)
		return true;
	auto &cdef = cfg.def->shared_clocks[def.clk_shared];
	auto &ccfg = cfg.shared_clocks[def.clk_shared];
	if (cdef.anyedge) {
		if (!ccfg.used) {
			ccfg.used = true;
			ccfg.clk = clk;
			ccfg.polarity = clk_polarity;
			return true;
		} else {
			return ccfg.clk == clk && ccfg.polarity == clk_polarity;
		}
	} else {
		bool invert = clk_polarity ^ (def.clk_pol == ClkPolKind::Posedge);
		if (!ccfg.used) {
			ccfg.used = true;
			ccfg.clk = clk;
			ccfg.invert = invert;
			return true;
		} else {
			return ccfg.clk == clk && ccfg.invert == invert;
		}
	}
}

// Perform write port assignment, validating clock options as we go.
void MemMapping::assign_wr_ports() {
	log_reject(stringf("Assigning write ports... (candidate configs: %zu)", (size_t) cfgs.size()));
	for (auto &port: mem.wr_ports) {
		if (!port.clk_enable) {
			// Async write ports not supported.
			cfgs.clear();
			log_reject("can't map at all: async write port");
			return;
		}
		MemConfigs new_cfgs;
		for (auto &cfg: cfgs) {
			for (int pgi = 0; pgi < GetSize(cfg.def->port_groups); pgi++) {
				auto &pg = cfg.def->port_groups[pgi];
				// Make sure the target port group still has a free port.
				int used = 0;
				for (auto &oport: cfg.wr_ports)
					if (oport.port_group == pgi)
						used++;
				if (used >= GetSize(pg.names)) {
					log_reject(*cfg.def, pg, "not enough unassigned ports remaining");
					continue;
				}
				for (int pvi = 0; pvi < GetSize(pg.variants); pvi++) {
					auto &def = pg.variants[pvi];
					// Make sure the target is a write port.
					if (def.kind == PortKind::Ar || def.kind == PortKind::Sr) {
						log_reject(*cfg.def, pg, pvi, "not a write port");
						continue;
					}
					MemConfig new_cfg = cfg;
					WrPortConfig pcfg;
					pcfg.rd_port = -1;
					pcfg.port_group = pgi;
					pcfg.port_variant = pvi;
					pcfg.def = &def;
					if (!apply_clock(new_cfg, def, port.clk, port.clk_polarity)) {
						log_reject(*cfg.def, pg, pvi, "incompatible clock polarity");
						continue;
					}
					new_cfg.wr_ports.push_back(pcfg);
					new_cfgs.push_back(new_cfg);
				}
			}
		}
		cfgs = new_cfgs;
	}
}

// Perform read port assignment, validating clock and rden options as we go.
void MemMapping::assign_rd_ports() {
	log_reject(stringf("Assigning read ports... (candidate configs: %zu)", (size_t) cfgs.size()));
	for (int pidx = 0; pidx < GetSize(mem.rd_ports); pidx++) {
		auto &port = mem.rd_ports[pidx];
		MemConfigs new_cfgs;
		for (auto &cfg: cfgs) {
			// First pass: read port not shared with a write port.
			for (int pgi = 0; pgi < GetSize(cfg.def->port_groups); pgi++) {
				auto &pg = cfg.def->port_groups[pgi];
				// Make sure the target port group has a port not used up by write ports.
				// Overuse by other read ports is not a problem — this will just result
				// in memory duplication.
				int used = 0;
				for (auto &oport: cfg.wr_ports)
					if (oport.port_group == pgi)
						used++;
				if (used >= GetSize(pg.names)) {
					log_reject(*cfg.def, pg, "not enough unassigned ports remaining");
					continue;
				}
				for (int pvi = 0; pvi < GetSize(pg.variants); pvi++) {
					auto &def = pg.variants[pvi];
					// Make sure the target is a read port.
					if (def.kind == PortKind::Sw) {
						log_reject(*cfg.def, pg, pvi, "not a read port");
						continue;
					}
					// If mapping an async port, accept only async defs.
					if (!port.clk_enable) {
						if (def.kind == PortKind::Sr || def.kind == PortKind::Srsw) {
							log_reject(*cfg.def, pg, pvi, "not an asynchronous read port");
							continue;
						}
					}
					MemConfig new_cfg = cfg;
					RdPortConfig pcfg;
					pcfg.wr_port = -1;
					pcfg.port_group = pgi;
					pcfg.port_variant = pvi;
					pcfg.def = &def;
					if (def.kind == PortKind::Sr || def.kind == PortKind::Srsw) {
						pcfg.emu_sync = false;
						if (!apply_clock(new_cfg, def, port.clk, port.clk_polarity)) {
							log_reject(*cfg.def, pg, pvi, "incompatible clock polarity");
							continue;
						}
						// Decide if rden is usable.
						if (port.en != State::S1) {
							if (def.clk_en) {
								pcfg.rd_en_to_clk_en = true;
							} else {
								pcfg.emu_en = !def.rd_en;
							}
						}
					} else {
						pcfg.emu_sync = port.clk_enable;
					}
					new_cfg.rd_ports.push_back(pcfg);
					new_cfgs.push_back(new_cfg);
				}
			}
			// Second pass: read port shared with a write port.
			for (int wpidx = 0; wpidx < GetSize(mem.wr_ports); wpidx++) {
				auto &wport = mem.wr_ports[wpidx];
				auto &wpcfg = cfg.wr_ports[wpidx];
				auto &def = *wpcfg.def;
				// Make sure the write port is not yet shared.
				if (wpcfg.rd_port != -1) {
					log_reject(stringf("can't share write port %d: already shared by a different read port", wpidx));
					continue;
				}
				// Make sure the target is a read port.
				if (def.kind == PortKind::Sw) {
					log_reject(stringf("can't share write port %d: not a read-write port", wpidx));
					continue;
				}
				// Validate address compatibility.
				if (!addr_compatible(wpidx, pidx)) {
					log_reject(stringf("can't share write port %d: addresses are not compatible", wpidx));
					continue;
				}
				// Validate clock compatibility, if needed.
				if (def.kind == PortKind::Srsw) {
					if (!port.clk_enable) {
						log_reject(stringf("can't share write port %d: incompatible enable", wpidx));
						continue;
					}
					if (port.clk != wport.clk) {
						log_reject(stringf("can't share write port %d: different clock signal", wpidx));
						continue;
					}
					if (port.clk_polarity != wport.clk_polarity) {
						log_reject(stringf("can't share write port %d: incompatible clock polarity", wpidx));
						continue;
					}
				}
				// Okay, let's fill it in.
				MemConfig new_cfg = cfg;
				new_cfg.wr_ports[wpidx].rd_port = pidx;
				RdPortConfig pcfg;
				pcfg.wr_port = wpidx;
				pcfg.port_group = wpcfg.port_group;
				pcfg.port_variant = wpcfg.port_variant;
				pcfg.def = wpcfg.def;
				pcfg.emu_sync = port.clk_enable && def.kind == PortKind::Arsw;
				// For srsw, check rden capability.
				if (def.kind == PortKind::Srsw) {
					bool trans = port.transparency_mask[wpidx];
					bool col_x = port.collision_x_mask[wpidx];
					if (def.rdwr == RdWrKind::NoChange) {
						if (!get_wr_excludes_rd(wpidx, pidx)) {
							if (!trans && !col_x) {
								log_reject(stringf("can't share write port %d: conflict in simultaneous read and write operations", wpidx));
								continue;
							}
							if (trans)
								pcfg.emu_trans.push_back(wpidx);
							new_cfg.wr_ports[wpidx].force_uniform = true;
						}
						if (port.en != State::S1) {
							if (def.clk_en) {
								pcfg.rd_en_to_clk_en = true;
							} else {
								pcfg.emu_en = !def.rd_en;
							}
						}
					} else {
						if (!col_x && !trans && def.rdwr != RdWrKind::Old) {
							log_reject(stringf("can't share write port %d: simultaneous read and write operations should result in new value but port reads old", wpidx));
							continue;
						}
						if (trans) {
							if (def.rdwr != RdWrKind::New && def.rdwr != RdWrKind::NewOnly)
								pcfg.emu_trans.push_back(wpidx);
						}
						if (def.rdwr == RdWrKind::NewOnly) {
							if (!get_wr_excludes_rd(wpidx, pidx))
								new_cfg.wr_ports[wpidx].force_uniform = true;
						}
						if (port.en != State::S1) {
							if (def.clk_en) {
								if (get_wr_implies_rd(wpidx, pidx)) {
									pcfg.rd_en_to_clk_en = true;
								} else {
									pcfg.emu_en = !def.rd_en;
								}
							} else {
								pcfg.emu_en = !def.rd_en;
							}
						}
					}
				}
				new_cfg.rd_ports.push_back(pcfg);
				new_cfgs.push_back(new_cfg);
			}
		}
		cfgs = new_cfgs;
	}
}

// Validate transparency restrictions, determine where to add soft transparency logic.
void MemMapping::handle_trans() {
	log_reject(stringf("Handling transparency... (candidate configs: %zu)", (size_t) cfgs.size()));
	if (mem.emulate_read_first_ok()) {
		MemConfigs new_cfgs;
		for (auto &cfg: cfgs) {
			new_cfgs.push_back(cfg);
			bool ok = true;
			// Using this trick will break read-write port sharing.
			for (auto &pcfg: cfg.rd_ports)
				if (pcfg.wr_port != -1)
					ok = false;
			if (ok) {
				cfg.emu_read_first = true;
				new_cfgs.push_back(cfg);
			}
		}
		cfgs = new_cfgs;
	}
	for (int rpidx = 0; rpidx < GetSize(mem.rd_ports); rpidx++) {
		auto &rport = mem.rd_ports[rpidx];
		if (!rport.clk_enable)
			continue;
		for (int wpidx = 0; wpidx < GetSize(mem.wr_ports); wpidx++) {
			auto &wport = mem.wr_ports[wpidx];
			if (!wport.clk_enable)
				continue;
			if (rport.clk != wport.clk)
				continue;
			if (rport.clk_polarity != wport.clk_polarity)
				continue;
			// If we got this far, we have a transparency restriction
			// to uphold.
			MemConfigs new_cfgs;
			for (auto &cfg: cfgs) {
				auto &rpcfg = cfg.rd_ports[rpidx];
				auto &wpcfg = cfg.wr_ports[wpidx];
				// The transparency relation for shared ports already handled while assigning them.
				if (rpcfg.wr_port == wpidx) {
					new_cfgs.push_back(cfg);
					continue;
				}
				if (rport.collision_x_mask[wpidx] && !cfg.emu_read_first) {
					new_cfgs.push_back(cfg);
					continue;
				}
				bool transparent = rport.transparency_mask[wpidx] || cfg.emu_read_first;
				if (rpcfg.emu_sync) {
					// For async read port, just add the transparency logic
					// if necessary.
					if (transparent)
						rpcfg.emu_trans.push_back(wpidx);
					new_cfgs.push_back(cfg);
				} else {
					// Otherwise, split through the relevant wrtrans caps.
					// For non-transparent ports, the cap needs to be present.
					// For transparent ports, we can emulate transparency
					// even without a direct cap.
					bool found = false;
					for (auto &tdef: wpcfg.def->wrtrans) {
						// Check if the target matches.
						if (tdef.target_kind == WrTransTargetKind::Group && rpcfg.port_group != tdef.target_group) {
							log_reject(*cfg.def, stringf("transparency with target port group %d not supported", tdef.target_group));
							continue;
						}
						// Check if the transparency kind is acceptable.
						if (transparent) {
							if (tdef.kind == WrTransKind::Old) {
								log_reject(*cfg.def, stringf("target %d has wrong transparency kind: new value required", tdef.target_group));
								continue;
							}
						} else {
							if (tdef.kind != WrTransKind::Old) {
								log_reject(*cfg.def, stringf("target %d has wrong transparency kind: old value required", tdef.target_group));
								continue;
							}
						}
						// Okay, we can use this cap.
						new_cfgs.push_back(cfg);
						found = true;
						break;
					}
					if (!found && transparent) {
						// If the port pair is transparent, but no cap was
						// found, use emulation.
						rpcfg.emu_trans.push_back(wpidx);
						new_cfgs.push_back(cfg);
					}
				}
			}
			cfgs = new_cfgs;
		}
	}
}

// Determine where to add soft priority logic.
void MemMapping::handle_priority() {
	for (int p1idx = 0; p1idx < GetSize(mem.wr_ports); p1idx++) {
		for (int p2idx = 0; p2idx < GetSize(mem.wr_ports); p2idx++) {
			auto &port2 = mem.wr_ports[p2idx];
			if (!port2.priority_mask[p1idx])
				continue;
			for (auto &cfg: cfgs) {
				auto &p1cfg = cfg.wr_ports[p1idx];
				auto &p2cfg = cfg.wr_ports[p2idx];
				bool found = false;
				for (auto &pgi: p2cfg.def->wrprio) {
					if (pgi == p1cfg.port_group) {
						found = true;
						break;
					}
				}
				// If no cap was found, emulate.
				if (!found)
					p2cfg.emu_prio.push_back(p1idx);
			}
		}
	}
}

bool is_all_zero(const Const &val) {
	for (auto bit: val.bits)
		if (bit == State::S1)
			return false;
	return true;
}

// Determine where to add soft init value / reset logic.
void MemMapping::handle_rd_rst() {
	for (auto &cfg: cfgs) {
		for (int pidx = 0; pidx < GetSize(mem.rd_ports); pidx++) {
			auto &port = mem.rd_ports[pidx];
			auto &pcfg = cfg.rd_ports[pidx];
			// Only sync ports are relevant.
			// If emulated by async port or we already emulate CE, init will be
			// included for free.
			if (!port.clk_enable || pcfg.emu_sync || pcfg.emu_en)
				continue;
			switch (pcfg.def->rdinitval) {
				case ResetValKind::None:
					pcfg.emu_init = !port.init_value.is_fully_undef();
					break;
				case ResetValKind::Zero:
					pcfg.emu_init = !is_all_zero(port.init_value);
					break;
				default:
					break;
			}
			Const init_val = port.init_value;
			if (port.arst != State::S0) {
				switch (pcfg.def->rdarstval) {
					case ResetValKind::None:
						pcfg.emu_arst = true;
						break;
					case ResetValKind::Zero:
						pcfg.emu_arst = !is_all_zero(port.arst_value);
						break;
					case ResetValKind::Init:
						if (init_val.is_fully_undef())
							init_val = port.arst_value;
						pcfg.emu_arst = init_val != port.arst_value;
						break;
					default:
						break;
				}
			}
			if (port.srst != State::S0) {
				switch (pcfg.def->rdsrstval) {
					case ResetValKind::None:
						pcfg.emu_srst = true;
						break;
					case ResetValKind::Zero:
						pcfg.emu_srst = !is_all_zero(port.srst_value);
						break;
					case ResetValKind::Init:
						if (init_val.is_fully_undef())
							init_val = port.srst_value;
						pcfg.emu_srst = init_val != port.srst_value;
						break;
					default:
						break;
				}
				if (!pcfg.emu_srst && pcfg.def->rdsrst_block_wr && pcfg.wr_port != -1) {
					if (!get_wr_excludes_srst(pcfg.wr_port, pidx))
						pcfg.emu_srst = true;
				}
				if (!pcfg.emu_srst && port.en != State::S1) {
					if (port.ce_over_srst) {
						switch (pcfg.def->rdsrstmode) {
							case SrstKind::Ungated:
								pcfg.emu_srst_en_prio = true;
								break;
							case SrstKind::GatedClkEn:
								pcfg.emu_srst_en_prio = !pcfg.rd_en_to_clk_en;
								break;
							case SrstKind::GatedRdEn:
								break;
							default:
								log_assert(0);
						}
					} else {
						switch (pcfg.def->rdsrstmode) {
							case SrstKind::Ungated:
								break;
							case SrstKind::GatedClkEn:
								if (pcfg.rd_en_to_clk_en) {
									if (pcfg.def->rd_en) {
										pcfg.rd_en_to_clk_en = false;
									} else {
										pcfg.emu_srst_en_prio = true;
									}
								}
								break;
							case SrstKind::GatedRdEn:
								pcfg.emu_srst_en_prio = true;
								break;
							default:
								log_assert(0);
						}
					}
				}
			} else {
				if (pcfg.def->rd_en && pcfg.def->rdwr == RdWrKind::NoChange && pcfg.wr_port != -1) {
					pcfg.rd_en_to_clk_en = false;
				}
			}
		}
	}
}

void MemMapping::score_emu_ports() {
	for (auto &cfg: cfgs) {
		std::vector<int> port_usage_wr(cfg.def->port_groups.size());
		std::vector<int> port_usage_rd(cfg.def->port_groups.size());
		int score = 0;
		// 3 points for every write port if we need to do read-first emulation.
		if (cfg.emu_read_first)
			score += 3 * GetSize(cfg.wr_ports);
		for (auto &pcfg: cfg.wr_ports) {
			// 1 point for every priority relation we need to fix up.
			// This is just a gate for every distinct wren pair.
			score += GetSize(pcfg.emu_prio);
			port_usage_wr[pcfg.port_group]++;
		}
		for (auto &pcfg: cfg.rd_ports) {
			// 3 points for every soft transparency logic instance.  This involves
			// registers and other major mess.
			score += 3 * GetSize(pcfg.emu_trans);
			// 3 points for CE soft logic.  Likewise involves registers.
			// If we already do this, subsumes any init/srst/arst emulation.
			if (pcfg.emu_en)
				score += 3;
			// 2 points for soft init value / reset logic: involves single bit
			// register and some muxes.
			if (pcfg.emu_init)
				score += 2;
			if (pcfg.emu_arst)
				score += 2;
			if (pcfg.emu_srst)
				score += 2;
			// 1 point for wrong srst/en priority (fixed with a single gate).
			if (pcfg.emu_srst_en_prio)
				score++;
			// 1 point for every non-shared read port used, as a tiebreaker
			// to prefer single-port configs.
			if (pcfg.wr_port == -1) {
				score++;
				port_usage_rd[pcfg.port_group]++;
			}
		}
		cfg.score_emu = score;
		int repl_port = 1;
		for (int i = 0; i < GetSize(cfg.def->port_groups); i++) {
			int space = GetSize(cfg.def->port_groups[i].names) - port_usage_wr[i];
			log_assert(space >= 0);
			if (port_usage_rd[i] > 0) {
				log_assert(space > 0);
				int usage = port_usage_rd[i];
				int cur = (usage + space - 1) / space;
				if (cur > repl_port)
					repl_port = cur;
			}
		}
		cfg.repl_port = repl_port;
	}
}

void MemMapping::handle_geom() {
	std::vector<int> wren_size;
	for (auto &port: mem.wr_ports) {
		SigSpec en = port.en;
		en.sort_and_unify();
		wren_size.push_back(GetSize(en));
	}
	for (auto &cfg: cfgs) {
		// First, create a set of "byte boundaries": the bit positions in source memory word
		// that have write enable different from the previous bit in any write port.
		// Bit 0 is considered to be a byte boundary as well.
		// Likewise, create a set of "word boundaries" that are like above, but only for write ports
		// with the "force uniform" flag set.
		std::vector<bool> byte_boundary(mem.width, false);
		std::vector<bool> word_boundary(mem.width, false);
		byte_boundary[0] = true;
		for (int pidx = 0; pidx < GetSize(mem.wr_ports); pidx++) {
			auto &port = mem.wr_ports[pidx];
			auto &pcfg = cfg.wr_ports[pidx];
			if (pcfg.force_uniform)
				word_boundary[0] = true;
			for (int sub = 0; sub < (1 << port.wide_log2); sub++) {
				for (int i = 1; i < mem.width; i++) {
					int pos = sub * mem.width + i;
					if (port.en[pos] != port.en[pos-1]) {
						byte_boundary[i] = true;
						if (pcfg.force_uniform)
							word_boundary[i] = true;
					}
				}
			}
		}
		bool got_config = false;
		int best_cost = 0;
		int byte_width_log2 = 0;
		for (int i = 0; i < GetSize(cfg.def->dbits); i++)
			if (cfg.def->byte >= cfg.def->dbits[i])
				byte_width_log2 = i;
		if (cfg.def->byte == 0)
			byte_width_log2 = GetSize(cfg.def->dbits) - 1;
		pool<int> no_wide_bits;
		// Determine which of the source address bits involved in wide ports
		// are "uniform".  Bits are considered uniform if, when a port is widened through
		// them, the write enables are the same for both values of the bit.
		int max_wr_wide_log2 = 0;
		for (auto &port: mem.wr_ports)
			if (port.wide_log2 > max_wr_wide_log2)
				max_wr_wide_log2 = port.wide_log2;
		int max_wide_log2 = max_wr_wide_log2;
		for (auto &port: mem.rd_ports)
			if (port.wide_log2 > max_wide_log2)
				max_wide_log2 = port.wide_log2;
		int wide_nu_start = max_wide_log2;
		int wide_nu_end = max_wr_wide_log2;
		for (int i = 0; i < GetSize(mem.wr_ports); i++) {
			auto &port = mem.wr_ports[i];
			auto &pcfg = cfg.wr_ports[i];
			for (int j = 0; j < port.wide_log2; j++) {
				bool uniform = true;
				// If write enables don't match, mark bit as non-uniform.
				for (int k = 0; k < (1 << port.wide_log2); k += 2 << j)
					if (port.en.extract(k * mem.width, mem.width << j) != port.en.extract((k + (1 << j)) * mem.width, mem.width << j))
						uniform = false;
				if (!uniform) {
					if (pcfg.force_uniform) {
						for (int k = j; k < port.wide_log2; k++)
							no_wide_bits.insert(k);
					}
					if (j < wide_nu_start)
						wide_nu_start = j;
					break;
				}
			}
			if (pcfg.def->width_tied && pcfg.rd_port != -1) {
				// If:
				//
				// - the write port is merged with a read port
				// - the read port is wider than the write port
				// - read and write widths are tied
				//
				// then we will have to artificially widen the write
				// port to the width of the read port, and emulate
				// a narrower write path by use of write enables,
				// which will definitely be non-uniform over the added
				// bits.
				auto &rport = mem.rd_ports[pcfg.rd_port];
				if (rport.wide_log2 > port.wide_log2) {
					if (port.wide_log2 < wide_nu_start)
						wide_nu_start = port.wide_log2;
					if (rport.wide_log2 > wide_nu_end)
						wide_nu_end = rport.wide_log2;
					if (pcfg.force_uniform) {
						for (int k = port.wide_log2; k < rport.wide_log2; k++)
							no_wide_bits.insert(k);
					}
				}
			}
		}
		// Iterate over base widths.
		for (int base_width_log2 = 0; base_width_log2 < GetSize(cfg.def->dbits); base_width_log2++) {
			// Now, see how many data bits we actually have available.
			// This is usually dbits[base_width_log2], but could be smaller if we
			// ran afoul of a max width limitation.  Configurations where this
			// happens are not useful, unless we need it to satisfy a *minimum*
			// width limitation.
			int unit_width_log2 = base_width_log2;
			for (auto &pcfg: cfg.wr_ports)
				if (unit_width_log2 > pcfg.def->max_wr_wide_log2)
					unit_width_log2 = pcfg.def->max_wr_wide_log2;
			for (auto &pcfg: cfg.rd_ports)
				if (unit_width_log2 > pcfg.def->max_rd_wide_log2)
					unit_width_log2 = pcfg.def->max_rd_wide_log2;
			if (unit_width_log2 != base_width_log2 && got_config)
				break;
			int unit_width = cfg.def->dbits[unit_width_log2];
			// Also determine effective byte width (the granularity of write enables).
			int effective_byte = cfg.def->byte;
			if (effective_byte == 0 || effective_byte > unit_width)
				effective_byte = unit_width;
			if (mem.wr_ports.empty())
				effective_byte = 1;
			log_assert(unit_width % effective_byte == 0);
			// Create the swizzle pattern.
			std::vector<int> swizzle;
			for (int i = 0; i < mem.width; i++) {
				if (word_boundary[i])
					while (GetSize(swizzle) % unit_width)
						swizzle.push_back(-1);
				else if (byte_boundary[i])
					while (GetSize(swizzle) % effective_byte)
						swizzle.push_back(-1);
				swizzle.push_back(i);
			}
			if (word_boundary[0])
				while (GetSize(swizzle) % unit_width)
					swizzle.push_back(-1);
			else
				while (GetSize(swizzle) % effective_byte)
					swizzle.push_back(-1);
			// Now evaluate the configuration, then keep adding more hard wide bits
			// and evaluating.
			int hard_wide_mask = 0;
			int hard_wide_num = 0;
			bool byte_failed = false;
			while (1) {
				// Check if all min width constraints are satisfied.
				// Only check these constraints for write ports with width below
				// byte width — for other ports, we can emulate narrow width with
				// a larger one.
				bool min_width_ok = true;
				int min_width_bit = wide_nu_start;
				for (int pidx = 0; pidx < GetSize(mem.wr_ports); pidx++) {
					auto &port = mem.wr_ports[pidx];
					int w = base_width_log2;
					for (int i = 0; i < port.wide_log2; i++)
						if (hard_wide_mask & 1 << i)
							w++;
					if (w < cfg.wr_ports[pidx].def->min_wr_wide_log2 && w < byte_width_log2) {
						min_width_ok = false;
						if (min_width_bit > port.wide_log2)
							min_width_bit = port.wide_log2;
					}
				}
				if (min_width_ok) {
					int emu_wide_bits = max_wide_log2 - hard_wide_num;
					int mult_wide = 1 << emu_wide_bits;
					int addrs = 1 << (cfg.def->abits - base_width_log2 + emu_wide_bits);
					int min_addr = mem.start_offset / addrs;
					int max_addr = (mem.start_offset + mem.size - 1) / addrs;
					int mult_a = max_addr - min_addr + 1;
					int bits = mult_a * mult_wide * GetSize(swizzle);
					int repl = (bits + unit_width - 1) / unit_width;
					int score_demux = 0;
					for (int i = 0; i < GetSize(mem.wr_ports); i++) {
						auto &port = mem.wr_ports[i];
						int w = emu_wide_bits;
						for (int i = 0; i < port.wide_log2; i++)
							if (!(hard_wide_mask & 1 << i))
								w--;
						if (w || mult_a != 1)
							score_demux += (mult_a << w) * wren_size[i];
					}
					int score_mux = 0;
					for (auto &port: mem.rd_ports) {
						int w = emu_wide_bits;
						for (int i = 0; i < port.wide_log2; i++)
							if (!(hard_wide_mask & 1 << i))
								w--;
						score_mux += ((mult_a << w) - 1) * GetSize(port.data);
					}
					double cost = (cfg.def->cost - cfg.def->widthscale) * repl * cfg.repl_port;
					cost += cfg.def->widthscale * mult_a * mult_wide * mem.width / unit_width * cfg.repl_port;
					cost += score_mux * FACTOR_MUX;
					cost += score_demux * FACTOR_DEMUX;
					cost += cfg.score_emu * FACTOR_EMU;
					if (!got_config || cost < best_cost) {
						cfg.base_width_log2 = base_width_log2;
						cfg.unit_width_log2 = unit_width_log2;
						cfg.swizzle = swizzle;
						cfg.hard_wide_mask = hard_wide_mask;
						cfg.emu_wide_mask = ((1 << max_wide_log2) - 1) & ~hard_wide_mask;
						cfg.repl_d = repl;
						cfg.score_demux = score_demux;
						cfg.score_mux = score_mux;
						cfg.cost = cost;
						best_cost = cost;
						got_config = true;
					}
				}
				if (cfg.def->width_mode != WidthMode::PerPort)
					break;
				// Now, pick the next bit to add to the hard wide mask.
next_hw:
				int scan_from;
				int scan_to;
				bool retry = false;
				if (!min_width_ok) {
					// If we still haven't met the minimum width limits,
					// add the highest one that will be useful for working
					// towards all unmet limits.
					scan_from = min_width_bit;
					scan_to = 0;
					// If the relevant write port is not wide, it's impossible.
				} else if (byte_failed) {
					// If we already failed with uniformly-written bits only,
					// go with uniform bits that are only involved in reads.
					scan_from = max_wide_log2;
					scan_to = wide_nu_end;
				} else if (base_width_log2 + hard_wide_num < byte_width_log2) {
					// If we still need uniform bits, prefer the low ones.
					scan_from = wide_nu_start;
					scan_to = 0;
					retry = true;
				} else {
					scan_from = max_wide_log2;
					scan_to = 0;
				}
				int bit = scan_from - 1;
				while (1) {
					if (bit < scan_to) {
hw_bit_failed:
						if (retry) {
							byte_failed = true;
							goto next_hw;
						} else {
							goto bw_done;
						}
					}
					if (!(hard_wide_mask & 1 << bit) && !no_wide_bits.count(bit))
						break;
					bit--;
				}
				int new_hw_mask = hard_wide_mask | 1 << bit;
				// Check if all max width constraints are satisfied.
				for (int pidx = 0; pidx < GetSize(mem.wr_ports); pidx++) {
					auto &port = mem.wr_ports[pidx];
					int w = base_width_log2;
					for (int i = 0; i < port.wide_log2; i++)
						if (new_hw_mask & 1 << i)
							w++;
					if (w > cfg.wr_ports[pidx].def->max_wr_wide_log2) {
						goto hw_bit_failed;
					}
				}
				for (int pidx = 0; pidx < GetSize(mem.rd_ports); pidx++) {
					auto &port = mem.rd_ports[pidx];
					int w = base_width_log2;
					for (int i = 0; i < port.wide_log2; i++)
						if (new_hw_mask & 1 << i)
							w++;
					if (w > cfg.rd_ports[pidx].def->max_rd_wide_log2) {
						goto hw_bit_failed;
					}
				}
				// Bit ok, commit.
				hard_wide_mask = new_hw_mask;
				hard_wide_num++;
			}
bw_done:;
		}
		log_assert(got_config);
	}
}

void MemMapping::prune_post_geom() {
	std::vector<bool> keep;
	dict<std::string, int> rsrc;
	for (int i = 0; i < GetSize(cfgs); i++) {
		auto &cfg = cfgs[i];
		std::string key = cfg.def->resource_name;
		if (key.empty()) {
			switch (cfg.def->kind) {
				case RamKind::Distributed:
					key = "[distributed]";
					break;
				case RamKind::Block:
					key = "[block]";
					break;
				case RamKind::Huge:
					key = "[huge]";
					break;
				default:
					break;
			}
		}
		auto it = rsrc.find(key);
		if (it == rsrc.end()) {
			rsrc[key] = i;
			keep.push_back(true);
		} else {
			auto &ocfg = cfgs[it->second];
			if (cfg.cost < ocfg.cost) {
				keep[it->second] = false;
				it->second = i;
				keep.push_back(true);
			} else {
				keep.push_back(false);
			}
		}
	}
	MemConfigs new_cfgs;
	for (int i = 0; i < GetSize(cfgs); i++)
		if (keep[i])
			new_cfgs.push_back(cfgs[i]);
	cfgs = new_cfgs;
}

Swizzle gen_swizzle(const Mem &mem, const MemConfig &cfg, int sw_wide_log2, int hw_wide_log2) {
	Swizzle res;

	std::vector<int> emu_wide_bits;
	std::vector<int> hard_wide_bits;
	for (int i = 0; i < ceil_log2(mem.size); i++) {
		if (cfg.emu_wide_mask & 1 << i)
			emu_wide_bits.push_back(i);
		else if (GetSize(hard_wide_bits) < hw_wide_log2 - cfg.base_width_log2)
			hard_wide_bits.push_back(i);
	}
	for (int x : hard_wide_bits)
		if (x >= sw_wide_log2)
			res.addr_mux_bits.push_back(x);
	for (int x : emu_wide_bits)
		if (x >= sw_wide_log2)
			res.addr_mux_bits.push_back(x);

	res.addr_shift = cfg.def->abits - cfg.base_width_log2 + GetSize(emu_wide_bits);
	res.addr_start = mem.start_offset & ~((1 << res.addr_shift) - 1);
	res.addr_end = ((mem.start_offset + mem.size - 1) | ((1 << res.addr_shift) - 1)) + 1;
	int hnum = (res.addr_end - res.addr_start) >> res.addr_shift;
	int unit_width = cfg.def->dbits[cfg.unit_width_log2];

	for (int rd = 0; rd < cfg.repl_d; rd++) {
		std::vector<SwizzleBit> bits(cfg.def->dbits[hw_wide_log2]);
		for (auto &bit: bits)
			bit.valid = false;
		res.bits.push_back(bits);
	}

	for (int hi = 0; hi < hnum; hi++) {
		for (int ewi = 0; ewi < (1 << GetSize(emu_wide_bits)); ewi++) {
			for (int hwi = 0; hwi < (1 << GetSize(hard_wide_bits)); hwi++) {
				int mux_idx = 0;
				int sub = 0;
				int mib = 0;
				int hbit_base = 0;
				for (int i = 0; i < GetSize(hard_wide_bits); i++) {
					if (hard_wide_bits[i] < sw_wide_log2) {
						if (hwi & 1 << i)
							sub |= 1 << hard_wide_bits[i];
					} else {
						if (hwi & 1 << i)
							mux_idx |= 1 << mib;
						mib++;
					}
					if (hwi & 1 << i)
						hbit_base += cfg.def->dbits[i + cfg.base_width_log2];
				}
				for (int i = 0; i < GetSize(emu_wide_bits); i++) {
					if (emu_wide_bits[i] < sw_wide_log2) {
						if (ewi & 1 << i)
							sub |= 1 << emu_wide_bits[i];
					} else {
						if (ewi & 1 << i)
							mux_idx |= 1 << mib;
						mib++;
					}
				}
				mux_idx |= hi << mib;
				int addr = res.addr_start + (hi << res.addr_shift);
				for (int i = 0; i < GetSize(res.addr_mux_bits); i++)
					if (mux_idx & 1 << i)
						addr += 1 << res.addr_mux_bits[i];
				for (int bit = 0; bit < GetSize(cfg.swizzle); bit++) {
					if (cfg.swizzle[bit] == -1)
						continue;
					int rbit = bit + GetSize(cfg.swizzle) * (ewi + (hi << GetSize(emu_wide_bits)));
					int rep = rbit / unit_width;
					int hbit = hbit_base + rbit % unit_width;
					auto &swz = res.bits[rep][hbit];
					swz.valid = true;
					swz.addr = addr;
					swz.mux_idx = mux_idx;
					swz.bit = cfg.swizzle[bit] + sub * mem.width;
				}
			}
		}
	}

	return res;
}

void clean_undef(std::vector<State> &val) {
	for (auto &bit : val)
		if (bit != State::S1)
			bit = State::S0;
}

std::vector<SigSpec> generate_demux(Mem &mem, int wpidx, const Swizzle &swz) {
	auto &port = mem.wr_ports[wpidx];
	std::vector<SigSpec> res;
	int hi_bits = ceil_log2(swz.addr_end - swz.addr_start) - swz.addr_shift;
	auto compressed = port.compress_en();
	SigSpec sig_a = compressed.first;
	SigSpec addr = port.addr;
	if (GetSize(addr) > hi_bits + swz.addr_shift) {
		int lo = mem.start_offset;
		int hi = mem.start_offset + mem.size;
		int bits = ceil_log2(hi);
		for (int i = 0; i < bits; i++) {
			int new_lo = lo;
			if (lo & 1 << i)
				new_lo -= 1 << i;
			int new_hi = hi;
			if (hi & 1 << i)
				new_hi += 1 << i;
			if (new_hi - new_lo > (1 << (hi_bits + swz.addr_shift)))
				break;
			lo = new_lo;
			hi = new_hi;
		}
		SigSpec in_range = mem.module->And(NEW_ID, mem.module->Ge(NEW_ID, addr, lo), mem.module->Lt(NEW_ID, addr, hi));
		sig_a = mem.module->Mux(NEW_ID, Const(State::S0, GetSize(sig_a)), sig_a, in_range);
	}
	addr.extend_u0(swz.addr_shift + hi_bits, false);
	SigSpec sig_s;
	for (int x : swz.addr_mux_bits)
		sig_s.append(addr[x]);
	for (int i = 0; i < hi_bits; i++)
		sig_s.append(addr[swz.addr_shift + i]);
	SigSpec sig_y;
	if (GetSize(sig_s) == 0)
		sig_y = sig_a;
	else
		sig_y = mem.module->Demux(NEW_ID, sig_a, sig_s);
	for (int i = 0; i < ((swz.addr_end - swz.addr_start) >> swz.addr_shift); i++) {
		for (int j = 0; j < (1 << GetSize(swz.addr_mux_bits)); j++) {
			int hi = ((swz.addr_start >> swz.addr_shift) + i) & ((1 << hi_bits) - 1);
			int pos = (hi << GetSize(swz.addr_mux_bits) | j) * GetSize(sig_a);
			res.push_back(port.decompress_en(compressed.second, sig_y.extract(pos, GetSize(sig_a))));
		}
	}
	return res;
}

std::vector<SigSpec> generate_mux(Mem &mem, int rpidx, const Swizzle &swz) {
	auto &port = mem.rd_ports[rpidx];
	std::vector<SigSpec> res;
	int hi_bits = ceil_log2(swz.addr_end - swz.addr_start) - swz.addr_shift;
	SigSpec sig_s;
	SigSpec addr = port.addr;
	addr.extend_u0(swz.addr_shift + hi_bits, false);
	for (int x : swz.addr_mux_bits)
		sig_s.append(addr[x]);
	for (int i = 0; i < hi_bits; i++)
		sig_s.append(addr[swz.addr_shift + i]);
	if (GetSize(sig_s) == 0) {
		return {port.data};
	}
	if (port.clk_enable) {
		SigSpec new_sig_s = mem.module->addWire(NEW_ID, GetSize(sig_s));
		mem.module->addDffe(NEW_ID, port.clk, port.en, sig_s, new_sig_s, port.clk_polarity);
		sig_s = new_sig_s;
	}
	SigSpec sig_a = Const(State::Sx, GetSize(port.data) << hi_bits << GetSize(swz.addr_mux_bits));
	for (int i = 0; i < ((swz.addr_end - swz.addr_start) >> swz.addr_shift); i++) {
		for (int j = 0; j < (1 << GetSize(swz.addr_mux_bits)); j++) {
			SigSpec sig = mem.module->addWire(NEW_ID, GetSize(port.data));
			int hi = ((swz.addr_start >> swz.addr_shift) + i) & ((1 << hi_bits) - 1);
			int pos = (hi << GetSize(swz.addr_mux_bits) | j) * GetSize(port.data);
			for (int k = 0; k < GetSize(port.data); k++)
				sig_a[pos + k] = sig[k];
			res.push_back(sig);
		}
	}
	mem.module->addBmux(NEW_ID, sig_a, sig_s, port.data);
	return res;
}

void MemMapping::emit_port(const MemConfig &cfg, std::vector<Cell*> &cells, const PortVariant &pdef, const char *name, int wpidx, int rpidx, const std::vector<int> &hw_addr_swizzle) {
	for (auto &it: pdef.options)
		for (auto cell: cells)
			cell->setParam(stringf("\\PORT_%s_OPTION_%s", name, it.first.c_str()), it.second);
	SigSpec addr = Const(State::Sx, cfg.def->abits);
	int wide_log2 = 0, wr_wide_log2 = 0, rd_wide_log2 = 0;
	SigSpec clk = State::S0;
	SigSpec clk_en = State::S0;
	bool clk_pol = true;
	if (wpidx != -1) {
		auto &wport = mem.wr_ports[wpidx];
		clk = wport.clk;
		clk_pol = wport.clk_polarity;
		addr = wport.addr;
		wide_log2 = wr_wide_log2 = wport.wide_log2;
		if (rpidx != -1) {
			auto &rport = mem.rd_ports[rpidx];
			auto &rpcfg = cfg.rd_ports[rpidx];
			rd_wide_log2 = rport.wide_log2;
			if (rd_wide_log2 > wr_wide_log2)
				wide_log2 = rd_wide_log2;
			else
				addr = rport.addr;
			if (pdef.clk_en) {
				if (rpcfg.rd_en_to_clk_en) {
					if (pdef.rdwr == RdWrKind::NoChange) {
						clk_en = mem.module->Or(NEW_ID, rport.en, mem.module->ReduceOr(NEW_ID, wport.en));
					} else {
						clk_en = rport.en;
					}
				} else {
					clk_en = State::S1;
				}
			}
		} else {
			if (pdef.clk_en)
				clk_en = State::S1;
		}
	} else if (rpidx != -1) {
		auto &rport = mem.rd_ports[rpidx];
		auto &rpcfg = cfg.rd_ports[rpidx];
		if (rport.clk_enable) {
			clk = rport.clk;
			clk_pol = rport.clk_polarity;
		}
		addr = rport.addr;
		wide_log2 = rd_wide_log2 = rport.wide_log2;
		if (pdef.clk_en) {
			if (rpcfg.rd_en_to_clk_en)
				clk_en = rport.en;
			else
				clk_en = State::S1;
		}

	}
	addr = worker.sigmap_xmux(addr);
	if (pdef.kind != PortKind::Ar) {
		switch (pdef.clk_pol) {
			case ClkPolKind::Posedge:
				if (!clk_pol)
					clk = mem.module->Not(NEW_ID, clk);
				break;
			case ClkPolKind::Negedge:
				if (clk_pol)
					clk = mem.module->Not(NEW_ID, clk);
				break;
			case ClkPolKind::Anyedge:
				for (auto cell: cells)
					cell->setParam(stringf("\\PORT_%s_CLK_POL", name), clk_pol);
		}
		for (auto cell: cells) {
			cell->setPort(stringf("\\PORT_%s_CLK", name), clk);
			if (pdef.clk_en)
				cell->setPort(stringf("\\PORT_%s_CLK_EN", name), clk_en);
		}
	}

	// Width determination.
	if (pdef.width_tied) {
		rd_wide_log2 = wr_wide_log2 = wide_log2;
	}
	int hw_wr_wide_log2 = cfg.base_width_log2;
	for (int i = 0; i < wr_wide_log2; i++)
		if (cfg.hard_wide_mask & (1 << i))
			hw_wr_wide_log2++;
	if (hw_wr_wide_log2 < pdef.min_wr_wide_log2)
		hw_wr_wide_log2 = pdef.min_wr_wide_log2;
	if (hw_wr_wide_log2 > pdef.max_wr_wide_log2)
		hw_wr_wide_log2 = pdef.max_wr_wide_log2;
	int hw_rd_wide_log2 = cfg.base_width_log2;
	for (int i = 0; i < rd_wide_log2; i++)
		if (cfg.hard_wide_mask & (1 << i))
			hw_rd_wide_log2++;
	if (hw_rd_wide_log2 < pdef.min_rd_wide_log2)
		hw_rd_wide_log2 = pdef.min_rd_wide_log2;
	if (hw_rd_wide_log2 > pdef.max_rd_wide_log2)
		hw_rd_wide_log2 = pdef.max_rd_wide_log2;
	if (pdef.width_tied) {
		// For unused ports, pick max available width,
		// in case narrow ports require disabling parity
		// bits etc.
		if (wpidx == -1 && rpidx == -1) {
			hw_wr_wide_log2 = pdef.max_wr_wide_log2;
			hw_rd_wide_log2 = pdef.max_rd_wide_log2;
		}
	} else {
		if (wpidx == -1)
			hw_wr_wide_log2 = pdef.max_wr_wide_log2;
		if (rpidx == -1)
			hw_rd_wide_log2 = pdef.max_rd_wide_log2;
	}
	if (cfg.def->width_mode == WidthMode::PerPort) {
		for (auto cell: cells) {
			if (pdef.width_tied) {
				cell->setParam(stringf("\\PORT_%s_WIDTH", name), cfg.def->dbits[hw_wr_wide_log2]);
			} else {
				if (pdef.kind != PortKind::Ar && pdef.kind != PortKind::Sr)
					cell->setParam(stringf("\\PORT_%s_WR_WIDTH", name), cfg.def->dbits[hw_wr_wide_log2]);
				if (pdef.kind != PortKind::Sw)
					cell->setParam(stringf("\\PORT_%s_RD_WIDTH", name), cfg.def->dbits[hw_rd_wide_log2]);
			}
		}
	}

	// Address determination.
	SigSpec hw_addr;
	for (int x: hw_addr_swizzle) {
		if (x == -1 || x >= GetSize(addr))
			hw_addr.append(State::S0);
		else
			hw_addr.append(addr[x]);
	}
	for (int i = 0; i < hw_wr_wide_log2 && i < hw_rd_wide_log2; i++)
		hw_addr[i] = State::S0;
	for (auto cell: cells)
		cell->setPort(stringf("\\PORT_%s_ADDR", name), hw_addr);

	// Write part.
	if (pdef.kind != PortKind::Ar && pdef.kind != PortKind::Sr) {
		int width = cfg.def->dbits[hw_wr_wide_log2];
		int effective_byte = cfg.def->byte;
		if (effective_byte == 0 || effective_byte > width)
			effective_byte = width;
		if (wpidx != -1) {
			auto &wport = mem.wr_ports[wpidx];
			Swizzle port_swz = gen_swizzle(mem, cfg, wport.wide_log2, hw_wr_wide_log2);
			std::vector<SigSpec> big_wren = generate_demux(mem, wpidx, port_swz);
			for (int rd = 0; rd < cfg.repl_d; rd++) {
				auto cell = cells[rd];
				SigSpec hw_wdata;
				SigSpec hw_wren;
				for (auto &bit : port_swz.bits[rd]) {
					if (!bit.valid) {
						hw_wdata.append(State::Sx);
					} else {
						hw_wdata.append(wport.data[bit.bit]);
					}
				}
				for (int i = 0; i < GetSize(port_swz.bits[rd]); i += effective_byte) {
					auto &bit = port_swz.bits[rd][i];
					if (!bit.valid) {
						hw_wren.append(State::S0);
					} else {
						hw_wren.append(big_wren[bit.mux_idx][bit.bit]);
					}
				}
				cell->setPort(stringf("\\PORT_%s_WR_DATA", name), hw_wdata);
				if (pdef.wrbe_separate) {
					// TODO make some use of it
					SigSpec en = mem.module->ReduceOr(NEW_ID, hw_wren);
					cell->setPort(stringf("\\PORT_%s_WR_EN", name), en);
					cell->setPort(stringf("\\PORT_%s_WR_BE", name), hw_wren);
					if (cfg.def->width_mode != WidthMode::Single)
						cell->setParam(stringf("\\PORT_%s_WR_BE_WIDTH", name), GetSize(hw_wren));
				} else {
					cell->setPort(stringf("\\PORT_%s_WR_EN", name), hw_wren);
					if (cfg.def->byte != 0 && cfg.def->width_mode != WidthMode::Single)
						cell->setParam(stringf("\\PORT_%s_WR_EN_WIDTH", name), GetSize(hw_wren));
				}
			}
		} else {
			for (auto cell: cells) {
				cell->setPort(stringf("\\PORT_%s_WR_DATA", name), Const(State::Sx, width));
				SigSpec hw_wren = Const(State::S0, width / effective_byte);
				if (pdef.wrbe_separate) {
					cell->setPort(stringf("\\PORT_%s_WR_EN", name), State::S0);
					cell->setPort(stringf("\\PORT_%s_WR_BE", name), hw_wren);
					if (cfg.def->width_mode != WidthMode::Single)
						cell->setParam(stringf("\\PORT_%s_WR_BE_WIDTH", name), GetSize(hw_wren));
				} else {
					cell->setPort(stringf("\\PORT_%s_WR_EN", name), hw_wren);
					if (cfg.def->byte != 0 && cfg.def->width_mode != WidthMode::Single)
						cell->setParam(stringf("\\PORT_%s_WR_EN_WIDTH", name), GetSize(hw_wren));
				}
			}
		}
	}

	// Read part.
	if (pdef.kind != PortKind::Sw) {
		int width = cfg.def->dbits[hw_rd_wide_log2];
		if (rpidx != -1) {
			auto &rport = mem.rd_ports[rpidx];
			auto &rpcfg = cfg.rd_ports[rpidx];
			Swizzle port_swz = gen_swizzle(mem, cfg, rport.wide_log2, hw_rd_wide_log2);
			std::vector<SigSpec> big_rdata = generate_mux(mem, rpidx, port_swz);
			for (int rd = 0; rd < cfg.repl_d; rd++) {
				auto cell = cells[rd];
				if (pdef.kind == PortKind::Sr || pdef.kind == PortKind::Srsw) {
					if (pdef.rd_en)
						cell->setPort(stringf("\\PORT_%s_RD_EN", name), rpcfg.rd_en_to_clk_en ? State::S1 : rport.en);
					if (pdef.rdarstval != ResetValKind::None)
						cell->setPort(stringf("\\PORT_%s_RD_ARST", name), rport.arst);
					if (pdef.rdsrstval != ResetValKind::None)
						cell->setPort(stringf("\\PORT_%s_RD_SRST", name), rport.srst);
					if (pdef.rdinitval == ResetValKind::Any || pdef.rdinitval == ResetValKind::NoUndef) {
						Const val = rport.init_value;
						if (pdef.rdarstval == ResetValKind::Init && rport.arst != State::S0) {
							log_assert(val.is_fully_undef() || val == rport.arst_value);
							val = rport.arst_value;
						}
						if (pdef.rdsrstval == ResetValKind::Init && rport.srst != State::S0) {
							log_assert(val.is_fully_undef() || val == rport.srst_value);
							val = rport.srst_value;
						}
						std::vector<State> hw_val;
						for (auto &bit : port_swz.bits[rd]) {
							if (!bit.valid) {
								hw_val.push_back(State::Sx);
							} else {
								hw_val.push_back(val.bits[bit.bit]);
							}
						}
						if (pdef.rdinitval == ResetValKind::NoUndef)
							clean_undef(hw_val);
						cell->setParam(stringf("\\PORT_%s_RD_INIT_VALUE", name), hw_val);
					}
					if (pdef.rdarstval == ResetValKind::Any || pdef.rdarstval == ResetValKind::NoUndef) {
						std::vector<State> hw_val;
						for (auto &bit : port_swz.bits[rd]) {
							if (!bit.valid) {
								hw_val.push_back(State::Sx);
							} else {
								hw_val.push_back(rport.arst_value.bits[bit.bit]);
							}
						}
						if (pdef.rdarstval == ResetValKind::NoUndef)
							clean_undef(hw_val);
						cell->setParam(stringf("\\PORT_%s_RD_ARST_VALUE", name), hw_val);
					}
					if (pdef.rdsrstval == ResetValKind::Any || pdef.rdsrstval == ResetValKind::NoUndef) {
						std::vector<State> hw_val;
						for (auto &bit : port_swz.bits[rd]) {
							if (!bit.valid) {
								hw_val.push_back(State::Sx);
							} else {
								hw_val.push_back(rport.srst_value.bits[bit.bit]);
							}
						}
						if (pdef.rdsrstval == ResetValKind::NoUndef)
							clean_undef(hw_val);
						cell->setParam(stringf("\\PORT_%s_RD_SRST_VALUE", name), hw_val);
					}
				}
				SigSpec hw_rdata = mem.module->addWire(NEW_ID, width);
				cell->setPort(stringf("\\PORT_%s_RD_DATA", name), hw_rdata);
				SigSpec lhs;
				SigSpec rhs;
				for (int i = 0; i < GetSize(hw_rdata); i++) {
					auto &bit = port_swz.bits[rd][i];
					if (bit.valid) {
						lhs.append(big_rdata[bit.mux_idx][bit.bit]);
						rhs.append(hw_rdata[i]);
					}
				}
				mem.module->connect(lhs, rhs);
			}
		} else {
			for (auto cell: cells) {
				if (pdef.kind == PortKind::Sr || pdef.kind == PortKind::Srsw) {
					if (pdef.rd_en)
						cell->setPort(stringf("\\PORT_%s_RD_EN", name), State::S0);
					if (pdef.rdarstval != ResetValKind::None)
						cell->setPort(stringf("\\PORT_%s_RD_ARST", name), State::S0);
					if (pdef.rdsrstval != ResetValKind::None)
						cell->setPort(stringf("\\PORT_%s_RD_SRST", name), State::S0);
					if (pdef.rdinitval == ResetValKind::Any)
						cell->setParam(stringf("\\PORT_%s_RD_INIT_VALUE", name), Const(State::Sx, width));
					else if (pdef.rdinitval == ResetValKind::NoUndef)
						cell->setParam(stringf("\\PORT_%s_RD_INIT_VALUE", name), Const(State::S0, width));
					if (pdef.rdarstval == ResetValKind::Any)
						cell->setParam(stringf("\\PORT_%s_RD_ARST_VALUE", name), Const(State::Sx, width));
					else if (pdef.rdarstval == ResetValKind::NoUndef)
						cell->setParam(stringf("\\PORT_%s_RD_ARST_VALUE", name), Const(State::S0, width));
					if (pdef.rdsrstval == ResetValKind::Any)
						cell->setParam(stringf("\\PORT_%s_RD_SRST_VALUE", name), Const(State::Sx, width));
					else if (pdef.rdsrstval == ResetValKind::NoUndef)
						cell->setParam(stringf("\\PORT_%s_RD_SRST_VALUE", name), Const(State::S0, width));
				}
				SigSpec hw_rdata = mem.module->addWire(NEW_ID, width);
				cell->setPort(stringf("\\PORT_%s_RD_DATA", name), hw_rdata);
			}
		}
	}
}

void MemMapping::emit(const MemConfig &cfg) {
	log("mapping memory %s.%s via %s\n", log_id(mem.module->name), log_id(mem.memid), log_id(cfg.def->id));
	// First, handle emulations.
	if (cfg.emu_read_first)
		mem.emulate_read_first(&worker.initvals);
	for (int pidx = 0; pidx < GetSize(mem.rd_ports); pidx++) {
		auto &pcfg = cfg.rd_ports[pidx];
		auto &port = mem.rd_ports[pidx];
		if (pcfg.emu_sync)
			mem.extract_rdff(pidx, &worker.initvals);
		else if (pcfg.emu_en)
			mem.emulate_rden(pidx, &worker.initvals);
		else {
			if (pcfg.emu_srst_en_prio) {
				if (port.ce_over_srst)
					mem.emulate_rd_ce_over_srst(pidx);
				else
					mem.emulate_rd_srst_over_ce(pidx);
			}
			mem.emulate_reset(pidx, pcfg.emu_init, pcfg.emu_arst, pcfg.emu_srst, &worker.initvals);
		}
	}
	for (int pidx = 0; pidx < GetSize(mem.wr_ports); pidx++) {
		auto &pcfg = cfg.wr_ports[pidx];
		for (int opidx: pcfg.emu_prio) {
			mem.emulate_priority(opidx, pidx, &worker.initvals);
		}
	}
	for (int pidx = 0; pidx < GetSize(mem.rd_ports); pidx++) {
		auto &port = mem.rd_ports[pidx];
		auto &pcfg = cfg.rd_ports[pidx];
		for (int opidx: pcfg.emu_trans) {
			// The port may no longer be transparent due to transparency being
			// nuked as part of emu_sync or emu_prio.
			if (port.transparency_mask[opidx])
				mem.emulate_transparency(opidx, pidx, &worker.initvals);
		}
	}

	// tgt (repl, port group, port) -> mem (wr port, rd port), where -1 means no port.
	std::vector<std::vector<std::vector<std::pair<int, int>>>> ports(cfg.repl_port);
	for (int i = 0; i < cfg.repl_port; i++)
		ports[i].resize(cfg.def->port_groups.size());
	for (int i = 0; i < GetSize(cfg.wr_ports); i++) {
		auto &pcfg = cfg.wr_ports[i];
		for (int j = 0; j < cfg.repl_port; j++) {
			if (j == 0) {
				ports[j][pcfg.port_group].push_back({i, pcfg.rd_port});
			} else {
				ports[j][pcfg.port_group].push_back({i, -1});
			}
		}
	}
	for (int i = 0; i < GetSize(cfg.rd_ports); i++) {
		auto &pcfg = cfg.rd_ports[i];
		if (pcfg.wr_port != -1)
			continue;
		auto &pg = cfg.def->port_groups[pcfg.port_group];
		int j = 0;
		while (GetSize(ports[j][pcfg.port_group]) >= GetSize(pg.names))
			j++;
		ports[j][pcfg.port_group].push_back({-1, i});
	}

	Swizzle init_swz = gen_swizzle(mem, cfg, 0, GetSize(cfg.def->dbits) - 1);
	Const init_data = mem.get_init_data();

	std::vector<int> hw_addr_swizzle;
	for (int i = 0; i < cfg.base_width_log2; i++)
		hw_addr_swizzle.push_back(-1);
	for (int i = 0; i < init_swz.addr_shift; i++)
		if (!(cfg.emu_wide_mask & 1 << i))
			hw_addr_swizzle.push_back(i);
	log_assert(GetSize(hw_addr_swizzle) == cfg.def->abits);

	for (int rp = 0; rp < cfg.repl_port; rp++) {
		std::vector<Cell *> cells;
		for (int rd = 0; rd < cfg.repl_d; rd++) {
			Cell *cell = mem.module->addCell(stringf("%s.%d.%d", mem.memid.c_str(), rp, rd), cfg.def->id);
			if (cfg.def->width_mode == WidthMode::Global)
				cell->setParam(ID::WIDTH, cfg.def->dbits[cfg.base_width_log2]);
			if (cfg.def->widthscale) {
				std::vector<State> val;
				for (auto &bit: init_swz.bits[rd])
					val.push_back(bit.valid ? State::S1 : State::S0);
				cell->setParam(ID::BITS_USED, val);
			}
			for (auto &it: cfg.def->options)
				cell->setParam(stringf("\\OPTION_%s", it.first.c_str()), it.second);
			for (int i = 0; i < GetSize(cfg.def->shared_clocks); i++) {
				auto &cdef = cfg.def->shared_clocks[i];
				auto &ccfg = cfg.shared_clocks[i];
				if (cdef.anyedge) {
					cell->setParam(stringf("\\CLK_%s_POL", cdef.name.c_str()), ccfg.used ? ccfg.polarity : true);
					cell->setPort(stringf("\\CLK_%s", cdef.name.c_str()), ccfg.used ? ccfg.clk : State::S0);
				} else {
					SigSpec sig = ccfg.used ? ccfg.clk : State::S0;
					if (ccfg.used && ccfg.invert)
						sig = mem.module->Not(NEW_ID, sig);
					cell->setPort(stringf("\\CLK_%s", cdef.name.c_str()), sig);
				}
			}
			if (cfg.def->init == MemoryInitKind::Any || cfg.def->init == MemoryInitKind::NoUndef) {
				std::vector<State> initval;
				for (int hwa = 0; hwa < (1 << cfg.def->abits); hwa += 1 << (GetSize(cfg.def->dbits) - 1)) {
					for (auto &bit: init_swz.bits[rd]) {
						if (!bit.valid) {
							initval.push_back(State::Sx);
						} else {
							int addr = bit.addr;
							for (int i = GetSize(cfg.def->dbits) - 1; i < cfg.def->abits; i++)
								if (hwa & 1 << i)
									addr += 1 << hw_addr_swizzle[i];
							if (addr >= mem.start_offset && addr < mem.start_offset + mem.size)
								initval.push_back(init_data.bits[(addr - mem.start_offset) * mem.width + bit.bit]);
							else
								initval.push_back(State::Sx);
						}
					}
				}
				if (cfg.def->init == MemoryInitKind::NoUndef)
					clean_undef(initval);
				cell->setParam(ID::INIT, initval);
			}
			cells.push_back(cell);
		}
		for (int pgi = 0; pgi < GetSize(cfg.def->port_groups); pgi++) {
			auto &pg = cfg.def->port_groups[pgi];
			for (int pi = 0; pi < GetSize(pg.names); pi++) {
				bool used = pi < GetSize(ports[rp][pgi]);
				bool used_r = false;
				bool used_w = false;
				if (used) {
					auto &pd = ports[rp][pgi][pi];
					const PortVariant *pdef;
					if (pd.first != -1)
						pdef = cfg.wr_ports[pd.first].def;
					else
						pdef = cfg.rd_ports[pd.second].def;
					used_w = pd.first != -1;
					used_r = pd.second != -1;
					emit_port(cfg, cells, *pdef, pg.names[pi].c_str(), pd.first, pd.second, hw_addr_swizzle);
				} else {
					emit_port(cfg, cells, pg.variants[0], pg.names[pi].c_str(), -1, -1, hw_addr_swizzle);
				}
				if (pg.optional)
					for (auto cell: cells)
						cell->setParam(stringf("\\PORT_%s_USED", pg.names[pi].c_str()), used);
				if (pg.optional_rw)
					for (auto cell: cells) {
						cell->setParam(stringf("\\PORT_%s_RD_USED", pg.names[pi].c_str()), used_r);
						cell->setParam(stringf("\\PORT_%s_WR_USED", pg.names[pi].c_str()), used_w);
					}
			}
		}
	}
	mem.remove();
}

struct MemoryLibMapPass : public Pass {
	MemoryLibMapPass() : Pass("memory_libmap", "map memories to cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_libmap -lib <library_file> [-D <condition>] [selection]\n");
		log("\n");
		log("This pass takes a description of available RAM cell types and maps\n");
		log("all selected memories to one of them, or leaves them to be mapped to FFs.\n");
		log("\n");
		log("  -lib <library_file>\n");
		log("    Selects a library file containing RAM cell definitions. This option\n");
		log("    can be passed more than once to select multiple libraries.\n");
		log("    See passes/memory/memlib.md for description of the library format.\n");
		log("\n");
		log("  -D <condition>\n");
		log("    Enables a condition that can be checked within the library file\n");
		log("    to eg. select between slightly different hardware variants.\n");
		log("    This option can be passed any number of times.\n");
		log("\n");
		log("  -logic-cost-rom <num>\n");
		log("  -logic-cost-ram <num>\n");
		log("    Sets the cost of a single bit for memory lowered to soft logic.\n");
		log("\n");
		log("  -no-auto-distributed\n");
		log("  -no-auto-block\n");
		log("  -no-auto-huge\n");
		log("    Disables automatic mapping of given kind of RAMs.  Manual mapping\n");
		log("    (using ram_style or other attributes) is still supported.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::vector<std::string> lib_files;
		pool<std::string> defines;
		PassOptions opts;
		opts.no_auto_distributed = false;
		opts.no_auto_block = false;
		opts.no_auto_huge = false;
		opts.logic_cost_ram = 1.0;
		opts.logic_cost_rom = 1.0/16.0;
		log_header(design, "Executing MEMORY_LIBMAP pass (mapping memories to cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-lib" && argidx+1 < args.size()) {
				lib_files.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-D" && argidx+1 < args.size()) {
				defines.insert(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-no-auto-distributed") {
				opts.no_auto_distributed = true;
				continue;
			}
			if (args[argidx] == "-no-auto-block") {
				opts.no_auto_block = true;
				continue;
			}
			if (args[argidx] == "-no-auto-huge") {
				opts.no_auto_huge = true;
				continue;
			}
			if (args[argidx] == "-logic-cost-rom" && argidx+1 < args.size()) {
				opts.logic_cost_rom = strtod(args[++argidx].c_str(), nullptr);
				continue;
			}
			if (args[argidx] == "-logic-cost-ram" && argidx+1 < args.size()) {
				opts.logic_cost_ram = strtod(args[++argidx].c_str(), nullptr);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		Library lib = parse_library(lib_files, defines);

		for (auto module : design->selected_modules()) {
			MapWorker worker(module);
			auto mems = Mem::get_selected_memories(module);
			for (auto &mem : mems)
			{
				MemMapping map(worker, mem, lib, opts);
				int idx = -1;
				int best = map.logic_cost;
				if (!map.logic_ok) {
					if (map.cfgs.empty()) {
						log_debug("Rejected candidates for mapping memory %s.%s:\n", log_id(module->name), log_id(mem.memid));
						log_debug("%s", map.rejected_cfg_debug_msgs.c_str());
						log_error("no valid mapping found for memory %s.%s\n", log_id(module->name), log_id(mem.memid));
					}
					idx = 0;
					best = map.cfgs[0].cost;
				}
				for (int i = 0; i < GetSize(map.cfgs); i++) {
					if (map.cfgs[i].cost < best) {
						idx = i;
						best = map.cfgs[i].cost;
					}
				}
				if (idx == -1) {
					log("using FF mapping for memory %s.%s\n", log_id(module->name), log_id(mem.memid));
				} else {
					map.emit(map.cfgs[idx]);
				}
			}
		}
	}
} MemoryLibMapPass;

PRIVATE_NAMESPACE_END
