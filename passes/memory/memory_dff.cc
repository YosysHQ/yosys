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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/modtools.h"
#include "kernel/ffinit.h"
#include "kernel/qcsat.h"
#include "kernel/mem.h"
#include "kernel/ff.h"
#include "kernel/ffmerge.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MuxData {
	int base_idx;
	int size;
	bool is_b;
	SigSpec sig_s;
	std::vector<SigSpec> sig_other;
};

struct PortData {
	bool relevant;
	std::vector<bool> uncollidable_mask;
	std::vector<bool> transparency_mask;
	std::vector<bool> collision_x_mask;
	bool final_transparency;
	bool final_collision_x;
};

// A helper with some caching for transparency-related SAT queries.
// Bound to a single memory read port in the process of being converted
// from async to sync..
struct MemQueryCache
{
	QuickConeSat &qcsat;
	// The memory.
	Mem &mem;
	// The port, still async at this point.
	MemRd &port;
	// The virtual FF that will end up merged into this port.
	FfData &ff;
	// An ezSAT variable that is true when we actually care about the data
	// read from memory (ie. the FF has enable on and is not in reset).
	int port_ren;
	// Some caches.
	dict<std::pair<int, SigBit>, bool> cache_can_collide_rdwr;
	dict<std::tuple<int, int, SigBit, SigBit>, bool> cache_can_collide_together;
	dict<std::tuple<int, SigBit, SigBit, bool>, bool> cache_is_w2rbyp;
	dict<std::tuple<SigBit, bool>, bool> cache_impossible_with_ren;

	MemQueryCache(QuickConeSat &qcsat, Mem &mem, MemRd &port, FfData &ff) : qcsat(qcsat), mem(mem), port(port), ff(ff) {
		// port_ren is an upper bound on when we care about the value fetched
		// from memory this cycle.
		int ren = ezSAT::CONST_TRUE;
		if (ff.has_ce) {
			ren = qcsat.importSigBit(ff.sig_ce);
			if (!ff.pol_ce)
				ren = qcsat.ez->NOT(ren);
		}
		if (ff.has_srst) {
			int nrst = qcsat.importSigBit(ff.sig_srst);
			if (ff.pol_srst)
				nrst = qcsat.ez->NOT(nrst);
			ren = qcsat.ez->AND(ren, nrst);
		}
		port_ren = ren;
	}

	// Returns ezSAT variable that is true iff the two addresses are the same.
	int addr_eq(SigSpec raddr, SigSpec waddr) {
		int abits = std::max(GetSize(raddr), GetSize(waddr));
		raddr.extend_u0(abits);
		waddr.extend_u0(abits);
		return qcsat.ez->vec_eq(qcsat.importSig(raddr), qcsat.importSig(waddr));
	}

	// Returns true if a given write port bit can be active at the same time
	// as this read port and at the same address.
	bool can_collide_rdwr(int widx, SigBit wen) {
		std::pair<int, SigBit> key(widx, wen);
		auto it = cache_can_collide_rdwr.find(key);
		if (it != cache_can_collide_rdwr.end())
			return it->second;
		auto &wport = mem.wr_ports[widx];
		int aeq = addr_eq(port.addr, wport.addr);
		int wen_sat = qcsat.importSigBit(wen);
		qcsat.prepare();
		bool res = qcsat.ez->solve(aeq, wen_sat, port_ren);
		cache_can_collide_rdwr[key] = res;
		return res;
	}

	// Returns true if both given write port bits can be active at the same
	// time as this read port and at the same address (three-way collision).
	bool can_collide_together(int widx1, int widx2, int bitidx) {
		auto &wport1 = mem.wr_ports[widx1];
		auto &wport2 = mem.wr_ports[widx2];
		SigBit wen1 = wport1.en[bitidx];
		SigBit wen2 = wport2.en[bitidx];
		std::tuple<int, int, SigBit, SigBit> key(widx1, widx2, wen1, wen2);
		auto it = cache_can_collide_together.find(key);
		if (it != cache_can_collide_together.end())
			return it->second;
		int aeq1 = addr_eq(port.addr, wport1.addr);
		int aeq2 = addr_eq(port.addr, wport2.addr);
		int wen1_sat = qcsat.importSigBit(wen1);
		int wen2_sat = qcsat.importSigBit(wen2);
		qcsat.prepare();
		bool res = qcsat.ez->solve(wen1_sat, wen2_sat, aeq1, aeq2, port_ren);
		cache_can_collide_together[key] = res;
		return res;
	}

	// Returns true if the given mux selection signal is a valid data-bypass
	// signal in soft transparency logic for a given write port bit.
	bool is_w2rbyp(int widx, SigBit wen, SigBit sel, bool neg_sel) {
		std::tuple<int, SigBit, SigBit, bool> key(widx, wen, sel, neg_sel);
		auto it = cache_is_w2rbyp.find(key);
		if (it != cache_is_w2rbyp.end())
			return it->second;
		auto &wport = mem.wr_ports[widx];
		int aeq = addr_eq(port.addr, wport.addr);
		int wen_sat = qcsat.importSigBit(wen);
		int sel_expected = qcsat.ez->AND(aeq, wen_sat);
		int sel_sat = qcsat.importSigBit(sel);
		if (neg_sel)
			sel_sat = qcsat.ez->NOT(sel_sat);
		qcsat.prepare();
		bool res = !qcsat.ez->solve(port_ren, qcsat.ez->XOR(sel_expected, sel_sat));
		cache_is_w2rbyp[key] = res;
		return res;
	}

	// Returns true if the given mux selection signal can never be true
	// when this port is active.
	bool impossible_with_ren(SigBit sel, bool neg_sel) {
		std::tuple<SigBit, bool> key(sel, neg_sel);
		auto it = cache_impossible_with_ren.find(key);
		if (it != cache_impossible_with_ren.end())
			return it->second;
		int sel_sat = qcsat.importSigBit(sel);
		if (neg_sel)
			sel_sat = qcsat.ez->NOT(sel_sat);
		qcsat.prepare();
		bool res = !qcsat.ez->solve(port_ren, sel_sat);
		cache_impossible_with_ren[key] = res;
		return res;
	}

	// Helper for data_eq: walks up a multiplexer when the value of its
	// sel signal is constant under the assumption that this read port
	// is active and a given other mux sel signal is true.
	bool walk_up_mux_cond(SigBit sel, bool neg_sel, SigBit &bit) {
		auto &drivers = qcsat.modwalker.signal_drivers[qcsat.modwalker.sigmap(bit)];
		if (GetSize(drivers) != 1)
			return false;
		auto driver = *drivers.begin();
		if (!driver.cell->type.in(ID($mux), ID($pmux)))
			return false;
		log_assert(driver.port == ID::Y);
		SigSpec sig_s = driver.cell->getPort(ID::S);
		int sel_sat = qcsat.importSigBit(sel);
		if (neg_sel)
			sel_sat = qcsat.ez->NOT(sel_sat);
		bool all_0 = true;
		int width = driver.cell->parameters.at(ID::WIDTH).as_int();
		for (int i = 0; i < GetSize(sig_s); i++) {
			int sbit = qcsat.importSigBit(sig_s[i]);
			qcsat.prepare();
			if (!qcsat.ez->solve(port_ren, sel_sat, qcsat.ez->NOT(sbit))) {
				bit = driver.cell->getPort(ID::B)[i * width + driver.offset];
				return true;
			}
			if (qcsat.ez->solve(port_ren, sel_sat, sbit))
				all_0 = false;
		}
		if (all_0) {
			bit = driver.cell->getPort(ID::A)[driver.offset];
			return true;
		}
		return false;
	}

	// Returns true if a given data signal is equivalent to another, under
	// the assumption that this read port is active and a given mux sel signal
	// is true.  Used to match transparency logic data with write port data.
	// The walk_up_mux_cond part is necessary because write ports in yosys
	// tend to be connected to things like (wen ? wdata : 'x).
	bool data_eq(SigBit sel, bool neg_sel, SigBit dbit, SigBit odbit) {
		if (qcsat.modwalker.sigmap(dbit) == qcsat.modwalker.sigmap(odbit))
			return true;
		while (walk_up_mux_cond(sel, neg_sel, dbit));
		while (walk_up_mux_cond(sel, neg_sel, odbit));
		return qcsat.modwalker.sigmap(dbit) == qcsat.modwalker.sigmap(odbit);
	}
};

struct MemoryDffWorker
{
	Module *module;
	ModWalker modwalker;
	FfInitVals initvals;
	FfMergeHelper merger;
	bool flag_no_rw_check;

	MemoryDffWorker(Module *module, bool flag_no_rw_check) : module(module), modwalker(module->design), flag_no_rw_check(flag_no_rw_check)
	{
		modwalker.setup(module);
		initvals.set(&modwalker.sigmap, module);
		merger.set(&initvals, module);
	}

	// Starting from the output of an async read port, as long as the data
	// signal's only user is a mux data signal, passes through the mux
	// and remembers information about it.  Conceptually works on every
	// bit separately, but coalesces the result when possible.
	SigSpec walk_muxes(SigSpec data, std::vector<MuxData> &res) {
		bool did_something;
		do {
			did_something = false;
			int prev_idx = -1;
			Cell *prev_cell = nullptr;
			bool prev_is_b = false;
			for (int i = 0; i < GetSize(data); i++) {
				SigBit bit = modwalker.sigmap(data[i]);
				auto &consumers = modwalker.signal_consumers[bit];
				if (GetSize(consumers) != 1 || modwalker.signal_outputs.count(bit))
					continue;
				auto consumer = *consumers.begin();
				bool is_b;
				if (consumer.cell->type == ID($mux)) {
					if (consumer.port == ID::A) {
						is_b = false;
					} else if (consumer.port == ID::B) {
						is_b = true;
					} else {
						continue;
					}
				} else if (consumer.cell->type == ID($pmux)) {
					if (consumer.port == ID::A) {
						is_b = false;
					} else {
						continue;
					}
				} else {
					continue;
				}
				SigSpec y = consumer.cell->getPort(ID::Y);
				int mux_width = GetSize(y);
				SigBit ybit = y.extract(consumer.offset);
				if (prev_cell != consumer.cell || prev_idx+1 != i || prev_is_b != is_b) {
					MuxData md;
					md.base_idx = i;
					md.size = 0;
					md.is_b = is_b;
					md.sig_s = consumer.cell->getPort(ID::S);
					md.sig_other.resize(GetSize(md.sig_s));
					prev_cell = consumer.cell;
					prev_is_b = is_b;
					res.push_back(md);
				}
				auto &md = res.back();
				md.size++;
				for (int j = 0; j < GetSize(md.sig_s); j++) {
					SigBit obit = consumer.cell->getPort(is_b ? ID::A : ID::B).extract(j * mux_width + consumer.offset);
					md.sig_other[j].append(obit);
				}
				prev_idx = i;
				data[i] = ybit;
				did_something = true;
			}
		} while (did_something);
		return data;
	}

	// Merges FF and possibly soft transparency logic into an asynchronous
	// read port, making it into a synchronous one.
	//
	// There are three moving parts involved here:
	//
	// - the async port, which we start from, whose data port is input to...
	// - an arbitrary chain of $mux and $pmux cells implementing soft transparency
	//   logic (ie. bypassing write port's data iff the write port is active and
	//   writing to the same address as this read port), which in turn feeds...
	// - a final FF
	//
	// The async port and the mux chain are not allowed to have any users that
	// are not part of the above.
	//
	// The algorithm is:
	//
	// 1. Walk through the muxes.
	// 2. Recognize the final FF.
	// 3. Knowing the FF's clock and read enable, make a list of write ports
	//    that we'll run transparency analysis on.
	// 4. For every mux bit, recognize it as one of:
	//    - a transparency bypass mux for some port
	//    - a bypass mux that feeds 'x instead (this will result in collision
	//      don't care behavior being recognized)
	//    - a mux that never selects the other value when read port is active,
	//      and can thus be skipped (this is necessary because this could
	//      be a transparency bypass mux for never-colliding port that other
	//      passes failed to optimize)
	//    - a mux whose other input is 'x, and can thus be skipped
	// 5. When recognizing transparency bypasses, take care to preserve priority
	//    behavior — when two bypasses are sequential muxes on the chain, they
	//    effectively have priority over one another, and the transform can
	//    only be performed when either a) their corresponding write ports
	//    also have priority, or b) there can never be a three-way collision
	//    between the two write ports and the read port.
	// 6. Check consistency of per-bit transparency masks, merge them into
	//    per-port transparency masks
	// 7. If everything went fine in the previous steps, actually perform
	//    the merge.
	void handle_rd_port(Mem &mem, QuickConeSat &qcsat, int idx)
	{
		auto &port = mem.rd_ports[idx];
		log("Checking read port `%s'[%d] in module `%s': ", mem.memid.c_str(), idx, module->name.c_str());

		std::vector<MuxData> muxdata;
		SigSpec data = walk_muxes(port.data, muxdata);
		FfData ff;
		pool<std::pair<Cell *, int>> bits;
		if (!merger.find_output_ff(data, ff, bits)) {
			log("no output FF found.\n");
			return;
		}
		if (!ff.has_clk) {
			log("output latches are not supported.\n");
			return;
		}
		if (ff.has_aload) {
			log("output FF has async load, not supported.\n");
			return;
		}
		if (ff.has_sr) {
			// Latches and FFs with SR are not supported.
			log("output FF has both set and reset, not supported.\n");
			return;
		}

		// Check for no_rw_check
		bool no_rw_check = flag_no_rw_check || mem.get_bool_attribute(ID::no_rw_check);
		for (auto attr: {ID::ram_block, ID::rom_block, ID::ram_style, ID::rom_style, ID::ramstyle, ID::romstyle, ID::syn_ramstyle, ID::syn_romstyle}) {
			if (mem.get_string_attribute(attr) == "no_rw_check") {
				no_rw_check = true;
			}
		}

		// Construct cache.
		MemQueryCache cache(qcsat, mem, port, ff);

		// Prepare information structure about all ports, recognize port bits
		// that can never collide at all and don't need to be checked.
		std::vector<PortData> portdata;
		for (int i = 0; i < GetSize(mem.wr_ports); i++) {
			PortData pd;
			auto &wport = mem.wr_ports[i];
			pd.relevant = true;
			if (!wport.clk_enable)
				pd.relevant = false;
			if (wport.clk != ff.sig_clk)
				pd.relevant = false;
			if (wport.clk_polarity != ff.pol_clk)
				pd.relevant = false;
			// In theory, we *could* support mismatched width
			// ports here.  However, it's not worth it — wide
			// ports are recognized *after* memory_dff in
			// a normal flow.
			if (wport.wide_log2 != port.wide_log2)
				pd.relevant = false;
			pd.uncollidable_mask.resize(GetSize(port.data));
			pd.transparency_mask.resize(GetSize(port.data));
			pd.collision_x_mask.resize(GetSize(port.data));
			if (pd.relevant) {
				// If we got this far, this port is potentially
				// transparent and/or has undefined collision
				// behavior.  Now, for every bit, check if it can
				// ever collide.
				for (int j = 0; j < ff.width; j++) {
					if (!cache.can_collide_rdwr(i, wport.en[j])) {
						pd.uncollidable_mask[j] = true;
						pd.collision_x_mask[j] = true;
					}
					if (no_rw_check)
						pd.collision_x_mask[j] = true;
				}
			}
			portdata.push_back(pd);
		}

		// Now inspect the mux chain.
		for (auto &md : muxdata) {
			// We only mark transparent bits after processing a complete
			// mux, so that the transparency priority validation check
			// below sees transparency information as of previous mux.
			std::vector<std::pair<PortData&, int>> trans_queue;
			for (int sel_idx = 0; sel_idx < GetSize(md.sig_s); sel_idx++) {
				SigBit sbit = md.sig_s[sel_idx];
				SigSpec &odata = md.sig_other[sel_idx];
				for (int bitidx = md.base_idx; bitidx < md.base_idx+md.size; bitidx++) {
					SigBit odbit = odata[bitidx-md.base_idx];
					bool recognized = false;
					for (int pi = 0; pi < GetSize(mem.wr_ports); pi++) {
						auto &pd = portdata[pi];
						auto &wport = mem.wr_ports[pi];
						if (!pd.relevant)
							continue;
						if (pd.uncollidable_mask[bitidx])
							continue;
						bool match = cache.is_w2rbyp(pi, wport.en[bitidx], sbit, md.is_b);
						if (!match)
							continue;
						// If we got here, we recognized this mux sel
						// as valid bypass sel for a given port bit.
						if (odbit == State::Sx) {
							// 'x, mark collision don't care.
							pd.collision_x_mask[bitidx] = true;
							pd.transparency_mask[bitidx] = false;
						} else if (cache.data_eq(sbit, md.is_b, wport.data[bitidx], odbit)) {
							// Correct data value, mark transparency,
							// but only after verifying that priority
							// is fine.
							for (int k = 0; k < GetSize(mem.wr_ports); k++) {
								if (portdata[k].transparency_mask[bitidx]) {
									if (wport.priority_mask[k])
										continue;
									if (!cache.can_collide_together(pi, k, bitidx))
										continue;
									log("FF found, but transparency logic priority doesn't match write priority.\n");
									return;
								}
							}
							recognized = true;
							trans_queue.push_back({pd, bitidx});
							break;
						} else {
							log("FF found, but with a mux data input that doesn't seem to correspond to transparency logic.\n");
							return;
						}
					}
					if (!recognized) {
						// If we haven't positively identified this as
						// a bypass: it's still skippable if the
						// data is 'x, or if the sel cannot actually be
						// active.
						if (odbit == State::Sx)
							continue;
						if (cache.impossible_with_ren(sbit, md.is_b))
							continue;
						log("FF found, but with a mux select that doesn't seem to correspond to transparency logic.\n");
						return;
					}
				}
			}
			// Done with this mux, now actually apply the transparencies.
			for (auto it : trans_queue) {
				it.first.transparency_mask[it.second] = true;
				it.first.collision_x_mask[it.second] = false;
			}
		}

		// Final merging and validation of per-bit masks.
		for (int pi = 0; pi < GetSize(mem.wr_ports); pi++) {
			auto &pd = portdata[pi];
			if (!pd.relevant)
				continue;
			bool trans = false;
			bool non_trans = false;
			for (int i = 0; i < ff.width; i++) {
				if (pd.collision_x_mask[i])
					continue;
				if (pd.transparency_mask[i])
					trans = true;
				else
					non_trans = true;
			}
			if (trans && non_trans) {
				log("FF found, but soft transparency logic is inconsistent for port %d.\n", pi);
				return;
			}
			pd.final_transparency = trans;
			pd.final_collision_x = !trans && !non_trans;
		}

		// OK, it worked.
		log("merging output FF to cell.\n");

		merger.remove_output_ff(bits);
		if (ff.has_ce && !ff.pol_ce)
			ff.sig_ce = module->LogicNot(NEW_ID, ff.sig_ce);
		if (ff.has_arst && !ff.pol_arst)
			ff.sig_arst = module->LogicNot(NEW_ID, ff.sig_arst);
		if (ff.has_srst && !ff.pol_srst)
			ff.sig_srst = module->LogicNot(NEW_ID, ff.sig_srst);
		port.clk = ff.sig_clk;
		port.clk_enable = true;
		port.clk_polarity = ff.pol_clk;
		if (ff.has_ce)
			port.en = ff.sig_ce;
		else
			port.en = State::S1;
		if (ff.has_arst) {
			port.arst = ff.sig_arst;
			port.arst_value = ff.val_arst;
		} else {
			port.arst = State::S0;
		}
		if (ff.has_srst) {
			port.srst = ff.sig_srst;
			port.srst_value = ff.val_srst;
			port.ce_over_srst = ff.ce_over_srst;
		} else {
			port.srst = State::S0;
		}
		port.init_value = ff.val_init;
		port.data = ff.sig_q;
		for (int pi = 0; pi < GetSize(mem.wr_ports); pi++) {
			auto &pd = portdata[pi];
			if (!pd.relevant)
				continue;
			if (pd.final_collision_x) {
				log("    Write port %d: don't care on collision.\n", pi);
				port.collision_x_mask[pi] = true;
			} else if (pd.final_transparency) {
				log("    Write port %d: transparent.\n", pi);
				port.transparency_mask[pi] = true;
			} else {
				log("    Write port %d: non-transparent.\n", pi);
			}
		}
		mem.emit();
	}

	void handle_rd_port_addr(Mem &mem, int idx)
	{
		auto &port = mem.rd_ports[idx];
		log("Checking read port address `%s'[%d] in module `%s': ", mem.memid.c_str(), idx, module->name.c_str());

		FfData ff;
		pool<std::pair<Cell *, int>> bits;
		if (!merger.find_input_ff(port.addr, ff, bits)) {
			log("no address FF found.\n");
			return;
		}
		if (!ff.has_clk) {
			log("address latches are not supported.\n");
			return;
		}
		if (ff.has_aload) {
			log("address FF has async load, not supported.\n");
			return;
		}
		if (ff.has_sr || ff.has_arst) {
			log("address FF has async set and/or reset, not supported.\n");
			return;
		}
		// Trick part: this transform is invalid if the initial
		// value of the FF is fully-defined.  However, we
		// cannot simply reject FFs with any defined init bit,
		// as this is often the result of merging a const bit.
		if (ff.val_init.is_fully_def()) {
			log("address FF has fully-defined init value, not supported.\n");
			return;
		}
		for (int i = 0; i < GetSize(mem.wr_ports); i++) {
			auto &wport = mem.wr_ports[i];
			if (!wport.clk_enable || wport.clk != ff.sig_clk || wport.clk_polarity != ff.pol_clk) {
				log("address FF clock is not compatible with write clock.\n");
				return;
			}
		}
		// Now we're commited to merge it.
		merger.mark_input_ff(bits);
		// If the address FF has enable and/or sync reset, unmap it.
		ff.unmap_ce_srst();
		port.clk = ff.sig_clk;
		port.en = State::S1;
		port.addr = ff.sig_d;
		port.clk_enable = true;
		port.clk_polarity = ff.pol_clk;
		for (int i = 0; i < GetSize(mem.wr_ports); i++)
			port.transparency_mask[i] = true;
		mem.emit();
		log("merged address FF to cell.\n");
	}

	void run()
	{
		std::vector<Mem> memories = Mem::get_selected_memories(module);
		for (auto &mem : memories) {
			QuickConeSat qcsat(modwalker);
			for (int i = 0; i < GetSize(mem.rd_ports); i++) {
				if (!mem.rd_ports[i].clk_enable)
					handle_rd_port(mem, qcsat, i);
			}
		}
		for (auto &mem : memories) {
			for (int i = 0; i < GetSize(mem.rd_ports); i++) {
				if (!mem.rd_ports[i].clk_enable)
					handle_rd_port_addr(mem, i);
			}
		}
	}
};

struct MemoryDffPass : public Pass {
	MemoryDffPass() : Pass("memory_dff", "merge input/output DFFs into memory read ports") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_dff [-no-rw-check] [selection]\n");
		log("\n");
		log("This pass detects DFFs at memory read ports and merges them into the memory\n");
		log("port. I.e. it consumes an asynchronous memory port and the flip-flops at its\n");
		log("interface and yields a synchronous memory port.\n");
		log("\n");
		log("    -no-rw-check\n");
		log("        marks all recognized read ports as \"return don't-care value on\n");
		log("        read/write collision\" (same result as setting the no_rw_check\n");
		log("        attribute on all memories).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool flag_no_rw_check = false;
		log_header(design, "Executing MEMORY_DFF pass (merging $dff cells to $memrd).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-no-rw-check") {
				flag_no_rw_check = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			MemoryDffWorker worker(mod, flag_no_rw_check);
			worker.run();
		}
	}
} MemoryDffPass;

PRIVATE_NAMESPACE_END
