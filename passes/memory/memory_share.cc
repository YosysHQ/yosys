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
#include "kernel/qcsat.h"
#include "kernel/sigtools.h"
#include "kernel/modtools.h"
#include "kernel/mem.h"
#include "kernel/ffinit.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct MemoryShareWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap sigmap, sigmap_xmux;
	ModWalker modwalker;
	FfInitVals initvals;
	bool flag_widen;
	bool flag_sat;

	// --------------------------------------------------
	// Consolidate read ports that read the same address
	// (or close enough to be merged to wide ports)
	// --------------------------------------------------

	// A simple function to detect ports that couldn't possibly collide
	// because of opposite const address bits (simplistic, but enough
	// to fix problems with inferring wide ports).
	bool rdwr_can_collide(Mem &mem, int ridx, int widx) {
		auto &rport = mem.rd_ports[ridx];
		auto &wport = mem.wr_ports[widx];
		for (int i = std::max(rport.wide_log2, wport.wide_log2); i < GetSize(rport.addr) && i < GetSize(wport.addr); i++) {
			if (rport.addr[i] == State::S1 && wport.addr[i] == State::S0)
				return false;
			if (rport.addr[i] == State::S0 && wport.addr[i] == State::S1)
				return false;
		}
		return true;
	}

	bool merge_rst_value(Mem &mem, Const &res, int wide_log2, const Const &src1, int sub1, const Const &src2, int sub2) {
		res = Const(State::Sx, mem.width << wide_log2);
		for (int i = 0; i < GetSize(src1); i++)
			res[i + sub1 * mem.width] = src1[i];
		for (int i = 0; i < GetSize(src2); i++) {
			if (src2[i] == State::Sx)
				continue;
			auto &dst = res[i + sub2 * mem.width];
			if (dst == src2[i])
				continue;
			if (dst != State::Sx)
				return false;
			dst = src2[i];
		}
		return true;
	}

	bool consolidate_rd_by_addr(Mem &mem)
	{
		if (GetSize(mem.rd_ports) <= 1)
			return false;

		log("Consolidating read ports of memory %s.%s by address:\n", log_id(module), log_id(mem.memid));

		bool changed = false;
		int abits = 0;
		for (auto &port: mem.rd_ports) {
			if (GetSize(port.addr) > abits)
				abits = GetSize(port.addr);
		}
		for (int i = 0; i < GetSize(mem.rd_ports); i++)
		{
			auto &port1 = mem.rd_ports[i];
			if (port1.removed)
				continue;
			for (int j = i + 1; j < GetSize(mem.rd_ports); j++)
			{
				auto &port2 = mem.rd_ports[j];
				if (port2.removed)
					continue;
				if (port1.clk_enable != port2.clk_enable)
					continue;
				if (port1.clk_enable) {
					if (port1.clk != port2.clk)
						continue;
					if (port1.clk_polarity != port2.clk_polarity)
						continue;
				}
				if (port1.en != port2.en)
					continue;
				if (port1.arst != port2.arst)
					continue;
				if (port1.srst != port2.srst)
					continue;
				if (port1.ce_over_srst != port2.ce_over_srst)
					continue;
				// If the width of the ports doesn't match, they can still be
				// merged by widening the narrow one.  Check if the conditions
				// hold for that.
				int wide_log2 = std::max(port1.wide_log2, port2.wide_log2);
				SigSpec addr1 = sigmap_xmux(port1.addr);
				SigSpec addr2 = sigmap_xmux(port2.addr);
				addr1.extend_u0(abits);
				addr2.extend_u0(abits);
				if (GetSize(addr1) <= wide_log2)
					continue;
				if (GetSize(addr2) <= wide_log2)
					continue;
				if (!addr1.extract(0, wide_log2).is_fully_const())
					continue;
				if (!addr2.extract(0, wide_log2).is_fully_const())
					continue;
				if (addr1.extract_end(wide_log2) != addr2.extract_end(wide_log2)) {
					// Incompatible addresses after widening.  Last chance — widen both
					// ports by one more bit to merge them.
					if (!flag_widen)
						continue;
					wide_log2++;
					if (addr1.extract_end(wide_log2) != addr2.extract_end(wide_log2))
						continue;
					if (!addr1.extract(0, wide_log2).is_fully_const())
						continue;
					if (!addr2.extract(0, wide_log2).is_fully_const())
						continue;
				}
				// Combine init/reset values.
				SigSpec sub1_c = port1.addr.extract(0, wide_log2);
				log_assert(sub1_c.is_fully_const());
				int sub1 = sub1_c.as_int();
				SigSpec sub2_c = port2.addr.extract(0, wide_log2);
				log_assert(sub2_c.is_fully_const());
				int sub2 = sub2_c.as_int();
				Const init_value, arst_value, srst_value;
				if (!merge_rst_value(mem, init_value, wide_log2, port1.init_value, sub1, port2.init_value, sub2))
					continue;
				if (!merge_rst_value(mem, arst_value, wide_log2, port1.arst_value, sub1, port2.arst_value, sub2))
					continue;
				if (!merge_rst_value(mem, srst_value, wide_log2, port1.srst_value, sub1, port2.srst_value, sub2))
					continue;
				// At this point we are committed to the merge.
				{
					log("  Merging ports %d, %d (address %s).\n", i, j, log_signal(port1.addr));
					port1.addr = addr1;
					port2.addr = addr2;
					mem.prepare_rd_merge(i, j, &initvals);
					mem.widen_prep(wide_log2);
					SigSpec new_data = module->addWire(NEW_ID, mem.width << wide_log2);
					module->connect(port1.data, new_data.extract(sub1 * mem.width, mem.width << port1.wide_log2));
					module->connect(port2.data, new_data.extract(sub2 * mem.width, mem.width << port2.wide_log2));
					for (int k = 0; k < wide_log2; k++)
						port1.addr[k] = State::S0;
					port1.init_value = init_value;
					port1.arst_value = arst_value;
					port1.srst_value = srst_value;
					port1.wide_log2 = wide_log2;
					port1.data = new_data;
					port2.removed = true;
					changed = true;
				}
			}
		}

		if (changed)
			mem.emit();

		return changed;
	}


	// ------------------------------------------------------
	// Consolidate write ports that write to the same address
	// (or close enough to be merged to wide ports)
	// ------------------------------------------------------

	bool consolidate_wr_by_addr(Mem &mem)
	{
		if (GetSize(mem.wr_ports) <= 1)
			return false;

		log("Consolidating write ports of memory %s.%s by address:\n", log_id(module), log_id(mem.memid));

		bool changed = false;
		int abits = 0;
		for (auto &port: mem.wr_ports) {
			if (GetSize(port.addr) > abits)
				abits = GetSize(port.addr);
		}
		for (int i = 0; i < GetSize(mem.wr_ports); i++)
		{
			auto &port1 = mem.wr_ports[i];
			if (port1.removed)
				continue;
			if (!port1.clk_enable)
				continue;
			for (int j = i + 1; j < GetSize(mem.wr_ports); j++)
			{
				auto &port2 = mem.wr_ports[j];
				if (port2.removed)
					continue;
				if (!port2.clk_enable)
					continue;
				if (port1.clk != port2.clk)
					continue;
				if (port1.clk_polarity != port2.clk_polarity)
					continue;
				// If the width of the ports doesn't match, they can still be
				// merged by widening the narrow one.  Check if the conditions
				// hold for that.
				int wide_log2 = std::max(port1.wide_log2, port2.wide_log2);
				SigSpec addr1 = sigmap_xmux(port1.addr);
				SigSpec addr2 = sigmap_xmux(port2.addr);
				addr1.extend_u0(abits);
				addr2.extend_u0(abits);
				if (GetSize(addr1) <= wide_log2)
					continue;
				if (GetSize(addr2) <= wide_log2)
					continue;
				if (!addr1.extract(0, wide_log2).is_fully_const())
					continue;
				if (!addr2.extract(0, wide_log2).is_fully_const())
					continue;
				if (addr1.extract_end(wide_log2) != addr2.extract_end(wide_log2)) {
					// Incompatible addresses after widening.  Last chance — widen both
					// ports by one more bit to merge them.
					if (!flag_widen)
						continue;
					wide_log2++;
					if (addr1.extract_end(wide_log2) != addr2.extract_end(wide_log2))
						continue;
					if (!addr1.extract(0, wide_log2).is_fully_const())
						continue;
					if (!addr2.extract(0, wide_log2).is_fully_const())
						continue;
				}
				log("  Merging ports %d, %d (address %s).\n", i, j, log_signal(addr1));
				port1.addr = addr1;
				port2.addr = addr2;
				mem.prepare_wr_merge(i, j, &initvals);
				mem.widen_wr_port(i, wide_log2);
				mem.widen_wr_port(j, wide_log2);
				int pos = 0;
				while (pos < GetSize(port1.data)) {
					int epos = pos;
					while (epos < GetSize(port1.data) && port1.en[epos] == port1.en[pos] && port2.en[epos] == port2.en[pos])
						epos++;
					int width = epos - pos;
					SigBit new_en;
					if (port2.en[pos] == State::S0) {
						new_en = port1.en[pos];
					} else if (port1.en[pos] == State::S0) {
						port1.data.replace(pos, port2.data.extract(pos, width));
						new_en = port2.en[pos];
					} else {
						port1.data.replace(pos, module->Mux(NEW_ID, port1.data.extract(pos, width), port2.data.extract(pos, width), port2.en[pos]));
						new_en = module->Or(NEW_ID, port1.en[pos], port2.en[pos]);
					}
					for (int k = pos; k < epos; k++)
						port1.en[k] = new_en;
					pos = epos;
				}
				changed = true;
				port2.removed = true;
			}
		}

		if (changed)
			mem.emit();

		return changed;
	}


	// --------------------------------------------------------
	// Consolidate write ports using sat-based resource sharing
	// --------------------------------------------------------

	void consolidate_wr_using_sat(Mem &mem)
	{
		if (GetSize(mem.wr_ports) <= 1)
			return;

		// Get a list of ports that have any chance of being mergeable.

		pool<int> eligible_ports;

		for (int i = 0; i < GetSize(mem.wr_ports); i++) {
			auto &port = mem.wr_ports[i];
			std::vector<RTLIL::SigBit> bits = modwalker.sigmap(port.en);
			for (auto bit : bits)
				if (bit == RTLIL::State::S1)
					goto port_is_always_active;
			eligible_ports.insert(i);
		port_is_always_active:;
		}

		if (eligible_ports.size() <= 1)
			return;

		log("Consolidating write ports of memory %s.%s using sat-based resource sharing:\n", log_id(module), log_id(mem.memid));

		// Group eligible ports by clock domain and width.

		pool<int> checked_ports;
		std::vector<std::vector<int>> groups;
		for (int i = 0; i < GetSize(mem.wr_ports); i++)
		{
			auto &port1 = mem.wr_ports[i];
			if (!eligible_ports.count(i))
				continue;
			if (checked_ports.count(i))
				continue;

			std::vector<int> group;
			group.push_back(i);

			for (int j = i + 1; j < GetSize(mem.wr_ports); j++)
			{
				auto &port2 = mem.wr_ports[j];
				if (!eligible_ports.count(j))
					continue;
				if (checked_ports.count(j))
					continue;
				if (port1.clk_enable != port2.clk_enable)
					continue;
				if (port1.clk_enable) {
					if (port1.clk != port2.clk)
						continue;
					if (port1.clk_polarity != port2.clk_polarity)
						continue;
				}
				if (port1.wide_log2 != port2.wide_log2)
					continue;
				group.push_back(j);
			}

			for (auto j : group)
				checked_ports.insert(j);

			if (group.size() <= 1)
				continue;

			groups.push_back(group);
		}

		bool changed = false;
		for (auto &group : groups) {
			auto &some_port = mem.wr_ports[group[0]];
			string ports;
			for (auto idx : group) {
				if (idx != group[0])
					ports += ", ";
				ports += std::to_string(idx);
			}
			if (!some_port.clk_enable) {
				log("  Checking unclocked group, width %d: ports %s.\n", mem.width << some_port.wide_log2, ports.c_str());
			} else {
				log("  Checking group clocked with %sedge %s, width %d: ports %s.\n", some_port.clk_polarity ? "pos" : "neg", log_signal(some_port.clk), mem.width << some_port.wide_log2, ports.c_str());
			}

			// Okay, time to actually run the SAT solver.

			QuickConeSat qcsat(modwalker);

			// create SAT representation of common input cone of all considered EN signals

			dict<int, int> port_to_sat_variable;

			for (auto idx : group)
				port_to_sat_variable[idx] = qcsat.ez->expression(qcsat.ez->OpOr, qcsat.importSig(mem.wr_ports[idx].en));

			qcsat.prepare();

			log("  Common input cone for all EN signals: %d cells.\n", GetSize(qcsat.imported_cells));

			log("  Size of unconstrained SAT problem: %d variables, %d clauses\n", qcsat.ez->numCnfVariables(), qcsat.ez->numCnfClauses());

			// now try merging the ports.

			for (int ii = 0; ii < GetSize(group); ii++) {
				int idx1 = group[ii];
				auto &port1 = mem.wr_ports[idx1];
				if (port1.removed)
					continue;
				for (int jj = ii + 1; jj < GetSize(group); jj++) {
					int idx2 = group[jj];
					auto &port2 = mem.wr_ports[idx2];
					if (port2.removed)
						continue;

					if (qcsat.ez->solve(port_to_sat_variable.at(idx1), port_to_sat_variable.at(idx2))) {
						log("  According to SAT solver sharing of port %d with port %d is not possible.\n", idx1, idx2);
						continue;
					}

					log("  Merging port %d into port %d.\n", idx2, idx1);
					mem.prepare_wr_merge(idx1, idx2, &initvals);
					port_to_sat_variable.at(idx1) = qcsat.ez->OR(port_to_sat_variable.at(idx1), port_to_sat_variable.at(idx2));

					RTLIL::SigSpec last_addr = port1.addr;
					RTLIL::SigSpec last_data = port1.data;
					std::vector<RTLIL::SigBit> last_en = modwalker.sigmap(port1.en);

					RTLIL::SigSpec this_addr = port2.addr;
					RTLIL::SigSpec this_data = port2.data;
					std::vector<RTLIL::SigBit> this_en = modwalker.sigmap(port2.en);

					RTLIL::SigBit this_en_active = module->ReduceOr(NEW_ID, this_en);

					if (GetSize(last_addr) < GetSize(this_addr))
						last_addr.extend_u0(GetSize(this_addr));
					else
						this_addr.extend_u0(GetSize(last_addr));

					SigSpec new_addr = module->Mux(NEW_ID, last_addr.extract_end(port1.wide_log2), this_addr.extract_end(port1.wide_log2), this_en_active);

					port1.addr = SigSpec({new_addr, port1.addr.extract(0, port1.wide_log2)});
					port1.data = module->Mux(NEW_ID, last_data, this_data, this_en_active);

					std::map<std::pair<RTLIL::SigBit, RTLIL::SigBit>, int> groups_en;
					RTLIL::SigSpec grouped_last_en, grouped_this_en, en;
					RTLIL::Wire *grouped_en = module->addWire(NEW_ID, 0);

					for (int j = 0; j < int(this_en.size()); j++) {
						std::pair<RTLIL::SigBit, RTLIL::SigBit> key(last_en[j], this_en[j]);
						if (!groups_en.count(key)) {
							grouped_last_en.append(last_en[j]);
							grouped_this_en.append(this_en[j]);
							groups_en[key] = grouped_en->width;
							grouped_en->width++;
						}
						en.append(RTLIL::SigSpec(grouped_en, groups_en[key]));
					}

					module->addMux(NEW_ID, grouped_last_en, grouped_this_en, this_en_active, grouped_en);
					port1.en = en;

					port2.removed = true;
					changed = true;
				}
			}
		}

		if (changed)
			mem.emit();
	}


	// -------------
	// Setup and run
	// -------------

	MemoryShareWorker(RTLIL::Design *design, bool flag_widen, bool flag_sat) : design(design), modwalker(design), flag_widen(flag_widen), flag_sat(flag_sat) {}

	void operator()(RTLIL::Module* module)
	{
		std::vector<Mem> memories = Mem::get_selected_memories(module);

		this->module = module;
		sigmap.set(module);
		initvals.set(&sigmap, module);

		sigmap_xmux = sigmap;
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

		for (auto &mem : memories) {
			while (consolidate_rd_by_addr(mem));
			while (consolidate_wr_by_addr(mem));
		}

		if (!flag_sat)
			return;

		modwalker.setup(module);

		for (auto &mem : memories)
			consolidate_wr_using_sat(mem);
	}
};

struct MemorySharePass : public Pass {
	MemorySharePass() : Pass("memory_share", "consolidate memory ports") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    memory_share [-nosat] [-nowiden] [selection]\n");
		log("\n");
		log("This pass merges share-able memory ports into single memory ports.\n");
		log("\n");
		log("The following methods are used to consolidate the number of memory ports:\n");
		log("\n");
		log("  - When multiple write ports access the same address then this is converted\n");
		log("    to a single write port with a more complex data and/or enable logic path.\n");
		log("\n");
		log("  - When multiple read or write ports access adjacent aligned addresses, they\n");
		log("    are merged to a single wide read or write port.  This transformation can be\n");
		log("    disabled with the \"-nowiden\" option.\n");
		log("\n");
		log("  - When multiple write ports are never accessed at the same time (a SAT\n");
		log("    solver is used to determine this), then the ports are merged into a single\n");
		log("    write port.  This transformation can be disabled with the \"-nosat\" option.\n");
		log("\n");
		log("Note that in addition to the algorithms implemented in this pass, the $memrd\n");
		log("and $memwr cells are also subject to generic resource sharing passes (and other\n");
		log("optimizations) such as \"share\" and \"opt_merge\".\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		bool flag_widen = true;
		bool flag_sat = true;
		log_header(design, "Executing MEMORY_SHARE pass (consolidating $memrd/$memwr cells).\n");
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-nosat")
			{
				flag_sat = false;
				continue;
			}
			if (args[argidx] == "-nowiden")
			{
				flag_widen = false;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);
		MemoryShareWorker msw(design, flag_widen, flag_sat);

		for (auto module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;

			msw(module);
		}
	}
} MemorySharePass;

PRIVATE_NAMESPACE_END
