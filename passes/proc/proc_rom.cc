/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022  Marcelina Kościelnicka <mwk@0x04.net>
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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/mem.h"
#include <stdlib.h>
#include <stdio.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RomWorker
{
	RTLIL::Module *module;
	SigMap sigmap;

	int count = 0;

	RomWorker(RTLIL::Module *mod) : module(mod), sigmap(mod) {}

	void do_switch(RTLIL::SwitchRule *sw)
	{
		for (auto cs : sw->cases) {
			do_case(cs);
		}

		if (sw->cases.empty()) {
			log_debug("rejecting switch: no cases\n");
			return;
		}

		// A switch can be converted into ROM when:
		//
		// 1. No case contains a nested switch
		// 2. All cases have the same set of assigned signals
		// 3. All right-hand values in cases are constants
		// 4. All compare values used in cases are fully-defined constants
		// 5. The cases must cover all possible values (possibly by using default case)

		SigSpec lhs;
		dict<SigBit, int> lhs_lookup;
		for (auto &it: sw->cases[0]->actions) {
			for (auto bit: it.first) {
				if (!lhs_lookup.count(bit)) {
					lhs_lookup[bit] = GetSize(lhs);
					lhs.append(bit);
				}
			}
		}

		if (lhs.empty()) {
			log_debug("rejecting switch: lhs empty\n");
			return;
		}

		int swsigbits = 0;
		for (int i = 0; i < GetSize(sw->signal); i++)
			if (sw->signal[i] != State::S0)
				swsigbits = i + 1;

		dict<int, Const> vals;
		Const default_val;
		bool got_default = false;
		int maxaddr = 0;
		for (auto cs : sw->cases) {
			if (!cs->switches.empty()) {
				log_debug("rejecting switch: has nested switches\n");
				return;
			}
			Const val = Const(State::Sm, GetSize(lhs));
			for (auto &it: cs->actions) {
				if (!it.second.is_fully_const()) {
					log_debug("rejecting switch: rhs not const\n");
					return;
				}
				for (int i = 0; i < GetSize(it.first); i++) {
					auto it2 = lhs_lookup.find(it.first[i]);
					if (it2 == lhs_lookup.end()) {
						log_debug("rejecting switch: lhs not uniform\n");
						return;
					}
					val[it2->second] = it.second[i].data;
				}
			}
			for (auto bit: val.bits) {
				if (bit == State::Sm) {
					log_debug("rejecting switch: lhs not uniform\n");
					return;
				}
			}

			for (auto &addr: cs->compare) {
				if (!addr.is_fully_def()) {
					log_debug("rejecting switch: case value has undef bits\n");
					return;
				}
				Const c = addr.as_const();
				while (GetSize(c) && c.bits.back() == State::S0)
					c.bits.pop_back();
				if (GetSize(c) > swsigbits)
					continue;
				if (GetSize(c) > 30) {
					log_debug("rejecting switch: address too large\n");
					return;
				}
				int a = c.as_int();
				if (vals.count(a))
					continue;
				vals[a] = val;
				if (a > maxaddr)
					maxaddr = a;
			}
			if (cs->compare.empty()) {
				default_val = val;
				got_default = true;
				break;
			}
		}
		int abits = ceil_log2(maxaddr + 1);
		if (!got_default && (swsigbits > 30 || GetSize(vals) != (1 << swsigbits))) {
			log_debug("rejecting switch: not all values are covered\n");
			return;
		}

		// TODO: better density heuristic?
		if (GetSize(vals) < 8) {
			log_debug("rejecting switch: not enough values\n");
			return;
		}
		if ((1 << abits) / GetSize(vals) > 4) {
			log_debug("rejecting switch: not enough density\n");
			return;
		}

		// Ok, let's do it.
		SigSpec rdata = module->addWire(NEW_ID, GetSize(lhs));
		Mem mem(module, NEW_ID, GetSize(lhs), 0, 1 << abits);
		mem.attributes = sw->attributes;

		Const init_data;
		for (int i = 0; i < mem.size; i++) {
			auto it = vals.find(i);
			if (it == vals.end()) {
				log_assert(got_default);
				for (auto bit: default_val.bits)
					init_data.bits.push_back(bit);
			} else {
				for (auto bit: it->second.bits)
					init_data.bits.push_back(bit);
			}
		}

		MemInit init;
		init.addr = 0;
		init.data = init_data;
		init.en = Const(State::S1, GetSize(lhs));
		mem.inits.push_back(std::move(init));

		MemRd rd;
		rd.addr = sw->signal.extract(0, abits);
		rd.data = rdata;
		rd.init_value = Const(State::Sx, GetSize(lhs));
		rd.arst_value = Const(State::Sx, GetSize(lhs));
		rd.srst_value = Const(State::Sx, GetSize(lhs));
		mem.rd_ports.push_back(std::move(rd));

		mem.emit();
		for (auto cs: sw->cases)
			delete cs;
		sw->cases.clear();
		sw->signal = sw->signal.extract(0, swsigbits);
		if (abits == GetSize(sw->signal)) {
			sw->signal = SigSpec();
			RTLIL::CaseRule *cs = new RTLIL::CaseRule;
			cs->actions.push_back(SigSig(lhs, rdata));
			sw->cases.push_back(cs);
		} else {
			sw->signal = sw->signal.extract_end(abits);
			RTLIL::CaseRule *cs = new RTLIL::CaseRule;
			cs->compare.push_back(Const(State::S0, GetSize(sw->signal)));
			cs->actions.push_back(SigSig(lhs, rdata));
			sw->cases.push_back(cs);
			RTLIL::CaseRule *cs2 = new RTLIL::CaseRule;
			cs2->actions.push_back(SigSig(lhs, default_val));
			sw->cases.push_back(cs2);
		}

		count += 1;
	}

	void do_case(RTLIL::CaseRule *cs)
	{
		for (auto sw: cs->switches) {
			do_switch(sw);
		}
	}

	void do_process(RTLIL::Process *pr)
	{
		do_case(&pr->root_case);
	}
};

struct ProcRomPass : public Pass {
	ProcRomPass() : Pass("proc_rom", "convert switches to ROMs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_rom [selection]\n");
		log("\n");
		log("This pass converts switches into read-only memories when appropriate.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		int total_count = 0;
		log_header(design, "Executing PROC_ROM pass (convert switches to ROMs).\n");

		extra_args(args, 1, design);

		for (auto mod : design->modules()) {
			if (!design->selected(mod))
				continue;
			RomWorker worker(mod);
			for (auto &proc_it : mod->processes) {
				if (!design->selected(mod, proc_it.second))
					continue;
				worker.do_process(proc_it.second);
			}
			total_count += worker.count;
		}

		log("Converted %d switch%s.\n",
		    total_count, total_count == 1 ? "" : "es");
	}
} ProcRomPass;

PRIVATE_NAMESPACE_END
