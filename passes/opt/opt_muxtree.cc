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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
#include <stdlib.h>
#include <stdio.h>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using RTLIL::id2cstr;

struct OptMuxtreeWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap assign_map;
	int removed_count;
	int glob_abort_cnt = 100000;

	struct bitinfo_t {
		bool seen_non_mux;
		pool<int> mux_users;
		pool<int> mux_drivers;
	};

	idict<SigBit> bit2num;
	vector<bitinfo_t> bit2info;

	struct portinfo_t {
		int ctrl_sig;
		pool<int> input_sigs;
		pool<int> input_muxes;
		bool const_activated;
		bool const_deactivated;
		bool enabled;
	};

	struct muxinfo_t {
		RTLIL::Cell *cell;
		vector<portinfo_t> ports;
	};

	vector<muxinfo_t> mux2info;
	vector<bool> root_muxes;
	vector<bool> root_enable_muxes;
	pool<int> root_mux_rerun;

	OptMuxtreeWorker(RTLIL::Design *design, RTLIL::Module *module) :
			design(design), module(module), assign_map(module), removed_count(0)
	{
		log("Running muxtree optimizer on module %s..\n", module->name.c_str());

		log("  Creating internal representation of mux trees.\n");

		// Populate bit2info[]:
		//	.seen_non_mux
		//	.mux_users
		//	.mux_drivers
		// Populate mux2info[].ports[]:
		//	.ctrl_sig
		//	.input_sigs
		//	.const_activated
		//	.const_deactivated
		for (auto cell : module->cells())
		{
			if (cell->type.in(ID($mux), ID($pmux)))
			{
				RTLIL::SigSpec sig_a = cell->getPort(ID::A);
				RTLIL::SigSpec sig_b = cell->getPort(ID::B);
				RTLIL::SigSpec sig_s = cell->getPort(ID(S));
				RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

				muxinfo_t muxinfo;
				muxinfo.cell = cell;

				for (int i = 0; i < GetSize(sig_s); i++) {
					RTLIL::SigSpec sig = sig_b.extract(i*GetSize(sig_a), GetSize(sig_a));
					RTLIL::SigSpec ctrl_sig = assign_map(sig_s.extract(i, 1));
					portinfo_t portinfo;
					portinfo.ctrl_sig = sig2bits(ctrl_sig, false).front();
					for (int idx : sig2bits(sig)) {
						bit2info[idx].mux_users.insert(GetSize(mux2info));
						portinfo.input_sigs.insert(idx);
					}
					portinfo.const_activated = ctrl_sig.is_fully_const() && ctrl_sig.as_bool();
					portinfo.const_deactivated = ctrl_sig.is_fully_const() && !ctrl_sig.as_bool();
					portinfo.enabled = false;
					muxinfo.ports.push_back(portinfo);
				}

				portinfo_t portinfo;
				for (int idx : sig2bits(sig_a)) {
					bit2info[idx].mux_users.insert(GetSize(mux2info));
					portinfo.input_sigs.insert(idx);
				}
				portinfo.ctrl_sig = -1;
				portinfo.const_activated = false;
				portinfo.const_deactivated = false;
				portinfo.enabled = false;
				muxinfo.ports.push_back(portinfo);

				for (int idx : sig2bits(sig_y))
					bit2info[idx].mux_drivers.insert(GetSize(mux2info));

				for (int idx : sig2bits(sig_s))
					bit2info[idx].seen_non_mux = true;

				mux2info.push_back(muxinfo);
			}
			else
			{
				for (auto &it : cell->connections()) {
					for (int idx : sig2bits(it.second))
						bit2info[idx].seen_non_mux = true;
				}
			}
		}
		for (auto wire : module->wires()) {
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (int idx : sig2bits(RTLIL::SigSpec(wire)))
					bit2info[idx].seen_non_mux = true;
		}

		if (mux2info.empty()) {
			log("  No muxes found in this module.\n");
			return;
		}

		// Populate mux2info[].ports[]:
		//	.input_muxes
		for (int i = 0; i < GetSize(bit2info); i++)
		for (int j : bit2info[i].mux_users)
		for (auto &p : mux2info[j].ports) {
			if (p.input_sigs.count(i))
				for (int k : bit2info[i].mux_drivers)
					p.input_muxes.insert(k);
		}

		log("  Evaluating internal representation of mux trees.\n");

		dict<int, pool<int>> mux_to_users;
		root_muxes.resize(GetSize(mux2info));
		root_enable_muxes.resize(GetSize(mux2info));

		for (auto &bi : bit2info) {
			for (int i : bi.mux_drivers)
				for (int j : bi.mux_users)
					mux_to_users[i].insert(j);
			if (!bi.seen_non_mux)
				continue;
			for (int mux_idx : bi.mux_drivers) {
				root_muxes.at(mux_idx) = true;
				root_enable_muxes.at(mux_idx) = true;
			}
		}

		for (auto &it : mux_to_users)
			if (GetSize(it.second) > 1)
				root_muxes.at(it.first) = true;

		for (int mux_idx = 0; mux_idx < GetSize(root_muxes); mux_idx++)
			if (root_muxes.at(mux_idx)) {
				log_debug("    Root of a mux tree: %s%s\n", log_id(mux2info[mux_idx].cell), root_enable_muxes.at(mux_idx) ? " (pure)" : "");
				root_mux_rerun.erase(mux_idx);
				eval_root_mux(mux_idx);
				if (glob_abort_cnt == 0) {
					log("  Giving up (too many iterations)\n");
					return;
				}
			}

		while (!root_mux_rerun.empty()) {
			int mux_idx = *root_mux_rerun.begin();
			log_debug("    Root of a mux tree: %s (rerun as non-pure)\n", log_id(mux2info[mux_idx].cell));
			log_assert(root_enable_muxes.at(mux_idx));
			root_mux_rerun.erase(mux_idx);
			eval_root_mux(mux_idx);
			if (glob_abort_cnt == 0) {
				log("  Giving up (too many iterations)\n");
				return;
			}
		}

		log("  Analyzing evaluation results.\n");
		log_assert(glob_abort_cnt > 0);

		for (auto &mi : mux2info)
		{
			vector<int> live_ports;
			for (int port_idx = 0; port_idx < GetSize(mi.ports); port_idx++) {
				portinfo_t &pi = mi.ports[port_idx];
				if (pi.enabled) {
					live_ports.push_back(port_idx);
				} else {
					log("    dead port %d/%d on %s %s.\n", port_idx+1, GetSize(mi.ports),
							mi.cell->type.c_str(), mi.cell->name.c_str());
					removed_count++;
				}
			}

			if (GetSize(live_ports) == GetSize(mi.ports))
				continue;

			if (live_ports.empty()) {
				module->remove(mi.cell);
				continue;
			}

			RTLIL::SigSpec sig_a = mi.cell->getPort(ID::A);
			RTLIL::SigSpec sig_b = mi.cell->getPort(ID::B);
			RTLIL::SigSpec sig_s = mi.cell->getPort(ID(S));
			RTLIL::SigSpec sig_y = mi.cell->getPort(ID::Y);

			RTLIL::SigSpec sig_ports = sig_b;
			sig_ports.append(sig_a);

			if (GetSize(live_ports) == 1)
			{
				RTLIL::SigSpec sig_in = sig_ports.extract(live_ports[0]*GetSize(sig_a), GetSize(sig_a));
				module->connect(RTLIL::SigSig(sig_y, sig_in));
				module->remove(mi.cell);
			}
			else
			{
				RTLIL::SigSpec new_sig_a, new_sig_b, new_sig_s;

				for (int i = 0; i < GetSize(live_ports); i++) {
					RTLIL::SigSpec sig_in = sig_ports.extract(live_ports[i]*GetSize(sig_a), GetSize(sig_a));
					if (i == GetSize(live_ports)-1) {
						new_sig_a = sig_in;
					} else {
						new_sig_b.append(sig_in);
						new_sig_s.append(sig_s.extract(live_ports[i], 1));
					}
				}

				mi.cell->setPort(ID::A, new_sig_a);
				mi.cell->setPort(ID::B, new_sig_b);
				mi.cell->setPort(ID(S), new_sig_s);
				if (GetSize(new_sig_s) == 1) {
					mi.cell->type = ID($mux);
					mi.cell->parameters.erase(ID(S_WIDTH));
				} else {
					mi.cell->parameters[ID(S_WIDTH)] = RTLIL::Const(GetSize(new_sig_s));
				}
			}
		}
	}

	vector<int> sig2bits(RTLIL::SigSpec sig, bool skip_non_wires = true)
	{
		vector<int> results;
		assign_map.apply(sig);
		for (auto &bit : sig)
			if (bit.wire != NULL) {
				if (bit2num.count(bit) == 0) {
					bitinfo_t info;
					info.seen_non_mux = false;
					bit2num.expect(bit, GetSize(bit2info));
					bit2info.push_back(info);
				}
				results.push_back(bit2num.at(bit));
			} else if (!skip_non_wires)
				results.push_back(-1);
		return results;
	}

	struct knowledge_t
	{
		// database of known inactive signals
		// the payload is a reference counter used to manage the
		// list. when it is non-zero the signal in known to be inactive
		vector<int> known_inactive;

		// database of known active signals
		vector<int> known_active;

		// this is just used to keep track of visited muxes in order to prohibit
		// endless recursion in mux loops
		vector<bool> visited_muxes;
	};

	void eval_mux_port(knowledge_t &knowledge, int mux_idx, int port_idx, bool do_replace_known, bool do_enable_ports, int abort_count)
	{
		if (glob_abort_cnt == 0)
			return;

		muxinfo_t &muxinfo = mux2info[mux_idx];

		if (do_enable_ports)
			muxinfo.ports[port_idx].enabled = true;

		for (int i = 0; i < GetSize(muxinfo.ports); i++) {
			if (i == port_idx)
				continue;
			if (muxinfo.ports[i].ctrl_sig >= 0)
				knowledge.known_inactive.at(muxinfo.ports[i].ctrl_sig)++;
		}

		if (port_idx < GetSize(muxinfo.ports)-1 && !muxinfo.ports[port_idx].const_activated)
			knowledge.known_active.at(muxinfo.ports[port_idx].ctrl_sig)++;

		vector<int> parent_muxes;
		for (int m : muxinfo.ports[port_idx].input_muxes) {
			if (knowledge.visited_muxes[m])
				continue;
			knowledge.visited_muxes[m] = true;
			parent_muxes.push_back(m);
		}
		for (int m : parent_muxes) {
			if (root_enable_muxes.at(m))
				continue;
			else if (root_muxes.at(m)) {
				if (abort_count == 0) {
					root_mux_rerun.insert(m);
					root_enable_muxes.at(m) = true;
					log_debug("      Removing pure flag from root mux %s.\n", log_id(mux2info[m].cell));
				} else
					eval_mux(knowledge, m, false, do_enable_ports, abort_count - 1);
			} else
				eval_mux(knowledge, m, do_replace_known, do_enable_ports, abort_count);
			if (glob_abort_cnt == 0)
				return;
		}
		for (int m : parent_muxes)
			knowledge.visited_muxes[m] = false;

		if (port_idx < GetSize(muxinfo.ports)-1 && !muxinfo.ports[port_idx].const_activated)
			knowledge.known_active.at(muxinfo.ports[port_idx].ctrl_sig)--;

		for (int i = 0; i < GetSize(muxinfo.ports); i++) {
			if (i == port_idx)
				continue;
			if (muxinfo.ports[i].ctrl_sig >= 0)
				knowledge.known_inactive.at(muxinfo.ports[i].ctrl_sig)--;
		}
	}

	void replace_known(knowledge_t &knowledge, muxinfo_t &muxinfo, IdString portname)
	{
		SigSpec sig = muxinfo.cell->getPort(portname);
		bool did_something = false;

		int width = 0;
		idict<int> ctrl_bits;
		if (portname == ID::B)
			width = GetSize(muxinfo.cell->getPort(ID::A));
		for (int bit : sig2bits(muxinfo.cell->getPort(ID(S)), false))
			ctrl_bits(bit);

		int port_idx = 0, port_off = 0;
		vector<int> bits = sig2bits(sig, false);
		for (int i = 0; i < GetSize(bits); i++) {
			if (bits[i] < 0)
				continue;
			if (knowledge.known_inactive.at(bits[i])) {
				sig[i] = State::S0;
				did_something = true;
			} else
			if (knowledge.known_active.at(bits[i])) {
				sig[i] = State::S1;
				did_something = true;
			}
			if (width) {
				if (ctrl_bits.count(bits[i])) {
					sig[i] = ctrl_bits.at(bits[i]) == port_idx ? State::S1 : State::S0;
					did_something = true;
				}
				if (++port_off == width)
					port_idx++, port_off=0;
			} else {
				if (ctrl_bits.count(bits[i])) {
					sig[i] = State::S0;
					did_something = true;
				}
			}
		}

		if (did_something) {
			log("      Replacing known input bits on port %s of cell %s: %s -> %s\n", log_id(portname),
					log_id(muxinfo.cell), log_signal(muxinfo.cell->getPort(portname)), log_signal(sig));
			muxinfo.cell->setPort(portname, sig);
		}
	}

	void eval_mux(knowledge_t &knowledge, int mux_idx, bool do_replace_known, bool do_enable_ports, int abort_count)
	{
		if (glob_abort_cnt == 0)
			return;
		glob_abort_cnt--;

		muxinfo_t &muxinfo = mux2info[mux_idx];

		// set input ports to constants if we find known active or inactive signals
		if (do_replace_known) {
			replace_known(knowledge, muxinfo, ID::A);
			replace_known(knowledge, muxinfo, ID::B);
		}

		// if there is a constant activated port we just use it
		for (int port_idx = 0; port_idx < GetSize(muxinfo.ports); port_idx++)
		{
			portinfo_t &portinfo = muxinfo.ports[port_idx];
			if (portinfo.const_activated) {
				eval_mux_port(knowledge, mux_idx, port_idx, do_replace_known, do_enable_ports, abort_count);
				return;
			}
		}

		// compare ports with known_active signals. if we find a match, only this
		// port can be active. do not include the last port (its the default port
		// that has no control signals).
		for (int port_idx = 0; port_idx < GetSize(muxinfo.ports)-1; port_idx++)
		{
			portinfo_t &portinfo = muxinfo.ports[port_idx];
			if (portinfo.const_deactivated)
				continue;
			if (knowledge.known_active.at(portinfo.ctrl_sig)) {
				eval_mux_port(knowledge, mux_idx, port_idx, do_replace_known, do_enable_ports, abort_count);
				return;
			}
		}

		// eval all ports that could be activated (control signal is not in
		// known_inactive or const_deactivated).
		for (int port_idx = 0; port_idx < GetSize(muxinfo.ports); port_idx++)
		{
			portinfo_t &portinfo = muxinfo.ports[port_idx];
			if (portinfo.const_deactivated)
				continue;
			if (port_idx < GetSize(muxinfo.ports)-1)
				if (knowledge.known_inactive.at(portinfo.ctrl_sig))
					continue;
			eval_mux_port(knowledge, mux_idx, port_idx, do_replace_known, do_enable_ports, abort_count);

			if (glob_abort_cnt == 0)
				return;
		}
	}

	void eval_root_mux(int mux_idx)
	{
		log_assert(glob_abort_cnt > 0);
		knowledge_t knowledge;
		knowledge.known_inactive.resize(GetSize(bit2info));
		knowledge.known_active.resize(GetSize(bit2info));
		knowledge.visited_muxes.resize(GetSize(mux2info));
		knowledge.visited_muxes[mux_idx] = true;
		eval_mux(knowledge, mux_idx, true, root_enable_muxes.at(mux_idx), 3);
	}
};

struct OptMuxtreePass : public Pass {
	OptMuxtreePass() : Pass("opt_muxtree", "eliminate dead trees in multiplexer trees") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    opt_muxtree [selection]\n");
		log("\n");
		log("This pass analyzes the control signals for the multiplexer trees in the design\n");
		log("and identifies inputs that can never be active. It then removes this dead\n");
		log("branches from the multiplexer trees.\n");
		log("\n");
		log("This pass only operates on completely selected modules without processes.\n");
		log("\n");
	}
	void execute(vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing OPT_MUXTREE pass (detect dead branches in mux trees).\n");
		extra_args(args, 1, design);

		int total_count = 0;
		for (auto module : design->selected_whole_modules_warn()) {
			if (module->has_processes_warn())
				continue;
			OptMuxtreeWorker worker(design, module);
			total_count += worker.removed_count;
		}
		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Removed %d multiplexer ports.\n", total_count);
	}
} OptMuxtreePass;

PRIVATE_NAMESPACE_END
