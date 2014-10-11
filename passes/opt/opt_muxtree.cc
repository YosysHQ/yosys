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

        struct bitDef_t : public std::pair<RTLIL::Wire*, int> {
		bitDef_t() : std::pair<RTLIL::Wire*, int>(NULL, 0) { }
		bitDef_t(const RTLIL::SigBit &bit) : std::pair<RTLIL::Wire*, int>(bit.wire, bit.offset) { }
	};


	struct bitinfo_t {
		int num;
		bitDef_t bit;
		bool seen_non_mux;
		std::vector<int> mux_users;
		std::vector<int> mux_drivers;
	};

	std::map<bitDef_t, int> bit2num;
	std::vector<bitinfo_t> bit2info;

	struct portinfo_t {
		std::vector<int> ctrl_sigs;
		std::vector<int> input_sigs;
		std::vector<int> input_muxes;
		bool const_activated;
		bool enabled;
	};

	struct muxinfo_t {
		RTLIL::Cell *cell;
		std::vector<portinfo_t> ports;
	};

	std::vector<muxinfo_t> mux2info;

	OptMuxtreeWorker(RTLIL::Design *design, RTLIL::Module *module) :
			design(design), module(module), assign_map(module), removed_count(0)
	{
		log("Running muxtree optimizier on module %s..\n", module->name.c_str());

		log("  Creating internal representation of mux trees.\n");

		// Populate bit2info[]:
		//	.seen_non_mux
		//	.mux_users
		//	.mux_drivers
		// Populate mux2info[].ports[]:
		//	.ctrl_sigs
		//	.input_sigs
		//	.const_activated
		for (auto cell : module->cells())
		{
			if (cell->type == "$mux" || cell->type == "$pmux")
			{
				RTLIL::SigSpec sig_a = cell->getPort("\\A");
				RTLIL::SigSpec sig_b = cell->getPort("\\B");
				RTLIL::SigSpec sig_s = cell->getPort("\\S");
				RTLIL::SigSpec sig_y = cell->getPort("\\Y");

				muxinfo_t muxinfo;
				muxinfo.cell = cell;

				for (int i = 0; i < sig_s.size(); i++) {
					RTLIL::SigSpec sig = sig_b.extract(i*sig_a.size(), sig_a.size());
					RTLIL::SigSpec ctrl_sig = assign_map(sig_s.extract(i, 1));
					portinfo_t portinfo;
					for (int idx : sig2bits(sig)) {
						add_to_list(bit2info[idx].mux_users, mux2info.size());
						add_to_list(portinfo.input_sigs, idx);
					}
					for (int idx : sig2bits(ctrl_sig))
						add_to_list(portinfo.ctrl_sigs, idx);
					portinfo.const_activated = ctrl_sig.is_fully_const() && ctrl_sig.as_bool();
					portinfo.enabled = false;
					muxinfo.ports.push_back(portinfo);
				}

				portinfo_t portinfo;
				for (int idx : sig2bits(sig_a)) {
					add_to_list(bit2info[idx].mux_users, mux2info.size());
					add_to_list(portinfo.input_sigs, idx);
				}
				portinfo.const_activated = false;
				portinfo.enabled = false;
				muxinfo.ports.push_back(portinfo);

				for (int idx : sig2bits(sig_y))
					add_to_list(bit2info[idx].mux_drivers, mux2info.size());

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
			if (wire->port_output)
				for (int idx : sig2bits(RTLIL::SigSpec(wire)))
					bit2info[idx].seen_non_mux = true;
		}

		if (mux2info.size() == 0) {
			log("  No muxes found in this module.\n");
			return;
		}

		// Populate mux2info[].ports[]:
		//	.input_muxes
		for (size_t i = 0; i < bit2info.size(); i++)
		for (int j : bit2info[i].mux_users)
		for (auto &p : mux2info[j].ports) {
			if (is_in_list(p.input_sigs, i))
				for (int k : bit2info[i].mux_drivers)
					add_to_list(p.input_muxes, k);
		}

		log("  Evaluating internal representation of mux trees.\n");

		std::set<int> root_muxes;
		for (auto &bi : bit2info) {
			if (!bi.seen_non_mux)
				continue;
			for (int mux_idx : bi.mux_drivers)
				root_muxes.insert(mux_idx);
		}
		for (int mux_idx : root_muxes)
			eval_root_mux(mux_idx);

		log("  Analyzing evaluation results.\n");

		for (auto &mi : mux2info)
		{
			std::vector<int> live_ports;
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

			if (live_ports.size() == mi.ports.size())
				continue;

			if (live_ports.size() == 0) {
				module->remove(mi.cell);
				continue;
			}

			RTLIL::SigSpec sig_a = mi.cell->getPort("\\A");
			RTLIL::SigSpec sig_b = mi.cell->getPort("\\B");
			RTLIL::SigSpec sig_s = mi.cell->getPort("\\S");
			RTLIL::SigSpec sig_y = mi.cell->getPort("\\Y");

			RTLIL::SigSpec sig_ports = sig_b;
			sig_ports.append(sig_a);

			if (live_ports.size() == 1)
			{
				RTLIL::SigSpec sig_in = sig_ports.extract(live_ports[0]*sig_a.size(), sig_a.size());
				module->connect(RTLIL::SigSig(sig_y, sig_in));
				module->remove(mi.cell);
			}
			else
			{
				RTLIL::SigSpec new_sig_a, new_sig_b, new_sig_s;

				for (size_t i = 0; i < live_ports.size(); i++) {
					RTLIL::SigSpec sig_in = sig_ports.extract(live_ports[i]*sig_a.size(), sig_a.size());
					if (i == live_ports.size()-1) {
						new_sig_a = sig_in;
					} else {
						new_sig_b.append(sig_in);
						new_sig_s.append(sig_s.extract(live_ports[i], 1));
					}
				}

				mi.cell->setPort("\\A", new_sig_a);
				mi.cell->setPort("\\B", new_sig_b);
				mi.cell->setPort("\\S", new_sig_s);
				if (new_sig_s.size() == 1) {
					mi.cell->type = "$mux";
					mi.cell->parameters.erase("\\S_WIDTH");
				} else {
					mi.cell->parameters["\\S_WIDTH"] = RTLIL::Const(new_sig_s.size());
				}
			}
		}
	}

	bool list_is_subset(const std::vector<int> &sub, const std::vector<int> &super)
	{
		for (int v : sub)
			if (!is_in_list(super, v))
				return false;
		return true;
	}

	bool is_in_list(const std::vector<int> &list, int value)
	{
		for (int v : list)
			if (v == value)
				return true;
		return false;
	}

	void add_to_list(std::vector<int> &list, int value)
	{
		if (!is_in_list(list, value))
			list.push_back(value);
	}

	std::vector<int> sig2bits(RTLIL::SigSpec sig)
	{
		std::vector<int> results;
		assign_map.apply(sig);
		for (auto &bit : sig)
			if (bit.wire != NULL) {
				if (bit2num.count(bit) == 0) {
					bitinfo_t info;
					info.num = bit2info.size();
					info.bit = bit;
					info.seen_non_mux = false;
					bit2info.push_back(info);
					bit2num[info.bit] = info.num;
				}
				results.push_back(bit2num[bit]);
			}
		return results;
	}

	struct knowledge_t
	{
		// database of known inactive signals
		// the 2nd integer is a reference counter used to manage the
		// list. when it is non-zero the signal in known to be inactive
		std::map<int, int> known_inactive;

		// database of known active signals
		// the 2nd dimension is the list of or-ed signals. so we know that
		// for each i there is a j so that known_active[i][j] points to an
		// inactive control signal.
		std::vector<std::vector<int>> known_active;

		// this is just used to keep track of visited muxes in order to prohibit
		// endless recursion in mux loops
		std::set<int> visited_muxes;
	};

	void eval_mux_port(knowledge_t &knowledge, int mux_idx, int port_idx)
	{
		muxinfo_t &muxinfo = mux2info[mux_idx];
		muxinfo.ports[port_idx].enabled = true;

		for (size_t i = 0; i < muxinfo.ports.size(); i++) {
			if (int(i) == port_idx)
				continue;
			for (int b : muxinfo.ports[i].ctrl_sigs)
				knowledge.known_inactive[b]++;
		}

		if (port_idx < int(muxinfo.ports.size())-1 && !muxinfo.ports[port_idx].const_activated)
			knowledge.known_active.push_back(muxinfo.ports[port_idx].ctrl_sigs);

		std::vector<int> parent_muxes;
		for (int m : muxinfo.ports[port_idx].input_muxes) {
			if (knowledge.visited_muxes.count(m) > 0)
				continue;
			knowledge.visited_muxes.insert(m);
			parent_muxes.push_back(m);
		}
		for (int m : parent_muxes)
			eval_mux(knowledge, m);
		for (int m : parent_muxes)
			knowledge.visited_muxes.erase(m);

		if (port_idx < int(muxinfo.ports.size())-1 && !muxinfo.ports[port_idx].const_activated)
			knowledge.known_active.pop_back();

		for (size_t i = 0; i < muxinfo.ports.size(); i++) {
			if (int(i) == port_idx)
				continue;
			for (int b : muxinfo.ports[i].ctrl_sigs)
				knowledge.known_inactive[b]--;
		}
	}

	void eval_mux(knowledge_t &knowledge, int mux_idx)
	{
		muxinfo_t &muxinfo = mux2info[mux_idx];

		// if there is a constant activated port we just use it
		for (size_t port_idx = 0; port_idx < muxinfo.ports.size()-1; port_idx++)
		{
			portinfo_t &portinfo = muxinfo.ports[port_idx];
			if (portinfo.const_activated) {
				eval_mux_port(knowledge, mux_idx, port_idx);
				return;
			}
		}

		// compare ports with known_active signals. if we find a match, only this
		// port can be active. do not include the last port (its the default port
		// that has no control signals).
		for (size_t port_idx = 0; port_idx < muxinfo.ports.size()-1; port_idx++)
		{
			portinfo_t &portinfo = muxinfo.ports[port_idx];
			for (size_t i = 0; i < knowledge.known_active.size(); i++) {
				if (list_is_subset(knowledge.known_active[i], portinfo.ctrl_sigs)) {
					eval_mux_port(knowledge, mux_idx, port_idx);
					return;
				}
			}
		}

		// compare ports with known_inactive and known_active signals. If all control
		// signals of the port are know_inactive or if the control signals of all other
		// ports are known_active this port can't be activated. this loop includes the
		// default port but no known_inactive match is performed on the default port.
		for (size_t port_idx = 0; port_idx < muxinfo.ports.size(); port_idx++)
		{
			portinfo_t &portinfo = muxinfo.ports[port_idx];

			if (port_idx < muxinfo.ports.size()-1) {
				bool found_non_known_inactive = false;
				for (int i : portinfo.ctrl_sigs)
					if (knowledge.known_inactive[i] == 0)
						found_non_known_inactive = true;
				if (!found_non_known_inactive)
					continue;
			}

			bool port_active = true;
			std::vector<int> other_ctrl_sig;
			for (size_t i = 0; i < muxinfo.ports.size()-1; i++) {
				if (i == port_idx)
					continue;
				other_ctrl_sig.insert(other_ctrl_sig.end(),
						muxinfo.ports[i].ctrl_sigs.begin(), muxinfo.ports[i].ctrl_sigs.end());
			}
			for (size_t i = 0; i < knowledge.known_active.size(); i++) {
				if (list_is_subset(knowledge.known_active[i], other_ctrl_sig))
					port_active = false;
			}
			if (port_active)
				eval_mux_port(knowledge, mux_idx, port_idx);
		}
	}

	void eval_root_mux(int mux_idx)
	{
		knowledge_t knowledge;
		knowledge.visited_muxes.insert(mux_idx);
		eval_mux(knowledge, mux_idx);
	}
};

struct OptMuxtreePass : public Pass {
	OptMuxtreePass() : Pass("opt_muxtree", "eliminate dead trees in multiplexer trees") { }
	virtual void help()
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
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Executing OPT_MUXTREE pass (detect dead branches in mux trees).\n");
		extra_args(args, 1, design);

		int total_count = 0;
		for (auto mod : design->modules()) {
			if (!design->selected_whole_module(mod)) {
				if (design->selected(mod))
					log("Skipping module %s as it is only partially selected.\n", log_id(mod));
				continue;
			}
			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", log_id(mod));
			} else {
				OptMuxtreeWorker worker(design, mod);
				total_count += worker.removed_count;
			}
		}
		if (total_count)
			design->scratchpad_set_bool("opt.did_something", true);
		log("Removed %d multiplexer ports.\n", total_count);
	}
} OptMuxtreePass;
 
PRIVATE_NAMESPACE_END
