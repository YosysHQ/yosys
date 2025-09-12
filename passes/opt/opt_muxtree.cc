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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/celltypes.h"
#include <stdlib.h>
#include <stdio.h>
#include <unordered_map>
#include <unordered_set>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

/**
  * TERMINOLOGY
  *
  * A multiplexer tree (mux tree) is a tree composed exclusively of muxes.
  * By mux, I mean $mux or $pmux. By port, I usually mean input port.
  * The children of a node are all the muxes driving its input ports (A, B).
  * It must be rooted in a "root mux", a mux which has multiple mux users
  * or any number of non-mux users. Only the root and leaf nodes can be
  * root muxes, not the internal nodes. Leaf nodes that are root muxes
  * are roots of "input trees".
  *
  * OPERATING PRINCIPLE
  *
  * This pass traverses mux trees, learning port activations and making
  * assumptions about them as it goes. When valid, ports are replaced
  * with constants, or removed if they can never be activated.
  * When valid, muxes are replaced with shorts from port to output,
  * or removed if their outputs are found to be no longer observable.
  *
  * Input trees can be recursed into if limits_t::recursions_left allows.
  * Otherwise, the input tree is queued for a re-run with a fresh knowledge_t.
  * At any point, if glob_evals_left goes to 0, the pass terminates.
  *
  * Unlike share, this pass doesn't use SAT to learn things about logic
  * driving the mux control signals, and traverses mux regions from users
  * to drivers.
  */

struct OptMuxtreeWorker
{
	RTLIL::Design *design;
	RTLIL::Module *module;
	SigMap assign_map;
	int removed_count;
	int glob_evals_left = 10000000;

	struct bitinfo_t {
		// Is bit directly used by non-mux cells or ports?
		bool seen_non_mux;
		pool<int> mux_users;
		pool<int> mux_drivers;
	};

	idict<SigBit> bit2num;
	vector<bitinfo_t> bit2info;

	struct portinfo_t {
		int ctrl_sig = -1; // No associated control signal by default
		pool<int> input_sigs = {};
		pool<int> input_muxes = {};
		bool const_activated = false;
		bool const_deactivated = false;
		// Is the port reachable from inputs of a mux tree?
		bool observable = false;
	};

	struct muxinfo_t {
		RTLIL::Cell *cell;
		vector<portinfo_t> ports;
	};

	vector<muxinfo_t> mux2info;
	vector<bool> root_muxes;
	vector<bool> root_enable_muxes;
	pool<int> root_mux_rerun;

	portinfo_t used_port_bit(RTLIL::SigSpec& sig, int mux_idx) {
		portinfo_t portinfo = {};
		for (int bit_idx : sig2bits(sig)) {
			bit2info[bit_idx].mux_users.insert(mux_idx);
			portinfo.input_sigs.insert(bit_idx);
		}
		return portinfo;
	}

	void track_mux(Cell* cell) {
		// Populate bit2info[]:
		//	.seen_non_mux
		//	.mux_users
		//	.mux_drivers
		// Populate mux2info[].ports[]:
		//	.ctrl_sig
		//	.input_sigs
		//	.const_activated
		//	.const_deactivated
		RTLIL::SigSpec sig_a = cell->getPort(ID::A);
		RTLIL::SigSpec sig_b = cell->getPort(ID::B);
		RTLIL::SigSpec sig_s = cell->getPort(ID::S);
		RTLIL::SigSpec sig_y = cell->getPort(ID::Y);

		muxinfo_t muxinfo;
		muxinfo.cell = cell;
		int this_mux_idx = GetSize(mux2info);

		// Analyze port B
		// In case of $pmux, port B is multiple slices, concatenated, one per bit of port S
		for (int i = 0; i < GetSize(sig_s); i++) {
			RTLIL::SigSpec sig = sig_b.extract(i*GetSize(sig_a), GetSize(sig_a));
			RTLIL::SigSpec ctrl_sig = assign_map(sig_s.extract(i, 1));
			portinfo_t portinfo = used_port_bit(sig, this_mux_idx);
			portinfo.ctrl_sig = sig2bits(ctrl_sig, false).front();
			portinfo.const_activated = ctrl_sig.is_fully_const() && ctrl_sig.as_bool();
			portinfo.const_deactivated = ctrl_sig.is_fully_const() && !ctrl_sig.as_bool();
			muxinfo.ports.push_back(portinfo);
		}

		// Analyze port A
		muxinfo.ports.push_back(used_port_bit(sig_a, this_mux_idx));

		for (int idx : sig2bits(sig_y))
			bit2info[idx].mux_drivers.insert(this_mux_idx);

		for (int idx : sig2bits(sig_s))
			bit2info[idx].seen_non_mux = true;

		mux2info.push_back(muxinfo);
	}

	void see_non_mux_cell(Cell* cell) {
		for (auto &it : cell->connections()) {
			for (int idx : sig2bits(it.second))
				bit2info[idx].seen_non_mux = true;
		}
	}

	void see_non_mux_wires() {
		for (auto wire : module->wires()) {
			if (wire->port_output || wire->get_bool_attribute(ID::keep))
				for (int idx : sig2bits(RTLIL::SigSpec(wire)))
					bit2info[idx].seen_non_mux = true;
		}
	}

	// Populate mux2info[].ports[]:
	//	.input_muxes
	void fixup_input_muxes() {
		// bit2info knows the mux users and mux drivers of bits
		// use this to tell mux2info ports about what muxes are driven by it
		for (int i = 0; i < GetSize(bit2info); i++)
		for (int j : bit2info[i].mux_users)
		for (auto &p : mux2info[j].ports) {
			if (p.input_sigs.count(i))
				for (int k : bit2info[i].mux_drivers)
					p.input_muxes.insert(k);
		}
	}

	void populate_roots() {
		// mux_to_users[i] means "set of muxes using output of mux i"
		dict<int, pool<int>> mux_to_users;
		// Pure root muxes (outputs seen by non-muxes)
		root_enable_muxes.resize(GetSize(mux2info));
		// All root muxes (outputs seen by non-muxes or multiple muxes)
		root_muxes.resize(GetSize(mux2info));

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

		for (auto &[driving_mux, user_muxes] : mux_to_users)
			if (GetSize(user_muxes) > 1)
				root_muxes.at(driving_mux) = true;
	}

	OptMuxtreeWorker(RTLIL::Design *design, RTLIL::Module *module) :
			design(design), module(module), assign_map(module), removed_count(0)
	{
		log("Running muxtree optimizer on module %s..\n", module->name);

		log("  Creating internal representation of mux trees.\n");

		for (auto cell : module->cells())
		{
			if (cell->type.in(ID($mux), ID($pmux)))
				track_mux(cell);
			else
				see_non_mux_cell(cell);
		}
		see_non_mux_wires();

		if (mux2info.empty()) {
			log("  No muxes found in this module.\n");
			return;
		}

		fixup_input_muxes();

		log("  Evaluating internal representation of mux trees.\n");

		populate_roots();

		for (int mux_idx = 0; mux_idx < GetSize(root_muxes); mux_idx++)
			if (root_muxes.at(mux_idx)) {
				log_debug("    Root of a mux tree: %s%s\n", log_id(mux2info[mux_idx].cell), root_enable_muxes.at(mux_idx) ? " (pure)" : "");
				root_mux_rerun.erase(mux_idx);
				eval_root_mux(mux_idx);
				if (glob_evals_left == 0) {
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
			if (glob_evals_left == 0) {
				log("  Giving up (too many iterations)\n");
				return;
			}
		}

		log("  Analyzing evaluation results.\n");
		log_assert(glob_evals_left > 0);

		for (auto &mi : mux2info)
		{
			vector<int> live_ports;
			for (int port_idx = 0; port_idx < GetSize(mi.ports); port_idx++) {
				portinfo_t &pi = mi.ports[port_idx];
				if (pi.observable) {
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
			RTLIL::SigSpec sig_s = mi.cell->getPort(ID::S);
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
				mi.cell->setPort(ID::S, new_sig_s);
				if (GetSize(new_sig_s) == 1) {
					mi.cell->type = ID($mux);
					mi.cell->parameters.erase(ID::S_WIDTH);
				} else {
					mi.cell->parameters[ID::S_WIDTH] = RTLIL::Const(GetSize(new_sig_s));
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
		// Known inactive signals
		// The payload is a reference counter used to manage the list
		// When it is non-zero, the signal in known to be inactive
		// When it reaches zero, the map element is removed
		std::unordered_map<int, int> known_inactive;

		// database of known active signals
		std::unordered_map<int, int> known_active;

		// this is just used to keep track of visited muxes in order to prohibit
		// endless recursion in mux loops
		std::unordered_set<int> visited_muxes;
	};

	static void activate_port(knowledge_t &knowledge, int port_idx, const muxinfo_t &muxinfo) {
		// First, mark all other ports inactive
		for (int i = 0; i < GetSize(muxinfo.ports); i++) {
			if (i == port_idx)
				continue;
			if (muxinfo.ports[i].ctrl_sig >= 0)
				++knowledge.known_inactive[muxinfo.ports[i].ctrl_sig];
		}
		// Mark port active unless it's the last one
		if (port_idx < GetSize(muxinfo.ports)-1 && !muxinfo.ports[port_idx].const_activated)
			++knowledge.known_active[muxinfo.ports[port_idx].ctrl_sig];
	}

	static void deactivate_port(knowledge_t &knowledge, int port_idx, const muxinfo_t &muxinfo) {
		auto unlearn = [](std::unordered_map<int, int>& knowns, int i) {
			auto it = knowns.find(i);
			if (it != knowns.end())
				if (--it->second == 0)
					knowns.erase(it);
		};

		if (port_idx < GetSize(muxinfo.ports)-1 && !muxinfo.ports[port_idx].const_activated)
			unlearn(knowledge.known_active, muxinfo.ports[port_idx].ctrl_sig);

		// Undo inactivity assumptions for other ports
		for (int i = 0; i < GetSize(muxinfo.ports); i++) {
			if (i == port_idx)
				continue;
			if (muxinfo.ports[i].ctrl_sig >= 0)
				unlearn(knowledge.known_inactive, muxinfo.ports[i].ctrl_sig);
		}
	}

	struct limits_t {
		// Are we allowed to replace inputs with constants?
		// True if knowledge doesn't contain assumptions
		bool do_replace_known = true;
		// Are we allowed to mark ports as observable?
		// True if we're recursing from a pure root mux
		bool do_mark_ports_observable = true;
		// How many more subtree recursions into input trees can we take?
		// Then shalt thou count to three, no more, no less. Three shall be the number thou shalt count, and the number of the counting shall be three.
		int recursions_left = 3;
		limits_t subtree() const {
			limits_t ret = *this;
			log_assert(ret.recursions_left > 0);
			ret.recursions_left--;
			return ret;
		}
	};
	void eval_mux_port(knowledge_t &knowledge, int mux_idx, int port_idx, limits_t limits)
	{
		if (glob_evals_left == 0)
			return;

		muxinfo_t &muxinfo = mux2info[mux_idx];

		if (limits.do_mark_ports_observable)
			muxinfo.ports[port_idx].observable = true;

		// For the purposes of recursion, we assume the port is active,
		// meaning all other ports are inactive
		activate_port(knowledge, port_idx, muxinfo);

		vector<int> input_mux_queue;
		for (int m : muxinfo.ports[port_idx].input_muxes) {
			if (knowledge.visited_muxes.count(m))
				continue;
			knowledge.visited_muxes.insert(m);
			input_mux_queue.push_back(m);
		}
		for (int m : input_mux_queue) {
			if (root_enable_muxes.at(m))
				continue;
			else if (root_muxes.at(m)) {
				// This leaf node of the current tree
				// is the root of an input tree of the current tree
				if (limits.recursions_left == 0) {
					// Ran out of subtree depth, re-eval this input tree in the next re-run
					root_mux_rerun.insert(m);
					root_enable_muxes.at(m) = true;
					log_debug("      Removing pure flag from root mux %s.\n", log_id(mux2info[m].cell));
				} else {
					auto new_limits = limits.subtree();
					// Since our knowledge includes assumption,
					// we can't generally allow replacing in an input tree based on it
					new_limits.do_replace_known = false;
					eval_mux(knowledge, m, new_limits);
				}
			} else {
				// This non-root input mux has only this mux as a user,
				// so here we are allowed to pass along do_replace_known
				eval_mux(knowledge, m, limits);
			}
			if (glob_evals_left == 0)
				return;
		}

		// Allow revisiting input muxes, since evaluating other ports should
		// revisit these input muxes with different activation assumptions
		for (int m : input_mux_queue)
			knowledge.visited_muxes.erase(m);

		// Undo our assumptions that the port is active
		deactivate_port(knowledge, port_idx, muxinfo);
	}

	void replace_known(knowledge_t &knowledge, muxinfo_t &muxinfo, IdString portname)
	{
		SigSpec sig = muxinfo.cell->getPort(portname);
		bool did_something = false;

		int width_if_b = 0;
		idict<int> ctrl_bits;
		if (portname == ID::B)
			width_if_b = GetSize(muxinfo.cell->getPort(ID::A));
		for (int bit : sig2bits(muxinfo.cell->getPort(ID::S), false))
			ctrl_bits(bit);

		int slice_idx = 0, slice_off = 0;
		vector<int> bits = sig2bits(sig, false);
		for (int i = 0; i < GetSize(bits); i++) {
			if (bits[i] >= 0) {
				if (knowledge.known_inactive.count(bits[i]) > 0) {
					sig[i] = State::S0;
					did_something = true;
				} else
				if (knowledge.known_active.count(bits[i]) > 0) {
					sig[i] = State::S1;
					did_something = true;
				}
				if (ctrl_bits.count(bits[i])) {
					if (!width_if_b) {
						// Single-bit $mux example
						//  mux: S ? B : A = Y
						// A=S
						//  0 ? B : 0 = 0
						//  1 ? B : 1 = B
						// rewrite to A=0
						//  0 ? B : 0 = 0
						//  1 ? B : 0 = B
						// which is equivalent
						sig[i] = State::S0;
					} else {
						// "Sliced" $pmux example
						// B[i]=S[j]
						// i == j => B[i] activated only when B[i] is high, safe to rewrite to 1
						// i != j => B[i] activated only when B[i] is low, safe to rewrite to 0
						sig[i] = ctrl_bits.at(bits[i]) == slice_idx ? State::S1 : State::S0;
					}
					did_something = true;
				}
			}
			if (width_if_b) {
				// Roll over into next slice
				if (++slice_off == width_if_b)
					slice_idx++, slice_off=0;
			}
		}

		if (did_something) {
			log("      Replacing known input bits on port %s of cell %s: %s -> %s\n", log_id(portname),
					log_id(muxinfo.cell), log_signal(muxinfo.cell->getPort(portname)), log_signal(sig));
			muxinfo.cell->setPort(portname, sig);
		}
	}

	void eval_mux(knowledge_t &knowledge, int mux_idx, limits_t limits)
	{
		if (glob_evals_left == 0)
			return;
		glob_evals_left--;

		muxinfo_t &muxinfo = mux2info[mux_idx];
		log_debug("\t\teval %s (replace %d enable %d)\n", log_id(muxinfo.cell), limits.do_replace_known, limits.do_mark_ports_observable);

		// set input ports to constants if we find known active or inactive signals
		if (limits.do_replace_known) {
			replace_known(knowledge, muxinfo, ID::A);
			replace_known(knowledge, muxinfo, ID::B);
		}

		// if there is a constant activated port we just use it
		for (int port_idx = 0; port_idx < GetSize(muxinfo.ports); port_idx++)
		{
			portinfo_t &portinfo = muxinfo.ports[port_idx];
			if (portinfo.const_activated) {
				eval_mux_port(knowledge, mux_idx, port_idx, limits);
				return;
			}
		}

		// Compare ports with known active control signals. if we find a match,
		// only this port can be active. Do not include the last port,
		// it's the default port without an associated control signal
		for (int port_idx = 0; port_idx < GetSize(muxinfo.ports)-1; port_idx++)
		{
			portinfo_t &portinfo = muxinfo.ports[port_idx];
			if (portinfo.const_deactivated)
				continue;
			if (knowledge.known_active.count(portinfo.ctrl_sig) > 0) {
				eval_mux_port(knowledge, mux_idx, port_idx, limits);
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
				if (knowledge.known_inactive.count(portinfo.ctrl_sig) > 0)
					continue;
			eval_mux_port(knowledge, mux_idx, port_idx, limits);

			if (glob_evals_left == 0)
				return;
		}
	}

	void eval_root_mux(int mux_idx)
	{
		log_assert(glob_evals_left > 0);
		knowledge_t knowledge;
		knowledge.visited_muxes.insert(mux_idx);
		limits_t limits = {};
		limits.do_mark_ports_observable = root_enable_muxes.at(mux_idx);
		eval_mux(knowledge, mux_idx, limits);
	}
};

struct OptMuxtreePass : public Pass {
	OptMuxtreePass() : Pass("opt_muxtree", "eliminate dead trees in multiplexer trees") { }
	void help() override
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
	void execute(vector<std::string> args, RTLIL::Design *design) override
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
