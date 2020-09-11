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


// Currently supported SVA sequence and property syntax:
// http://symbiyosys.readthedocs.io/en/latest/verific.html
//
// Next gen property syntax:
//   basic_property
//   [antecedent_condition] property
//   [antecedent_condition] always.. property
//   [antecedent_condition] eventually.. basic_property
//   [antecedent_condition] property until.. expression
//   [antecedent_condition] basic_property until.. basic_property      (assert/assume only)
//
// antecedent_condition:
//   sequence |->
//   sequence |=>
//
// basic_property:
//   sequence
//   not basic_property
//   nexttime basic_property
//   nexttime[N] basic_property
//   sequence #-# basic_property
//   sequence #=# basic_property
//   basic_property or basic_property           (cover only)
//   basic_property and basic_property          (assert/assume only)
//   basic_property implies basic_property
//   basic_property iff basic_property
//
// sequence:
//   expression
//   sequence ##N sequence
//   sequence ##[*] sequence
//   sequence ##[+] sequence
//   sequence ##[N:M] sequence
//   sequence ##[N:$] sequence
//   expression [*]
//   expression [+]
//   expression [*N]
//   expression [*N:M]
//   expression [*N:$]
//   sequence or sequence
//   sequence and sequence
//   expression throughout sequence
//   sequence intersect sequence
//   sequence within sequence
//   first_match( sequence )
//   expression [=N]
//   expression [=N:M]
//   expression [=N:$]
//   expression [->N]
//   expression [->N:M]
//   expression [->N:$]


#include "kernel/yosys.h"
#include "frontends/verific/verific.h"

USING_YOSYS_NAMESPACE

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

PRIVATE_NAMESPACE_BEGIN

// Non-deterministic FSM
struct SvaNFsmNode
{
	// Edge: Activate the target node if ctrl signal is true, consumes clock cycle
	// Link: Activate the target node if ctrl signal is true, doesn't consume clock cycle
	vector<pair<int, SigBit>> edges, links;
	bool is_cond_node;
};

// Non-deterministic FSM after resolving links
struct SvaUFsmNode
{
	// Edge: Activate the target node if all bits in ctrl signal are true, consumes clock cycle
	// Accept: This node functions as an accept node if all bits in ctrl signal are true
	vector<pair<int, SigSpec>> edges;
	vector<SigSpec> accept, cond;
	bool reachable;
};

// Deterministic FSM
struct SvaDFsmNode
{
	// A DFSM state corresponds to a set of NFSM states. We represent DFSM states as sorted vectors
	// of NFSM state node ids. Edge/accept controls are constants matched against the ctrl sigspec.
	SigSpec ctrl;
	vector<pair<vector<int>, Const>> edges;
	vector<Const> accept, reject;

	// additional temp data for getReject()
	Wire *ffoutwire;
	SigBit statesig;
	SigSpec nextstate;

	// additional temp data for getDFsm()
	int outnode;
};

struct SvaFsm
{
	Module *module;
	VerificClocking clocking;

	SigBit trigger_sig = State::S1, disable_sig;
	SigBit throughout_sig = State::S1;
	bool in_cond_mode = false;

	vector<SigBit> disable_stack;
	vector<SigBit> throughout_stack;

	int startNode, acceptNode, condNode;
	vector<SvaNFsmNode> nodes;

	vector<SvaUFsmNode> unodes;
	dict<vector<int>, SvaDFsmNode> dnodes;
	dict<pair<SigSpec, SigSpec>, SigBit> cond_eq_cache;
	bool materialized = false;

	SigBit final_accept_sig = State::Sx;
	SigBit final_reject_sig = State::Sx;

	SvaFsm(const VerificClocking &clking, SigBit trig = State::S1)
	{
		module = clking.module;
		clocking = clking;
		trigger_sig = trig;

		startNode = createNode();
		acceptNode = createNode();

		in_cond_mode = true;
		condNode = createNode();
		in_cond_mode = false;
	}

	void pushDisable(SigBit sig)
	{
		log_assert(!materialized);

		disable_stack.push_back(disable_sig);

		if (disable_sig == State::S0)
			disable_sig = sig;
		else
			disable_sig = module->Or(NEW_ID, disable_sig, sig);
	}

	void popDisable()
	{
		log_assert(!materialized);
		log_assert(!disable_stack.empty());

		disable_sig = disable_stack.back();
		disable_stack.pop_back();
	}

	void pushThroughout(SigBit sig)
	{
		log_assert(!materialized);

		throughout_stack.push_back(throughout_sig);

		if (throughout_sig == State::S1)
			throughout_sig = sig;
		else
			throughout_sig = module->And(NEW_ID, throughout_sig, sig);
	}

	void popThroughout()
	{
		log_assert(!materialized);
		log_assert(!throughout_stack.empty());

		throughout_sig = throughout_stack.back();
		throughout_stack.pop_back();
	}

	int createNode(int link_node = -1)
	{
		log_assert(!materialized);

		int idx = GetSize(nodes);
		nodes.push_back(SvaNFsmNode());
		nodes.back().is_cond_node = in_cond_mode;
		if (link_node >= 0)
			createLink(link_node, idx);
		return idx;
	}

	int createStartNode()
	{
		return createNode(startNode);
	}

	void createEdge(int from_node, int to_node, SigBit ctrl = State::S1)
	{
		log_assert(!materialized);
		log_assert(0 <= from_node && from_node < GetSize(nodes));
		log_assert(0 <= to_node && to_node < GetSize(nodes));
		log_assert(from_node != acceptNode);
		log_assert(to_node != acceptNode);
		log_assert(from_node != condNode);
		log_assert(to_node != condNode);
		log_assert(to_node != startNode);

		if (from_node != startNode)
			log_assert(nodes.at(from_node).is_cond_node == nodes.at(to_node).is_cond_node);

		if (throughout_sig != State::S1) {
			if (ctrl != State::S1)
				ctrl = module->And(NEW_ID, throughout_sig, ctrl);
			else
				ctrl = throughout_sig;
		}

		nodes[from_node].edges.push_back(make_pair(to_node, ctrl));
	}

	void createLink(int from_node, int to_node, SigBit ctrl = State::S1)
	{
		log_assert(!materialized);
		log_assert(0 <= from_node && from_node < GetSize(nodes));
		log_assert(0 <= to_node && to_node < GetSize(nodes));
		log_assert(from_node != acceptNode);
		log_assert(from_node != condNode);
		log_assert(to_node != startNode);

		if (from_node != startNode)
			log_assert(nodes.at(from_node).is_cond_node == nodes.at(to_node).is_cond_node);

		if (throughout_sig != State::S1) {
			if (ctrl != State::S1)
				ctrl = module->And(NEW_ID, throughout_sig, ctrl);
			else
				ctrl = throughout_sig;
		}

		nodes[from_node].links.push_back(make_pair(to_node, ctrl));
	}

	void make_link_order(vector<int> &order, int node, int min)
	{
		order[node] = std::max(order[node], min);
		for (auto &it : nodes[node].links)
			make_link_order(order, it.first, order[node]+1);
	}

	// ----------------------------------------------------
	// Generating NFSM circuit to acquire accept signal

	SigBit getAccept()
	{
		log_assert(!materialized);
		materialized = true;

		vector<Wire*> state_wire(GetSize(nodes));
		vector<SigBit> state_sig(GetSize(nodes));
		vector<SigBit> next_state_sig(GetSize(nodes));

		// Create state signals

		{
			SigBit not_disable = State::S1;

			if (disable_sig != State::S0)
				not_disable = module->Not(NEW_ID, disable_sig);

			for (int i = 0; i < GetSize(nodes); i++)
			{
				Wire *w = module->addWire(NEW_ID);
				state_wire[i] = w;
				state_sig[i] = w;

				if (i == startNode)
					state_sig[i] = module->Or(NEW_ID, state_sig[i], trigger_sig);

				if (disable_sig != State::S0)
					state_sig[i] = module->And(NEW_ID, state_sig[i], not_disable);
			}
		}

		// Follow Links

		{
			vector<int> node_order(GetSize(nodes));
			vector<vector<int>> order_to_nodes;

			for (int i = 0; i < GetSize(nodes); i++)
				make_link_order(node_order, i, 0);

			for (int i = 0; i < GetSize(nodes); i++) {
				if (node_order[i] >= GetSize(order_to_nodes))
					order_to_nodes.resize(node_order[i]+1);
				order_to_nodes[node_order[i]].push_back(i);
			}

			for (int order = 0; order < GetSize(order_to_nodes); order++)
			for (int node : order_to_nodes[order])
			{
				for (auto &it : nodes[node].links)
				{
					int target = it.first;
					SigBit ctrl = state_sig[node];

					if (it.second != State::S1)
						ctrl = module->And(NEW_ID, ctrl, it.second);

					state_sig[target] = module->Or(NEW_ID, state_sig[target], ctrl);
				}
			}
		}

		// Construct activations

		{
			vector<SigSpec> activate_sig(GetSize(nodes));
			vector<SigBit> activate_bit(GetSize(nodes));

			for (int i = 0; i < GetSize(nodes); i++) {
				for (auto &it : nodes[i].edges)
					activate_sig[it.first].append(module->And(NEW_ID, state_sig[i], it.second));
			}

			for (int i = 0; i < GetSize(nodes); i++) {
				if (GetSize(activate_sig[i]) == 0)
					next_state_sig[i] = State::S0;
				else if (GetSize(activate_sig[i]) == 1)
					next_state_sig[i] = activate_sig[i];
				else
					next_state_sig[i] = module->ReduceOr(NEW_ID, activate_sig[i]);
			}
		}

		// Create state FFs

		for (int i = 0; i < GetSize(nodes); i++)
		{
			if (next_state_sig[i] != State::S0) {
				clocking.addDff(NEW_ID, next_state_sig[i], state_wire[i], State::S0);
			} else {
				module->connect(state_wire[i], State::S0);
			}
		}

		final_accept_sig = state_sig[acceptNode];
		return final_accept_sig;
	}

	// ----------------------------------------------------
	// Generating quantifier-based NFSM circuit to acquire reject signal

	SigBit getAnyAllRejectWorker(bool /* allMode */)
	{
		// FIXME
		log_abort();
	}

	SigBit getAnyReject()
	{
		return getAnyAllRejectWorker(false);
	}

	SigBit getAllReject()
	{
		return getAnyAllRejectWorker(true);
	}

	// ----------------------------------------------------
	// Generating DFSM circuit to acquire reject signal

	void node_to_unode(int node, int unode, SigSpec ctrl)
	{
		if (node == acceptNode)
			unodes[unode].accept.push_back(ctrl);

		if (node == condNode)
			unodes[unode].cond.push_back(ctrl);

		for (auto &it : nodes[node].edges) {
			if (it.second != State::S1) {
				SigSpec s = {ctrl, it.second};
				s.sort_and_unify();
				unodes[unode].edges.push_back(make_pair(it.first, s));
			} else {
				unodes[unode].edges.push_back(make_pair(it.first, ctrl));
			}
		}

		for (auto &it : nodes[node].links) {
			if (it.second != State::S1) {
				SigSpec s = {ctrl, it.second};
				s.sort_and_unify();
				node_to_unode(it.first, unode, s);
			} else {
				node_to_unode(it.first, unode, ctrl);
			}
		}
	}

	void mark_reachable_unode(int unode)
	{
		if (unodes[unode].reachable)
			return;

		unodes[unode].reachable = true;
		for (auto &it : unodes[unode].edges)
			mark_reachable_unode(it.first);
	}

	void usortint(vector<int> &vec)
	{
		vector<int> newvec;
		std::sort(vec.begin(), vec.end());
		for (int i = 0; i < GetSize(vec); i++)
			if (i == GetSize(vec)-1 || vec[i] != vec[i+1])
				newvec.push_back(vec[i]);
		vec.swap(newvec);
	}

	bool cmp_ctrl(const pool<SigBit> &ctrl_bits, const SigSpec &ctrl)
	{
		for (int i = 0; i < GetSize(ctrl); i++)
			if (ctrl_bits.count(ctrl[i]) == 0)
				return false;
		return true;
	}

	void create_dnode(const vector<int> &state, bool firstmatch, bool condaccept)
	{
		if (dnodes.count(state) != 0)
			return;

		SvaDFsmNode dnode;
		dnodes[state] = SvaDFsmNode();

		for (int unode : state) {
			log_assert(unodes[unode].reachable);
			for (auto &it : unodes[unode].edges)
				dnode.ctrl.append(it.second);
			for (auto &it : unodes[unode].accept)
				dnode.ctrl.append(it);
			for (auto &it : unodes[unode].cond)
				dnode.ctrl.append(it);
		}

		dnode.ctrl.sort_and_unify();

		if (GetSize(dnode.ctrl) > verific_sva_fsm_limit) {
			if (verific_verbose >= 2) {
				log("    detected state explosion in DFSM generation:\n");
				dump();
				log("      ctrl signal: %s\n", log_signal(dnode.ctrl));
			}
			log_error("SVA DFSM state ctrl signal has %d (>%d) bits. Stopping to prevent exponential design size explosion.\n",
					GetSize(dnode.ctrl), verific_sva_fsm_limit);
		}

		for (int i = 0; i < (1 << GetSize(dnode.ctrl)); i++)
		{
			Const ctrl_val(i, GetSize(dnode.ctrl));
			pool<SigBit> ctrl_bits;

			for (int i = 0; i < GetSize(dnode.ctrl); i++)
				if (ctrl_val[i] == State::S1)
					ctrl_bits.insert(dnode.ctrl[i]);

			vector<int> new_state;
			bool accept = false, cond = false;

			for (int unode : state) {
				for (auto &it : unodes[unode].accept)
					if (cmp_ctrl(ctrl_bits, it))
						accept = true;
				for (auto &it : unodes[unode].cond)
					if (cmp_ctrl(ctrl_bits, it))
						cond = true;
			}

			bool new_state_cond = false;
			bool new_state_noncond = false;

			if (accept && condaccept)
				accept = cond;

			if (!accept || !firstmatch) {
				for (int unode : state)
				for (auto &it : unodes[unode].edges)
					if (cmp_ctrl(ctrl_bits, it.second)) {
						if (nodes.at(it.first).is_cond_node)
							new_state_cond = true;
						else
							new_state_noncond = true;
						new_state.push_back(it.first);
					}
			}

			if (accept)
				dnode.accept.push_back(ctrl_val);

			if (condaccept && (!new_state_cond || !new_state_noncond))
				new_state.clear();

			if (new_state.empty()) {
				if (!accept)
					dnode.reject.push_back(ctrl_val);
			} else {
				usortint(new_state);
				dnode.edges.push_back(make_pair(new_state, ctrl_val));
				create_dnode(new_state, firstmatch, condaccept);
			}
		}

		dnodes[state] = dnode;
	}

	void optimize_cond(vector<Const> &values)
	{
		bool did_something = true;

		while (did_something)
		{
			did_something = false;

			for (int i = 0; i < GetSize(values); i++)
			for (int j = 0; j < GetSize(values); j++)
			{
				if (i == j)
					continue;

				log_assert(GetSize(values[i]) == GetSize(values[j]));

				int delta_pos = -1;
				bool i_within_j = true;
				bool j_within_i = true;

				for (int k = 0; k < GetSize(values[i]); k++) {
					if (values[i][k] == State::Sa && values[j][k] != State::Sa) {
						i_within_j = false;
						continue;
					}
					if (values[i][k] != State::Sa && values[j][k] == State::Sa) {
						j_within_i = false;
						continue;
					}
					if (values[i][k] == values[j][k])
						continue;
					if (delta_pos >= 0)
						goto next_pair;
					delta_pos = k;
				}

				if (delta_pos >= 0 && i_within_j && j_within_i) {
					did_something = true;
					values[i][delta_pos] = State::Sa;
					values[j] = values.back();
					values.pop_back();
					goto next_pair;
				}

				if (delta_pos < 0 && i_within_j) {
					did_something = true;
					values[i] = values.back();
					values.pop_back();
					goto next_pair;
				}

				if (delta_pos < 0 && j_within_i) {
					did_something = true;
					values[j] = values.back();
					values.pop_back();
					goto next_pair;
				}
		next_pair:;
			}
		}
	}

	SigBit make_cond_eq(const SigSpec &ctrl, const Const &value, SigBit enable = State::S1)
	{
		SigSpec sig_a, sig_b;

		log_assert(GetSize(ctrl) == GetSize(value));

		for (int i = 0; i < GetSize(ctrl); i++)
			if (value[i] != State::Sa) {
				sig_a.append(ctrl[i]);
				sig_b.append(value[i]);
			}

		if (GetSize(sig_a) == 0)
			return enable;

		if (enable != State::S1) {
			sig_a.append(enable);
			sig_b.append(State::S1);
		}

		auto key = make_pair(sig_a, sig_b);

		if (cond_eq_cache.count(key) == 0)
		{
			if (sig_b == State::S1)
				cond_eq_cache[key] = sig_a;
			else if (sig_b == State::S0)
				cond_eq_cache[key] = module->Not(NEW_ID, sig_a);
			else
				cond_eq_cache[key] = module->Eq(NEW_ID, sig_a, sig_b);

			if (verific_verbose >= 2) {
				log("    Cond: %s := %s == %s\n", log_signal(cond_eq_cache[key]),
						log_signal(sig_a), log_signal(sig_b));
			}
		}

		return cond_eq_cache.at(key);
	}

	void getFirstAcceptReject(SigBit *accept_p, SigBit *reject_p)
	{
		log_assert(!materialized);
		materialized = true;

		// Create unlinked NFSM

		unodes.resize(GetSize(nodes));

		for (int node = 0; node < GetSize(nodes); node++)
			node_to_unode(node, node, SigSpec());

		mark_reachable_unode(startNode);

		// Create DFSM

		create_dnode(vector<int>{startNode}, true, false);
		dnodes.sort();

		// Create DFSM Circuit

		SigSpec accept_sig, reject_sig;

		for (auto &it : dnodes)
		{
			SvaDFsmNode &dnode = it.second;
			dnode.ffoutwire = module->addWire(NEW_ID);
			dnode.statesig = dnode.ffoutwire;

			if (it.first == vector<int>{startNode})
				dnode.statesig = module->Or(NEW_ID, dnode.statesig, trigger_sig);
		}

		for (auto &it : dnodes)
		{
			SvaDFsmNode &dnode = it.second;
			dict<vector<int>, vector<Const>> edge_cond;

			for (auto &edge : dnode.edges)
				edge_cond[edge.first].push_back(edge.second);

			for (auto &it : edge_cond) {
				optimize_cond(it.second);
				for (auto &value : it.second)
					dnodes.at(it.first).nextstate.append(make_cond_eq(dnode.ctrl, value, dnode.statesig));
			}

			if (accept_p) {
				vector<Const> accept_cond = dnode.accept;
				optimize_cond(accept_cond);
				for (auto &value : accept_cond)
					accept_sig.append(make_cond_eq(dnode.ctrl, value, dnode.statesig));
			}

			if (reject_p) {
				vector<Const> reject_cond = dnode.reject;
				optimize_cond(reject_cond);
				for (auto &value : reject_cond)
					reject_sig.append(make_cond_eq(dnode.ctrl, value, dnode.statesig));
			}
		}

		for (auto &it : dnodes)
		{
			SvaDFsmNode &dnode = it.second;
			if (GetSize(dnode.nextstate) == 0) {
				module->connect(dnode.ffoutwire, State::S0);
			} else
			if (GetSize(dnode.nextstate) == 1) {
				clocking.addDff(NEW_ID, dnode.nextstate, dnode.ffoutwire, State::S0);
			} else {
				SigSpec nextstate = module->ReduceOr(NEW_ID, dnode.nextstate);
				clocking.addDff(NEW_ID, nextstate, dnode.ffoutwire, State::S0);
			}
		}

		if (accept_p)
		{
			if (GetSize(accept_sig) == 0)
				final_accept_sig = State::S0;
			else if (GetSize(accept_sig) == 1)
				final_accept_sig = accept_sig;
			else
				final_accept_sig = module->ReduceOr(NEW_ID, accept_sig);
			*accept_p = final_accept_sig;
		}

		if (reject_p)
		{
			if (GetSize(reject_sig) == 0)
				final_reject_sig = State::S0;
			else if (GetSize(reject_sig) == 1)
				final_reject_sig = reject_sig;
			else
				final_reject_sig = module->ReduceOr(NEW_ID, reject_sig);
			*reject_p = final_reject_sig;
		}
	}

	SigBit getFirstAccept()
	{
		SigBit accept;
		getFirstAcceptReject(&accept, nullptr);
		return accept;
	}

	SigBit getReject()
	{
		SigBit reject;
		getFirstAcceptReject(nullptr, &reject);
		return reject;
	}

	void getDFsm(SvaFsm &output_fsm, int output_start_node, int output_accept_node, int output_reject_node = -1, bool firstmatch = true, bool condaccept = false)
	{
		log_assert(!materialized);
		materialized = true;

		// Create unlinked NFSM

		unodes.resize(GetSize(nodes));

		for (int node = 0; node < GetSize(nodes); node++)
			node_to_unode(node, node, SigSpec());

		mark_reachable_unode(startNode);

		// Create DFSM

		create_dnode(vector<int>{startNode}, firstmatch, condaccept);
		dnodes.sort();

		// Create DFSM Graph

		for (auto &it : dnodes)
		{
			SvaDFsmNode &dnode = it.second;
			dnode.outnode = output_fsm.createNode();

			if (it.first == vector<int>{startNode})
				output_fsm.createLink(output_start_node, dnode.outnode);

			if (output_accept_node >= 0) {
				vector<Const> accept_cond = dnode.accept;
				optimize_cond(accept_cond);
				for (auto &value : accept_cond)
					output_fsm.createLink(it.second.outnode, output_accept_node, make_cond_eq(dnode.ctrl, value));
			}

			if (output_reject_node >= 0) {
				vector<Const> reject_cond = dnode.reject;
				optimize_cond(reject_cond);
				for (auto &value : reject_cond)
					output_fsm.createLink(it.second.outnode, output_reject_node, make_cond_eq(dnode.ctrl, value));
			}
		}

		for (auto &it : dnodes)
		{
			SvaDFsmNode &dnode = it.second;
			dict<vector<int>, vector<Const>> edge_cond;

			for (auto &edge : dnode.edges)
				edge_cond[edge.first].push_back(edge.second);

			for (auto &it : edge_cond) {
				optimize_cond(it.second);
				for (auto &value : it.second)
					output_fsm.createEdge(dnode.outnode, dnodes.at(it.first).outnode, make_cond_eq(dnode.ctrl, value));
			}
		}
	}

	// ----------------------------------------------------
	// State dump for verbose log messages

	void dump_nodes()
	{
		if (nodes.empty())
			return;

		log("      non-deterministic encoding:\n");
		for (int i = 0; i < GetSize(nodes); i++)
		{
			log("        node %d:%s\n", i,
					i == startNode ? " [start]" :
					i == acceptNode ? " [accept]" :
					i == condNode ? " [cond]" : "");

			for (auto &it : nodes[i].edges) {
				if (it.second != State::S1)
					log("          edge %s -> %d\n", log_signal(it.second), it.first);
				else
					log("          edge -> %d\n", it.first);
			}

			for (auto &it : nodes[i].links) {
				if (it.second != State::S1)
					log("          link %s -> %d\n", log_signal(it.second), it.first);
				else
					log("          link -> %d\n", it.first);
			}
		}
	}

	void dump_unodes()
	{
		if (unodes.empty())
			return;

		log("      unlinked non-deterministic encoding:\n");
		for (int i = 0; i < GetSize(unodes); i++)
		{
			if (!unodes[i].reachable)
				continue;

			log("        unode %d:%s\n", i, i == startNode ? " [start]" : "");

			for (auto &it : unodes[i].edges) {
				if (!it.second.empty())
					log("          edge %s -> %d\n", log_signal(it.second), it.first);
				else
					log("          edge -> %d\n", it.first);
			}

			for (auto &ctrl : unodes[i].accept) {
				if (!ctrl.empty())
					log("          accept %s\n", log_signal(ctrl));
				else
					log("          accept\n");
			}

			for (auto &ctrl : unodes[i].cond) {
				if (!ctrl.empty())
					log("          cond %s\n", log_signal(ctrl));
				else
					log("          cond\n");
			}
		}
	}

	void dump_dnodes()
	{
		if (dnodes.empty())
			return;

		log("      deterministic encoding:\n");
		for (auto &it : dnodes)
		{
			log("        dnode {");
			for (int i = 0; i < GetSize(it.first); i++)
				log("%s%d", i ? "," : "", it.first[i]);
			log("}:%s\n", GetSize(it.first) == 1 && it.first[0] == startNode ? " [start]" : "");

			log("          ctrl %s\n", log_signal(it.second.ctrl));

			for (auto &edge : it.second.edges) {
				log("          edge %s -> {", log_signal(edge.second));
				for (int i = 0; i < GetSize(edge.first); i++)
					log("%s%d", i ? "," : "", edge.first[i]);
				log("}\n");
			}

			for (auto &value : it.second.accept)
				log("          accept %s\n", log_signal(value));

			for (auto &value : it.second.reject)
				log("          reject %s\n", log_signal(value));
		}
	}

	void dump()
	{
		if (!nodes.empty())
			log("      number of NFSM states: %d\n", GetSize(nodes));

		if (!unodes.empty()) {
			int count = 0;
			for (auto &unode : unodes)
				if (unode.reachable)
					count++;
			log("      number of reachable UFSM states: %d\n", count);
		}

		if (!dnodes.empty())
			log("      number of DFSM states: %d\n", GetSize(dnodes));

		if (verific_verbose >= 2) {
			dump_nodes();
			dump_unodes();
			dump_dnodes();
		}

		if (trigger_sig != State::S1)
			log("      trigger signal: %s\n", log_signal(trigger_sig));

		if (final_accept_sig != State::Sx)
			log("      accept signal: %s\n", log_signal(final_accept_sig));

		if (final_reject_sig != State::Sx)
			log("      reject signal: %s\n", log_signal(final_reject_sig));
	}
};

PRIVATE_NAMESPACE_END

YOSYS_NAMESPACE_BEGIN

pool<int> verific_sva_prims = {
	// Copy&paste from Verific 3.16_484_32_170630 Netlist.h
	PRIM_SVA_IMMEDIATE_ASSERT, PRIM_SVA_ASSERT, PRIM_SVA_COVER, PRIM_SVA_ASSUME,
	PRIM_SVA_EXPECT, PRIM_SVA_POSEDGE, PRIM_SVA_NOT, PRIM_SVA_FIRST_MATCH,
	PRIM_SVA_ENDED, PRIM_SVA_MATCHED, PRIM_SVA_CONSECUTIVE_REPEAT,
	PRIM_SVA_NON_CONSECUTIVE_REPEAT, PRIM_SVA_GOTO_REPEAT,
	PRIM_SVA_MATCH_ITEM_TRIGGER, PRIM_SVA_AND, PRIM_SVA_OR, PRIM_SVA_SEQ_AND,
	PRIM_SVA_SEQ_OR, PRIM_SVA_EVENT_OR, PRIM_SVA_OVERLAPPED_IMPLICATION,
	PRIM_SVA_NON_OVERLAPPED_IMPLICATION, PRIM_SVA_OVERLAPPED_FOLLOWED_BY,
	PRIM_SVA_NON_OVERLAPPED_FOLLOWED_BY, PRIM_SVA_INTERSECT, PRIM_SVA_THROUGHOUT,
	PRIM_SVA_WITHIN, PRIM_SVA_AT, PRIM_SVA_DISABLE_IFF, PRIM_SVA_SAMPLED,
	PRIM_SVA_ROSE, PRIM_SVA_FELL, PRIM_SVA_STABLE, PRIM_SVA_PAST,
	PRIM_SVA_MATCH_ITEM_ASSIGN, PRIM_SVA_SEQ_CONCAT, PRIM_SVA_IF,
	PRIM_SVA_RESTRICT, PRIM_SVA_TRIGGERED, PRIM_SVA_STRONG, PRIM_SVA_WEAK,
	PRIM_SVA_NEXTTIME, PRIM_SVA_S_NEXTTIME, PRIM_SVA_ALWAYS, PRIM_SVA_S_ALWAYS,
	PRIM_SVA_S_EVENTUALLY, PRIM_SVA_EVENTUALLY, PRIM_SVA_UNTIL, PRIM_SVA_S_UNTIL,
	PRIM_SVA_UNTIL_WITH, PRIM_SVA_S_UNTIL_WITH, PRIM_SVA_IMPLIES, PRIM_SVA_IFF,
	PRIM_SVA_ACCEPT_ON, PRIM_SVA_REJECT_ON, PRIM_SVA_SYNC_ACCEPT_ON,
	PRIM_SVA_SYNC_REJECT_ON, PRIM_SVA_GLOBAL_CLOCKING_DEF,
	PRIM_SVA_GLOBAL_CLOCKING_REF, PRIM_SVA_IMMEDIATE_ASSUME,
	PRIM_SVA_IMMEDIATE_COVER, OPER_SVA_SAMPLED, OPER_SVA_STABLE
};

struct VerificSvaImporter
{
	VerificImporter *importer = nullptr;
	Module *module = nullptr;

	Netlist *netlist = nullptr;
	Instance *root = nullptr;

	VerificClocking clocking;

	bool mode_assert = false;
	bool mode_assume = false;
	bool mode_cover = false;
	bool mode_trigger = false;

	Instance *net_to_ast_driver(Net *n)
	{
		if (n == nullptr)
			return nullptr;

		if (n->IsMultipleDriven())
			return nullptr;

		Instance *inst = n->Driver();

		if (inst == nullptr)
			return nullptr;

		if (!verific_sva_prims.count(inst->Type()))
			return nullptr;

		if (inst->Type() == PRIM_SVA_ROSE || inst->Type() == PRIM_SVA_FELL ||
				inst->Type() == PRIM_SVA_STABLE || inst->Type() == OPER_SVA_STABLE ||
				inst->Type() == PRIM_SVA_PAST || inst->Type() == PRIM_SVA_TRIGGERED)
			return nullptr;

		return inst;
	}

	Instance *get_ast_input(Instance *inst) { return net_to_ast_driver(inst->GetInput()); }
	Instance *get_ast_input1(Instance *inst) { return net_to_ast_driver(inst->GetInput1()); }
	Instance *get_ast_input2(Instance *inst) { return net_to_ast_driver(inst->GetInput2()); }
	Instance *get_ast_input3(Instance *inst) { return net_to_ast_driver(inst->GetInput3()); }
	Instance *get_ast_control(Instance *inst) { return net_to_ast_driver(inst->GetControl()); }

	// ----------------------------------------------------------
	// SVA Importer

	struct ParserErrorException {
	};

	[[noreturn]] void parser_error(std::string errmsg)
	{
		if (!importer->mode_keep)
			log_error("%s", errmsg.c_str());
		log_warning("%s", errmsg.c_str());
		throw ParserErrorException();
	}

	[[noreturn]] void parser_error(std::string errmsg, linefile_type loc)
	{
		parser_error(stringf("%s at %s:%d.\n", errmsg.c_str(), LineFile::GetFileName(loc), LineFile::GetLineNo(loc)));
	}

	[[noreturn]] void parser_error(std::string errmsg, Instance *inst)
	{
		parser_error(stringf("%s at %s (%s)", errmsg.c_str(), inst->View()->Owner()->Name(), inst->Name()), inst->Linefile());
	}

	[[noreturn]] void parser_error(Instance *inst)
	{
		parser_error(stringf("Verific SVA primitive %s (%s) is currently unsupported in this context",
				inst->View()->Owner()->Name(), inst->Name()), inst->Linefile());
	}

	dict<Net*, bool, hash_ptr_ops> check_expression_cache;

	bool check_expression(Net *net, bool raise_error = false)
	{
		while (!check_expression_cache.count(net))
		{
			Instance *inst = net_to_ast_driver(net);

			if (inst == nullptr) {
				check_expression_cache[net] = true;
				break;
			}

			if (inst->Type() == PRIM_SVA_AT)
			{
				VerificClocking new_clocking(importer, net);
				log_assert(new_clocking.cond_net == nullptr);
				if (!clocking.property_matches_sequence(new_clocking))
					parser_error("Mixed clocking is currently not supported", inst);
				check_expression_cache[net] = check_expression(new_clocking.body_net, raise_error);
				break;
			}

			if (inst->Type() == PRIM_SVA_FIRST_MATCH || inst->Type() == PRIM_SVA_NOT)
			{
				check_expression_cache[net] = check_expression(inst->GetInput(), raise_error);
				break;
			}

			if (inst->Type() == PRIM_SVA_SEQ_OR || inst->Type() == PRIM_SVA_SEQ_AND || inst->Type() == PRIM_SVA_INTERSECT ||
					inst->Type() == PRIM_SVA_WITHIN || inst->Type() == PRIM_SVA_THROUGHOUT ||
					inst->Type() == PRIM_SVA_OR || inst->Type() == PRIM_SVA_AND)
			{
				check_expression_cache[net] = check_expression(inst->GetInput1(), raise_error) && check_expression(inst->GetInput2(), raise_error);
				break;
			}

			if (inst->Type() == PRIM_SVA_SEQ_CONCAT)
			{
				const char *sva_low_s = inst->GetAttValue("sva:low");
				const char *sva_high_s = inst->GetAttValue("sva:high");

				int sva_low = atoi(sva_low_s);
				int sva_high = atoi(sva_high_s);
				bool sva_inf = !strcmp(sva_high_s, "$");

				if (sva_low == 0 && sva_high == 0 && !sva_inf)
					check_expression_cache[net] = check_expression(inst->GetInput1(), raise_error) && check_expression(inst->GetInput2(), raise_error);
				else
					check_expression_cache[net] = false;
				break;
			}

			check_expression_cache[net] = false;
		}

		if (raise_error && !check_expression_cache.at(net))
			parser_error(net_to_ast_driver(net));
		return check_expression_cache.at(net);
	}

	SigBit parse_expression(Net *net)
	{
		check_expression(net, true);

		Instance *inst = net_to_ast_driver(net);

		if (inst == nullptr) {
			return importer->net_map_at(net);
		}

		if (inst->Type() == PRIM_SVA_AT)
		{
			VerificClocking new_clocking(importer, net);
			log_assert(new_clocking.cond_net == nullptr);
			if (!clocking.property_matches_sequence(new_clocking))
				parser_error("Mixed clocking is currently not supported", inst);
			return parse_expression(new_clocking.body_net);
		}

		if (inst->Type() == PRIM_SVA_FIRST_MATCH)
			return parse_expression(inst->GetInput());

		if (inst->Type() == PRIM_SVA_NOT)
			return module->Not(NEW_ID, parse_expression(inst->GetInput()));

		if (inst->Type() == PRIM_SVA_SEQ_OR || inst->Type() == PRIM_SVA_OR)
			return module->Or(NEW_ID, parse_expression(inst->GetInput1()), parse_expression(inst->GetInput2()));

		if (inst->Type() == PRIM_SVA_SEQ_AND || inst->Type() == PRIM_SVA_AND || inst->Type() == PRIM_SVA_INTERSECT ||
				inst->Type() == PRIM_SVA_WITHIN || inst->Type() == PRIM_SVA_THROUGHOUT || inst->Type() == PRIM_SVA_SEQ_CONCAT)
			return module->And(NEW_ID, parse_expression(inst->GetInput1()), parse_expression(inst->GetInput2()));

		log_abort();
	}

	bool check_zero_consecutive_repeat(Net *net)
	{
		Instance *inst = net_to_ast_driver(net);

		if (inst == nullptr)
			return false;

		if (inst->Type() != PRIM_SVA_CONSECUTIVE_REPEAT)
			return false;

		const char *sva_low_s = inst->GetAttValue("sva:low");
		int sva_low = atoi(sva_low_s);

		return sva_low == 0;
	}

	int parse_consecutive_repeat(SvaFsm &fsm, int start_node, Net *net, bool add_pre_delay, bool add_post_delay)
	{
		Instance *inst = net_to_ast_driver(net);

		log_assert(inst->Type() == PRIM_SVA_CONSECUTIVE_REPEAT);

		const char *sva_low_s = inst->GetAttValue("sva:low");
		const char *sva_high_s = inst->GetAttValue("sva:high");

		int sva_low = atoi(sva_low_s);
		int sva_high = atoi(sva_high_s);
		bool sva_inf = !strcmp(sva_high_s, "$");

		Net *body_net = inst->GetInput();

		if (add_pre_delay || add_post_delay)
			log_assert(sva_low == 0);

		if (sva_low == 0) {
			if (!add_pre_delay && !add_post_delay)
				parser_error("Possibly zero-length consecutive repeat must follow or precede a delay of at least one cycle", inst);
			sva_low++;
		}

		int node = fsm.createNode(start_node);
		start_node = node;

		if (add_pre_delay) {
			node = fsm.createNode(start_node);
			fsm.createEdge(start_node, node);
		}

		int prev_node = node;
		node = parse_sequence(fsm, node, body_net);

		for (int i = 1; i < sva_low; i++)
		{
			int next_node = fsm.createNode();
			fsm.createEdge(node, next_node);

			prev_node = node;
			node = parse_sequence(fsm, next_node, body_net);
		}

		if (sva_inf)
		{
			log_assert(prev_node >= 0);
			fsm.createEdge(node, prev_node);
		}
		else
		{
			for (int i = sva_low; i < sva_high; i++)
			{
				int next_node = fsm.createNode();
				fsm.createEdge(node, next_node);

				prev_node = node;
				node = parse_sequence(fsm, next_node, body_net);

				fsm.createLink(prev_node, node);
			}
		}

		if (add_post_delay) {
			int next_node = fsm.createNode();
			fsm.createEdge(node, next_node);
			node = next_node;
		}

		if (add_pre_delay || add_post_delay)
			fsm.createLink(start_node, node);

		return node;
	}

	int parse_sequence(SvaFsm &fsm, int start_node, Net *net)
	{
		if (check_expression(net)) {
			int node = fsm.createNode();
			fsm.createLink(start_node, node, parse_expression(net));
			return node;
		}

		Instance *inst = net_to_ast_driver(net);

		if (inst->Type() == PRIM_SVA_AT)
		{
			VerificClocking new_clocking(importer, net);
			log_assert(new_clocking.cond_net == nullptr);
			if (!clocking.property_matches_sequence(new_clocking))
				parser_error("Mixed clocking is currently not supported", inst);
			return parse_sequence(fsm, start_node, new_clocking.body_net);
		}

		if (inst->Type() == PRIM_SVA_FIRST_MATCH)
		{
			SvaFsm match_fsm(clocking);
			match_fsm.createLink(parse_sequence(match_fsm, match_fsm.createStartNode(), inst->GetInput()), match_fsm.acceptNode);

			int node = fsm.createNode();
			match_fsm.getDFsm(fsm, start_node, node);

			if (verific_verbose) {
				log("    First Match FSM:\n");
				match_fsm.dump();
			}

			return node;
		}

		if (inst->Type() == PRIM_SVA_NEXTTIME || inst->Type() == PRIM_SVA_S_NEXTTIME)
		{
			const char *sva_low_s = inst->GetAttValue("sva:low");
			const char *sva_high_s = inst->GetAttValue("sva:high");

			int sva_low = atoi(sva_low_s);
			int sva_high = atoi(sva_high_s);
			log_assert(sva_low == sva_high);

			int node = start_node;

			for (int i = 0; i < sva_low; i++) {
				int next_node = fsm.createNode();
				fsm.createEdge(node, next_node);
				node = next_node;
			}

			return parse_sequence(fsm, node, inst->GetInput());
		}

		if (inst->Type() == PRIM_SVA_SEQ_CONCAT)
		{
			const char *sva_low_s = inst->GetAttValue("sva:low");
			const char *sva_high_s = inst->GetAttValue("sva:high");

			int sva_low = atoi(sva_low_s);
			int sva_high = atoi(sva_high_s);
			bool sva_inf = !strcmp(sva_high_s, "$");

			int node = -1;
			bool past_add_delay = false;

			if (check_zero_consecutive_repeat(inst->GetInput1()) && sva_low > 0) {
				node = parse_consecutive_repeat(fsm, start_node, inst->GetInput1(), false, true);
				sva_low--, sva_high--;
			} else {
				node = parse_sequence(fsm, start_node, inst->GetInput1());
			}

			if (check_zero_consecutive_repeat(inst->GetInput2()) && sva_low > 0) {
				past_add_delay = true;
				sva_low--, sva_high--;
			}

			for (int i = 0; i < sva_low; i++) {
				int next_node = fsm.createNode();
				fsm.createEdge(node, next_node);
				node = next_node;
			}

			if (sva_inf)
			{
				fsm.createEdge(node, node);
			}
			else
			{
				for (int i = sva_low; i < sva_high; i++)
				{
					int next_node = fsm.createNode();
					fsm.createEdge(node, next_node);
					fsm.createLink(node, next_node);
					node = next_node;
				}
			}

			if (past_add_delay)
				node = parse_consecutive_repeat(fsm, node, inst->GetInput2(), true, false);
			else
				node = parse_sequence(fsm, node, inst->GetInput2());

			return node;
		}

		if (inst->Type() == PRIM_SVA_CONSECUTIVE_REPEAT)
		{
			return parse_consecutive_repeat(fsm, start_node, net, false, false);
		}

		if (inst->Type() == PRIM_SVA_NON_CONSECUTIVE_REPEAT || inst->Type() == PRIM_SVA_GOTO_REPEAT)
		{
			const char *sva_low_s = inst->GetAttValue("sva:low");
			const char *sva_high_s = inst->GetAttValue("sva:high");

			int sva_low = atoi(sva_low_s);
			int sva_high = atoi(sva_high_s);
			bool sva_inf = !strcmp(sva_high_s, "$");

			Net *body_net = inst->GetInput();
			int node = fsm.createNode(start_node);

			SigBit cond = parse_expression(body_net);
			SigBit not_cond = module->Not(NEW_ID, cond);

			for (int i = 0; i < sva_low; i++)
			{
				int wait_node = fsm.createNode();
				fsm.createEdge(wait_node, wait_node, not_cond);

				if (i == 0)
					fsm.createLink(node, wait_node);
				else
					fsm.createEdge(node, wait_node);

				int next_node = fsm.createNode();
				fsm.createLink(wait_node, next_node, cond);

				node = next_node;
			}

			if (sva_inf)
			{
				int wait_node = fsm.createNode();
				fsm.createEdge(wait_node, wait_node, not_cond);
				fsm.createEdge(node, wait_node);
				fsm.createLink(wait_node, node, cond);
			}
			else
			{
				for (int i = sva_low; i < sva_high; i++)
				{
					int wait_node = fsm.createNode();
					fsm.createEdge(wait_node, wait_node, not_cond);

					if (i == 0)
						fsm.createLink(node, wait_node);
					else
						fsm.createEdge(node, wait_node);

					int next_node = fsm.createNode();
					fsm.createLink(wait_node, next_node, cond);

					fsm.createLink(node, next_node);
					node = next_node;
				}
			}

			if (inst->Type() == PRIM_SVA_NON_CONSECUTIVE_REPEAT)
				fsm.createEdge(node, node);

			return node;
		}

		if (inst->Type() == PRIM_SVA_SEQ_OR || inst->Type() == PRIM_SVA_OR)
		{
			int node = parse_sequence(fsm, start_node, inst->GetInput1());
			int node2 = parse_sequence(fsm, start_node, inst->GetInput2());
			fsm.createLink(node2, node);
			return node;
		}

		if (inst->Type() == PRIM_SVA_SEQ_AND || inst->Type() == PRIM_SVA_AND)
		{
			SvaFsm fsm1(clocking);
			fsm1.createLink(parse_sequence(fsm1, fsm1.createStartNode(), inst->GetInput1()), fsm1.acceptNode);

			SvaFsm fsm2(clocking);
			fsm2.createLink(parse_sequence(fsm2, fsm2.createStartNode(), inst->GetInput2()), fsm2.acceptNode);

			SvaFsm combined_fsm(clocking);
			fsm1.getDFsm(combined_fsm, combined_fsm.createStartNode(), -1, combined_fsm.acceptNode);
			fsm2.getDFsm(combined_fsm, combined_fsm.createStartNode(), -1, combined_fsm.acceptNode);

			int node = fsm.createNode();
			combined_fsm.getDFsm(fsm, start_node, -1, node);

			if (verific_verbose)
			{
				log("    Left And FSM:\n");
				fsm1.dump();

				log("    Right And FSM:\n");
				fsm1.dump();

				log("    Combined And FSM:\n");
				combined_fsm.dump();
			}

			return node;
		}

		if (inst->Type() == PRIM_SVA_INTERSECT || inst->Type() == PRIM_SVA_WITHIN)
		{
			SvaFsm intersect_fsm(clocking);

			if (inst->Type() == PRIM_SVA_INTERSECT)
			{
				intersect_fsm.createLink(parse_sequence(intersect_fsm, intersect_fsm.createStartNode(), inst->GetInput1()), intersect_fsm.acceptNode);
			}
			else
			{
				int n = intersect_fsm.createNode();
				intersect_fsm.createLink(intersect_fsm.createStartNode(), n);
				intersect_fsm.createEdge(n, n);

				n = parse_sequence(intersect_fsm, n, inst->GetInput1());

				intersect_fsm.createLink(n, intersect_fsm.acceptNode);
				intersect_fsm.createEdge(n, n);
			}

			intersect_fsm.in_cond_mode = true;
			intersect_fsm.createLink(parse_sequence(intersect_fsm, intersect_fsm.createStartNode(), inst->GetInput2()), intersect_fsm.condNode);
			intersect_fsm.in_cond_mode = false;

			int node = fsm.createNode();
			intersect_fsm.getDFsm(fsm, start_node, node, -1, false, true);

			if (verific_verbose) {
				log("    Intersect FSM:\n");
				intersect_fsm.dump();
			}

			return node;
		}

		if (inst->Type() == PRIM_SVA_THROUGHOUT)
		{
			SigBit expr = parse_expression(inst->GetInput1());

			fsm.pushThroughout(expr);
			int node = parse_sequence(fsm, start_node, inst->GetInput2());
			fsm.popThroughout();

			return node;
		}

		parser_error(inst);
	}

	void get_fsm_accept_reject(SvaFsm &fsm, SigBit *accept_p, SigBit *reject_p, bool swap_accept_reject = false)
	{
		log_assert(accept_p != nullptr || reject_p != nullptr);

		if (swap_accept_reject)
			get_fsm_accept_reject(fsm, reject_p, accept_p);
		else if (reject_p == nullptr)
			*accept_p = fsm.getAccept();
		else if (accept_p == nullptr)
			*reject_p = fsm.getReject();
		else
			fsm.getFirstAcceptReject(accept_p, reject_p);
	}

	bool eventually_property(Net *&net, SigBit &trig)
	{
		Instance *inst = net_to_ast_driver(net);

		if (inst == nullptr)
			return false;

		if (clocking.cond_net != nullptr)
			trig = importer->net_map_at(clocking.cond_net);
		else
			trig = State::S1;

		if (inst->Type() == PRIM_SVA_S_EVENTUALLY || inst->Type() == PRIM_SVA_EVENTUALLY)
		{
			if (mode_cover || mode_trigger)
				parser_error(inst);

			net = inst->GetInput();
			clocking.cond_net = nullptr;

			return true;
		}

		if (inst->Type() == PRIM_SVA_OVERLAPPED_IMPLICATION ||
				inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION)
		{
			Net *antecedent_net = inst->GetInput1();
			Net *consequent_net = inst->GetInput2();

			Instance *consequent_inst = net_to_ast_driver(consequent_net);

			if (consequent_inst == nullptr)
				return false;

			if (consequent_inst->Type() != PRIM_SVA_S_EVENTUALLY && consequent_inst->Type() != PRIM_SVA_EVENTUALLY)
				return false;

			if (mode_cover || mode_trigger)
				parser_error(consequent_inst);

			int node;

			SvaFsm antecedent_fsm(clocking, trig);
			node = parse_sequence(antecedent_fsm, antecedent_fsm.createStartNode(), antecedent_net);
			if (inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION) {
				int next_node = antecedent_fsm.createNode();
				antecedent_fsm.createEdge(node, next_node);
				node = next_node;
			}
			antecedent_fsm.createLink(node, antecedent_fsm.acceptNode);

			trig = antecedent_fsm.getAccept();
			net = consequent_inst->GetInput();
			clocking.cond_net = nullptr;

			if (verific_verbose) {
				log("    Eventually Antecedent FSM:\n");
				antecedent_fsm.dump();
			}

			return true;
		}

		return false;
	}

	void parse_property(Net *net, SigBit *accept_p, SigBit *reject_p)
	{
		Instance *inst = net_to_ast_driver(net);

		SigBit trig = State::S1;

		if (clocking.cond_net != nullptr)
			trig = importer->net_map_at(clocking.cond_net);

		if (inst == nullptr)
		{
			log_assert(trig == State::S1);

			if (accept_p != nullptr)
				*accept_p = importer->net_map_at(net);
			if (reject_p != nullptr)
				*reject_p = module->Not(NEW_ID, importer->net_map_at(net));
		}
		else
		if (inst->Type() == PRIM_SVA_OVERLAPPED_IMPLICATION ||
				inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION)
		{
			Net *antecedent_net = inst->GetInput1();
			Net *consequent_net = inst->GetInput2();
			int node;

			SvaFsm antecedent_fsm(clocking, trig);
			node = parse_sequence(antecedent_fsm, antecedent_fsm.createStartNode(), antecedent_net);
			if (inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION) {
				int next_node = antecedent_fsm.createNode();
				antecedent_fsm.createEdge(node, next_node);
				node = next_node;
			}

			Instance *consequent_inst = net_to_ast_driver(consequent_net);

			if (consequent_inst && (consequent_inst->Type() == PRIM_SVA_UNTIL || consequent_inst->Type() == PRIM_SVA_S_UNTIL ||
					consequent_inst->Type() == PRIM_SVA_UNTIL_WITH || consequent_inst->Type() == PRIM_SVA_S_UNTIL_WITH ||
					consequent_inst->Type() == PRIM_SVA_ALWAYS || consequent_inst->Type() == PRIM_SVA_S_ALWAYS))
			{
				bool until_with = consequent_inst->Type() == PRIM_SVA_UNTIL_WITH || consequent_inst->Type() == PRIM_SVA_S_UNTIL_WITH;

				Net *until_net = nullptr;
				if (consequent_inst->Type() == PRIM_SVA_ALWAYS || consequent_inst->Type() == PRIM_SVA_S_ALWAYS)
				{
					consequent_net = consequent_inst->GetInput();
					consequent_inst = net_to_ast_driver(consequent_net);
				}
				else
				{
					until_net = consequent_inst->GetInput2();
					consequent_net = consequent_inst->GetInput1();
					consequent_inst = net_to_ast_driver(consequent_net);
				}

				SigBit until_sig = until_net ? parse_expression(until_net) : RTLIL::S0;
				SigBit not_until_sig = module->Not(NEW_ID, until_sig);
				antecedent_fsm.createEdge(node, node, not_until_sig);

				antecedent_fsm.createLink(node, antecedent_fsm.acceptNode, until_with ? State::S1 : not_until_sig);
			}
			else
			{
				antecedent_fsm.createLink(node, antecedent_fsm.acceptNode);
			}

			SigBit antecedent_match = antecedent_fsm.getAccept();

			if (verific_verbose) {
				log("    Antecedent FSM:\n");
				antecedent_fsm.dump();
			}

			bool consequent_not = false;
			if (consequent_inst && consequent_inst->Type() == PRIM_SVA_NOT) {
				consequent_not = true;
				consequent_net = consequent_inst->GetInput();
				consequent_inst = net_to_ast_driver(consequent_net);
			}

			SvaFsm consequent_fsm(clocking, antecedent_match);
			node = parse_sequence(consequent_fsm, consequent_fsm.createStartNode(), consequent_net);
			consequent_fsm.createLink(node, consequent_fsm.acceptNode);

			get_fsm_accept_reject(consequent_fsm, accept_p, reject_p, consequent_not);

			if (verific_verbose) {
				log("    Consequent FSM:\n");
				consequent_fsm.dump();
			}
		}
		else
		{
			bool prop_not = inst->Type() == PRIM_SVA_NOT;
			if (prop_not) {
				net = inst->GetInput();
				inst = net_to_ast_driver(net);
			}

			SvaFsm fsm(clocking, trig);
			int node = parse_sequence(fsm, fsm.createStartNode(), net);
			fsm.createLink(node, fsm.acceptNode);

			get_fsm_accept_reject(fsm, accept_p, reject_p, prop_not);

			if (verific_verbose) {
				log("    Sequence FSM:\n");
				fsm.dump();
			}
		}
	}

	void import()
	{
		try
		{
			module = importer->module;
			netlist = root->Owner();

			if (verific_verbose)
				log("  importing SVA property at root cell %s (%s) at %s:%d.\n", root->Name(), root->View()->Owner()->Name(),
						LineFile::GetFileName(root->Linefile()), LineFile::GetLineNo(root->Linefile()));

			bool is_user_declared = root->IsUserDeclared();

			// FIXME
			if (!is_user_declared) {
				const char *name = root->Name();
				for (int i = 0; name[i]; i++) {
					if (i ? (name[i] < '0' || name[i] > '9') : (name[i] != 'i')) {
						is_user_declared = true;
						break;
					}
				}
			}

			RTLIL::IdString root_name = module->uniquify(importer->mode_names || is_user_declared ? RTLIL::escape_id(root->Name()) : NEW_ID);

			// parse SVA sequence into trigger signal

			clocking = VerificClocking(importer, root->GetInput(), true);
			SigBit accept_bit = State::S0, reject_bit = State::S0;

			if (clocking.body_net == nullptr)
			{
				if (clocking.clock_net != nullptr || clocking.enable_net != nullptr || clocking.disable_net != nullptr ||  clocking.cond_net != nullptr)
					parser_error(stringf("Failed to parse SVA clocking"), root);

				if (mode_assert || mode_assume) {
					reject_bit = module->Not(NEW_ID, parse_expression(root->GetInput()));
				} else {
					accept_bit = parse_expression(root->GetInput());
				}
			}
			else
			{
				Net *net = clocking.body_net;
				SigBit trig;

				if (eventually_property(net, trig))
				{
					SigBit sig_a, sig_en = trig;
					parse_property(net, &sig_a, nullptr);

					// add final FF stage

					SigBit sig_a_q, sig_en_q;

					if (clocking.body_net == nullptr) {
						sig_a_q = sig_a;
						sig_en_q = sig_en;
					} else {
						sig_a_q = module->addWire(NEW_ID);
						sig_en_q = module->addWire(NEW_ID);
						clocking.addDff(NEW_ID, sig_a, sig_a_q, State::S0);
						clocking.addDff(NEW_ID, sig_en, sig_en_q, State::S0);
					}

					// generate fair/live cell

					RTLIL::Cell *c = nullptr;

					if (mode_assert) c = module->addLive(root_name, sig_a_q, sig_en_q);
					if (mode_assume) c = module->addFair(root_name, sig_a_q, sig_en_q);

					importer->import_attributes(c->attributes, root);

					return;
				}
				else
				{
					if (mode_assert || mode_assume) {
						parse_property(net, nullptr, &reject_bit);
					} else {
						parse_property(net, &accept_bit, nullptr);
					}
				}
			}

			if (mode_trigger)
			{
				module->connect(importer->net_map_at(root->GetOutput()), accept_bit);
			}
			else
			{
				SigBit sig_a = module->Not(NEW_ID, reject_bit);
				SigBit sig_en = module->Or(NEW_ID, accept_bit, reject_bit);

				// add final FF stage

				SigBit sig_a_q, sig_en_q;

				if (clocking.body_net == nullptr) {
					sig_a_q = sig_a;
					sig_en_q = sig_en;
				} else {
					sig_a_q = module->addWire(NEW_ID);
					sig_en_q = module->addWire(NEW_ID);
					clocking.addDff(NEW_ID, sig_a, sig_a_q, State::S0);
					clocking.addDff(NEW_ID, sig_en, sig_en_q, State::S0);
				}

				// generate assert/assume/cover cell

				RTLIL::Cell *c = nullptr;

				if (mode_assert) c = module->addAssert(root_name, sig_a_q, sig_en_q);
				if (mode_assume) c = module->addAssume(root_name, sig_a_q, sig_en_q);
				if (mode_cover) c = module->addCover(root_name, sig_a_q, sig_en_q);

				importer->import_attributes(c->attributes, root);
			}
		}
		catch (ParserErrorException)
		{
		}
	}
};

void verific_import_sva_assert(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_assert = true;
	worker.import();
}

void verific_import_sva_assume(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_assume = true;
	worker.import();
}

void verific_import_sva_cover(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_cover = true;
	worker.import();
}

void verific_import_sva_trigger(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_trigger = true;
	worker.import();
}

bool verific_is_sva_net(VerificImporter *importer, Verific::Net *net)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	return worker.net_to_ast_driver(net) != nullptr;
}

YOSYS_NAMESPACE_END
