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


// Currently supported property styles:
//   seq
//   not seq
//   seq |-> seq
//   seq |-> not seq
//   seq |-> seq until expr
//   seq |-> not seq until expr
//
// Currently supported sequence operators:
//   seq ##[N:M] seq
//   seq or seq
//   seq and seq
//   expr throughout seq
//   seq [*N:M]
//
// Notes:
//   |-> is a placeholder for |-> and |=>
//   "until" is a placeholder for all until operators
//   ##[N:M] includes ##N, ##[*], ##[+]
//   [*N:M] includes [*N], [*], [+]
//   [=N:M], [->N:M] includes [=N], [->N]
//
// Expressions can be any boolean expression, including expressions
// that use $past, $rose, $fell, $stable, and sequence.triggered.
//
// -------------------------------------------------------
//
// SVA Properties Simplified Syntax (essentially a todo-list):
//
// prop:
//   not prop
//   prop or prop
//   prop and prop
//   seq |-> prop
//   if (expr) prop [else prop]
//   always prop
//   prop until prop
//   prop implies prop
//   prop iff prop
//   accept_on (expr) prop
//   reject_on (expr) prop
//
// seq:
//   expr
//   seq ##[N:M] seq
//   seq or seq
//   seq and seq
//   seq intersect seq
//   first_match (seq)
//   expr throughout seq
//   seq within seq
//   seq [*N:M]
//   expr [=N:M]
//   expr [->N:M]


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
};

// Non-deterministic FSM after resolving links
struct SvaUFsmNode
{
	// Edge: Activate the target node if all bits in ctrl signal are true, consumes clock cycle
	// Accept: This node functions as an accept node if all bits in ctrl signal are true
	vector<pair<int, SigSpec>> edges;
	vector<SigSpec> accept;
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
	bool materialized = false;

	vector<SigBit> disable_stack;
	vector<SigBit> throughout_stack;

	int startNode, acceptNode;
	vector<SvaNFsmNode> nodes;

	SigBit final_accept_sig = State::Sx;
	SigBit final_reject_sig = State::Sx;

	SvaFsm(const VerificClocking &clking, SigBit trig = State::S1)
	{
		module = clking.module;
		clocking = clking;
		trigger_sig = trig;

		startNode = createNode();
		acceptNode = createNode();
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

	int createNode()
	{
		log_assert(!materialized);

		int idx = GetSize(nodes);
		nodes.push_back(SvaNFsmNode());
		return idx;
	}

	void createEdge(int from_node, int to_node, SigBit ctrl = State::S1)
	{
		log_assert(!materialized);
		log_assert(0 <= from_node && from_node < GetSize(nodes));
		log_assert(0 <= to_node && to_node < GetSize(nodes));
		log_assert(from_node != acceptNode);
		log_assert(to_node != acceptNode);

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
				clocking.addDff(NEW_ID, next_state_sig[i], state_wire[i], Const(0, 1));
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

	vector<SvaUFsmNode> unodes;
	dict<vector<int>, SvaDFsmNode> dnodes;

	void node_to_unode(int node, int unode, SigSpec ctrl)
	{
		if (node == acceptNode)
			unodes[unode].accept.push_back(ctrl);

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

	void create_dnode(const vector<int> &state, bool firstmatch)
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
		}

		dnode.ctrl.sort_and_unify();

		if (GetSize(dnode.ctrl) > 10)
			log_error("SVA property DFSM state ctrl signal has over 10 bits. Stopping to prevent exponential design size explosion.\n");

		for (int i = 0; i < (1 << GetSize(dnode.ctrl)); i++)
		{
			Const ctrl_val(i, GetSize(dnode.ctrl));
			pool<SigBit> ctrl_bits;

			for (int i = 0; i < GetSize(dnode.ctrl); i++)
				if (ctrl_val[i] == State::S1)
					ctrl_bits.insert(dnode.ctrl[i]);

			vector<int> new_state;
			bool accept = false;

			for (int unode : state)
			for (auto &it : unodes[unode].accept)
				if (cmp_ctrl(ctrl_bits, it))
					accept = true;

			if (!accept || !firstmatch) {
				for (int unode : state)
				for (auto &it : unodes[unode].edges)
					if (cmp_ctrl(ctrl_bits, it.second))
						new_state.push_back(it.first);
			}

			if (accept)
				dnode.accept.push_back(ctrl_val);

			if (new_state.empty()) {
				if (!accept)
					dnode.reject.push_back(ctrl_val);
			} else {
				usortint(new_state);
				dnode.edges.push_back(make_pair(new_state, ctrl_val));
				create_dnode(new_state, firstmatch);
			}
		}

		dnodes[state] = dnode;
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

		create_dnode(vector<int>{startNode}, true);
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

			for (auto &edge : dnode.edges) {
				SigBit trig = module->Eq(NEW_ID, {dnode.ctrl, dnode.statesig}, {edge.second, State::S1});
				dnodes.at(edge.first).nextstate.append(trig);
			}

			if (accept_p) {
				for (auto &value : dnode.accept)
					accept_sig.append(module->Eq(NEW_ID, {dnode.ctrl, dnode.statesig}, {value, State::S1}));
			}

			if (reject_p) {
				for (auto &value : dnode.reject)
					reject_sig.append(module->Eq(NEW_ID, {dnode.ctrl, dnode.statesig}, {value, State::S1}));
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
		getFirstAcceptReject(nullptr, &accept);
		return accept;
	}

	SigBit getReject()
	{
		SigBit reject;
		getFirstAcceptReject(nullptr, &reject);
		return reject;
	}

	void getDFsm(SvaFsm &output_fsm, int output_start_node, int output_accept_node, int output_reject_node)
	{
		log_assert(!materialized);
		materialized = true;

		// Create unlinked NFSM

		unodes.resize(GetSize(nodes));

		for (int node = 0; node < GetSize(nodes); node++)
			node_to_unode(node, node, SigSpec());

		mark_reachable_unode(startNode);

		// Create DFSM

		create_dnode(vector<int>{startNode}, true);
		dnodes.sort();

		// Create DFSM Graph

		for (auto &it : dnodes)
		{
			it.second.outnode = output_fsm.createNode();

			if (it.first == vector<int>{startNode})
				output_fsm.createLink(output_start_node, it.second.outnode);

			if (output_accept_node >= 0) {
				for (auto &value : it.second.accept)
					output_fsm.createLink(it.second.outnode, output_accept_node, module->Eq(NEW_ID, it.second.ctrl, value));
			}

			if (output_reject_node >= 0) {
				for (auto &value : it.second.reject)
					output_fsm.createLink(it.second.outnode, output_reject_node, module->Eq(NEW_ID, it.second.ctrl, value));
			}
		}

		for (auto &it : dnodes)
		{
			for (auto &edge : it.second.edges)
				output_fsm.createEdge(it.second.outnode, dnodes.at(edge.first).outnode, module->Eq(NEW_ID, it.second.ctrl, edge.second));
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
			log("        node %d:%s\n", i, i == startNode ? " [start]" : i == acceptNode ? " [accept]" : "");

			for (auto &it : nodes[i].edges) {
				if (it.second != State::S1)
					log("          egde %s -> %d\n", log_signal(it.second), it.first);
				else
					log("          egde -> %d\n", it.first);
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
					log("          egde %s -> %d\n", log_signal(it.second), it.first);
				else
					log("          egde -> %d\n", it.first);
			}

			for (auto &ctrl : unodes[i].accept) {
				if (!ctrl.empty())
					log("          accept %s\n", log_signal(ctrl));
				else
					log("          accept\n");
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
	bool eventually = false;

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

	int parse_sequence(SvaFsm &fsm, int start_node, Net *net)
	{
		Instance *inst = net_to_ast_driver(net);

		if (inst == nullptr) {
			int node = fsm.createNode();
			fsm.createLink(start_node, node, importer->net_map_at(net));
			return node;
		}

		if (inst->Type() == PRIM_SVA_AT)
		{
			VerificClocking new_clocking(importer, net);
			if (!clocking.property_matches_sequence(new_clocking))
				parser_error("Mixed clocking is currently not supported", inst);
			return parse_sequence(fsm, start_node, new_clocking.body_net);
		}

		if (inst->Type() == PRIM_SVA_SEQ_CONCAT)
		{
			const char *sva_low_s = inst->GetAttValue("sva:low");
			const char *sva_high_s = inst->GetAttValue("sva:high");

			int sva_low = atoi(sva_low_s);
			int sva_high = atoi(sva_high_s);
			bool sva_inf = !strcmp(sva_high_s, "$");

			int node = parse_sequence(fsm, start_node, inst->GetInput1());

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

			node = parse_sequence(fsm, node, inst->GetInput2());

			return node;
		}

		if (inst->Type() == PRIM_SVA_CONSECUTIVE_REPEAT)
		{
			const char *sva_low_s = inst->GetAttValue("sva:low");
			const char *sva_high_s = inst->GetAttValue("sva:high");

			int sva_low = atoi(sva_low_s);
			int sva_high = atoi(sva_high_s);
			bool sva_inf = !strcmp(sva_high_s, "$");

			Net *body_net = inst->GetInput();
			Instance *body_inst = net_to_ast_driver(body_net);

			if (body_inst != nullptr)
				parser_error(body_inst);

			int node = parse_sequence(fsm, start_node, body_net);

			for (int i = 1; i < sva_low; i++)
			{
				int next_node = fsm.createNode();
				fsm.createEdge(node, next_node);
				node = parse_sequence(fsm, next_node, body_net);
			}

			if (sva_inf)
			{
				int next_node = fsm.createNode();
				fsm.createEdge(node, next_node);
				next_node = parse_sequence(fsm, next_node, body_net);
				fsm.createLink(next_node, node);
			}
			else
			{
				for (int i = sva_low; i < sva_high; i++)
				{
					int next_node = fsm.createNode();
					fsm.createEdge(node, next_node);
					next_node = parse_sequence(fsm, next_node, body_net);
					fsm.createLink(node, next_node);
					node = next_node;
				}
			}

			return node;
		}

		if (inst->Type() == PRIM_SVA_SEQ_OR)
		{
			int node = parse_sequence(fsm, start_node, inst->GetInput1());
			int node2 = parse_sequence(fsm, start_node, inst->GetInput2());
			fsm.createLink(node2, node);
			return node;
		}

		if (inst->Type() == PRIM_SVA_SEQ_AND)
		{
			SvaFsm fsm1(clocking);
			fsm1.createLink(parse_sequence(fsm1, fsm1.startNode, inst->GetInput1()), fsm1.acceptNode);

			SvaFsm fsm2(clocking);
			fsm2.createLink(parse_sequence(fsm2, fsm2.startNode, inst->GetInput2()), fsm2.acceptNode);

			SvaFsm combined_fsm(clocking);
			fsm1.getDFsm(combined_fsm, combined_fsm.startNode, -1, combined_fsm.acceptNode);
			fsm2.getDFsm(combined_fsm, combined_fsm.startNode, -1, combined_fsm.acceptNode);

			int node = fsm.createNode();
			combined_fsm.getDFsm(fsm, start_node, -1, node);
			return node;
		}

		if (inst->Type() == PRIM_SVA_THROUGHOUT)
		{
			log_assert(get_ast_input1(inst) == nullptr);
			SigBit expr = importer->net_map_at(inst->GetInput1());

			fsm.pushThroughout(expr);
			int node = parse_sequence(fsm, start_node, inst->GetInput2());
			fsm.popThroughout();

			return node;
		}

		parser_error(inst);
	}

	void get_fsm_accept_reject(SvaFsm &fsm, SigBit *accept_p, SigBit *reject_p, bool swap_accpet_reject = false)
	{
		log_assert(accept_p != nullptr || reject_p != nullptr);

		if (swap_accpet_reject)
			get_fsm_accept_reject(fsm, reject_p, accept_p);
		else if (reject_p == nullptr)
			*accept_p = fsm.getAccept();
		else if (accept_p == nullptr)
			*reject_p = fsm.getReject();
		else
			fsm.getFirstAcceptReject(accept_p, reject_p);
	}

	void parse_property(Net *net, SigBit *accept_p, SigBit *reject_p)
	{
		Instance *inst = net_to_ast_driver(net);

		if (inst == nullptr)
		{
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

			SvaFsm antecedent_fsm(clocking);
			node = parse_sequence(antecedent_fsm, antecedent_fsm.startNode, antecedent_net);
			if (inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION) {
				int next_node = antecedent_fsm.createNode();
				antecedent_fsm.createEdge(node, next_node);
				node = next_node;
			}

			Instance *consequent_inst = net_to_ast_driver(consequent_net);

			if (consequent_inst && (consequent_inst->Type() == PRIM_SVA_UNTIL || consequent_inst->Type() == PRIM_SVA_S_UNTIL ||
					consequent_inst->Type() == PRIM_SVA_UNTIL_WITH || consequent_inst->Type() == PRIM_SVA_S_UNTIL_WITH))
			{
				bool until_with = consequent_inst->Type() == PRIM_SVA_UNTIL_WITH || consequent_inst->Type() == PRIM_SVA_S_UNTIL_WITH;

				Net *until_net = consequent_inst->GetInput2();
				Instance *until_inst = net_to_ast_driver(until_net);

				consequent_net = consequent_inst->GetInput1();
				consequent_inst = net_to_ast_driver(consequent_net);

				if (until_inst != nullptr)
					parser_error(until_inst);

				SigBit until_sig = importer->net_map_at(until_net);
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
			node = parse_sequence(consequent_fsm, consequent_fsm.startNode, consequent_net);
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

			SvaFsm fsm(clocking);
			int node = parse_sequence(fsm, fsm.startNode, net);
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

			RTLIL::IdString root_name = module->uniquify(importer->mode_names || root->IsUserDeclared() ? RTLIL::escape_id(root->Name()) : NEW_ID);

			clocking = VerificClocking(importer, root->GetInput());

			if (clocking.body_net == nullptr)
				parser_error(stringf("Failed to parse SVA clocking"), root);

			// parse SVA sequence into trigger signal

			Net *net = clocking.body_net;
			SigBit accept_bit = State::S0, reject_bit =  State::S0;

			if (mode_assert || mode_assume) {
				parse_property(net, nullptr, &reject_bit);
			} else {
				parse_property(net, &accept_bit, nullptr);
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

				SigBit sig_a_q = module->addWire(NEW_ID);
				SigBit sig_en_q = module->addWire(NEW_ID);
				clocking.addDff(NEW_ID, sig_a, sig_a_q, State::S0);
				clocking.addDff(NEW_ID, sig_en, sig_en_q, State::S0);

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

void import_sva_assert(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_assert = true;
	worker.import();
}

void import_sva_assume(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_assume = true;
	worker.import();
}

void import_sva_cover(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_cover = true;
	worker.import();
}

void import_sva_trigger(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_trigger = true;
	worker.import();
}

YOSYS_NAMESPACE_END
