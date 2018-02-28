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


// SVA Properties Simplified Syntax:
//
// prop:
//   not prop
//   prop or prop
//   prop and prop
//   seq |=> prop
//   if (expr) prop [else prop]
//   prop until prop
//   prop implies prop
//   prop iff prop
//   accept_on (expr) prop
//   reject_on (expr) prop
//
// seq:
//   expr
//   expr ##[N:M] seq
//   seq or seq
//   seq and seq
//   seq intersect seq
//   first_match (seq)
//   expr throughout seq
//   seq within seq
//   seq [*N:M]
//   expr [=N:M]
//   expr [->N:M]
//
// Notes:
//   |=> is a placeholder for |-> and |=>
//   "until" is a placeholder for all until operators
//   ##[N:M], [*N:M], [=N:M], [->N:M] includes ##N, [*N], [=N], [->N]
//
// Currently supported property styles:
//   not seq
//   seq |=> seq
//   seq |=> seq until seq
//
// Currently supported sequence operators:
//   ##[N:M]
//   [*N:M]
//   throughout


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
};

struct SvaFsm
{
	Module *module;
	SigBit clock;
	bool clockpol;

	SigBit trigger_sig = State::S1, disable_sig;
	SigBit accept_sig = State::Sz, reject_sig = State::Sz;
	SigBit throughout_sig = State::S1;
	bool materialized = false;

	vector<SigBit> disable_stack;
	vector<SigBit> throughout_stack;

	int startNode, acceptNode;
	vector<SvaNFsmNode> nodes;

	// ----------------------------------------------------
	// API for creating FSM

	SvaFsm(Module *mod, SigBit clk, bool clkpol, SigBit dis = State::S0, SigBit trig = State::S1)
	{
		module = mod;
		clock = clk;
		clockpol = clkpol;
		disable_sig = dis;
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
	// API for generating NFSM circuit to acquire accept signal

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
				state_wire[i]->attributes["\\init"] = Const(0, 1);
				module->addDff(NEW_ID, clock, next_state_sig[i], state_wire[i], clockpol);
			} else {
				module->connect(state_wire[i], State::S0);
			}
		}

		return state_sig[acceptNode];
	}

	// ----------------------------------------------------
	// API for generating quantifier-based NFSM circuit to acquire reject signal

	SigBit getAnyAllRejectWorker(bool allMode)
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
	// API for generating DFSM circuit to acquire reject signal

	SigBit getReject()
	{
		// FIXME
		log("-----------------\n");
		dump();
		log_abort();
	}

	// ----------------------------------------------------
	// State dump for verbose log messages

	void dump()
	{
		if (!nodes.empty())
		{
			log("      non-deterministic encoding:\n");
			for (int i = 0; i < GetSize(nodes); i++)
			{
				log("        node %d:\n", i);

				if (i == startNode)
					log("          startNode\n");

				if (i == acceptNode)
					log("          acceptNode\n");

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

	SigBit clock = State::Sx;
	bool clockpol = false;

	SigBit disable_iff = State::S0;

	bool mode_assert = false;
	bool mode_assume = false;
	bool mode_cover = false;
	bool eventually = false;
	bool did_something = false;

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
				inst->Type() == PRIM_SVA_STABLE || inst->Type() == OPER_SVA_STABLE || inst->Type() == PRIM_SVA_PAST)
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

	int parse_sequence(SvaFsm *fsm, int start_node, Net *net)
	{
		Instance *inst = net_to_ast_driver(net);

		if (inst == nullptr) {
			int node = fsm->createNode();
			fsm->createLink(start_node, node, importer->net_map_at(net));
			return node;
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
				int next_node = fsm->createNode();
				fsm->createEdge(node, next_node);
				node = next_node;
			}

			if (sva_inf)
			{
				fsm->createEdge(node, node);
			}
			else
			{
				for (int i = sva_low; i < sva_high; i++)
				{
					int next_node = fsm->createNode();
					fsm->createEdge(node, next_node);
					fsm->createLink(node, next_node);
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

			int node = parse_sequence(fsm, start_node, inst->GetInput());

			for (int i = 1; i < sva_low; i++)
			{
				int next_node = fsm->createNode();
				fsm->createEdge(node, next_node);
				node = parse_sequence(fsm, next_node, inst->GetInput());
			}

			if (sva_inf)
			{
				int next_node = fsm->createNode();
				fsm->createEdge(node, next_node);
				next_node = parse_sequence(fsm, next_node, inst->GetInput());
				fsm->createLink(next_node, node);
			}
			else
			{
				for (int i = sva_low; i < sva_high; i++)
				{
					int next_node = fsm->createNode();
					fsm->createEdge(node, next_node);
					next_node = parse_sequence(fsm, next_node, inst->GetInput());
					fsm->createLink(node, next_node);
					node = next_node;
				}
			}

			return node;
		}

		if (inst->Type() == PRIM_SVA_THROUGHOUT)
		{
			log_assert(get_ast_input1(inst) == nullptr);
			SigBit expr = importer->net_map_at(inst->GetInput1());

			fsm->pushThroughout(expr);
			int node = parse_sequence(fsm, start_node, inst->GetInput2());
			fsm->popThroughout();

			return node;
		}

		// Handle unsupported primitives

		if (!importer->mode_keep)
			log_error("Verific SVA primitive %s (%s) is currently unsupported in this context.\n", inst->View()->Owner()->Name(), inst->Name());
		log_warning("Verific SVA primitive %s (%s) is currently unsupported in this context.\n", inst->View()->Owner()->Name(), inst->Name());

		return start_node;
	}

	void import()
	{
		module = importer->module;
		netlist = root->Owner();

		if (verific_verbose)
			log("  importing SVA property at root cell %s (%s) at %s:%d.\n", root->Name(), root->View()->Owner()->Name(),
					LineFile::GetFileName(root->Linefile()), LineFile::GetLineNo(root->Linefile()));

		RTLIL::IdString root_name = module->uniquify(importer->mode_names || root->IsUserDeclared() ? RTLIL::escape_id(root->Name()) : NEW_ID);

		// parse SVA property clock event

		Instance *at_node = get_ast_input(root);

		// asynchronous immediate assertion/assumption/cover
		if (at_node == nullptr && (root->Type() == PRIM_SVA_IMMEDIATE_ASSERT ||
				root->Type() == PRIM_SVA_IMMEDIATE_COVER || root->Type() == PRIM_SVA_IMMEDIATE_ASSUME))
		{
			SigSpec sig_a = importer->net_map_at(root->GetInput());
			RTLIL::Cell *c = nullptr;

			if (eventually) {
				if (mode_assert) c = module->addLive(root_name, sig_a, State::S1);
				if (mode_assume) c = module->addFair(root_name, sig_a, State::S1);
			} else {
				if (mode_assert) c = module->addAssert(root_name, sig_a, State::S1);
				if (mode_assume) c = module->addAssume(root_name, sig_a, State::S1);
				if (mode_cover) c = module->addCover(root_name, sig_a, State::S1);
			}

			importer->import_attributes(c->attributes, root);
			return;
		}

		log_assert(at_node && at_node->Type() == PRIM_SVA_AT);

		VerificClockEdge clock_edge(importer, get_ast_input1(at_node));
		clock = clock_edge.clock_sig;
		clockpol = clock_edge.posedge;

		// parse disable_iff expression

		Net *net = at_node->GetInput2();

		while (1)
		{
			Instance *sequence_node = net_to_ast_driver(net);

			if (sequence_node && sequence_node->Type() == PRIM_SVA_S_EVENTUALLY) {
				eventually = true;
				net = sequence_node->GetInput();
				continue;
			}

			if (sequence_node && sequence_node->Type() == PRIM_SVA_DISABLE_IFF) {
				disable_iff = importer->net_map_at(sequence_node->GetInput1());
				net = sequence_node->GetInput2();
				continue;
			}

			break;
		}

		// parse SVA sequence into trigger signal

		SigBit prop_okay;
		Instance *inst = net_to_ast_driver(net);

		if (inst == nullptr)
		{
			prop_okay = importer->net_map_at(net);
		}
		else
		if (inst->Type() == PRIM_SVA_OVERLAPPED_IMPLICATION ||
				inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION)
		{
			Net *antecedent_net = inst->GetInput1();
			Net *consequent_net = inst->GetInput2();
			int node;

			SvaFsm antecedent_fsm(module, clock, clockpol, disable_iff);
			node = parse_sequence(&antecedent_fsm, antecedent_fsm.startNode, antecedent_net);
			if (inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION) {
				int next_node = antecedent_fsm.createNode();
				antecedent_fsm.createEdge(node, next_node);
				node = next_node;
			}
			antecedent_fsm.createLink(node, antecedent_fsm.acceptNode);

			SigBit antecedent_match = antecedent_fsm.getAccept();

			if (verific_verbose) {
				log("    Antecedent FSM:\n");
				antecedent_fsm.dump();
			}

			bool consequent_not = false;
			Instance *consequent_inst = net_to_ast_driver(consequent_net);

			if (consequent_inst && consequent_inst->Type() == PRIM_SVA_NOT) {
				consequent_not = true;
				consequent_net = consequent_inst->GetInput();
			}

			SvaFsm consequent_fsm(module, clock, clockpol, disable_iff, antecedent_match);
			node = parse_sequence(&consequent_fsm, consequent_fsm.startNode, consequent_net);
			consequent_fsm.createLink(node, consequent_fsm.acceptNode);

			if (mode_cover) {
				prop_okay = consequent_not ? consequent_fsm.getReject() : consequent_fsm.getAccept();
			} else {
				SigBit consequent_match = consequent_not ? consequent_fsm.getAccept() : consequent_fsm.getReject();
				prop_okay = module->Not(NEW_ID, consequent_match);
			}

			if (verific_verbose) {
				log("    Consequent FSM:\n");
				antecedent_fsm.dump();
			}
		}
		else
		if (inst->Type() == PRIM_SVA_NOT || mode_cover)
		{
			SvaFsm fsm(module, clock, clockpol, disable_iff);
			int node = parse_sequence(&fsm, fsm.startNode, mode_cover ? net : inst->GetInput());
			fsm.createLink(node, fsm.acceptNode);
			SigBit accept = fsm.getAccept();
			prop_okay = module->Not(NEW_ID, accept);

			if (verific_verbose) {
				log("    Sequence FSM:\n");
				fsm.dump();
			}
		}
		else
		{
			// Handle unsupported primitives

			if (!importer->mode_keep)
				log_error("Verific SVA primitive %s (%s) is currently unsupported in this context.\n", inst->View()->Owner()->Name(), inst->Name());
			log_warning("Verific SVA primitive %s (%s) is currently unsupported in this context.\n", inst->View()->Owner()->Name(), inst->Name());
			return;
		}

		// add final FF stage

		Wire *prop_okay_q = module->addWire(NEW_ID);
		prop_okay_q->attributes["\\init"] = Const(mode_cover ? 0 : 1, 1);
		module->addDff(NEW_ID, clock, prop_okay, prop_okay_q, clockpol);

		// generate assert/assume/cover cell

		RTLIL::Cell *c = nullptr;

		if (eventually) {
			log_error("No support for eventually in Verific SVA bindings yet.\n");
			// if (mode_assert) c = module->addLive(root_name, prop_okay_q, prop_start_q);
			// if (mode_assume) c = module->addFair(root_name, prop_okay_q, prop_start_q);
		} else {
			if (mode_assert) c = module->addAssert(root_name, prop_okay_q, State::S1);
			if (mode_assume) c = module->addAssume(root_name, prop_okay_q, State::S1);
			if (mode_cover) c = module->addCover(root_name, prop_okay_q, State::S1);
		}

		importer->import_attributes(c->attributes, root);
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

YOSYS_NAMESPACE_END
