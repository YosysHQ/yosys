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

struct SvaFsmNode
{
	vector<pair<int, SigBit>> edges, links;
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

	int startNode, acceptNode, rejectNode;
	vector<SvaFsmNode> nodes;

	SvaFsm(Module *mod, SigBit clk, bool clkpol, SigBit dis = State::S0, SigBit trig = State::S1)
	{
		module = mod;
		clock = clk;
		clockpol = clkpol;
		disable_sig = dis;
		trigger_sig = trig;

		startNode = createNode();
		acceptNode = createNode();
		rejectNode = createNode();
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

	SigBit getAccept()
	{
		if (accept_sig != State::Sz)
			return accept_sig;

		log_assert(!materialized);
		accept_sig = module->addWire(NEW_ID);
		return accept_sig;
	}

	SigBit getReject()
	{
		if (reject_sig != State::Sz)
			return reject_sig;

		log_assert(!materialized);
		reject_sig = module->addWire(NEW_ID);
		return reject_sig;
	}

	int createNode()
	{
		log_assert(!materialized);

		int idx = GetSize(nodes);
		nodes.push_back(SvaFsmNode());
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

	void materialize_ndfsm()
	{
		log_assert(!materialized);
		materialized = true;

		vector<SigBit> next_state_sig(GetSize(nodes));
		vector<SigBit> state_sig(GetSize(nodes));

		// Create state FFs

		{
			SigBit not_disable = State::S1;

			if (disable_sig != State::S0)
				not_disable = module->Not(NEW_ID, disable_sig);

			for (int i = 0; i < GetSize(nodes); i++)
			{
				next_state_sig[i] = module->addWire(NEW_ID);

				Wire *w = module->addWire(NEW_ID);
				w->attributes["\\init"] = Const(0, 1);
				state_sig[i] = w;

				module->addDff(NEW_ID, clock, next_state_sig[i], state_sig[i], clockpol);

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
					activate_bit[i] = State::S0;
				else if (GetSize(activate_sig[i]) == 1)
					activate_bit[i] = activate_sig[i];
				else
					activate_bit[i] = module->ReduceOr(NEW_ID, activate_sig[i]);
			}

			if (activate_bit[rejectNode] != State::S0)
			{
				SigBit not_rej = module->Not(NEW_ID, next_state_sig[rejectNode]);
				for (int i = 0; i < GetSize(nodes); i++)
					if (i != rejectNode && activate_bit[i] != State::S0)
						activate_bit[i] = module->And(NEW_ID, activate_bit[i], not_rej);
				activate_bit[rejectNode] = State::S0;
			}

			for (int i = 0; i < GetSize(nodes); i++) {
				module->connect(next_state_sig[i], activate_bit[i]);
			}
		}

		// Construct output signals

		if (accept_sig != State::Sz) {
			module->connect(accept_sig, state_sig[acceptNode]);
		}

		if (reject_sig != State::Sz)
		{
			SigBit fsm_active = module->ReduceOr(NEW_ID, state_sig);
			SigBit fsm_next_active = module->ReduceOr(NEW_ID, next_state_sig);
			module->addEq(NEW_ID, {state_sig[acceptNode], fsm_next_active, fsm_active}, SigSpec(1, 3), reject_sig);
		}
	}

	void materialize_dfsm()
	{
		// FIXME
		log_abort();
	}

	bool is_linear()
	{
		for (int i = 0; i < GetSize(nodes); i++)
			if (GetSize(nodes[i].edges) + GetSize(nodes[i].links) > 1)
				return false;
		return true;
	}

	void dump()
	{
		log("-----------\n");
		for (int i = 0; i < GetSize(nodes); i++)
		{
			log("node %d:\n", i);

			if (i == startNode)
				log("  startNode\n");

			if (i == rejectNode)
				log("  rejectNode\n");

			if (i == acceptNode)
				log("  acceptNode\n");

			for (auto &it : nodes[i].edges) {
				if (it.second != State::S1)
					log("  egde %s -> %d\n", log_signal(it.second), it.first);
				else
					log("  egde -> %d\n", it.first);
			}

			for (auto &it : nodes[i].links) {
				if (it.second != State::S1)
					log("  link %s -> %d\n", log_signal(it.second), it.first);
				else
					log("  link -> %d\n", it.first);
			}
		}
		log("-----------\n");
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
	bool clock_posedge = false;

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
	// SVA AST Types

	struct svatype_t
	{
		bool flag_linear = true;
	};

	std::map<Instance*, svatype_t> svatype_cache;

	void svatype_visit_child(svatype_t &entry, Instance *inst)
	{
		if (inst == nullptr)
			return;

		const svatype_t &child_entry = svatype(inst);
		entry.flag_linear &= child_entry.flag_linear;
	}

	const svatype_t &svatype(Instance *inst)
	{
		if (svatype_cache.count(inst) != 0)
			return svatype_cache.at(inst);

		svatype_t &entry = svatype_cache[inst];

		if (inst == nullptr)
			return entry;

		if (inst->Type() == PRIM_SVA_SEQ_CONCAT || inst->Type() == PRIM_SVA_CONSECUTIVE_REPEAT)
		{
			const char *sva_low_s = inst->GetAttValue("sva:low");
			const char *sva_high_s = inst->GetAttValue("sva:high");

			int sva_low = atoi(sva_low_s);
			int sva_high = atoi(sva_high_s);
			bool sva_inf = !strcmp(sva_high_s, "$");

			if (sva_inf || sva_low != sva_high)
				entry.flag_linear = false;
		}

		svatype_visit_child(entry, get_ast_input(inst));
		svatype_visit_child(entry, get_ast_input1(inst));
		svatype_visit_child(entry, get_ast_input2(inst));
		svatype_visit_child(entry, get_ast_input3(inst));
		svatype_visit_child(entry, get_ast_control(inst));

		return entry;
	}

	// ----------------------------------------------------------
	// SVA Preprocessor

	Net *rewrite_input(Instance *inst) { return rewrite(get_ast_input(inst), inst->GetInput()); }
	Net *rewrite_input1(Instance *inst) { return rewrite(get_ast_input1(inst), inst->GetInput1()); }
	Net *rewrite_input2(Instance *inst) { return rewrite(get_ast_input2(inst), inst->GetInput2()); }
	Net *rewrite_input3(Instance *inst) { return rewrite(get_ast_input3(inst), inst->GetInput3()); }
	Net *rewrite_control(Instance *inst) { return rewrite(get_ast_control(inst), inst->GetControl()); }

	Net *rewrite(Instance *inst, Net *default_net = nullptr)
	{
		if (inst == nullptr)
			return default_net;

		if (inst->Type() == PRIM_SVA_ASSERT || inst->Type() == PRIM_SVA_COVER || inst->Type() == PRIM_SVA_ASSUME ||
				inst->Type() == PRIM_SVA_IMMEDIATE_ASSERT || inst->Type() == PRIM_SVA_IMMEDIATE_COVER || inst->Type() == PRIM_SVA_IMMEDIATE_ASSUME) {
			Net *new_net = rewrite(get_ast_input(inst));
			if (new_net) {
				inst->Disconnect(inst->View()->GetInput());
				inst->Connect(inst->View()->GetInput(), new_net);
			}
			return default_net;
		}

		if (inst->Type() == PRIM_SVA_AT || inst->Type() == PRIM_SVA_DISABLE_IFF) {
			Net *new_net = rewrite(get_ast_input2(inst));
			if (new_net) {
				inst->Disconnect(inst->View()->GetInput2());
				inst->Connect(inst->View()->GetInput2(), new_net);
			}
			return default_net;
		}

		if (inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION)
		{
			if (mode_cover) {
				did_something = true;
				Net *new_in1 = rewrite_input1(inst);
				Net *new_in2 = rewrite_input2(inst);
				return netlist->SvaBinary(PRIM_SVA_SEQ_CONCAT, new_in1, new_in2, inst->Linefile());
			}
			return default_net;
		}

		if (inst->Type() == PRIM_SVA_NOT)
		{
			if (mode_assert || mode_assume) {
				did_something = true;
				Net *new_in = rewrite_input(inst);
				Net *net_zero = netlist->Gnd(inst->Linefile());
				return netlist->SvaBinary(PRIM_SVA_OVERLAPPED_IMPLICATION, new_in, net_zero, inst->Linefile());
			}
			return default_net;
		}

		return default_net;
	}

	void rewrite()
	{
		netlist = root->Owner();
		do {
			did_something = false;
			rewrite(root);
		} while (did_something);
	}

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
		clock_posedge = clock_edge.posedge;

		// parse disable_iff expression

		Net *sequence_net = at_node->GetInput2();

		while (1)
		{
			Instance *sequence_node = net_to_ast_driver(sequence_net);

			if (sequence_node && sequence_node->Type() == PRIM_SVA_S_EVENTUALLY) {
				eventually = true;
				sequence_net = sequence_node->GetInput();
				continue;
			}

			if (sequence_node && sequence_node->Type() == PRIM_SVA_DISABLE_IFF) {
				disable_iff = importer->net_map_at(sequence_node->GetInput1());
				sequence_net = sequence_node->GetInput2();
				continue;
			}

			break;
		}

		// parse SVA sequence into trigger signal

		SigBit prop_okay;
		Instance *inst = net_to_ast_driver(sequence_net);

		if (inst == nullptr)
		{
			prop_okay = importer->net_map_at(sequence_net);
		}
		else
		if (inst->Type() == PRIM_SVA_OVERLAPPED_IMPLICATION ||
				inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION)
		{
			Net *antecedent_net = inst->GetInput1();
			Net *consequent_net = inst->GetInput2();
			int node;

			SvaFsm antecedent_fsm(module, clock, clock_posedge, disable_iff);
			node = parse_sequence(&antecedent_fsm, antecedent_fsm.startNode, antecedent_net);
			if (inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION) {
				int next_node = antecedent_fsm.createNode();
				antecedent_fsm.createEdge(node, next_node);
				node = next_node;
			}
			antecedent_fsm.createLink(node, antecedent_fsm.acceptNode);

			SigBit antecedent_accept = antecedent_fsm.getAccept();
			antecedent_fsm.materialize_ndfsm();
			antecedent_fsm.dump();

			SvaFsm consequent_fsm(module, clock, clock_posedge, disable_iff, antecedent_accept);
			node = parse_sequence(&consequent_fsm, consequent_fsm.startNode, consequent_net);
			consequent_fsm.createLink(node, consequent_fsm.acceptNode);

			SigBit consequent_reject = consequent_fsm.getReject();
			prop_okay = module->Not(NEW_ID, consequent_reject);

			if (consequent_fsm.is_linear())
				consequent_fsm.materialize_ndfsm();
			else
				log_error("Currently only linear sequences are allowed as impliciation consequent.\n");
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
		module->addDff(NEW_ID, clock, prop_okay, prop_okay_q, clock_posedge);

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

#if 0
	// ----------------------------------------------------------
	// Old SVA Importer

	vector<SigBit> sva_until_list_inclusive;
	vector<SigBit> sva_until_list_exclusive;
	vector<vector<SigBit>*> sva_sequence_alive_list;

	struct sequence_t {
		int length = 0;
		SigBit sig_a = State::S1;
		SigBit sig_en = State::S1;
	};

	void sequence_cond(sequence_t &seq, SigBit cond)
	{
		seq.sig_a = module->And(NEW_ID, seq.sig_a, cond);
	}

	void sequence_ff(sequence_t &seq)
	{
		if (disable_iff != State::S0)
			seq.sig_en = module->Mux(NEW_ID, seq.sig_en, State::S0, disable_iff);

		for (auto &expr : sva_until_list_exclusive)
			seq.sig_a = module->LogicAnd(NEW_ID, seq.sig_a, expr);

		Wire *sig_a_q = module->addWire(NEW_ID);
		sig_a_q->attributes["\\init"] = Const(0, 1);

		Wire *sig_en_q = module->addWire(NEW_ID);
		sig_en_q->attributes["\\init"] = Const(0, 1);

		for (auto list : sva_sequence_alive_list)
			list->push_back(module->LogicAnd(NEW_ID, seq.sig_a, seq.sig_en));

		module->addDff(NEW_ID, clock, seq.sig_a, sig_a_q, clock_posedge);
		module->addDff(NEW_ID, clock, seq.sig_en, sig_en_q, clock_posedge);

		if (seq.length >= 0)
			seq.length++;

		seq.sig_a = sig_a_q;
		seq.sig_en = sig_en_q;

		for (auto &expr : sva_until_list_inclusive)
			seq.sig_a = module->LogicAnd(NEW_ID, seq.sig_a, expr);
	}

	void combine_seq(sequence_t &seq, const sequence_t &other_seq)
	{
		if (seq.length != other_seq.length)
			seq.length = -1;

		SigBit filtered_a = module->LogicAnd(NEW_ID, seq.sig_a, seq.sig_en);
		SigBit other_filtered_a = module->LogicAnd(NEW_ID, other_seq.sig_a, other_seq.sig_en);

		seq.sig_a = module->LogicOr(NEW_ID, filtered_a, other_filtered_a);
		seq.sig_en = module->LogicOr(NEW_ID, seq.sig_en, other_seq.sig_en);
	}

	void combine_seq(sequence_t &seq, SigBit other_a, SigBit other_en)
	{
		SigBit filtered_a = module->LogicAnd(NEW_ID, seq.sig_a, seq.sig_en);
		SigBit other_filtered_a = module->LogicAnd(NEW_ID, other_a, other_en);

		seq.length = -1;
		seq.sig_a = module->LogicOr(NEW_ID, filtered_a, other_filtered_a);
		seq.sig_en = module->LogicOr(NEW_ID, seq.sig_en, other_en);
	}

	SigBit make_temporal_one_hot(SigBit enable = State::S1, SigBit *latched = nullptr)
	{
		Wire *state = module->addWire(NEW_ID);
		state->attributes["\\init"] = State::S0;

		SigBit any = module->Anyseq(NEW_ID);
		if (enable != State::S1)
			any = module->LogicAnd(NEW_ID, any, enable);

		SigBit next_state = module->LogicOr(NEW_ID, state, any);
		module->addDff(NEW_ID, clock, next_state, state, clock_posedge);

		if (latched != nullptr)
			*latched = state;

		SigBit not_state = module->LogicNot(NEW_ID, state);
		return module->LogicAnd(NEW_ID, next_state, not_state);
	}

	SigBit make_permanent_latch(SigBit enable, bool async = false)
	{
		Wire *state = module->addWire(NEW_ID);
		state->attributes["\\init"] = State::S0;

		SigBit next_state = module->LogicOr(NEW_ID, state, enable);
		module->addDff(NEW_ID, clock, next_state, state, clock_posedge);

		return async ? next_state : state;
	}

	void parse_sequence(sequence_t &seq, Net *n)
	{
		Instance *inst = net_to_ast_driver(n);

		// Regular expression

		if (inst == nullptr) {
			sequence_cond(seq, importer->net_map_at(n));
			return;
		}

		// SVA Primitives

		if (inst->Type() == PRIM_SVA_OVERLAPPED_IMPLICATION ||
				inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION)
		{
			Instance *consequent = get_ast_input2(inst);
			bool linear_consequent = svatype(consequent).flag_linear;

			parse_sequence(seq, inst->GetInput1());
			seq.sig_en = module->And(NEW_ID, seq.sig_en, seq.sig_a);

			if (inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION)
				sequence_ff(seq);

			if (!linear_consequent && mode_assume)
				log_error("Non-linear consequent is currently not supported in SVA assumptions.\n");

			if (linear_consequent)
			{
				parse_sequence(seq, inst->GetInput2());
			}
			else
			{
				SigBit activated;
				seq.sig_en = make_temporal_one_hot(seq.sig_en, &activated);

				SigBit pass_latch_en = module->addWire(NEW_ID);
				SigBit pass_latch = make_permanent_latch(pass_latch_en, true);

				vector<SigBit> alive_list;
				sva_sequence_alive_list.push_back(&alive_list);
				parse_sequence(seq, inst->GetInput2());
				sva_sequence_alive_list.pop_back();

				module->addLogicAnd(NEW_ID, seq.sig_a, seq.sig_en, pass_latch_en);
				alive_list.push_back(pass_latch);

				seq.length = -1;
				seq.sig_a = module->ReduceOr(NEW_ID, SigSpec(alive_list));
				seq.sig_en = module->ReduceOr(NEW_ID, activated);
			}

			return;
		}

		if (inst->Type() == PRIM_SVA_SEQ_CONCAT)
		{
			const char *sva_low_s = inst->GetAttValue("sva:low");
			const char *sva_high_s = inst->GetAttValue("sva:high");

			int sva_low = atoi(sva_low_s);
			int sva_high = atoi(sva_high_s);
			bool sva_inf = !strcmp(sva_high_s, "$");

			parse_sequence(seq, inst->GetInput1());

			for (int i = 0; i < sva_low; i++)
				sequence_ff(seq);

			if (sva_inf)
			{
				SigBit latched_a = module->addWire(NEW_ID);
				SigBit latched_en = module->addWire(NEW_ID);
				combine_seq(seq, latched_a, latched_en);

				sequence_t seq_latched = seq;
				sequence_ff(seq_latched);
				module->connect(latched_a, seq_latched.sig_a);
				module->connect(latched_en, seq_latched.sig_en);
			}
			else
			{
				for (int i = sva_low; i < sva_high; i++)
				{
					sequence_t last_seq = seq;
					sequence_ff(seq);
					combine_seq(seq, last_seq);
				}
			}

			parse_sequence(seq, inst->GetInput2());
			return;
		}

		if (inst->Type() == PRIM_SVA_CONSECUTIVE_REPEAT)
		{
			const char *sva_low_s = inst->GetAttValue("sva:low");
			const char *sva_high_s = inst->GetAttValue("sva:high");

			int sva_low = atoi(sva_low_s);
			int sva_high = atoi(sva_high_s);
			bool sva_inf = !strcmp(sva_high_s, "$");

			parse_sequence(seq, inst->GetInput());

			for (int i = 1; i < sva_low; i++) {
				sequence_ff(seq);
				parse_sequence(seq, inst->GetInput());
			}

			if (sva_inf)
			{
				SigBit latched_a = module->addWire(NEW_ID);
				SigBit latched_en = module->addWire(NEW_ID);
				combine_seq(seq, latched_a, latched_en);

				sequence_t seq_latched = seq;
				sequence_ff(seq_latched);
				parse_sequence(seq_latched, inst->GetInput());
				module->connect(latched_a, seq_latched.sig_a);
				module->connect(latched_en, seq_latched.sig_en);
			}
			else
			{
				for (int i = sva_low; i < sva_high; i++)
				{
					sequence_t last_seq = seq;
					sequence_ff(seq);
					parse_sequence(seq, inst->GetInput());
					combine_seq(seq, last_seq);
				}
			}

			return;
		}

		if (inst->Type() == PRIM_SVA_THROUGHOUT || inst->Type() == PRIM_SVA_UNTIL || inst->Type() == PRIM_SVA_S_UNTIL ||
				inst->Type() == PRIM_SVA_UNTIL_WITH || inst->Type() == PRIM_SVA_S_UNTIL_WITH)
		{
			bool flag_with = inst->Type() == PRIM_SVA_THROUGHOUT || inst->Type() == PRIM_SVA_UNTIL_WITH || inst->Type() == PRIM_SVA_S_UNTIL_WITH;

			if (get_ast_input1(inst) != nullptr)
				log_error("Currently only simple expression properties are supported as first operand to SVA_UNTIL.\n");

			SigBit expr = importer->net_map_at(inst->GetInput1());

			if (flag_with)
			{
				seq.sig_a = module->LogicAnd(NEW_ID, seq.sig_a, expr);
				sva_until_list_inclusive.push_back(expr);
				parse_sequence(seq, inst->GetInput2());
				sva_until_list_inclusive.pop_back();
			}
			else
			{
				sva_until_list_exclusive.push_back(expr);
				parse_sequence(seq, inst->GetInput2());
				sva_until_list_exclusive.pop_back();
			}

			return;
		}

		// Handle unsupported primitives

		if (!importer->mode_keep)
			log_error("Verific SVA primitive %s (%s) is currently unsupported in this context.\n", inst->View()->Owner()->Name(), inst->Name());
		log_warning("Verific SVA primitive %s (%s) is currently unsupported in this context.\n", inst->View()->Owner()->Name(), inst->Name());
	}

	void import()
	{
		module = importer->module;
		netlist = root->Owner();

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
		clock_posedge = clock_edge.posedge;

		// parse disable_iff expression

		Net *sequence_net = at_node->GetInput2();

		while (1)
		{
			Instance *sequence_node = net_to_ast_driver(sequence_net);

			if (sequence_node && sequence_node->Type() == PRIM_SVA_S_EVENTUALLY) {
				eventually = true;
				sequence_net = sequence_node->GetInput();
				continue;
			}

			if (sequence_node && sequence_node->Type() == PRIM_SVA_DISABLE_IFF) {
				disable_iff = importer->net_map_at(sequence_node->GetInput1());
				sequence_net = sequence_node->GetInput2();
				continue;
			}

			break;
		}

		// parse SVA sequence into trigger signal

		sequence_t seq;
		parse_sequence(seq, sequence_net);
		sequence_ff(seq);

		// generate assert/assume/cover cell

		RTLIL::Cell *c = nullptr;

		if (eventually) {
			if (mode_assert) c = module->addLive(root_name, seq.sig_a, seq.sig_en);
			if (mode_assume) c = module->addFair(root_name, seq.sig_a, seq.sig_en);
		} else {
			if (mode_assert) c = module->addAssert(root_name, seq.sig_a, seq.sig_en);
			if (mode_assume) c = module->addAssume(root_name, seq.sig_a, seq.sig_en);
			if (mode_cover) c = module->addCover(root_name, seq.sig_a, seq.sig_en);
		}

		importer->import_attributes(c->attributes, root);
	}
#endif
};

void svapp_assert(Instance *inst)
{
	VerificSvaImporter worker;
	worker.root = inst;
	worker.mode_assert = true;
	worker.rewrite();
}

void svapp_assume(Instance *inst)
{
	VerificSvaImporter worker;
	worker.root = inst;
	worker.mode_assume = true;
	worker.rewrite();
}

void svapp_cover(Instance *inst)
{
	VerificSvaImporter worker;
	worker.root = inst;
	worker.mode_cover = true;
	worker.rewrite();
}

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
