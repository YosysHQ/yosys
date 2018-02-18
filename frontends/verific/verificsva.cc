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

#include "kernel/yosys.h"
#include "frontends/verific/verific.h"

USING_YOSYS_NAMESPACE

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

YOSYS_NAMESPACE_BEGIN

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

		Wire *sig_a_q = module->addWire(NEW_ID);
		sig_a_q->attributes["\\init"] = Const(0, 1);

		Wire *sig_en_q = module->addWire(NEW_ID);
		sig_en_q->attributes["\\init"] = Const(0, 1);

		module->addDff(NEW_ID, clock, seq.sig_a, sig_a_q, clock_posedge);
		module->addDff(NEW_ID, clock, seq.sig_en, sig_en_q, clock_posedge);

		seq.length++;
		seq.sig_a = sig_a_q;
		seq.sig_en = sig_en_q;
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

		if (inst->Type() == PRIM_SVA_OVERLAPPED_IMPLICATION)
		{
			parse_sequence(seq, inst->GetInput1());
			seq.sig_en = module->And(NEW_ID, seq.sig_en, seq.sig_a);
			parse_sequence(seq, inst->GetInput2());
			return;
		}

		if (inst->Type() == PRIM_SVA_NON_OVERLAPPED_IMPLICATION)
		{
			parse_sequence(seq, inst->GetInput1());
			seq.sig_en = module->And(NEW_ID, seq.sig_en, seq.sig_a);
			sequence_ff(seq);
			parse_sequence(seq, inst->GetInput2());
			return;
		}

		if (inst->Type() == PRIM_SVA_SEQ_CONCAT)
		{
			int sva_low = atoi(inst->GetAttValue("sva:low"));
			int sva_high = atoi(inst->GetAttValue("sva:low"));

			if (sva_low != sva_high)
				log_error("Ranges on SVA sequence concatenation operator are not supported at the moment.\n");

			parse_sequence(seq, inst->GetInput1());

			for (int i = 0; i < sva_low; i++)
				sequence_ff(seq);

			parse_sequence(seq, inst->GetInput2());
			return;
		}

		if (inst->Type() == PRIM_SVA_CONSECUTIVE_REPEAT)
		{
			int sva_low = atoi(inst->GetAttValue("sva:low"));
			int sva_high = atoi(inst->GetAttValue("sva:low"));

			if (sva_low != sva_high)
				log_error("Ranges on SVA consecutive repeat operator are not supported at the moment.\n");

			parse_sequence(seq, inst->GetInput());

			for (int i = 1; i < sva_low; i++) {
				sequence_ff(seq);
				parse_sequence(seq, inst->GetInput());
			}
			return;
		}

		// Handle unsupported primitives

		if (!importer->mode_keep)
			log_error("Unsupported Verific SVA primitive %s of type %s.\n", inst->Name(), inst->View()->Owner()->Name());
		log_warning("Unsupported Verific SVA primitive %s of type %s.\n", inst->Name(), inst->View()->Owner()->Name());
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
