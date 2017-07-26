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
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#ifndef _WIN32
#  include <unistd.h>
#  include <dirent.h>
#endif

USING_YOSYS_NAMESPACE

#ifdef YOSYS_ENABLE_VERIFIC

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Woverloaded-virtual"
#endif

#include "veri_file.h"
#include "vhdl_file.h"
#include "VeriModule.h"
#include "VeriWrite.h"
#include "VhdlUnits.h"
#include "DataBase.h"
#include "Message.h"

#ifdef __clang__
#pragma clang diagnostic pop
#endif

#ifdef VERIFIC_NAMESPACE
using namespace Verific ;
#endif

#endif

PRIVATE_NAMESPACE_BEGIN

#ifdef YOSYS_ENABLE_VERIFIC

void msg_func(msg_type_t msg_type, const char *message_id, linefile_type linefile, const char *msg, va_list args)
{
	string message = stringf("VERIFIC-%s [%s] ",
			msg_type == VERIFIC_NONE ? "NONE" :
			msg_type == VERIFIC_ERROR ? "ERROR" :
			msg_type == VERIFIC_WARNING ? "WARNING" :
			msg_type == VERIFIC_IGNORE ? "IGNORE" :
			msg_type == VERIFIC_INFO ? "INFO" :
			msg_type == VERIFIC_COMMENT ? "COMMENT" :
			msg_type == VERIFIC_PROGRAM_ERROR ? "PROGRAM_ERROR" : "UNKNOWN", message_id);

	if (linefile)
		message += stringf("%s:%d: ", LineFile::GetFileName(linefile), LineFile::GetLineNo(linefile));

	message += vstringf(msg, args);

	if (msg_type == VERIFIC_ERROR || msg_type == VERIFIC_WARNING || msg_type == VERIFIC_PROGRAM_ERROR)
		log_warning("%s\n", message.c_str());
	else
		log("%s\n", message.c_str());
}

string get_full_netlist_name(Netlist *nl)
{
	if (nl->NumOfRefs() == 1) {
		Instance *inst = (Instance*)nl->GetReferences()->GetLast();
		return get_full_netlist_name(inst->Owner()) + "." + inst->Name();
	}

	return nl->CellBaseName();
}

struct VerificImporter;
void import_sva_assert(VerificImporter *importer, Instance *inst);
void import_sva_assume(VerificImporter *importer, Instance *inst);
void import_sva_cover(VerificImporter *importer, Instance *inst);

struct VerificImporter
{
	RTLIL::Module *module;
	Netlist *netlist;

	std::map<Net*, RTLIL::SigBit> net_map;
	std::map<Net*, Net*> sva_posedge_map;

	bool mode_gates, mode_keep, verbose;

	pool<int> verific_sva_prims;
	pool<int> verific_psl_prims;

	VerificImporter(bool mode_gates, bool mode_keep, bool verbose) :
			mode_gates(mode_gates), mode_keep(mode_keep), verbose(verbose)
	{
		// Copy&paste from Verific 3.16_484_32_170630 Netlist.h
		vector<int> sva_prims {
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

		for (int p : sva_prims)
			verific_sva_prims.insert(p);

		// Copy&paste from Verific 3.16_484_32_170630 Netlist.h
		vector<int> psl_prims {
			OPER_PSLPREV, OPER_PSLNEXTFUNC, PRIM_PSL_ASSERT, PRIM_PSL_ASSUME,
			PRIM_PSL_ASSUME_GUARANTEE, PRIM_PSL_RESTRICT, PRIM_PSL_RESTRICT_GUARANTEE,
			PRIM_PSL_COVER, PRIM_ENDPOINT,  PRIM_ROSE, PRIM_FELL, PRIM_AT, PRIM_ATSTRONG,
			PRIM_ABORT, PRIM_PSL_NOT, PRIM_PSL_AND, PRIM_PSL_OR, PRIM_IMPL, PRIM_EQUIV,
			PRIM_PSL_X, PRIM_PSL_XSTRONG, PRIM_PSL_G, PRIM_PSL_F, PRIM_PSL_U, PRIM_PSL_W,
			PRIM_NEXT, PRIM_NEXTSTRONG, PRIM_ALWAYS, PRIM_NEVER, PRIM_EVENTUALLY,
			PRIM_UNTIL, PRIM_UNTIL_, PRIM_UNTILSTRONG, PRIM_UNTILSTRONG_, PRIM_BEFORE,
			PRIM_BEFORE_, PRIM_BEFORESTRONG, PRIM_BEFORESTRONG_, PRIM_NEXT_A,
			PRIM_NEXT_ASTRONG, PRIM_NEXT_E, PRIM_NEXT_ESTRONG, PRIM_NEXT_EVENT,
			PRIM_NEXT_EVENTSTRONG, PRIM_NEXT_EVENT_A, PRIM_NEXT_EVENT_ASTRONG,
			PRIM_NEXT_EVENT_E, PRIM_NEXT_EVENT_ESTRONG, PRIM_SEQ_IMPL, PRIM_OSUFFIX_IMPL,
			PRIM_SUFFIX_IMPL, PRIM_OSUFFIX_IMPLSTRONG, PRIM_SUFFIX_IMPLSTRONG, PRIM_WITHIN,
			PRIM_WITHIN_, PRIM_WITHINSTRONG, PRIM_WITHINSTRONG_, PRIM_WHILENOT,
			PRIM_WHILENOT_, PRIM_WHILENOTSTRONG, PRIM_WHILENOTSTRONG_, PRIM_CONCAT,
			PRIM_FUSION, PRIM_SEQ_AND_LEN, PRIM_SEQ_AND, PRIM_SEQ_OR, PRIM_CONS_REP,
			PRIM_NONCONS_REP, PRIM_GOTO_REP
		};

		for (int p : sva_prims)
			verific_psl_prims.insert(p);
	}

	RTLIL::SigBit net_map_at(Net *net)
	{
		if (net->IsExternalTo(netlist))
			log_error("Found external reference to '%s.%s' in netlist '%s', please use -flatten or -extnets.\n",
					get_full_netlist_name(net->Owner()).c_str(), net->Name(), get_full_netlist_name(netlist).c_str());

		return net_map.at(net);
	}

	void import_attributes(dict<RTLIL::IdString, RTLIL::Const> &attributes, DesignObj *obj)
	{
		MapIter mi;
		Att *attr;

		if (obj->Linefile())
			attributes["\\src"] = stringf("%s:%d", LineFile::GetFileName(obj->Linefile()), LineFile::GetLineNo(obj->Linefile()));

		// FIXME: Parse numeric attributes
		FOREACH_ATTRIBUTE(obj, mi, attr)
			attributes[RTLIL::escape_id(attr->Key())] = RTLIL::Const(std::string(attr->Value()));
	}

	RTLIL::SigSpec operatorInput(Instance *inst)
	{
		RTLIL::SigSpec sig;
		for (int i = int(inst->InputSize())-1; i >= 0; i--)
			if (inst->GetInputBit(i))
				sig.append(net_map_at(inst->GetInputBit(i)));
			else
				sig.append(RTLIL::State::Sz);
		return sig;
	}

	RTLIL::SigSpec operatorInput1(Instance *inst)
	{
		RTLIL::SigSpec sig;
		for (int i = int(inst->Input1Size())-1; i >= 0; i--)
			if (inst->GetInput1Bit(i))
				sig.append(net_map_at(inst->GetInput1Bit(i)));
			else
				sig.append(RTLIL::State::Sz);
		return sig;
	}

	RTLIL::SigSpec operatorInput2(Instance *inst)
	{
		RTLIL::SigSpec sig;
		for (int i = int(inst->Input2Size())-1; i >= 0; i--)
			if (inst->GetInput2Bit(i))
				sig.append(net_map_at(inst->GetInput2Bit(i)));
			else
				sig.append(RTLIL::State::Sz);
		return sig;
	}

	RTLIL::SigSpec operatorInport(Instance *inst, const char *portname)
	{
		PortBus *portbus = inst->View()->GetPortBus(portname);
		if (portbus) {
			RTLIL::SigSpec sig;
			for (unsigned i = 0; i < portbus->Size(); i++) {
				Net *net = inst->GetNet(portbus->ElementAtIndex(i));
				if (net) {
					if (net->IsGnd())
						sig.append(RTLIL::State::S0);
					else if (net->IsPwr())
						sig.append(RTLIL::State::S1);
					else
						sig.append(net_map_at(net));
				} else
					sig.append(RTLIL::State::Sz);
			}
			return sig;
		} else {
			Port *port = inst->View()->GetPort(portname);
			log_assert(port != NULL);
			Net *net = inst->GetNet(port);
			return net_map_at(net);
		}
	}

	RTLIL::SigSpec operatorOutput(Instance *inst)
	{
		RTLIL::SigSpec sig;
		RTLIL::Wire *dummy_wire = NULL;
		for (int i = int(inst->OutputSize())-1; i >= 0; i--)
			if (inst->GetOutputBit(i)) {
				sig.append(net_map_at(inst->GetOutputBit(i)));
				dummy_wire = NULL;
			} else {
				if (dummy_wire == NULL)
					dummy_wire = module->addWire(NEW_ID);
				else
					dummy_wire->width++;
				sig.append(RTLIL::SigSpec(dummy_wire, dummy_wire->width - 1));
			}
		return sig;
	}

	bool import_netlist_instance_gates(Instance *inst, RTLIL::IdString inst_name)
	{
		if (inst->Type() == PRIM_AND) {
			module->addAndGate(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_NAND) {
			RTLIL::SigSpec tmp = module->addWire(NEW_ID);
			module->addAndGate(NEW_ID, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), tmp);
			module->addNotGate(inst_name, tmp, net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_OR) {
			module->addOrGate(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_NOR) {
			RTLIL::SigSpec tmp = module->addWire(NEW_ID);
			module->addOrGate(NEW_ID, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), tmp);
			module->addNotGate(inst_name, tmp, net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_XOR) {
			module->addXorGate(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_XNOR) {
			module->addXnorGate(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_BUF) {
			module->addBufGate(inst_name, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_INV) {
			module->addNotGate(inst_name, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_MUX) {
			module->addMuxGate(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetControl()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_TRI) {
			module->addMuxGate(inst_name, RTLIL::State::Sz, net_map_at(inst->GetInput()), net_map_at(inst->GetControl()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_FADD)
		{
			RTLIL::SigSpec a = net_map_at(inst->GetInput1()), b = net_map_at(inst->GetInput2()), c = net_map_at(inst->GetCin());
			RTLIL::SigSpec x = inst->GetCout() ? net_map_at(inst->GetCout()) : module->addWire(NEW_ID);
			RTLIL::SigSpec y = inst->GetOutput() ? net_map_at(inst->GetOutput()) : module->addWire(NEW_ID);
			RTLIL::SigSpec tmp1 = module->addWire(NEW_ID);
			RTLIL::SigSpec tmp2 = module->addWire(NEW_ID);
			RTLIL::SigSpec tmp3 = module->addWire(NEW_ID);
			module->addXorGate(NEW_ID, a, b, tmp1);
			module->addXorGate(inst_name, tmp1, c, y);
			module->addAndGate(NEW_ID, tmp1, c, tmp2);
			module->addAndGate(NEW_ID, a, b, tmp3);
			module->addOrGate(NEW_ID, tmp2, tmp3, x);
			return true;
		}

		if (inst->Type() == PRIM_DFFRS)
		{
			if (inst->GetSet()->IsGnd() && inst->GetReset()->IsGnd())
				module->addDffGate(inst_name, net_map_at(inst->GetClock()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
			else if (inst->GetSet()->IsGnd())
				module->addAdffGate(inst_name, net_map_at(inst->GetClock()), net_map_at(inst->GetReset()),
						net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()), false);
			else if (inst->GetReset()->IsGnd())
				module->addAdffGate(inst_name, net_map_at(inst->GetClock()), net_map_at(inst->GetSet()),
						net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()), true);
			else
				module->addDffsrGate(inst_name, net_map_at(inst->GetClock()), net_map_at(inst->GetSet()), net_map_at(inst->GetReset()),
						net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
			return true;
		}

		return false;
	}

	bool import_netlist_instance_cells(Instance *inst, RTLIL::IdString inst_name)
	{
		if (inst->Type() == PRIM_AND) {
			module->addAnd(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_NAND) {
			RTLIL::SigSpec tmp = module->addWire(NEW_ID);
			module->addAnd(NEW_ID, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), tmp);
			module->addNot(inst_name, tmp, net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_OR) {
			module->addOr(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_NOR) {
			RTLIL::SigSpec tmp = module->addWire(NEW_ID);
			module->addOr(NEW_ID, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), tmp);
			module->addNot(inst_name, tmp, net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_XOR) {
			module->addXor(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_XNOR) {
			module->addXnor(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_INV) {
			module->addNot(inst_name, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_MUX) {
			module->addMux(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetControl()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_TRI) {
			module->addMux(inst_name, RTLIL::State::Sz, net_map_at(inst->GetInput()), net_map_at(inst->GetControl()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_FADD)
		{
			RTLIL::SigSpec a_plus_b = module->addWire(NEW_ID, 2);
			RTLIL::SigSpec y = inst->GetOutput() ? net_map_at(inst->GetOutput()) : module->addWire(NEW_ID);
			if (inst->GetCout())
				y.append(net_map_at(inst->GetCout()));
			module->addAdd(NEW_ID, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), a_plus_b);
			module->addAdd(inst_name, a_plus_b, net_map_at(inst->GetCin()), y);
			return true;
		}

		if (inst->Type() == PRIM_DFFRS)
		{
			if (inst->GetSet()->IsGnd() && inst->GetReset()->IsGnd())
				module->addDff(inst_name, net_map_at(inst->GetClock()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
			else if (inst->GetSet()->IsGnd())
				module->addAdff(inst_name, net_map_at(inst->GetClock()), net_map_at(inst->GetReset()),
						net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()), RTLIL::State::S0);
			else if (inst->GetReset()->IsGnd())
				module->addAdff(inst_name, net_map_at(inst->GetClock()), net_map_at(inst->GetSet()),
						net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()), RTLIL::State::S1);
			else
				module->addDffsr(inst_name, net_map_at(inst->GetClock()), net_map_at(inst->GetSet()), net_map_at(inst->GetReset()),
						net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
			return true;
		}

		if (inst->Type() == PRIM_DLATCHRS)
		{
			if (inst->GetSet()->IsGnd() && inst->GetReset()->IsGnd())
				module->addDlatch(inst_name, net_map_at(inst->GetControl()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
			else
				module->addDlatchsr(inst_name, net_map_at(inst->GetControl()), net_map_at(inst->GetSet()), net_map_at(inst->GetReset()),
						net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
			return true;
		}

		#define IN  operatorInput(inst)
		#define IN1 operatorInput1(inst)
		#define IN2 operatorInput2(inst)
		#define OUT operatorOutput(inst)
		#define SIGNED inst->View()->IsSigned()

		if (inst->Type() == OPER_ADDER) {
			RTLIL::SigSpec out = OUT;
			if (inst->GetCout() != NULL)
				out.append(net_map_at(inst->GetCout()));
			if (inst->GetCin()->IsGnd()) {
				module->addAdd(inst_name, IN1, IN2, out, SIGNED);
			} else {
				RTLIL::SigSpec tmp = module->addWire(NEW_ID, GetSize(out));
				module->addAdd(NEW_ID, IN1, IN2, tmp, SIGNED);
				module->addAdd(inst_name, tmp, net_map_at(inst->GetCin()), out, false);
			}
			return true;
		}

		if (inst->Type() == OPER_MULTIPLIER) {
			module->addMul(inst_name, IN1, IN2, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_DIVIDER) {
			module->addDiv(inst_name, IN1, IN2, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_MODULO) {
			module->addMod(inst_name, IN1, IN2, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_REMAINDER) {
			module->addMod(inst_name, IN1, IN2, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_SHIFT_LEFT) {
			module->addShl(inst_name, IN1, IN2, OUT, false);
			return true;
		}

		if (inst->Type() == OPER_ENABLED_DECODER) {
			RTLIL::SigSpec vec;
			vec.append(net_map_at(inst->GetControl()));
			for (unsigned i = 1; i < inst->OutputSize(); i++) {
				vec.append(RTLIL::State::S0);
			}
			module->addShl(inst_name, vec, IN, OUT, false);
			return true;
		}

		if (inst->Type() == OPER_DECODER) {
			RTLIL::SigSpec vec;
			vec.append(RTLIL::State::S1);
			for (unsigned i = 1; i < inst->OutputSize(); i++) {
				vec.append(RTLIL::State::S0);
			}
			module->addShl(inst_name, vec, IN, OUT, false);
			return true;
		}

		if (inst->Type() == OPER_SHIFT_RIGHT) {
			Net *net_cin = inst->GetCin();
			Net *net_a_msb = inst->GetInput1Bit(0);
			if (net_cin->IsGnd())
				module->addShr(inst_name, IN1, IN2, OUT, false);
			else if (net_cin == net_a_msb)
				module->addSshr(inst_name, IN1, IN2, OUT, true);
			else
				log_error("Can't import Verific OPER_SHIFT_RIGHT instance %s: carry_in is neither 0 nor msb of left input\n", inst->Name());
			return true;
		}

		if (inst->Type() == OPER_REDUCE_AND) {
			module->addReduceAnd(inst_name, IN, net_map_at(inst->GetOutput()), SIGNED);
			return true;
		}

		if (inst->Type() == OPER_REDUCE_OR) {
			module->addReduceOr(inst_name, IN, net_map_at(inst->GetOutput()), SIGNED);
			return true;
		}

		if (inst->Type() == OPER_REDUCE_XOR) {
			module->addReduceXor(inst_name, IN, net_map_at(inst->GetOutput()), SIGNED);
			return true;
		}

		if (inst->Type() == OPER_REDUCE_XNOR) {
			module->addReduceXnor(inst_name, IN, net_map_at(inst->GetOutput()), SIGNED);
			return true;
		}

		if (inst->Type() == OPER_LESSTHAN) {
			Net *net_cin = inst->GetCin();
			if (net_cin->IsGnd())
				module->addLt(inst_name, IN1, IN2, net_map_at(inst->GetOutput()), SIGNED);
			else if (net_cin->IsPwr())
				module->addLe(inst_name, IN1, IN2, net_map_at(inst->GetOutput()), SIGNED);
			else
				log_error("Can't import Verific OPER_LESSTHAN instance %s: carry_in is neither 0 nor 1\n", inst->Name());
			return true;
		}

		if (inst->Type() == OPER_WIDE_AND) {
			module->addAnd(inst_name, IN1, IN2, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_WIDE_OR) {
			module->addOr(inst_name, IN1, IN2, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_WIDE_XOR) {
			module->addXor(inst_name, IN1, IN2, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_WIDE_XNOR) {
			module->addXnor(inst_name, IN1, IN2, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_WIDE_BUF) {
			module->addPos(inst_name, IN, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_WIDE_INV) {
			module->addNot(inst_name, IN, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_MINUS) {
			module->addSub(inst_name, IN1, IN2, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_UMINUS) {
			module->addNeg(inst_name, IN, OUT, SIGNED);
			return true;
		}

		if (inst->Type() == OPER_EQUAL) {
			module->addEq(inst_name, IN1, IN2, net_map_at(inst->GetOutput()), SIGNED);
			return true;
		}

		if (inst->Type() == OPER_NEQUAL) {
			module->addNe(inst_name, IN1, IN2, net_map_at(inst->GetOutput()), SIGNED);
			return true;
		}

		if (inst->Type() == OPER_WIDE_MUX) {
			module->addMux(inst_name, IN1, IN2, net_map_at(inst->GetControl()), OUT);
			return true;
		}

		if (inst->Type() == OPER_WIDE_TRI) {
			module->addMux(inst_name, RTLIL::SigSpec(RTLIL::State::Sz, inst->OutputSize()), IN, net_map_at(inst->GetControl()), OUT);
			return true;
		}

		if (inst->Type() == OPER_WIDE_DFFRS) {
			RTLIL::SigSpec sig_set = operatorInport(inst, "set");
			RTLIL::SigSpec sig_reset = operatorInport(inst, "reset");
			if (sig_set.is_fully_const() && !sig_set.as_bool() && sig_reset.is_fully_const() && !sig_reset.as_bool())
				module->addDff(inst_name, net_map_at(inst->GetClock()), IN, OUT);
			else
				module->addDffsr(inst_name, net_map_at(inst->GetClock()), sig_set, sig_reset, IN, OUT);
			return true;
		}

		#undef IN
		#undef IN1
		#undef IN2
		#undef OUT
		#undef SIGNED

		return false;
	}

	void import_netlist(RTLIL::Design *design, Netlist *nl, std::set<Netlist*> &nl_todo)
	{
		std::string module_name = nl->IsOperator() ? std::string("$verific$") + nl->Owner()->Name() : RTLIL::escape_id(nl->Owner()->Name());

		netlist = nl;

		if (design->has(module_name)) {
			if (!nl->IsOperator())
				log_cmd_error("Re-definition of module `%s'.\n", nl->Owner()->Name());
			return;
		}

		module = new RTLIL::Module;
		module->name = module_name;
		design->add(module);

		if (nl->IsBlackBox()) {
			log("Importing blackbox module %s.\n", RTLIL::id2cstr(module->name));
			module->set_bool_attribute("\\blackbox");
		} else {
			log("Importing module %s.\n", RTLIL::id2cstr(module->name));
		}

		SetIter si;
		MapIter mi, mi2;
		Port *port;
		PortBus *portbus;
		Net *net;
		NetBus *netbus;
		Instance *inst;
		PortRef *pr;

		FOREACH_PORT_OF_NETLIST(nl, mi, port)
		{
			if (port->Bus())
				continue;

			if (verbose)
				log("  importing port %s.\n", port->Name());

			RTLIL::Wire *wire = module->addWire(RTLIL::escape_id(port->Name()));
			import_attributes(wire->attributes, port);

			wire->port_id = nl->IndexOf(port) + 1;

			if (port->GetDir() == DIR_INOUT || port->GetDir() == DIR_IN)
				wire->port_input = true;
			if (port->GetDir() == DIR_INOUT || port->GetDir() == DIR_OUT)
				wire->port_output = true;

			if (port->GetNet()) {
				net = port->GetNet();
				if (net_map.count(net) == 0)
					net_map[net] = wire;
				else if (wire->port_input)
					module->connect(net_map_at(net), wire);
				else
					module->connect(wire, net_map_at(net));
			}
		}

		FOREACH_PORTBUS_OF_NETLIST(nl, mi, portbus)
		{
			if (verbose)
				log("  importing portbus %s.\n", portbus->Name());

			RTLIL::Wire *wire = module->addWire(RTLIL::escape_id(portbus->Name()), portbus->Size());
			wire->start_offset = min(portbus->LeftIndex(), portbus->RightIndex());
			import_attributes(wire->attributes, portbus);

			if (portbus->GetDir() == DIR_INOUT || portbus->GetDir() == DIR_IN)
				wire->port_input = true;
			if (portbus->GetDir() == DIR_INOUT || portbus->GetDir() == DIR_OUT)
				wire->port_output = true;

			for (int i = portbus->LeftIndex();; i += portbus->IsUp() ? +1 : -1) {
				if (portbus->ElementAtIndex(i) && portbus->ElementAtIndex(i)->GetNet()) {
					net = portbus->ElementAtIndex(i)->GetNet();
					RTLIL::SigBit bit(wire, i - wire->start_offset);
					if (net_map.count(net) == 0)
						net_map[net] = bit;
					else if (wire->port_input)
						module->connect(net_map_at(net), bit);
					else
						module->connect(bit, net_map_at(net));
				}
				if (i == portbus->RightIndex())
					break;
			}
		}

		module->fixup_ports();

		dict<Net*, char, hash_ptr_ops> init_nets;
		pool<Net*, hash_ptr_ops> anyconst_nets;
		pool<Net*, hash_ptr_ops> anyseq_nets;

		FOREACH_NET_OF_NETLIST(nl, mi, net)
		{
			if (net->IsRamNet())
			{
				RTLIL::Memory *memory = new RTLIL::Memory;
				memory->name = RTLIL::escape_id(net->Name());
				log_assert(module->count_id(memory->name) == 0);
				module->memories[memory->name] = memory;

				int number_of_bits = net->Size();
				int bits_in_word = number_of_bits;
				FOREACH_PORTREF_OF_NET(net, si, pr) {
					if (pr->GetInst()->Type() == OPER_READ_PORT) {
						bits_in_word = min<int>(bits_in_word, pr->GetInst()->OutputSize());
						continue;
					}
					if (pr->GetInst()->Type() == OPER_WRITE_PORT || pr->GetInst()->Type() == OPER_CLOCKED_WRITE_PORT) {
						bits_in_word = min<int>(bits_in_word, pr->GetInst()->Input2Size());
						continue;
					}
					log_error("Verific RamNet %s is connected to unsupported instance type %s (%s).\n",
							net->Name(), pr->GetInst()->View()->Owner()->Name(), pr->GetInst()->Name());
				}

				memory->width = bits_in_word;
				memory->size = number_of_bits / bits_in_word;

				const char *ascii_initdata = net->GetWideInitialValue();
				if (ascii_initdata) {
					while (*ascii_initdata != 0 && *ascii_initdata != '\'')
						ascii_initdata++;
					if (*ascii_initdata == '\'')
						ascii_initdata++;
					if (*ascii_initdata != 0) {
						log_assert(*ascii_initdata == 'b');
						ascii_initdata++;
					}
					for (int word_idx = 0; word_idx < memory->size; word_idx++) {
						Const initval = Const(State::Sx, memory->width);
						bool initval_valid = false;
						for (int bit_idx = memory->width-1; bit_idx >= 0; bit_idx--) {
							if (*ascii_initdata == 0)
								break;
							if (*ascii_initdata == '0' || *ascii_initdata == '1') {
								initval[bit_idx] = (*ascii_initdata == '0') ? State::S0 : State::S1;
								initval_valid = true;
							}
							ascii_initdata++;
						}
						if (initval_valid) {
							RTLIL::Cell *cell = module->addCell(NEW_ID, "$meminit");
							cell->parameters["\\WORDS"] = 1;
							if (net->GetOrigTypeRange()->LeftRangeBound() < net->GetOrigTypeRange()->RightRangeBound())
								cell->setPort("\\ADDR", word_idx);
							else
								cell->setPort("\\ADDR", memory->size - word_idx - 1);
							cell->setPort("\\DATA", initval);
							cell->parameters["\\MEMID"] = RTLIL::Const(memory->name.str());
							cell->parameters["\\ABITS"] = 32;
							cell->parameters["\\WIDTH"] = memory->width;
							cell->parameters["\\PRIORITY"] = RTLIL::Const(autoidx-1);
						}
					}
				}
				continue;
			}

			if (net->GetInitialValue())
				init_nets[net] = net->GetInitialValue();

			const char *rand_const_attr = net->GetAttValue(" rand_const");
			const char *rand_attr = net->GetAttValue(" rand");

			if (rand_const_attr != nullptr && !strcmp(rand_const_attr, "1"))
				anyconst_nets.insert(net);

			else if (rand_attr != nullptr && !strcmp(rand_attr, "1"))
				anyseq_nets.insert(net);

			if (net_map.count(net)) {
				if (verbose)
					log("  skipping net %s.\n", net->Name());
				continue;
			}

			if (net->Bus())
				continue;

			RTLIL::IdString wire_name = module->uniquify(net->IsUserDeclared() ? RTLIL::escape_id(net->Name()) : NEW_ID);

			if (verbose)
				log("  importing net %s as %s.\n", net->Name(), log_id(wire_name));

			RTLIL::Wire *wire = module->addWire(wire_name);
			import_attributes(wire->attributes, net);

			net_map[net] = wire;
		}

		FOREACH_NETBUS_OF_NETLIST(nl, mi, netbus)
		{
			bool found_new_net = false;
			for (int i = netbus->LeftIndex();; i += netbus->IsUp() ? +1 : -1) {
				net = netbus->ElementAtIndex(i);
				if (net_map.count(net) == 0)
					found_new_net = true;
				if (i == netbus->RightIndex())
					break;
			}

			if (found_new_net)
			{
				if (verbose)
					log("  importing netbus %s.\n", netbus->Name());

				RTLIL::IdString wire_name = module->uniquify(RTLIL::escape_id(netbus->Name()));
				RTLIL::Wire *wire = module->addWire(wire_name, netbus->Size());
				wire->start_offset = min(netbus->LeftIndex(), netbus->RightIndex());
				import_attributes(wire->attributes, netbus);

				RTLIL::Const initval = Const(State::Sx, GetSize(wire));
				bool initval_valid = false;

				for (int i = netbus->LeftIndex();; i += netbus->IsUp() ? +1 : -1)
				{
					if (netbus->ElementAtIndex(i))
					{
						int bitidx = i - wire->start_offset;
						net = netbus->ElementAtIndex(i);
						RTLIL::SigBit bit(wire, bitidx);

						if (init_nets.count(net)) {
							if (init_nets.at(net) == '0')
								initval.bits.at(bitidx) = State::S0;
							if (init_nets.at(net) == '1')
								initval.bits.at(bitidx) = State::S1;
							initval_valid = true;
							init_nets.erase(net);
						}

						if (net_map.count(net) == 0)
							net_map[net] = bit;
						else
							module->connect(bit, net_map_at(net));
					}

					if (i == netbus->RightIndex())
						break;
				}

				if (initval_valid)
					wire->attributes["\\init"] = initval;
			}
			else
			{
				if (verbose)
					log("  skipping netbus %s.\n", netbus->Name());
			}

			SigSpec anyconst_sig;
			SigSpec anyseq_sig;

			for (int i = netbus->RightIndex();; i += netbus->IsUp() ? -1 : +1) {
				net = netbus->ElementAtIndex(i);
				if (net != nullptr && anyconst_nets.count(net)) {
					anyconst_sig.append(net_map_at(net));
					anyconst_nets.erase(net);
				}
				if (net != nullptr && anyseq_nets.count(net)) {
					anyseq_sig.append(net_map_at(net));
					anyseq_nets.erase(net);
				}
				if (i == netbus->LeftIndex())
					break;
			}

			if (GetSize(anyconst_sig))
				module->connect(anyconst_sig, module->Anyconst(NEW_ID, GetSize(anyconst_sig)));

			if (GetSize(anyseq_sig))
				module->connect(anyseq_sig, module->Anyseq(NEW_ID, GetSize(anyseq_sig)));
		}

		for (auto it : init_nets)
		{
			Const initval;
			SigBit bit = net_map_at(it.first);
			log_assert(bit.wire);

			if (bit.wire->attributes.count("\\init"))
				initval = bit.wire->attributes.at("\\init");

			while (GetSize(initval) < GetSize(bit.wire))
				initval.bits.push_back(State::Sx);

			if (it.second == '0')
				initval.bits.at(bit.offset) = State::S0;
			if (it.second == '1')
				initval.bits.at(bit.offset) = State::S1;

			bit.wire->attributes["\\init"] = initval;
		}

		for (auto net : anyconst_nets)
			module->connect(net_map_at(net), module->Anyconst(NEW_ID));

		for (auto net : anyseq_nets)
			module->connect(net_map_at(net), module->Anyseq(NEW_ID));

		pool<Instance*, hash_ptr_ops> sva_asserts;
		pool<Instance*, hash_ptr_ops> sva_assumes;
		pool<Instance*, hash_ptr_ops> sva_covers;

		FOREACH_INSTANCE_OF_NETLIST(nl, mi, inst)
		{
			RTLIL::IdString inst_name = module->uniquify(inst->IsUserDeclared() ? RTLIL::escape_id(inst->Name()) : NEW_ID);

			if (verbose)
				log("  importing cell %s (%s) as %s.\n", inst->Name(), inst->View()->Owner()->Name(), log_id(inst_name));

			if (inst->Type() == PRIM_SVA_IMMEDIATE_ASSERT) {
				Net *in = inst->GetInput();
				module->addAssert(NEW_ID, net_map_at(in), State::S1);
				continue;
			}

			if (inst->Type() == PRIM_SVA_IMMEDIATE_ASSUME) {
				Net *in = inst->GetInput();
				module->addAssume(NEW_ID, net_map_at(in), State::S1);
				continue;
			}

			if (inst->Type() == PRIM_SVA_IMMEDIATE_COVER) {
				Net *in = inst->GetInput();
				module->addCover(NEW_ID, net_map_at(in), State::S1);
				continue;
			}

			if (inst->Type() == PRIM_PWR) {
				module->connect(net_map_at(inst->GetOutput()), RTLIL::State::S1);
				continue;
			}

			if (inst->Type() == PRIM_GND) {
				module->connect(net_map_at(inst->GetOutput()), RTLIL::State::S0);
				continue;
			}

			if (inst->Type() == PRIM_BUF) {
				module->addBufGate(inst_name, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
				continue;
			}

			if (inst->Type() == PRIM_X) {
				module->connect(net_map_at(inst->GetOutput()), RTLIL::State::Sx);
				continue;
			}

			if (inst->Type() == PRIM_Z) {
				module->connect(net_map_at(inst->GetOutput()), RTLIL::State::Sz);
				continue;
			}

			if (inst->Type() == OPER_READ_PORT)
			{
				RTLIL::Memory *memory = module->memories.at(RTLIL::escape_id(inst->GetInput()->Name()));
				if (memory->width != int(inst->OutputSize()))
					log_error("Import of asymetric memories from Verific is not supported yet: %s %s\n", inst->Name(), inst->GetInput()->Name());

				RTLIL::SigSpec addr = operatorInput1(inst);
				RTLIL::SigSpec data = operatorOutput(inst);

				RTLIL::Cell *cell = module->addCell(inst_name, "$memrd");
				cell->parameters["\\MEMID"] = memory->name.str();
				cell->parameters["\\CLK_ENABLE"] = false;
				cell->parameters["\\CLK_POLARITY"] = true;
				cell->parameters["\\TRANSPARENT"] = false;
				cell->parameters["\\ABITS"] = GetSize(addr);
				cell->parameters["\\WIDTH"] = GetSize(data);
				cell->setPort("\\CLK", RTLIL::State::Sx);
				cell->setPort("\\EN", RTLIL::State::Sx);
				cell->setPort("\\ADDR", addr);
				cell->setPort("\\DATA", data);
				continue;
			}

			if (inst->Type() == OPER_WRITE_PORT || inst->Type() == OPER_CLOCKED_WRITE_PORT)
			{
				RTLIL::Memory *memory = module->memories.at(RTLIL::escape_id(inst->GetOutput()->Name()));
				if (memory->width != int(inst->Input2Size()))
					log_error("Import of asymetric memories from Verific is not supported yet: %s %s\n", inst->Name(), inst->GetInput()->Name());

				RTLIL::SigSpec addr = operatorInput1(inst);
				RTLIL::SigSpec data = operatorInput2(inst);

				RTLIL::Cell *cell = module->addCell(inst_name, "$memwr");
				cell->parameters["\\MEMID"] = memory->name.str();
				cell->parameters["\\CLK_ENABLE"] = false;
				cell->parameters["\\CLK_POLARITY"] = true;
				cell->parameters["\\PRIORITY"] = 0;
				cell->parameters["\\ABITS"] = GetSize(addr);
				cell->parameters["\\WIDTH"] = GetSize(data);
				cell->setPort("\\EN", RTLIL::SigSpec(net_map_at(inst->GetControl())).repeat(GetSize(data)));
				cell->setPort("\\CLK", RTLIL::State::S0);
				cell->setPort("\\ADDR", addr);
				cell->setPort("\\DATA", data);

				if (inst->Type() == OPER_CLOCKED_WRITE_PORT) {
					cell->parameters["\\CLK_ENABLE"] = true;
					cell->setPort("\\CLK", net_map_at(inst->GetClock()));
				}
				continue;
			}

			if (!mode_gates) {
				if (import_netlist_instance_cells(inst, inst_name))
					continue;
				if (inst->IsOperator())
					log_warning("Unsupported Verific operator: %s (fallback to gate level implementation provided by verific)\n", inst->View()->Owner()->Name());
			} else {
				if (import_netlist_instance_gates(inst, inst_name))
					continue;
			}

			if (inst->Type() == PRIM_SVA_ASSERT)
				sva_asserts.insert(inst);

			if (inst->Type() == PRIM_SVA_ASSUME)
				sva_asserts.insert(inst);

			if (inst->Type() == PRIM_SVA_COVER)
				sva_covers.insert(inst);

			if (!mode_keep && (verific_sva_prims.count(inst->Type()) || verific_psl_prims.count(inst->Type()))) {
				if (verbose)
					log("    skipping SVA/PSL cell in non k-mode\n");
				continue;
			}

			if (inst->IsPrimitive())
			{
				if (!mode_keep)
					log_error("Unsupported Verific primitive %s of type %s\n", inst->Name(), inst->View()->Owner()->Name());

				if (!verific_sva_prims.count(inst->Type()) && !verific_psl_prims.count(inst->Type()))
					log_warning("Unsupported Verific primitive %s of type %s\n", inst->Name(), inst->View()->Owner()->Name());
			}

			nl_todo.insert(inst->View());

			RTLIL::Cell *cell = module->addCell(inst_name, inst->IsOperator() ?
					std::string("$verific$") + inst->View()->Owner()->Name() : RTLIL::escape_id(inst->View()->Owner()->Name()));

			if (inst->IsPrimitive() && mode_keep)
				cell->attributes["\\keep"] = 1;

			dict<IdString, vector<SigBit>> cell_port_conns;

			if (verbose)
				log("    ports in verific db:\n");

			FOREACH_PORTREF_OF_INST(inst, mi2, pr) {
				if (verbose)
					log("      .%s(%s)\n", pr->GetPort()->Name(), pr->GetNet()->Name());
				const char *port_name = pr->GetPort()->Name();
				int port_offset = 0;
				if (pr->GetPort()->Bus()) {
					port_name = pr->GetPort()->Bus()->Name();
					port_offset = pr->GetPort()->Bus()->IndexOf(pr->GetPort()) -
							min(pr->GetPort()->Bus()->LeftIndex(), pr->GetPort()->Bus()->RightIndex());
				}
				IdString port_name_id = RTLIL::escape_id(port_name);
				auto &sigvec = cell_port_conns[port_name_id];
				if (GetSize(sigvec) <= port_offset) {
					SigSpec zwires = module->addWire(NEW_ID, port_offset+1-GetSize(sigvec));
					for (auto bit : zwires)
						sigvec.push_back(bit);
				}
				sigvec[port_offset] = net_map_at(pr->GetNet());
			}

			if (verbose)
				log("    ports in yosys db:\n");

			for (auto &it : cell_port_conns) {
				if (verbose)
					log("      .%s(%s)\n", log_id(it.first), log_signal(it.second));
				cell->setPort(it.first, it.second);
			}
		}

		for (auto inst : sva_asserts)
			import_sva_assert(this, inst);

		for (auto inst : sva_assumes)
			import_sva_assume(this, inst);

		for (auto inst : sva_covers)
			import_sva_cover(this, inst);
	}
};

struct VerificSvaImporter
{
	VerificImporter *importer;
	Module *module;

	Netlist *netlist;
	Instance *root;

	SigBit clock = State::Sx;
	bool clock_posedge = false;

	SigBit disable_iff = State::S0;

	bool import_sva_disable_hiactive = true;
	int import_sva_init_disable_steps = 0;

	bool mode_assert = false;
	bool mode_assume = false;
	bool mode_cover = false;

	Instance *net_to_ast_driver(Net *n)
	{
		if (n == nullptr)
			return nullptr;

		if (n->IsMultipleDriven())
			return nullptr;

		Instance *inst = n->Driver();

		if (inst == nullptr)
			return nullptr;

		if (!importer->verific_sva_prims.count(inst->Type()) &&
				!importer->verific_psl_prims.count(inst->Type()))
			return nullptr;

		return inst;
	}

	Instance *get_ast_input(Instance *inst) { return net_to_ast_driver(inst->GetInput()); }
	Instance *get_ast_input1(Instance *inst) { return net_to_ast_driver(inst->GetInput1()); }
	Instance *get_ast_input2(Instance *inst) { return net_to_ast_driver(inst->GetInput2()); }
	Instance *get_ast_input3(Instance *inst) { return net_to_ast_driver(inst->GetInput3()); }
	Instance *get_ast_control(Instance *inst) { return net_to_ast_driver(inst->GetControl()); }

	SigBit parse_sequence(Net *n)
	{
		Instance *inst = net_to_ast_driver(n);

		if (inst == nullptr)
			return importer->net_map_at(n);

		if (!importer->mode_keep)
			log_error("Unsupported Verific SVA primitive %s of type %s.\n", inst->Name(), inst->View()->Owner()->Name());
		log_warning("Unsupported Verific SVA primitive %s of type %s.\n", inst->Name(), inst->View()->Owner()->Name());

		return importer->net_map_at(n);
	}

	void run()
	{
		module = importer->module;
		netlist = root->Owner();

		// parse SVA property clock event

		Instance *at_node = get_ast_input(root);
		log_assert(at_node && at_node->Type() == PRIM_SVA_AT);

		Instance *clock_node = get_ast_input1(at_node);
		log_assert(clock_node && (clock_node->Type() == PRIM_SVA_POSEDGE || clock_node->Type() == PRIM_SVA_POSEDGE));

		clock = importer->net_map_at(clock_node->GetInput());
		clock_posedge = (clock_node->Type() == PRIM_SVA_POSEDGE);

		import_sva_init_disable_steps = 1;

		// parse disable_iff expression

		Net *sequence_net = at_node->GetInput2();
		Instance *sequence_node = net_to_ast_driver(sequence_net);

		if (sequence_node && sequence_node->Type() == PRIM_SVA_DISABLE_IFF) {
			disable_iff = importer->net_map_at(sequence_node->GetInput1());
			sequence_net = sequence_node->GetInput2();
		}

		// parse SVA sequence into trigger signal

		SigBit sig_a_d = parse_sequence(sequence_net);
		Wire *sig_a_q = module->addWire(NEW_ID);
		sig_a_q->attributes["\\init"] = Const(import_sva_disable_hiactive ? State::S1 : State::S0, 1);
		module->addDff(NEW_ID, clock, sig_a_d, sig_a_q, clock_posedge);

		// generate properly delayed enable signal

		SigBit sig_en = State::S1;

		if (disable_iff != State::S0)
			sig_en = module->Mux(NEW_ID, sig_en, State::S0, disable_iff);

		for (int i = 0; i < import_sva_init_disable_steps; i++)
		{
			Wire *new_en = module->addWire(NEW_ID);
			new_en->attributes["\\init"] = Const(0, 1);

			module->addDff(NEW_ID, clock, sig_en, new_en, clock_posedge);

			if (disable_iff != State::S0 && i+1 < import_sva_init_disable_steps)
				sig_en = module->Mux(NEW_ID, new_en, State::S0, disable_iff);
			else
				sig_en = new_en;
		}

		// generate assert/assume/cover cell

		RTLIL::IdString root_name = module->uniquify(root->IsUserDeclared() ? RTLIL::escape_id(root->Name()) : NEW_ID);

		if (mode_assert) module->addAssert(root_name, sig_a_q, sig_en);
		if (mode_assume) module->addAssume(root_name, sig_a_q, sig_en);
		if (mode_cover) module->addCover(root_name, sig_a_q, sig_en);
	}
};

void import_sva_assert(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_assert = true;
	worker.run();
}

void import_sva_assume(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_assume = true;
	worker.run();
}

void import_sva_cover(VerificImporter *importer, Instance *inst)
{
	VerificSvaImporter worker;
	worker.importer = importer;
	worker.root = inst;
	worker.mode_cover = true;
	worker.run();
}

struct VerificExtNets
{
	int portname_cnt = 0;
	bool verbose = false;

	// a map from Net to the same Net one level up in the design hierarchy
	std::map<Net*, Net*> net_level_up;

	Net *get_net_level_up(Net *net)
	{
		if (net_level_up.count(net) == 0)
		{
			Netlist *nl = net->Owner();

			// Simply return if Netlist is not unique
			if (nl->NumOfRefs() != 1)
				return net;

			Instance *up_inst = (Instance*)nl->GetReferences()->GetLast();
			Netlist *up_nl = up_inst->Owner();

			// create new Port
			string name = stringf("___extnets_%d", portname_cnt++);
			Port *new_port = new Port(name.c_str(), DIR_OUT);
			nl->Add(new_port);
			net->Connect(new_port);

			// create new Net in up Netlist
			Net *new_net = new Net(name.c_str());
			up_nl->Add(new_net);
			up_inst->Connect(new_port, new_net);

			net_level_up[net] = new_net;
		}

		return net_level_up.at(net);
	}

	void run(Netlist *nl)
	{
		MapIter mi, mi2;
		Instance *inst;
		PortRef *pr;

		vector<tuple<Instance*, Port*, Net*>> todo_connect;

		FOREACH_INSTANCE_OF_NETLIST(nl, mi, inst)
			run(inst->View());

		FOREACH_INSTANCE_OF_NETLIST(nl, mi, inst)
		FOREACH_PORTREF_OF_INST(inst, mi2, pr)
		{
			Port *port = pr->GetPort();
			Net *net = pr->GetNet();

			if (!net->IsExternalTo(nl))
				continue;

			if (verbose)
				log("Fixing external net reference on port %s.%s.%s:\n", get_full_netlist_name(nl).c_str(), inst->Name(), port->Name());

			while (net->IsExternalTo(nl))
			{
				Net *newnet = get_net_level_up(net);
				if (newnet == net) break;

				if (verbose)
					log("  external net: %s.%s\n", get_full_netlist_name(net->Owner()).c_str(), net->Name());
				net = newnet;
			}

			if (verbose)
				log("  final net: %s.%s%s\n", get_full_netlist_name(net->Owner()).c_str(), net->Name(), net->IsExternalTo(nl) ? " (external)" : "");
			todo_connect.push_back(tuple<Instance*, Port*, Net*>(inst, port, net));
		}

		for (auto it : todo_connect) {
			get<0>(it)->Disconnect(get<1>(it));
			get<0>(it)->Connect(get<1>(it), get<2>(it));
		}
	}
};

#endif /* YOSYS_ENABLE_VERIFIC */

struct VerificPass : public Pass {
	VerificPass() : Pass("verific", "load Verilog and VHDL designs using Verific") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    verific {-vlog95|-vlog2k|-sv2005|-sv2009|-sv} <verilog-file>..\n");
		log("\n");
		log("Load the specified Verilog/SystemVerilog files into Verific.\n");
		log("\n");
		log("\n");
		log("    verific {-vhdl87|-vhdl93|-vhdl2k|-vhdl2008|-vhdpsl} <vhdl-file>..\n");
		log("\n");
		log("Load the specified VHDL files into Verific.\n");
		log("\n");
		log("\n");
		log("    verific -import [options] <top-module>..\n");
		log("\n");
		log("Elaborate the design for the specified top modules, import to Yosys and\n");
		log("reset the internal state of Verific.\n");
		log("\n");
		log("Import options:\n");
		log("\n");
		log("  -all\n");
		log("    Elaborate all modules, not just the hierarchy below the given top\n");
		log("    modules. With this option the list of modules to import is optional.\n");
		log("\n");
		log("  -gates\n");
		log("    Create a gate-level netlist.\n");
		log("\n");
		log("  -flatten\n");
		log("    Flatten the design in Verific before importing.\n");
		log("\n");
		log("  -extnets\n");
		log("    Resolve references to external nets by adding module ports as needed.\n");
		log("\n");
		log("  -v\n");
		log("    Verbose log messages.\n");
		log("\n");
		log("  -k\n");
		log("    Keep going after an unsupported verific primitive is found. The\n");
		log("    unsupported primitive is added as blockbox module to the design.\n");
		log("\n");
		log("  -d <dump_file>\n");
		log("    Dump the Verific netlist as a verilog file.\n");
		log("\n");
		log("Visit http://verific.com/ for more information on Verific.\n");
		log("\n");
	}
#ifdef YOSYS_ENABLE_VERIFIC
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Executing VERIFIC (loading SystemVerilog and VHDL designs using Verific).\n");

		Message::SetConsoleOutput(0);
		Message::RegisterCallBackMsg(msg_func);
		RuntimeFlags::SetVar("db_allow_external_nets", 1);

		const char *release_str = Message::ReleaseString();
		time_t release_time = Message::ReleaseDate();
		char *release_tmstr = ctime(&release_time);

		if (release_str == nullptr)
			release_str = "(no release string)";

		for (char *p = release_tmstr; *p; p++)
			if (*p == '\n') *p = 0;

		log("Built with Verific %s, released at %s.\n", release_str, release_tmstr);

		int argidx = 1;

		if (GetSize(args) > argidx && args[argidx] == "-vlog95") {
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!veri_file::Analyze(args[argidx].c_str(), veri_file::VERILOG_95))
					log_cmd_error("Reading `%s' in VERILOG_95 mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vlog2k") {
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!veri_file::Analyze(args[argidx].c_str(), veri_file::VERILOG_2K))
					log_cmd_error("Reading `%s' in VERILOG_2K mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-sv2005") {
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!veri_file::Analyze(args[argidx].c_str(), veri_file::SYSTEM_VERILOG_2005))
					log_cmd_error("Reading `%s' in SYSTEM_VERILOG_2005 mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-sv2009") {
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!veri_file::Analyze(args[argidx].c_str(), veri_file::SYSTEM_VERILOG_2009))
					log_cmd_error("Reading `%s' in SYSTEM_VERILOG_2009 mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-sv") {
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!veri_file::Analyze(args[argidx].c_str(), veri_file::SYSTEM_VERILOG))
					log_cmd_error("Reading `%s' in SYSTEM_VERILOG mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdl87") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_1987").c_str());
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!vhdl_file::Analyze(args[argidx].c_str(), "work", vhdl_file::VHDL_87))
					log_cmd_error("Reading `%s' in VHDL_87 mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdl93") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_1993").c_str());
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!vhdl_file::Analyze(args[argidx].c_str(), "work", vhdl_file::VHDL_93))
					log_cmd_error("Reading `%s' in VHDL_93 mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdl2k") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_1993").c_str());
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!vhdl_file::Analyze(args[argidx].c_str(), "work", vhdl_file::VHDL_2K))
					log_cmd_error("Reading `%s' in VHDL_2K mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdl2008") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_2008").c_str());
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!vhdl_file::Analyze(args[argidx].c_str(), "work", vhdl_file::VHDL_2008))
					log_cmd_error("Reading `%s' in VHDL_2008 mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdpsl") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_2008").c_str());
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!vhdl_file::Analyze(args[argidx].c_str(), "work", vhdl_file::VHDL_PSL))
					log_cmd_error("Reading `%s' in VHDL_PSL mode failed.\n", args[argidx].c_str());
			return;
		}

		if (GetSize(args) > argidx && args[argidx] == "-import")
		{
			std::set<Netlist*> nl_todo, nl_done;
			bool mode_all = false, mode_gates = false, mode_keep = false;
			bool verbose = false, flatten = false, extnets = false;
			string dumpfile;

			for (argidx++; argidx < GetSize(args); argidx++) {
				if (args[argidx] == "-all") {
					mode_all = true;
					continue;
				}
				if (args[argidx] == "-gates") {
					mode_gates = true;
					continue;
				}
				if (args[argidx] == "-flatten") {
					flatten = true;
					continue;
				}
				if (args[argidx] == "-extnets") {
					extnets = true;
					continue;
				}
				if (args[argidx] == "-k") {
					mode_keep = true;
					continue;
				}
				if (args[argidx] == "-v") {
					verbose = true;
					continue;
				}
				if (args[argidx] == "-d" && argidx+1 < GetSize(args)) {
					dumpfile = args[++argidx];
					continue;
				}
				break;
			}

			if (argidx > GetSize(args) && args[argidx].substr(0, 1) == "-")
				cmd_error(args, argidx, "unknown option");

			if (mode_all)
			{
				log("Running veri_file::ElaborateAll().\n");
				if (!veri_file::ElaborateAll())
					log_cmd_error("Elaboration of Verilog modules failed.\n");

				log("Running vhdl_file::ElaborateAll().\n");
				if (!vhdl_file::ElaborateAll())
					log_cmd_error("Elaboration of VHDL modules failed.\n");

				Library *lib = Netlist::PresentDesign()->Owner()->Owner();

				if (argidx == GetSize(args))
				{
					MapIter iter;
					char *iter_name;
					Verific::Cell *iter_cell;

					FOREACH_MAP_ITEM(lib->GetCells(), iter, &iter_name, &iter_cell) {
						if (*iter_name != '$')
							nl_todo.insert(iter_cell->GetFirstNetlist());
					}
				}
				else
				{
					for (; argidx < GetSize(args); argidx++)
					{
						Verific::Cell *cell = lib->GetCell(args[argidx].c_str());

						if (cell == nullptr)
							log_cmd_error("Module not found: %s\n", args[argidx].c_str());

						nl_todo.insert(cell->GetFirstNetlist());
						cell->GetFirstNetlist()->SetPresentDesign();
					}
				}
			}
			else
			{
				if (argidx == GetSize(args))
					log_cmd_error("No top module specified.\n");

				for (; argidx < GetSize(args); argidx++) {
					if (veri_file::GetModule(args[argidx].c_str())) {
						log("Running veri_file::Elaborate(\"%s\").\n", args[argidx].c_str());
						if (!veri_file::Elaborate(args[argidx].c_str()))
							log_cmd_error("Elaboration of top module `%s' failed.\n", args[argidx].c_str());
						nl_todo.insert(Netlist::PresentDesign());
					} else {
						log("Running vhdl_file::Elaborate(\"%s\").\n", args[argidx].c_str());
						if (!vhdl_file::Elaborate(args[argidx].c_str()))
							log_cmd_error("Elaboration of top module `%s' failed.\n", args[argidx].c_str());
						nl_todo.insert(Netlist::PresentDesign());
					}
				}
			}

			if (flatten) {
				for (auto nl : nl_todo)
					nl->Flatten();
			}

			if (extnets) {
				VerificExtNets worker;
				worker.verbose = verbose;
				for (auto nl : nl_todo)
					worker.run(nl);
			}

			if (!dumpfile.empty()) {
				VeriWrite veri_writer;
				veri_writer.WriteFile(dumpfile.c_str(), Netlist::PresentDesign());
			}

			while (!nl_todo.empty()) {
				Netlist *nl = *nl_todo.begin();
				if (nl_done.count(nl) == 0) {
					VerificImporter importer(mode_gates, mode_keep, verbose);
					importer.import_netlist(design, nl, nl_todo);
				}
				nl_todo.erase(nl);
				nl_done.insert(nl);
			}

			Libset::Reset();
			return;
		}

		log_cmd_error("Missing or unsupported mode parameter.\n");
	}
#else /* YOSYS_ENABLE_VERIFIC */
	virtual void execute(std::vector<std::string>, RTLIL::Design *) {
		log_cmd_error("This version of Yosys is built without Verific support.\n");
	}
#endif
} VerificPass;

PRIVATE_NAMESPACE_END

