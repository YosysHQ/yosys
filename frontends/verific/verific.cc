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
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#ifndef _WIN32
#  include <unistd.h>
#  include <dirent.h>
#endif

#include "frontends/verific/verific.h"

USING_YOSYS_NAMESPACE

#ifdef YOSYS_ENABLE_VERIFIC

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Woverloaded-virtual"
#endif

#include "veri_file.h"
#include "vhdl_file.h"
#include "hier_tree.h"
#include "VeriModule.h"
#include "VeriWrite.h"
#include "VhdlUnits.h"
#include "VeriLibrary.h"

#ifndef SYMBIOTIC_VERIFIC_API_VERSION
#  error "Only Symbiotic EDA flavored Verific is supported. Please contact office@symbioticeda.com for commercial support for Yosys+Verific."
#endif

#if SYMBIOTIC_VERIFIC_API_VERSION < 1
#  error "Please update your version of Symbiotic EDA flavored Verific."
#endif

#ifdef __clang__
#pragma clang diagnostic pop
#endif

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

#endif

#ifdef YOSYS_ENABLE_VERIFIC
YOSYS_NAMESPACE_BEGIN

int verific_verbose;
bool verific_import_pending;
string verific_error_msg;
int verific_sva_fsm_limit;

vector<string> verific_incdirs, verific_libdirs;

void msg_func(msg_type_t msg_type, const char *message_id, linefile_type linefile, const char *msg, va_list args)
{
	string message_prefix = stringf("VERIFIC-%s [%s] ",
			msg_type == VERIFIC_NONE ? "NONE" :
			msg_type == VERIFIC_ERROR ? "ERROR" :
			msg_type == VERIFIC_WARNING ? "WARNING" :
			msg_type == VERIFIC_IGNORE ? "IGNORE" :
			msg_type == VERIFIC_INFO ? "INFO" :
			msg_type == VERIFIC_COMMENT ? "COMMENT" :
			msg_type == VERIFIC_PROGRAM_ERROR ? "PROGRAM_ERROR" : "UNKNOWN", message_id);

	string message = linefile ? stringf("%s:%d: ", LineFile::GetFileName(linefile), LineFile::GetLineNo(linefile)) : "";
	message += vstringf(msg, args);

	if (msg_type == VERIFIC_ERROR || msg_type == VERIFIC_WARNING || msg_type == VERIFIC_PROGRAM_ERROR)
		log_warning_noprefix("%s%s\n", message_prefix.c_str(), message.c_str());
	else
		log("%s%s\n", message_prefix.c_str(), message.c_str());

	if (verific_error_msg.empty() && (msg_type == VERIFIC_ERROR || msg_type == VERIFIC_PROGRAM_ERROR))
		verific_error_msg = message;
}

string get_full_netlist_name(Netlist *nl)
{
	if (nl->NumOfRefs() == 1) {
		Instance *inst = (Instance*)nl->GetReferences()->GetLast();
		return get_full_netlist_name(inst->Owner()) + "." + inst->Name();
	}

	return nl->CellBaseName();
}

// ==================================================================

VerificImporter::VerificImporter(bool mode_gates, bool mode_keep, bool mode_nosva, bool mode_names, bool mode_verific, bool mode_autocover, bool mode_fullinit) :
		mode_gates(mode_gates), mode_keep(mode_keep), mode_nosva(mode_nosva),
		mode_names(mode_names), mode_verific(mode_verific), mode_autocover(mode_autocover),
		mode_fullinit(mode_fullinit)
{
}

RTLIL::SigBit VerificImporter::net_map_at(Net *net)
{
	if (net->IsExternalTo(netlist))
		log_error("Found external reference to '%s.%s' in netlist '%s', please use -flatten or -extnets.\n",
				get_full_netlist_name(net->Owner()).c_str(), net->Name(), get_full_netlist_name(netlist).c_str());

	return net_map.at(net);
}

bool is_blackbox(Netlist *nl)
{
	if (nl->IsBlackBox() || nl->IsEmptyBox())
		return true;

	const char *attr = nl->GetAttValue("blackbox");
	if (attr != nullptr && strcmp(attr, "0"))
		return true;

	return false;
}

RTLIL::IdString VerificImporter::new_verific_id(Verific::DesignObj *obj)
{
	std::string s = stringf("$verific$%s", obj->Name());
	if (obj->Linefile())
		s += stringf("$%s:%d", Verific::LineFile::GetFileName(obj->Linefile()), Verific::LineFile::GetLineNo(obj->Linefile()));
	s += stringf("$%d", autoidx++);
	return s;
}

void VerificImporter::import_attributes(dict<RTLIL::IdString, RTLIL::Const> &attributes, DesignObj *obj)
{
	MapIter mi;
	Att *attr;

	if (obj->Linefile())
		attributes["\\src"] = stringf("%s:%d", LineFile::GetFileName(obj->Linefile()), LineFile::GetLineNo(obj->Linefile()));

	// FIXME: Parse numeric attributes
	FOREACH_ATTRIBUTE(obj, mi, attr) {
		if (attr->Key()[0] == ' ' || attr->Value() == nullptr)
			continue;
		attributes[RTLIL::escape_id(attr->Key())] = RTLIL::Const(std::string(attr->Value()));
	}
}

RTLIL::SigSpec VerificImporter::operatorInput(Instance *inst)
{
	RTLIL::SigSpec sig;
	for (int i = int(inst->InputSize())-1; i >= 0; i--)
		if (inst->GetInputBit(i))
			sig.append(net_map_at(inst->GetInputBit(i)));
		else
			sig.append(RTLIL::State::Sz);
	return sig;
}

RTLIL::SigSpec VerificImporter::operatorInput1(Instance *inst)
{
	RTLIL::SigSpec sig;
	for (int i = int(inst->Input1Size())-1; i >= 0; i--)
		if (inst->GetInput1Bit(i))
			sig.append(net_map_at(inst->GetInput1Bit(i)));
		else
			sig.append(RTLIL::State::Sz);
	return sig;
}

RTLIL::SigSpec VerificImporter::operatorInput2(Instance *inst)
{
	RTLIL::SigSpec sig;
	for (int i = int(inst->Input2Size())-1; i >= 0; i--)
		if (inst->GetInput2Bit(i))
			sig.append(net_map_at(inst->GetInput2Bit(i)));
		else
			sig.append(RTLIL::State::Sz);
	return sig;
}

RTLIL::SigSpec VerificImporter::operatorInport(Instance *inst, const char *portname)
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

RTLIL::SigSpec VerificImporter::operatorOutput(Instance *inst, const pool<Net*, hash_ptr_ops> *any_all_nets)
{
	RTLIL::SigSpec sig;
	RTLIL::Wire *dummy_wire = NULL;
	for (int i = int(inst->OutputSize())-1; i >= 0; i--)
		if (inst->GetOutputBit(i) && (!any_all_nets || !any_all_nets->count(inst->GetOutputBit(i)))) {
			sig.append(net_map_at(inst->GetOutputBit(i)));
			dummy_wire = NULL;
		} else {
			if (dummy_wire == NULL)
				dummy_wire = module->addWire(new_verific_id(inst));
			else
				dummy_wire->width++;
			sig.append(RTLIL::SigSpec(dummy_wire, dummy_wire->width - 1));
		}
	return sig;
}

bool VerificImporter::import_netlist_instance_gates(Instance *inst, RTLIL::IdString inst_name)
{
	if (inst->Type() == PRIM_AND) {
		module->addAndGate(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
		return true;
	}

	if (inst->Type() == PRIM_NAND) {
		RTLIL::SigSpec tmp = module->addWire(new_verific_id(inst));
		module->addAndGate(new_verific_id(inst), net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), tmp);
		module->addNotGate(inst_name, tmp, net_map_at(inst->GetOutput()));
		return true;
	}

	if (inst->Type() == PRIM_OR) {
		module->addOrGate(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
		return true;
	}

	if (inst->Type() == PRIM_NOR) {
		RTLIL::SigSpec tmp = module->addWire(new_verific_id(inst));
		module->addOrGate(new_verific_id(inst), net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), tmp);
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
		auto outnet = inst->GetOutput();
		if (!any_all_nets.count(outnet))
			module->addBufGate(inst_name, net_map_at(inst->GetInput()), net_map_at(outnet));
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
		RTLIL::SigSpec x = inst->GetCout() ? net_map_at(inst->GetCout()) : module->addWire(new_verific_id(inst));
		RTLIL::SigSpec y = inst->GetOutput() ? net_map_at(inst->GetOutput()) : module->addWire(new_verific_id(inst));
		RTLIL::SigSpec tmp1 = module->addWire(new_verific_id(inst));
		RTLIL::SigSpec tmp2 = module->addWire(new_verific_id(inst));
		RTLIL::SigSpec tmp3 = module->addWire(new_verific_id(inst));
		module->addXorGate(new_verific_id(inst), a, b, tmp1);
		module->addXorGate(inst_name, tmp1, c, y);
		module->addAndGate(new_verific_id(inst), tmp1, c, tmp2);
		module->addAndGate(new_verific_id(inst), a, b, tmp3);
		module->addOrGate(new_verific_id(inst), tmp2, tmp3, x);
		return true;
	}

	if (inst->Type() == PRIM_DFFRS)
	{
		VerificClocking clocking(this, inst->GetClock());
		log_assert(clocking.disable_sig == State::S0);
		log_assert(clocking.body_net == nullptr);

		if (inst->GetSet()->IsGnd() && inst->GetReset()->IsGnd())
			clocking.addDff(inst_name, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		else if (inst->GetSet()->IsGnd())
			clocking.addAdff(inst_name, net_map_at(inst->GetReset()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()), State::S0);
		else if (inst->GetReset()->IsGnd())
			clocking.addAdff(inst_name, net_map_at(inst->GetSet()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()), State::S1);
		else
			clocking.addDffsr(inst_name, net_map_at(inst->GetSet()), net_map_at(inst->GetReset()),
					net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		return true;
	}

	return false;
}

bool VerificImporter::import_netlist_instance_cells(Instance *inst, RTLIL::IdString inst_name)
{
	RTLIL::Cell *cell = nullptr;

	if (inst->Type() == PRIM_AND) {
		cell = module->addAnd(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_NAND) {
		RTLIL::SigSpec tmp = module->addWire(new_verific_id(inst));
		cell = module->addAnd(new_verific_id(inst), net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), tmp);
		import_attributes(cell->attributes, inst);
		cell = module->addNot(inst_name, tmp, net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_OR) {
		cell = module->addOr(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_NOR) {
		RTLIL::SigSpec tmp = module->addWire(new_verific_id(inst));
		cell = module->addOr(new_verific_id(inst), net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), tmp);
		import_attributes(cell->attributes, inst);
		cell = module->addNot(inst_name, tmp, net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_XOR) {
		cell = module->addXor(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_XNOR) {
		cell = module->addXnor(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_INV) {
		cell = module->addNot(inst_name, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_MUX) {
		cell = module->addMux(inst_name, net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), net_map_at(inst->GetControl()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_TRI) {
		cell = module->addMux(inst_name, RTLIL::State::Sz, net_map_at(inst->GetInput()), net_map_at(inst->GetControl()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_FADD)
	{
		RTLIL::SigSpec a_plus_b = module->addWire(new_verific_id(inst), 2);
		RTLIL::SigSpec y = inst->GetOutput() ? net_map_at(inst->GetOutput()) : module->addWire(new_verific_id(inst));
		if (inst->GetCout())
			y.append(net_map_at(inst->GetCout()));
		cell = module->addAdd(new_verific_id(inst), net_map_at(inst->GetInput1()), net_map_at(inst->GetInput2()), a_plus_b);
		import_attributes(cell->attributes, inst);
		cell = module->addAdd(inst_name, a_plus_b, net_map_at(inst->GetCin()), y);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_DFFRS)
	{
		VerificClocking clocking(this, inst->GetClock());
		log_assert(clocking.disable_sig == State::S0);
		log_assert(clocking.body_net == nullptr);

		if (inst->GetSet()->IsGnd() && inst->GetReset()->IsGnd())
			cell = clocking.addDff(inst_name, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		else if (inst->GetSet()->IsGnd())
			cell = clocking.addAdff(inst_name, net_map_at(inst->GetReset()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()), RTLIL::State::S0);
		else if (inst->GetReset()->IsGnd())
			cell = clocking.addAdff(inst_name, net_map_at(inst->GetSet()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()), RTLIL::State::S1);
		else
			cell = clocking.addDffsr(inst_name, net_map_at(inst->GetSet()), net_map_at(inst->GetReset()),
					net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_DLATCHRS)
	{
		if (inst->GetSet()->IsGnd() && inst->GetReset()->IsGnd())
			cell = module->addDlatch(inst_name, net_map_at(inst->GetControl()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		else
			cell = module->addDlatchsr(inst_name, net_map_at(inst->GetControl()), net_map_at(inst->GetSet()), net_map_at(inst->GetReset()),
					net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	#define IN  operatorInput(inst)
	#define IN1 operatorInput1(inst)
	#define IN2 operatorInput2(inst)
	#define OUT operatorOutput(inst)
	#define FILTERED_OUT operatorOutput(inst, &any_all_nets)
	#define SIGNED inst->View()->IsSigned()

	if (inst->Type() == OPER_ADDER) {
		RTLIL::SigSpec out = OUT;
		if (inst->GetCout() != NULL)
			out.append(net_map_at(inst->GetCout()));
		if (inst->GetCin()->IsGnd()) {
			cell = module->addAdd(inst_name, IN1, IN2, out, SIGNED);
			import_attributes(cell->attributes, inst);
		} else {
			RTLIL::SigSpec tmp = module->addWire(new_verific_id(inst), GetSize(out));
			cell = module->addAdd(new_verific_id(inst), IN1, IN2, tmp, SIGNED);
			import_attributes(cell->attributes, inst);
			cell = module->addAdd(inst_name, tmp, net_map_at(inst->GetCin()), out, false);
			import_attributes(cell->attributes, inst);
		}
		return true;
	}

	if (inst->Type() == OPER_MULTIPLIER) {
		cell = module->addMul(inst_name, IN1, IN2, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_DIVIDER) {
		cell = module->addDiv(inst_name, IN1, IN2, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_MODULO) {
		cell = module->addMod(inst_name, IN1, IN2, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_REMAINDER) {
		cell = module->addMod(inst_name, IN1, IN2, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_SHIFT_LEFT) {
		cell = module->addShl(inst_name, IN1, IN2, OUT, false);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_ENABLED_DECODER) {
		RTLIL::SigSpec vec;
		vec.append(net_map_at(inst->GetControl()));
		for (unsigned i = 1; i < inst->OutputSize(); i++) {
			vec.append(RTLIL::State::S0);
		}
		cell = module->addShl(inst_name, vec, IN, OUT, false);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_DECODER) {
		RTLIL::SigSpec vec;
		vec.append(RTLIL::State::S1);
		for (unsigned i = 1; i < inst->OutputSize(); i++) {
			vec.append(RTLIL::State::S0);
		}
		cell = module->addShl(inst_name, vec, IN, OUT, false);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_SHIFT_RIGHT) {
		Net *net_cin = inst->GetCin();
		Net *net_a_msb = inst->GetInput1Bit(0);
		if (net_cin->IsGnd())
			cell = module->addShr(inst_name, IN1, IN2, OUT, false);
		else if (net_cin == net_a_msb)
			cell = module->addSshr(inst_name, IN1, IN2, OUT, true);
		else
			log_error("Can't import Verific OPER_SHIFT_RIGHT instance %s: carry_in is neither 0 nor msb of left input\n", inst->Name());
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_REDUCE_AND) {
		cell = module->addReduceAnd(inst_name, IN, net_map_at(inst->GetOutput()), SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_REDUCE_NAND) {
		Wire *tmp = module->addWire(NEW_ID);
		cell = module->addReduceAnd(inst_name, IN, tmp, SIGNED);
		module->addNot(NEW_ID, tmp, net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_REDUCE_OR) {
		cell = module->addReduceOr(inst_name, IN, net_map_at(inst->GetOutput()), SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_REDUCE_XOR) {
		cell = module->addReduceXor(inst_name, IN, net_map_at(inst->GetOutput()), SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_REDUCE_XNOR) {
		cell = module->addReduceXnor(inst_name, IN, net_map_at(inst->GetOutput()), SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_REDUCE_NOR) {
		SigSpec t = module->ReduceOr(new_verific_id(inst), IN, SIGNED);
		cell = module->addNot(inst_name, t, net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_LESSTHAN) {
		Net *net_cin = inst->GetCin();
		if (net_cin->IsGnd())
			cell = module->addLt(inst_name, IN1, IN2, net_map_at(inst->GetOutput()), SIGNED);
		else if (net_cin->IsPwr())
			cell = module->addLe(inst_name, IN1, IN2, net_map_at(inst->GetOutput()), SIGNED);
		else
			log_error("Can't import Verific OPER_LESSTHAN instance %s: carry_in is neither 0 nor 1\n", inst->Name());
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_AND) {
		cell = module->addAnd(inst_name, IN1, IN2, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_OR) {
		cell = module->addOr(inst_name, IN1, IN2, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_XOR) {
		cell = module->addXor(inst_name, IN1, IN2, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_XNOR) {
		cell = module->addXnor(inst_name, IN1, IN2, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_BUF) {
		cell = module->addPos(inst_name, IN, FILTERED_OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_INV) {
		cell = module->addNot(inst_name, IN, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_MINUS) {
		cell = module->addSub(inst_name, IN1, IN2, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_UMINUS) {
		cell = module->addNeg(inst_name, IN, OUT, SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_EQUAL) {
		cell = module->addEq(inst_name, IN1, IN2, net_map_at(inst->GetOutput()), SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_NEQUAL) {
		cell = module->addNe(inst_name, IN1, IN2, net_map_at(inst->GetOutput()), SIGNED);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_MUX) {
		cell = module->addMux(inst_name, IN1, IN2, net_map_at(inst->GetControl()), OUT);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_NTO1MUX) {
		cell = module->addShr(inst_name, IN2, IN1, net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_NTO1MUX)
	{
		SigSpec data = IN2, out = OUT;

		int wordsize_bits = ceil_log2(GetSize(out));
		int wordsize = 1 << wordsize_bits;

		SigSpec sel = {IN1, SigSpec(State::S0, wordsize_bits)};

		SigSpec padded_data;
		for (int i = 0; i < GetSize(data); i += GetSize(out)) {
			SigSpec d = data.extract(i, GetSize(out));
			d.extend_u0(wordsize);
			padded_data.append(d);
		}

		cell = module->addShr(inst_name, padded_data, sel, out);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_SELECTOR)
	{
		cell = module->addPmux(inst_name, State::S0, IN2, IN1, net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_SELECTOR)
	{
		SigSpec out = OUT;
		cell = module->addPmux(inst_name, SigSpec(State::S0, GetSize(out)), IN2, IN1, out);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_TRI) {
		cell = module->addMux(inst_name, RTLIL::SigSpec(RTLIL::State::Sz, inst->OutputSize()), IN, net_map_at(inst->GetControl()), OUT);
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_DFFRS)
	{
		VerificClocking clocking(this, inst->GetClock());
		log_assert(clocking.disable_sig == State::S0);
		log_assert(clocking.body_net == nullptr);

		RTLIL::SigSpec sig_set = operatorInport(inst, "set");
		RTLIL::SigSpec sig_reset = operatorInport(inst, "reset");

		if (sig_set.is_fully_const() && !sig_set.as_bool() && sig_reset.is_fully_const() && !sig_reset.as_bool())
			cell = clocking.addDff(inst_name, IN, OUT);
		else
			cell = clocking.addDffsr(inst_name, sig_set, sig_reset, IN, OUT);
		import_attributes(cell->attributes, inst);

		return true;
	}

	#undef IN
	#undef IN1
	#undef IN2
	#undef OUT
	#undef SIGNED

	return false;
}

void VerificImporter::merge_past_ffs_clock(pool<RTLIL::Cell*> &candidates, SigBit clock, bool clock_pol)
{
	bool keep_running = true;
	SigMap sigmap;

	while (keep_running)
	{
		keep_running = false;

		dict<SigBit, pool<RTLIL::Cell*>> dbits_db;
		SigSpec dbits;

		for (auto cell : candidates) {
			SigBit bit = sigmap(cell->getPort("\\D"));
			dbits_db[bit].insert(cell);
			dbits.append(bit);
		}

		dbits.sort_and_unify();

		for (auto chunk : dbits.chunks())
		{
			SigSpec sig_d = chunk;

			if (chunk.wire == nullptr || GetSize(sig_d) == 1)
				continue;

			SigSpec sig_q = module->addWire(NEW_ID, GetSize(sig_d));
			RTLIL::Cell *new_ff = module->addDff(NEW_ID, clock, sig_d, sig_q, clock_pol);

			if (verific_verbose)
				log("  merging single-bit past_ffs into new %d-bit ff %s.\n", GetSize(sig_d), log_id(new_ff));

			for (int i = 0; i < GetSize(sig_d); i++)
				for (auto old_ff : dbits_db[sig_d[i]])
				{
					if (verific_verbose)
						log("    replacing old ff %s on bit %d.\n", log_id(old_ff), i);

					SigBit old_q = old_ff->getPort("\\Q");
					SigBit new_q = sig_q[i];

					sigmap.add(old_q, new_q);
					module->connect(old_q, new_q);
					candidates.erase(old_ff);
					module->remove(old_ff);
					keep_running = true;
				}
		}
	}
}

void VerificImporter::merge_past_ffs(pool<RTLIL::Cell*> &candidates)
{
	dict<pair<SigBit, int>, pool<RTLIL::Cell*>> database;

	for (auto cell : candidates)
	{
		SigBit clock = cell->getPort("\\CLK");
		bool clock_pol = cell->getParam("\\CLK_POLARITY").as_bool();
		database[make_pair(clock, int(clock_pol))].insert(cell);
	}

	for (auto it : database)
		merge_past_ffs_clock(it.second, it.first.first, it.first.second);
}

void VerificImporter::import_netlist(RTLIL::Design *design, Netlist *nl, std::set<Netlist*> &nl_todo, bool norename)
{
	std::string netlist_name = nl->GetAtt(" \\top") ? nl->CellBaseName() : nl->Owner()->Name();
	std::string module_name = netlist_name;

	if (nl->IsOperator() || nl->IsPrimitive()) {
		module_name = "$verific$" + module_name;
	} else {
		if (!norename && *nl->Name()) {
			module_name += "(";
			module_name += nl->Name();
			module_name += ")";
		}
		module_name = "\\" + module_name;
	}

	netlist = nl;

	if (design->has(module_name)) {
		if (!nl->IsOperator() && !is_blackbox(nl))
			log_cmd_error("Re-definition of module `%s'.\n", netlist_name.c_str());
		return;
	}

	module = new RTLIL::Module;
	module->name = module_name;
	design->add(module);

	if (is_blackbox(nl)) {
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

		if (verific_verbose)
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
		if (verific_verbose)
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
	pool<Net*, hash_ptr_ops> anyconst_nets, anyseq_nets;
	pool<Net*, hash_ptr_ops> allconst_nets, allseq_nets;
	any_all_nets.clear();

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
						RTLIL::Cell *cell = module->addCell(new_verific_id(net), "$meminit");
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

		const char *anyconst_attr = net->GetAttValue("anyconst");
		const char *anyseq_attr = net->GetAttValue("anyseq");

		const char *allconst_attr = net->GetAttValue("allconst");
		const char *allseq_attr = net->GetAttValue("allseq");

		if (rand_const_attr != nullptr && (!strcmp(rand_const_attr, "1") || !strcmp(rand_const_attr, "'1'"))) {
			anyconst_nets.insert(net);
			any_all_nets.insert(net);
		}
		else if (rand_attr != nullptr && (!strcmp(rand_attr, "1") || !strcmp(rand_attr, "'1'"))) {
			anyseq_nets.insert(net);
			any_all_nets.insert(net);
		}
		else if (anyconst_attr != nullptr && (!strcmp(anyconst_attr, "1") || !strcmp(anyconst_attr, "'1'"))) {
			anyconst_nets.insert(net);
			any_all_nets.insert(net);
		}
		else if (anyseq_attr != nullptr && (!strcmp(anyseq_attr, "1") || !strcmp(anyseq_attr, "'1'"))) {
			anyseq_nets.insert(net);
			any_all_nets.insert(net);
		}
		else if (allconst_attr != nullptr && (!strcmp(allconst_attr, "1") || !strcmp(allconst_attr, "'1'"))) {
			allconst_nets.insert(net);
			any_all_nets.insert(net);
		}
		else if (allseq_attr != nullptr && (!strcmp(allseq_attr, "1") || !strcmp(allseq_attr, "'1'"))) {
			allseq_nets.insert(net);
			any_all_nets.insert(net);
		}

		if (net_map.count(net)) {
			if (verific_verbose)
				log("  skipping net %s.\n", net->Name());
			continue;
		}

		if (net->Bus())
			continue;

		RTLIL::IdString wire_name = module->uniquify(mode_names || net->IsUserDeclared() ? RTLIL::escape_id(net->Name()) : new_verific_id(net));

		if (verific_verbose)
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
			RTLIL::IdString wire_name = module->uniquify(mode_names || netbus->IsUserDeclared() ? RTLIL::escape_id(netbus->Name()) : new_verific_id(netbus));

			if (verific_verbose)
				log("  importing netbus %s as %s.\n", netbus->Name(), log_id(wire_name));

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
			if (verific_verbose)
				log("  skipping netbus %s.\n", netbus->Name());
		}

		SigSpec anyconst_sig;
		SigSpec anyseq_sig;
		SigSpec allconst_sig;
		SigSpec allseq_sig;

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
			if (net != nullptr && allconst_nets.count(net)) {
				allconst_sig.append(net_map_at(net));
				allconst_nets.erase(net);
			}
			if (net != nullptr && allseq_nets.count(net)) {
				allseq_sig.append(net_map_at(net));
				allseq_nets.erase(net);
			}
			if (i == netbus->LeftIndex())
				break;
		}

		if (GetSize(anyconst_sig))
			module->connect(anyconst_sig, module->Anyconst(new_verific_id(netbus), GetSize(anyconst_sig)));

		if (GetSize(anyseq_sig))
			module->connect(anyseq_sig, module->Anyseq(new_verific_id(netbus), GetSize(anyseq_sig)));

		if (GetSize(allconst_sig))
			module->connect(allconst_sig, module->Allconst(new_verific_id(netbus), GetSize(allconst_sig)));

		if (GetSize(allseq_sig))
			module->connect(allseq_sig, module->Allseq(new_verific_id(netbus), GetSize(allseq_sig)));
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
		module->connect(net_map_at(net), module->Anyconst(new_verific_id(net)));

	for (auto net : anyseq_nets)
		module->connect(net_map_at(net), module->Anyseq(new_verific_id(net)));

	pool<Instance*, hash_ptr_ops> sva_asserts;
	pool<Instance*, hash_ptr_ops> sva_assumes;
	pool<Instance*, hash_ptr_ops> sva_covers;
	pool<Instance*, hash_ptr_ops> sva_triggers;

	pool<RTLIL::Cell*> past_ffs;

	FOREACH_INSTANCE_OF_NETLIST(nl, mi, inst)
	{
		RTLIL::IdString inst_name = module->uniquify(mode_names || inst->IsUserDeclared() ? RTLIL::escape_id(inst->Name()) : new_verific_id(inst));

		if (verific_verbose)
			log("  importing cell %s (%s) as %s.\n", inst->Name(), inst->View()->Owner()->Name(), log_id(inst_name));

		if (mode_verific)
			goto import_verific_cells;

		if (inst->Type() == PRIM_PWR) {
			module->connect(net_map_at(inst->GetOutput()), RTLIL::State::S1);
			continue;
		}

		if (inst->Type() == PRIM_GND) {
			module->connect(net_map_at(inst->GetOutput()), RTLIL::State::S0);
			continue;
		}

		if (inst->Type() == PRIM_BUF) {
			auto outnet = inst->GetOutput();
			if (!any_all_nets.count(outnet))
				module->addBufGate(inst_name, net_map_at(inst->GetInput()), net_map_at(outnet));
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
			int numchunks = int(inst->OutputSize()) / memory->width;
			int chunksbits = ceil_log2(numchunks);

			if ((numchunks * memory->width) != int(inst->OutputSize()) || (numchunks & (numchunks - 1)) != 0)
				log_error("Import of asymmetric memories of this type is not supported yet: %s %s\n", inst->Name(), inst->GetInput()->Name());

			for (int i = 0; i < numchunks; i++)
			{
				RTLIL::SigSpec addr = {operatorInput1(inst), RTLIL::Const(i, chunksbits)};
				RTLIL::SigSpec data = operatorOutput(inst).extract(i * memory->width, memory->width);

				RTLIL::Cell *cell = module->addCell(numchunks == 1 ? inst_name :
						RTLIL::IdString(stringf("%s_%d", inst_name.c_str(), i)), "$memrd");
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
			}
			continue;
		}

		if (inst->Type() == OPER_WRITE_PORT || inst->Type() == OPER_CLOCKED_WRITE_PORT)
		{
			RTLIL::Memory *memory = module->memories.at(RTLIL::escape_id(inst->GetOutput()->Name()));
			int numchunks = int(inst->Input2Size()) / memory->width;
			int chunksbits = ceil_log2(numchunks);

			if ((numchunks * memory->width) != int(inst->Input2Size()) || (numchunks & (numchunks - 1)) != 0)
				log_error("Import of asymmetric memories of this type is not supported yet: %s %s\n", inst->Name(), inst->GetOutput()->Name());

			for (int i = 0; i < numchunks; i++)
			{
				RTLIL::SigSpec addr = {operatorInput1(inst), RTLIL::Const(i, chunksbits)};
				RTLIL::SigSpec data = operatorInput2(inst).extract(i * memory->width, memory->width);

				RTLIL::Cell *cell = module->addCell(numchunks == 1 ? inst_name :
						RTLIL::IdString(stringf("%s_%d", inst_name.c_str(), i)), "$memwr");
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
			}
			continue;
		}

		if (!mode_gates) {
			if (import_netlist_instance_cells(inst, inst_name))
				continue;
			if (inst->IsOperator() && !verific_sva_prims.count(inst->Type()))
				log_warning("Unsupported Verific operator: %s (fallback to gate level implementation provided by verific)\n", inst->View()->Owner()->Name());
		} else {
			if (import_netlist_instance_gates(inst, inst_name))
				continue;
		}

		if (inst->Type() == PRIM_SVA_ASSERT || inst->Type() == PRIM_SVA_IMMEDIATE_ASSERT)
			sva_asserts.insert(inst);

		if (inst->Type() == PRIM_SVA_ASSUME || inst->Type() == PRIM_SVA_IMMEDIATE_ASSUME || inst->Type() == PRIM_SVA_RESTRICT)
			sva_assumes.insert(inst);

		if (inst->Type() == PRIM_SVA_COVER || inst->Type() == PRIM_SVA_IMMEDIATE_COVER)
			sva_covers.insert(inst);

		if (inst->Type() == PRIM_SVA_TRIGGERED)
			sva_triggers.insert(inst);

		if (inst->Type() == OPER_SVA_STABLE)
		{
			VerificClocking clocking(this, inst->GetInput2Bit(0));
			log_assert(clocking.disable_sig == State::S0);
			log_assert(clocking.body_net == nullptr);

			log_assert(inst->Input1Size() == inst->OutputSize());

			SigSpec sig_d, sig_q, sig_o;
			sig_q = module->addWire(new_verific_id(inst), inst->Input1Size());

			for (int i = int(inst->Input1Size())-1; i >= 0; i--){
				sig_d.append(net_map_at(inst->GetInput1Bit(i)));
				sig_o.append(net_map_at(inst->GetOutputBit(i)));
			}

			if (verific_verbose) {
				log("    %sedge FF with D=%s, Q=%s, C=%s.\n", clocking.posedge ? "pos" : "neg",
						log_signal(sig_d), log_signal(sig_q), log_signal(clocking.clock_sig));
				log("    XNOR with A=%s, B=%s, Y=%s.\n",
						log_signal(sig_d), log_signal(sig_q), log_signal(sig_o));
			}

			clocking.addDff(new_verific_id(inst), sig_d, sig_q);
			module->addXnor(new_verific_id(inst), sig_d, sig_q, sig_o);

			if (!mode_keep)
				continue;
		}

		if (inst->Type() == PRIM_SVA_STABLE)
		{
			VerificClocking clocking(this, inst->GetInput2());
			log_assert(clocking.disable_sig == State::S0);
			log_assert(clocking.body_net == nullptr);

			SigSpec sig_d = net_map_at(inst->GetInput1());
			SigSpec sig_o = net_map_at(inst->GetOutput());
			SigSpec sig_q = module->addWire(new_verific_id(inst));

			if (verific_verbose) {
				log("    %sedge FF with D=%s, Q=%s, C=%s.\n", clocking.posedge ? "pos" : "neg",
						log_signal(sig_d), log_signal(sig_q), log_signal(clocking.clock_sig));
				log("    XNOR with A=%s, B=%s, Y=%s.\n",
						log_signal(sig_d), log_signal(sig_q), log_signal(sig_o));
			}

			clocking.addDff(new_verific_id(inst), sig_d, sig_q);
			module->addXnor(new_verific_id(inst), sig_d, sig_q, sig_o);

			if (!mode_keep)
				continue;
		}

		if (inst->Type() == PRIM_SVA_PAST)
		{
			VerificClocking clocking(this, inst->GetInput2());
			log_assert(clocking.disable_sig == State::S0);
			log_assert(clocking.body_net == nullptr);

			SigBit sig_d = net_map_at(inst->GetInput1());
			SigBit sig_q = net_map_at(inst->GetOutput());

			if (verific_verbose)
				log("    %sedge FF with D=%s, Q=%s, C=%s.\n", clocking.posedge ? "pos" : "neg",
						log_signal(sig_d), log_signal(sig_q), log_signal(clocking.clock_sig));

			past_ffs.insert(clocking.addDff(new_verific_id(inst), sig_d, sig_q));

			if (!mode_keep)
				continue;
		}

		if ((inst->Type() == PRIM_SVA_ROSE || inst->Type() == PRIM_SVA_FELL))
		{
			VerificClocking clocking(this, inst->GetInput2());
			log_assert(clocking.disable_sig == State::S0);
			log_assert(clocking.body_net == nullptr);

			SigBit sig_d = net_map_at(inst->GetInput1());
			SigBit sig_o = net_map_at(inst->GetOutput());
			SigBit sig_q = module->addWire(new_verific_id(inst));

			if (verific_verbose)
				log("    %sedge FF with D=%s, Q=%s, C=%s.\n", clocking.posedge ? "pos" : "neg",
						log_signal(sig_d), log_signal(sig_q), log_signal(clocking.clock_sig));

			clocking.addDff(new_verific_id(inst), sig_d, sig_q);
			module->addEq(new_verific_id(inst), {sig_q, sig_d}, Const(inst->Type() == PRIM_SVA_ROSE ? 1 : 2, 2), sig_o);

			if (!mode_keep)
				continue;
		}

		if (!mode_keep && verific_sva_prims.count(inst->Type())) {
			if (verific_verbose)
				log("    skipping SVA cell in non k-mode\n");
			continue;
		}

		if (inst->Type() == PRIM_HDL_ASSERTION)
		{
			SigBit cond = net_map_at(inst->GetInput());

			if (verific_verbose)
				log("    assert condition %s.\n", log_signal(cond));

			const char *assume_attr = nullptr; // inst->GetAttValue("assume");

			Cell *cell = nullptr;
			if (assume_attr != nullptr && !strcmp(assume_attr, "1"))
				cell = module->addAssume(new_verific_id(inst), cond, State::S1);
			else
				cell = module->addAssert(new_verific_id(inst), cond, State::S1);

			import_attributes(cell->attributes, inst);
			continue;
		}

		if (inst->IsPrimitive())
		{
			if (!mode_keep)
				log_error("Unsupported Verific primitive %s of type %s\n", inst->Name(), inst->View()->Owner()->Name());

			if (!verific_sva_prims.count(inst->Type()))
				log_warning("Unsupported Verific primitive %s of type %s\n", inst->Name(), inst->View()->Owner()->Name());
		}

	import_verific_cells:
		nl_todo.insert(inst->View());

		std::string inst_type = inst->View()->Owner()->Name();

		if (inst->View()->IsOperator() || inst->View()->IsPrimitive()) {
			inst_type = "$verific$" + inst_type;
		} else {
			if (*inst->View()->Name()) {
				inst_type += "(";
				inst_type += inst->View()->Name();
				inst_type += ")";
			}
			inst_type = "\\" + inst_type;
		}

		RTLIL::Cell *cell = module->addCell(inst_name, inst_type);

		if (inst->IsPrimitive() && mode_keep)
			cell->attributes["\\keep"] = 1;

		dict<IdString, vector<SigBit>> cell_port_conns;

		if (verific_verbose)
			log("    ports in verific db:\n");

		FOREACH_PORTREF_OF_INST(inst, mi2, pr) {
			if (verific_verbose)
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
				SigSpec zwires = module->addWire(new_verific_id(inst), port_offset+1-GetSize(sigvec));
				for (auto bit : zwires)
					sigvec.push_back(bit);
			}
			sigvec[port_offset] = net_map_at(pr->GetNet());
		}

		if (verific_verbose)
			log("    ports in yosys db:\n");

		for (auto &it : cell_port_conns) {
			if (verific_verbose)
				log("      .%s(%s)\n", log_id(it.first), log_signal(it.second));
			cell->setPort(it.first, it.second);
		}
	}

	if (!mode_nosva)
	{
		for (auto inst : sva_asserts) {
			if (mode_autocover)
				verific_import_sva_cover(this, inst);
			verific_import_sva_assert(this, inst);
		}

		for (auto inst : sva_assumes)
			verific_import_sva_assume(this, inst);

		for (auto inst : sva_covers)
			verific_import_sva_cover(this, inst);

		for (auto inst : sva_triggers)
			verific_import_sva_trigger(this, inst);

		merge_past_ffs(past_ffs);
	}

	if (!mode_fullinit)
	{
		pool<SigBit> non_ff_bits;
		CellTypes ff_types;

		ff_types.setup_internals_ff();
		ff_types.setup_stdcells_mem();

		for (auto cell : module->cells())
		{
			if (ff_types.cell_known(cell->type))
				continue;

			for (auto conn : cell->connections())
			{
				if (!cell->output(conn.first))
					continue;

				for (auto bit : conn.second)
					if (bit.wire != nullptr)
						non_ff_bits.insert(bit);
			}
		}

		for (auto wire : module->wires())
		{
			if (!wire->attributes.count("\\init"))
				continue;

			Const &initval = wire->attributes.at("\\init");
			for (int i = 0; i < GetSize(initval); i++)
			{
				if (initval[i] != State::S0 && initval[i] != State::S1)
					continue;

				if (non_ff_bits.count(SigBit(wire, i)))
					initval[i] = State::Sx;
			}

			if (initval.is_fully_undef())
				wire->attributes.erase("\\init");
		}
	}
}

// ==================================================================

VerificClocking::VerificClocking(VerificImporter *importer, Net *net, bool sva_at_only)
{
	module = importer->module;

	log_assert(importer != nullptr);
	log_assert(net != nullptr);

	Instance *inst = net->Driver();

	if (inst != nullptr && inst->Type() == PRIM_SVA_AT)
	{
		net = inst->GetInput1();
		body_net = inst->GetInput2();

		inst = net->Driver();

		Instance *body_inst = body_net->Driver();
		if (body_inst != nullptr && body_inst->Type() == PRIM_SVA_DISABLE_IFF) {
			disable_net = body_inst->GetInput1();
			disable_sig = importer->net_map_at(disable_net);
			body_net = body_inst->GetInput2();
		}
	}
	else
	{
		if (sva_at_only)
			return;
	}

	// Use while() instead of if() to work around VIPER #13453
	while (inst != nullptr && inst->Type() == PRIM_SVA_POSEDGE)
	{
		net = inst->GetInput();
		inst = net->Driver();;
	}

	if (inst != nullptr && inst->Type() == PRIM_INV)
	{
		net = inst->GetInput();
		inst = net->Driver();;
		posedge = false;
	}

	// Detect clock-enable circuit
	do {
		if (inst == nullptr || inst->Type() != PRIM_AND)
			break;

		Net *net_dlatch = inst->GetInput1();
		Instance *inst_dlatch = net_dlatch->Driver();

		if (inst_dlatch == nullptr || inst_dlatch->Type() != PRIM_DLATCHRS)
			break;

		if (!inst_dlatch->GetSet()->IsGnd() || !inst_dlatch->GetReset()->IsGnd())
			break;

		Net *net_enable = inst_dlatch->GetInput();
		Net *net_not_clock = inst_dlatch->GetControl();

		if (net_enable == nullptr || net_not_clock == nullptr)
			break;

		Instance *inst_not_clock = net_not_clock->Driver();

		if (inst_not_clock == nullptr || inst_not_clock->Type() != PRIM_INV)
			break;

		Net *net_clock1 = inst_not_clock->GetInput();
		Net *net_clock2 = inst->GetInput2();

		if (net_clock1 == nullptr || net_clock1 != net_clock2)
			break;

		enable_net = net_enable;
		enable_sig = importer->net_map_at(enable_net);

		net = net_clock1;
		inst = net->Driver();;
	} while (0);

	// Detect condition expression
	do {
		if (body_net == nullptr)
			break;

		Instance *inst_mux = body_net->Driver();

		if (inst_mux == nullptr || inst_mux->Type() != PRIM_MUX)
			break;

		if (!inst_mux->GetInput1()->IsPwr())
			break;

		Net *sva_net = inst_mux->GetInput2();
		if (!verific_is_sva_net(importer, sva_net))
			break;

		body_net = sva_net;
		cond_net = inst_mux->GetControl();
	} while (0);

	clock_net = net;
	clock_sig = importer->net_map_at(clock_net);

	const char *gclk_attr = clock_net->GetAttValue("gclk");
	if (gclk_attr != nullptr && (!strcmp(gclk_attr, "1") || !strcmp(gclk_attr, "'1'")))
		gclk = true;
}

Cell *VerificClocking::addDff(IdString name, SigSpec sig_d, SigSpec sig_q, Const init_value)
{
	log_assert(GetSize(sig_d) == GetSize(sig_q));

	if (GetSize(init_value) != 0) {
		log_assert(GetSize(sig_q) == GetSize(init_value));
		if (sig_q.is_wire()) {
			sig_q.as_wire()->attributes["\\init"] = init_value;
		} else {
			Wire *w = module->addWire(NEW_ID, GetSize(sig_q));
			w->attributes["\\init"] = init_value;
			module->connect(sig_q, w);
			sig_q = w;
		}
	}

	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	if (disable_sig != State::S0) {
		log_assert(gclk == false);
		log_assert(GetSize(sig_q) == GetSize(init_value));
		return module->addAdff(name, clock_sig, disable_sig, sig_d, sig_q, init_value, posedge);
	}

	if (gclk)
		return module->addFf(name, sig_d, sig_q);

	return module->addDff(name, clock_sig, sig_d, sig_q, posedge);
}

Cell *VerificClocking::addAdff(IdString name, RTLIL::SigSpec sig_arst, SigSpec sig_d, SigSpec sig_q, Const arst_value)
{
	log_assert(gclk == false);
	log_assert(disable_sig == State::S0);

	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	return module->addAdff(name, clock_sig, sig_arst, sig_d, sig_q, arst_value, posedge);
}

Cell *VerificClocking::addDffsr(IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, SigSpec sig_d, SigSpec sig_q)
{
	log_assert(gclk == false);
	log_assert(disable_sig == State::S0);

	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	return module->addDffsr(name, clock_sig, sig_set, sig_clr, sig_d, sig_q, posedge);
}

// ==================================================================

struct VerificExtNets
{
	int portname_cnt = 0;

	// a map from Net to the same Net one level up in the design hierarchy
	std::map<Net*, Net*> net_level_up_drive_up;
	std::map<Net*, Net*> net_level_up_drive_down;

	Net *route_up(Net *net, bool drive_up, Net *final_net = nullptr)
	{
		auto &net_level_up = drive_up ? net_level_up_drive_up : net_level_up_drive_down;

		if (net_level_up.count(net) == 0)
		{
			Netlist *nl = net->Owner();

			// Simply return if Netlist is not unique
			log_assert(nl->NumOfRefs() == 1);

			Instance *up_inst = (Instance*)nl->GetReferences()->GetLast();
			Netlist *up_nl = up_inst->Owner();

			// create new Port
			string name = stringf("___extnets_%d", portname_cnt++);
			Port *new_port = new Port(name.c_str(), drive_up ? DIR_OUT : DIR_IN);
			nl->Add(new_port);
			net->Connect(new_port);

			// create new Net in up Netlist
			Net *new_net = final_net;
			if (new_net == nullptr || new_net->Owner() != up_nl) {
				new_net = new Net(name.c_str());
				up_nl->Add(new_net);
			}
			up_inst->Connect(new_port, new_net);

			net_level_up[net] = new_net;
		}

		return net_level_up.at(net);
	}

	Net *route_up(Net *net, bool drive_up, Netlist *dest, Net *final_net = nullptr)
	{
		while (net->Owner() != dest)
			net = route_up(net, drive_up, final_net);
		if (final_net != nullptr)
			log_assert(net == final_net);
		return net;
	}

	Netlist *find_common_ancestor(Netlist *A, Netlist *B)
	{
		std::set<Netlist*> ancestors_of_A;

		Netlist *cursor = A;
		while (1) {
			ancestors_of_A.insert(cursor);
			if (cursor->NumOfRefs() != 1)
				break;
			cursor = ((Instance*)cursor->GetReferences()->GetLast())->Owner();
		}

		cursor = B;
		while (1) {
			if (ancestors_of_A.count(cursor))
				return cursor;
			if (cursor->NumOfRefs() != 1)
				break;
			cursor = ((Instance*)cursor->GetReferences()->GetLast())->Owner();
		}

		log_error("No common ancestor found between %s and %s.\n", get_full_netlist_name(A).c_str(), get_full_netlist_name(B).c_str());
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

			if (verific_verbose)
				log("Fixing external net reference on port %s.%s.%s:\n", get_full_netlist_name(nl).c_str(), inst->Name(), port->Name());

			Netlist *ext_nl = net->Owner();

			if (verific_verbose)
				log(" external net owner: %s\n", get_full_netlist_name(ext_nl).c_str());

			Netlist *ca_nl = find_common_ancestor(nl, ext_nl);

			if (verific_verbose)
				log(" common ancestor: %s\n", get_full_netlist_name(ca_nl).c_str());

			Net *ca_net = route_up(net, !port->IsOutput(), ca_nl);
			Net *new_net = ca_net;

			if (ca_nl != nl)
			{
				if (verific_verbose)
					log(" net in common ancestor: %s\n", ca_net->Name());

				string name = stringf("___extnets_%d", portname_cnt++);
				new_net = new Net(name.c_str());
				nl->Add(new_net);

				Net *n YS_ATTRIBUTE(unused) = route_up(new_net, port->IsOutput(), ca_nl, ca_net);
				log_assert(n == ca_net);
			}

			if (verific_verbose)
				log(" new local net: %s\n", new_net->Name());

			log_assert(!new_net->IsExternalTo(nl));
			todo_connect.push_back(tuple<Instance*, Port*, Net*>(inst, port, new_net));
		}

		for (auto it : todo_connect) {
			get<0>(it)->Disconnect(get<1>(it));
			get<0>(it)->Connect(get<1>(it), get<2>(it));
		}
	}
};

void verific_import(Design *design, const std::map<std::string,std::string> &parameters, std::string top)
{
	verific_sva_fsm_limit = 16;

	std::set<Netlist*> nl_todo, nl_done;

	VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary("work", 1);
	VeriLibrary *veri_lib = veri_file::GetLibrary("work", 1);
	Array *netlists = NULL;
	Array veri_libs, vhdl_libs;
	if (vhdl_lib) vhdl_libs.InsertLast(vhdl_lib);
	if (veri_lib) veri_libs.InsertLast(veri_lib);

	Map verific_params(STRING_HASH);
	for (const auto &i : parameters)
		verific_params.Insert(i.first.c_str(), i.second.c_str());

	if (top.empty()) {
		netlists = hier_tree::ElaborateAll(&veri_libs, &vhdl_libs, &verific_params);
	}
	else {
		Array veri_modules, vhdl_units;

		if (veri_lib) {
			VeriModule *veri_module = veri_lib->GetModule(top.c_str(), 1);
			if (veri_module) {
				veri_modules.InsertLast(veri_module);
			}

			// Also elaborate all root modules since they may contain bind statements
			MapIter mi;
			FOREACH_VERILOG_MODULE_IN_LIBRARY(veri_lib, mi, veri_module) {
				if (!veri_module->IsRootModule()) continue;
				veri_modules.InsertLast(veri_module);
			}
		}

		if (vhdl_lib) {
			VhdlDesignUnit *vhdl_unit = vhdl_lib->GetPrimUnit(top.c_str());
			if (vhdl_unit)
				vhdl_units.InsertLast(vhdl_unit);
		}

		netlists = hier_tree::Elaborate(&veri_modules, &vhdl_units, &verific_params);
	}

	Netlist *nl;
	int i;

	FOREACH_ARRAY_ITEM(netlists, i, nl) {
		if (top.empty() && nl->CellBaseName() != top)
			continue;
		nl->AddAtt(new Att(" \\top", NULL));
		nl_todo.insert(nl);
	}

	delete netlists;

	if (!verific_error_msg.empty())
		log_error("%s\n", verific_error_msg.c_str());

	for (auto nl : nl_todo)
	    nl->ChangePortBusStructures(1 /* hierarchical */);

	VerificExtNets worker;
	for (auto nl : nl_todo)
		worker.run(nl);

	while (!nl_todo.empty()) {
		Netlist *nl = *nl_todo.begin();
		if (nl_done.count(nl) == 0) {
			VerificImporter importer(false, false, false, false, false, false, false);
			importer.import_netlist(design, nl, nl_todo, nl->Owner()->Name() == top);
		}
		nl_todo.erase(nl);
		nl_done.insert(nl);
	}

	veri_file::Reset();
	vhdl_file::Reset();
	Libset::Reset();
	verific_incdirs.clear();
	verific_libdirs.clear();
	verific_import_pending = false;

	if (!verific_error_msg.empty())
		log_error("%s\n", verific_error_msg.c_str());
}

YOSYS_NAMESPACE_END
#endif /* YOSYS_ENABLE_VERIFIC */

PRIVATE_NAMESPACE_BEGIN

#ifdef YOSYS_ENABLE_VERIFIC
bool check_noverific_env()
{
	const char *e = getenv("YOSYS_NOVERIFIC");
	if (e == nullptr)
		return false;
	if (atoi(e) == 0)
		return false;
	return true;
}
#endif

struct VerificPass : public Pass {
	VerificPass() : Pass("verific", "load Verilog and VHDL designs using Verific") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    verific {-vlog95|-vlog2k|-sv2005|-sv2009|-sv2012|-sv} <verilog-file>..\n");
		log("\n");
		log("Load the specified Verilog/SystemVerilog files into Verific.\n");
		log("\n");
		log("All files specified in one call to this command are one compilation unit.\n");
		log("Files passed to different calls to this command are treated as belonging to\n");
		log("different compilation units.\n");
		log("\n");
		log("Additional -D<macro>[=<value>] options may be added after the option indicating\n");
		log("the language version (and before file names) to set additional verilog defines.\n");
		log("The macros SYNTHESIS and VERIFIC are defined implicitly.\n");
		log("\n");
		log("\n");
		log("    verific -formal <verilog-file>..\n");
		log("\n");
		log("Like -sv, but define FORMAL instead of SYNTHESIS.\n");
		log("\n");
		log("\n");
		log("    verific {-vhdl87|-vhdl93|-vhdl2k|-vhdl2008|-vhdl} <vhdl-file>..\n");
		log("\n");
		log("Load the specified VHDL files into Verific.\n");
		log("\n");
		log("\n");
		log("    verific [-work <libname>] {-sv|-vhdl|...} <hdl-file>\n");
		log("\n");
		log("Load the specified Verilog/SystemVerilog/VHDL file into the specified library.\n");
		log("(default library when -work is not present: \"work\")\n");
		log("\n");
		log("\n");
		log("    verific [-L <libname>] {-sv|-vhdl|...} <hdl-file>\n");
		log("\n");
		log("Look up external definitions in the specified library.\n");
		log("(-L may be used more than once)\n");
		log("\n");
		log("\n");
		log("    verific -vlog-incdir <directory>..\n");
		log("\n");
		log("Add Verilog include directories.\n");
		log("\n");
		log("\n");
		log("    verific -vlog-libdir <directory>..\n");
		log("\n");
		log("Add Verilog library directories. Verific will search in this directories to\n");
		log("find undefined modules.\n");
		log("\n");
		log("\n");
		log("    verific -vlog-define <macro>[=<value>]..\n");
		log("\n");
		log("Add Verilog defines.\n");
		log("\n");
		log("\n");
		log("    verific -vlog-undef <macro>..\n");
		log("\n");
		log("Remove Verilog defines previously set with -vlog-define.\n");
		log("\n");
		log("\n");
		log("    verific -set-error <msg_id>..\n");
		log("    verific -set-warning <msg_id>..\n");
		log("    verific -set-info <msg_id>..\n");
		log("    verific -set-ignore <msg_id>..\n");
		log("\n");
		log("Set message severity. <msg_id> is the string in square brackets when a message\n");
		log("is printed, such as VERI-1209.\n");
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
		log("  -autocover\n");
		log("    Generate automatic cover statements for all asserts\n");
		log("\n");
		log("  -fullinit\n");
		log("    Keep all register initializations, even those for non-FF registers.\n");
		log("\n");
		log("  -chparam name value \n");
		log("    Elaborate the specified top modules (all modules when -all given) using\n");
		log("    this parameter value. Modules on which this parameter does not exist will\n");
		log("    cause Verific to produce a VERI-1928 or VHDL-1676 message. This option\n");
		log("    can be specified multiple times to override multiple parameters.\n");
		log("    String values must be passed in double quotes (\").\n");
		log("\n");
		log("  -v, -vv\n");
		log("    Verbose log messages. (-vv is even more verbose than -v.)\n");
		log("\n");
		log("The following additional import options are useful for debugging the Verific\n");
		log("bindings (for Yosys and/or Verific developers):\n");
		log("\n");
		log("  -k\n");
		log("    Keep going after an unsupported verific primitive is found. The\n");
		log("    unsupported primitive is added as blockbox module to the design.\n");
		log("    This will also add all SVA related cells to the design parallel to\n");
		log("    the checker logic inferred by it.\n");
		log("\n");
		log("  -V\n");
		log("    Import Verific netlist as-is without translating to Yosys cell types. \n");
		log("\n");
		log("  -nosva\n");
		log("    Ignore SVA properties, do not infer checker logic.\n");
		log("\n");
		log("  -L <int>\n");
		log("    Maximum number of ctrl bits for SVA checker FSMs (default=16).\n");
		log("\n");
		log("  -n\n");
		log("    Keep all Verific names on instances and nets. By default only\n");
		log("    user-declared names are preserved.\n");
		log("\n");
		log("  -d <dump_file>\n");
		log("    Dump the Verific netlist as a verilog file.\n");
		log("\n");
		log("\n");
		log("Use Symbiotic EDA Suite if you need Yosys+Verifc.\n");
		log("https://www.symbioticeda.com/seda-suite\n");
		log("\n");
		log("Contact office@symbioticeda.com for free evaluation\n");
		log("binaries of Symbiotic EDA Suite.\n");
		log("\n");
	}
#ifdef YOSYS_ENABLE_VERIFIC
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		static bool set_verific_global_flags = true;

		if (check_noverific_env())
			log_cmd_error("This version of Yosys is built without Verific support.\n"
					"\n"
					"Use Symbiotic EDA Suite if you need Yosys+Verifc.\n"
					"https://www.symbioticeda.com/seda-suite\n"
					"\n"
					"Contact office@symbioticeda.com for free evaluation\n"
					"binaries of Symbiotic EDA Suite.\n");

		log_header(design, "Executing VERIFIC (loading SystemVerilog and VHDL designs using Verific).\n");

		if (set_verific_global_flags)
		{
			Message::SetConsoleOutput(0);
			Message::RegisterCallBackMsg(msg_func);

			RuntimeFlags::SetVar("db_preserve_user_nets", 1);
			RuntimeFlags::SetVar("db_allow_external_nets", 1);
			RuntimeFlags::SetVar("db_infer_wide_operators", 1);

			RuntimeFlags::SetVar("veri_extract_dualport_rams", 0);
			RuntimeFlags::SetVar("veri_extract_multiport_rams", 1);

			RuntimeFlags::SetVar("vhdl_extract_dualport_rams", 0);
			RuntimeFlags::SetVar("vhdl_extract_multiport_rams", 1);

			RuntimeFlags::SetVar("vhdl_support_variable_slice", 1);
			RuntimeFlags::SetVar("vhdl_ignore_assertion_statements", 0);

			// Workaround for VIPER #13851
			RuntimeFlags::SetVar("veri_create_name_for_unnamed_gen_block", 1);

			// WARNING: instantiating unknown module 'XYZ' (VERI-1063)
			Message::SetMessageType("VERI-1063", VERIFIC_ERROR);

			// https://github.com/YosysHQ/yosys/issues/1055
			RuntimeFlags::SetVar("veri_elaborate_top_level_modules_having_interface_ports", 1) ;

#ifndef DB_PRESERVE_INITIAL_VALUE
#  warning Verific was built without DB_PRESERVE_INITIAL_VALUE.
#endif

			set_verific_global_flags = false;
		}

		verific_verbose = 0;
		verific_sva_fsm_limit = 16;

		const char *release_str = Message::ReleaseString();
		time_t release_time = Message::ReleaseDate();
		char *release_tmstr = ctime(&release_time);

		if (release_str == nullptr)
			release_str = "(no release string)";

		for (char *p = release_tmstr; *p; p++)
			if (*p == '\n') *p = 0;

		log("Built with Verific %s, released at %s.\n", release_str, release_tmstr);

		int argidx = 1;
		std::string work = "work";

		if (GetSize(args) > argidx && (args[argidx] == "-set-error" || args[argidx] == "-set-warning" ||
				args[argidx] == "-set-info" || args[argidx] == "-set-ignore"))
		{
			msg_type_t new_type;

			if (args[argidx] == "-set-error")
				new_type = VERIFIC_ERROR;
			else if (args[argidx] == "-set-warning")
				new_type = VERIFIC_WARNING;
			else if (args[argidx] == "-set-info")
				new_type = VERIFIC_INFO;
			else if (args[argidx] == "-set-ignore")
				new_type = VERIFIC_IGNORE;
			else
				log_abort();

			for (argidx++; argidx < GetSize(args); argidx++)
				Message::SetMessageType(args[argidx].c_str(), new_type);

			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vlog-incdir") {
			for (argidx++; argidx < GetSize(args); argidx++)
				verific_incdirs.push_back(args[argidx]);
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vlog-libdir") {
			for (argidx++; argidx < GetSize(args); argidx++)
				verific_libdirs.push_back(args[argidx]);
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vlog-define") {
			for (argidx++; argidx < GetSize(args); argidx++) {
				string name = args[argidx];
				size_t equal = name.find('=');
				if (equal != std::string::npos) {
					string value = name.substr(equal+1);
					name = name.substr(0, equal);
					veri_file::DefineCmdLineMacro(name.c_str(), value.c_str());
				} else {
					veri_file::DefineCmdLineMacro(name.c_str());
				}
			}
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vlog-undef") {
			for (argidx++; argidx < GetSize(args); argidx++) {
				string name = args[argidx];
				veri_file::UndefineMacro(name.c_str());
			}
			goto check_error;
		}

		veri_file::RemoveAllLOptions();
		for (; argidx < GetSize(args); argidx++)
		{
			if (args[argidx] == "-work" && argidx+1 < GetSize(args)) {
				work = args[++argidx];
				continue;
			}
			if (args[argidx] == "-L" && argidx+1 < GetSize(args)) {
				veri_file::AddLOption(args[++argidx].c_str());
				continue;
			}
			break;
		}

		if (GetSize(args) > argidx && (args[argidx] == "-vlog95" || args[argidx] == "-vlog2k" || args[argidx] == "-sv2005" ||
				args[argidx] == "-sv2009" || args[argidx] == "-sv2012" || args[argidx] == "-sv" || args[argidx] == "-formal"))
		{
			Array file_names;
			unsigned verilog_mode;

			if (args[argidx] == "-vlog95")
				verilog_mode = veri_file::VERILOG_95;
			else if (args[argidx] == "-vlog2k")
				verilog_mode = veri_file::VERILOG_2K;
			else if (args[argidx] == "-sv2005")
				verilog_mode = veri_file::SYSTEM_VERILOG_2005;
			else if (args[argidx] == "-sv2009")
				verilog_mode = veri_file::SYSTEM_VERILOG_2009;
			else if (args[argidx] == "-sv2012" || args[argidx] == "-sv" || args[argidx] == "-formal")
				verilog_mode = veri_file::SYSTEM_VERILOG;
			else
				log_abort();

			veri_file::DefineMacro("VERIFIC");
			veri_file::DefineMacro(args[argidx] == "-formal" ? "FORMAL" : "SYNTHESIS");

			for (argidx++; argidx < GetSize(args) && GetSize(args[argidx]) >= 2 && args[argidx].compare(0, 2, "-D") == 0; argidx++) {
				std::string name = args[argidx].substr(2);
				if (args[argidx] == "-D") {
					if (++argidx >= GetSize(args))
						break;
					name = args[argidx];
				}
				size_t equal = name.find('=');
				if (equal != std::string::npos) {
					string value = name.substr(equal+1);
					name = name.substr(0, equal);
					veri_file::DefineMacro(name.c_str(), value.c_str());
				} else {
					veri_file::DefineMacro(name.c_str());
				}
			}

			for (auto &dir : verific_incdirs)
				veri_file::AddIncludeDir(dir.c_str());
			for (auto &dir : verific_libdirs)
				veri_file::AddYDir(dir.c_str());

			while (argidx < GetSize(args))
				file_names.Insert(args[argidx++].c_str());

			if (!veri_file::AnalyzeMultipleFiles(&file_names, verilog_mode, work.c_str(), veri_file::MFCU))
					log_cmd_error("Reading Verilog/SystemVerilog sources failed.\n");

			verific_import_pending = true;
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdl87") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_1987").c_str());
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!vhdl_file::Analyze(args[argidx].c_str(), work.c_str(), vhdl_file::VHDL_87))
					log_cmd_error("Reading `%s' in VHDL_87 mode failed.\n", args[argidx].c_str());
			verific_import_pending = true;
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdl93") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_1993").c_str());
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!vhdl_file::Analyze(args[argidx].c_str(), work.c_str(), vhdl_file::VHDL_93))
					log_cmd_error("Reading `%s' in VHDL_93 mode failed.\n", args[argidx].c_str());
			verific_import_pending = true;
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdl2k") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_1993").c_str());
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!vhdl_file::Analyze(args[argidx].c_str(), work.c_str(), vhdl_file::VHDL_2K))
					log_cmd_error("Reading `%s' in VHDL_2K mode failed.\n", args[argidx].c_str());
			verific_import_pending = true;
			goto check_error;
		}

		if (GetSize(args) > argidx && (args[argidx] == "-vhdl2008" || args[argidx] == "-vhdl")) {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_2008").c_str());
			for (argidx++; argidx < GetSize(args); argidx++)
				if (!vhdl_file::Analyze(args[argidx].c_str(), work.c_str(), vhdl_file::VHDL_2008))
					log_cmd_error("Reading `%s' in VHDL_2008 mode failed.\n", args[argidx].c_str());
			verific_import_pending = true;
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-import")
		{
			std::set<Netlist*> nl_todo, nl_done;
			bool mode_all = false, mode_gates = false, mode_keep = false;
			bool mode_nosva = false, mode_names = false, mode_verific = false;
			bool mode_autocover = false, mode_fullinit = false;
			bool flatten = false, extnets = false;
			string dumpfile;
			Map parameters(STRING_HASH);

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
				if (args[argidx] == "-nosva") {
					mode_nosva = true;
					continue;
				}
				if (args[argidx] == "-L" && argidx+1 < GetSize(args)) {
					verific_sva_fsm_limit = atoi(args[++argidx].c_str());
					continue;
				}
				if (args[argidx] == "-n") {
					mode_names = true;
					continue;
				}
				if (args[argidx] == "-autocover") {
					mode_autocover = true;
					continue;
				}
				if (args[argidx] == "-fullinit") {
					mode_fullinit = true;
					continue;
				}
				if (args[argidx] == "-chparam"  && argidx+2 < GetSize(args)) {
					const std::string &key = args[++argidx];
					const std::string &value = args[++argidx];
					unsigned new_insertion = parameters.Insert(key.c_str(), value.c_str(),
									           1 /* force_overwrite */);
					if (!new_insertion)
						log_warning_noprefix("-chparam %s already specified: overwriting.\n", key.c_str());
					continue;
				}
				if (args[argidx] == "-V") {
					mode_verific = true;
					continue;
				}
				if (args[argidx] == "-v") {
					verific_verbose = 1;
					continue;
				}
				if (args[argidx] == "-vv") {
					verific_verbose = 2;
					continue;
				}
				if (args[argidx] == "-d" && argidx+1 < GetSize(args)) {
					dumpfile = args[++argidx];
					continue;
				}
				break;
			}

			if (argidx > GetSize(args) && args[argidx].compare(0, 1, "-") == 0)
				cmd_error(args, argidx, "unknown option");

			std::set<std::string> top_mod_names;

			if (mode_all)
			{
				log("Running hier_tree::ElaborateAll().\n");

				VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work.c_str(), 1);
				VeriLibrary *veri_lib = veri_file::GetLibrary(work.c_str(), 1);

				Array veri_libs, vhdl_libs;
				if (vhdl_lib) vhdl_libs.InsertLast(vhdl_lib);
				if (veri_lib) veri_libs.InsertLast(veri_lib);

				Array *netlists = hier_tree::ElaborateAll(&veri_libs, &vhdl_libs, &parameters);
				Netlist *nl;
				int i;

				FOREACH_ARRAY_ITEM(netlists, i, nl)
					nl_todo.insert(nl);
				delete netlists;
			}
			else
			{
				if (argidx == GetSize(args))
					cmd_error(args, argidx, "No top module specified.\n");

				Array veri_modules, vhdl_units;
				for (; argidx < GetSize(args); argidx++)
				{
					const char *name = args[argidx].c_str();
					top_mod_names.insert(name);
					VeriLibrary* veri_lib = veri_file::GetLibrary(work.c_str(), 1);

					if (veri_lib) {
						VeriModule *veri_module = veri_lib->GetModule(name, 1);
						if (veri_module) {
							log("Adding Verilog module '%s' to elaboration queue.\n", name);
							veri_modules.InsertLast(veri_module);
							continue;
						}

						// Also elaborate all root modules since they may contain bind statements
						MapIter mi;
						FOREACH_VERILOG_MODULE_IN_LIBRARY(veri_lib, mi, veri_module) {
							if (!veri_module->IsRootModule()) continue;
							veri_modules.InsertLast(veri_module);
						}
					}

					VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work.c_str(), 1);
					VhdlDesignUnit *vhdl_unit = vhdl_lib->GetPrimUnit(name);
					if (vhdl_unit) {
						log("Adding VHDL unit '%s' to elaboration queue.\n", name);
						vhdl_units.InsertLast(vhdl_unit);
						continue;
					}

					log_error("Can't find module/unit '%s'.\n", name);
				}

				log("Running hier_tree::Elaborate().\n");
				Array *netlists = hier_tree::Elaborate(&veri_modules, &vhdl_units, &parameters);
				Netlist *nl;
				int i;

				FOREACH_ARRAY_ITEM(netlists, i, nl) {
					nl->AddAtt(new Att(" \\top", NULL));
					nl_todo.insert(nl);
				}
				delete netlists;
			}

			if (!verific_error_msg.empty())
				goto check_error;

			if (flatten) {
				for (auto nl : nl_todo)
					nl->Flatten();
			}

			if (extnets) {
				VerificExtNets worker;
				for (auto nl : nl_todo)
					worker.run(nl);
			}

			for (auto nl : nl_todo)
				nl->ChangePortBusStructures(1 /* hierarchical */);

			if (!dumpfile.empty()) {
				VeriWrite veri_writer;
				veri_writer.WriteFile(dumpfile.c_str(), Netlist::PresentDesign());
			}

			while (!nl_todo.empty()) {
				Netlist *nl = *nl_todo.begin();
				if (nl_done.count(nl) == 0) {
					VerificImporter importer(mode_gates, mode_keep, mode_nosva,
							mode_names, mode_verific, mode_autocover, mode_fullinit);
					importer.import_netlist(design, nl, nl_todo, top_mod_names.count(nl->Owner()->Name()));
				}
				nl_todo.erase(nl);
				nl_done.insert(nl);
			}

			veri_file::Reset();
			vhdl_file::Reset();
			Libset::Reset();
			verific_incdirs.clear();
			verific_libdirs.clear();
			verific_import_pending = false;
			goto check_error;
		}

		cmd_error(args, argidx, "Missing or unsupported mode parameter.\n");

	check_error:
		if (!verific_error_msg.empty())
			log_error("%s\n", verific_error_msg.c_str());

	}
#else /* YOSYS_ENABLE_VERIFIC */
	void execute(std::vector<std::string>, RTLIL::Design *) YS_OVERRIDE {
		log_cmd_error("This version of Yosys is built without Verific support.\n"
				"\n"
				"Use Symbiotic EDA Suite if you need Yosys+Verifc.\n"
				"https://www.symbioticeda.com/seda-suite\n"
				"\n"
				"Contact office@symbioticeda.com for free evaluation\n"
				"binaries of Symbiotic EDA Suite.\n");
	}
#endif
} VerificPass;

struct ReadPass : public Pass {
	ReadPass() : Pass("read", "load HDL designs") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    read {-vlog95|-vlog2k|-sv2005|-sv2009|-sv2012|-sv|-formal} <verilog-file>..\n");
		log("\n");
		log("Load the specified Verilog/SystemVerilog files. (Full SystemVerilog support\n");
		log("is only available via Verific.)\n");
		log("\n");
		log("Additional -D<macro>[=<value>] options may be added after the option indicating\n");
		log("the language version (and before file names) to set additional verilog defines.\n");
		log("\n");
		log("\n");
		log("    read {-vhdl87|-vhdl93|-vhdl2k|-vhdl2008|-vhdl} <vhdl-file>..\n");
		log("\n");
		log("Load the specified VHDL files. (Requires Verific.)\n");
		log("\n");
		log("\n");
		log("    read -define <macro>[=<value>]..\n");
		log("\n");
		log("Set global Verilog/SystemVerilog defines.\n");
		log("\n");
		log("\n");
		log("    read -undef <macro>..\n");
		log("\n");
		log("Unset global Verilog/SystemVerilog defines.\n");
		log("\n");
		log("\n");
		log("    read -incdir <directory>\n");
		log("\n");
		log("Add directory to global Verilog/SystemVerilog include directories.\n");
		log("\n");
		log("\n");
		log("    read -verific\n");
		log("    read -noverific\n");
		log("\n");
		log("Subsequent calls to 'read' will either use or not use Verific. Calling 'read'\n");
		log("with -verific will result in an error on Yosys binaries that are built without\n");
		log("Verific support. The default is to use Verific if it is available.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
#ifdef YOSYS_ENABLE_VERIFIC
		static bool verific_available = !check_noverific_env();
#else
		static bool verific_available = false;
#endif
		static bool use_verific = verific_available;

		if (args.size() < 2 || args[1][0] != '-')
			cmd_error(args, 1, "Missing mode parameter.\n");

		if (args[1] == "-verific" || args[1] == "-noverific") {
			if (args.size() != 2)
				cmd_error(args, 1, "Additional arguments to -verific/-noverific.\n");
			if (args[1] == "-verific") {
				if (!verific_available)
					cmd_error(args, 1, "This version of Yosys is built without Verific support.\n");
				use_verific = true;
			} else {
				use_verific = false;
			}
			return;
		}

		if (args.size() < 3)
			cmd_error(args, 3, "Missing file name parameter.\n");

		if (args[1] == "-vlog95" || args[1] == "-vlog2k") {
			if (use_verific) {
				args[0] = "verific";
			} else {
				args[0] = "read_verilog";
				args[1] = "-defer";
			}
			Pass::call(design, args);
			return;
		}

		if (args[1] == "-sv2005" || args[1] == "-sv2009" || args[1] == "-sv2012" || args[1] == "-sv" || args[1] == "-formal") {
			if (use_verific) {
				args[0] = "verific";
			} else {
				args[0] = "read_verilog";
				if (args[1] == "-formal")
					args.insert(args.begin()+1, std::string());
				args[1] = "-sv";
				args.insert(args.begin()+1, "-defer");
			}
			Pass::call(design, args);
			return;
		}

		if (args[1] == "-vhdl87" || args[1] == "-vhdl93" || args[1] == "-vhdl2k" || args[1] == "-vhdl2008" || args[1] == "-vhdl") {
			if (use_verific) {
				args[0] = "verific";
				Pass::call(design, args);
			} else {
				cmd_error(args, 1, "This version of Yosys is built without Verific support.\n");
			}
			return;
		}

		if (args[1] == "-define") {
			if (use_verific) {
				args[0] = "verific";
				args[1] = "-vlog-define";
				Pass::call(design, args);
			}
			args[0] = "verilog_defines";
			args.erase(args.begin()+1, args.begin()+2);
			for (int i = 1; i < GetSize(args); i++)
				args[i] = "-D" + args[i];
			Pass::call(design, args);
			return;
		}

		if (args[1] == "-undef") {
			if (use_verific) {
				args[0] = "verific";
				args[1] = "-vlog-undef";
				Pass::call(design, args);
			}
			args[0] = "verilog_defines";
			args.erase(args.begin()+1, args.begin()+2);
			for (int i = 1; i < GetSize(args); i++)
				args[i] = "-U" + args[i];
			Pass::call(design, args);
			return;
		}

		if (args[1] == "-incdir") {
			if (use_verific) {
				args[0] = "verific";
				args[1] = "-vlog-incdir";
				Pass::call(design, args);
			}
			args[0] = "verilog_defaults";
			args[1] = "-add";
			for (int i = 2; i < GetSize(args); i++)
				args[i] = "-I" + args[i];
			Pass::call(design, args);
			return;
		}

		cmd_error(args, 1, "Missing or unsupported mode parameter.\n");
	}
} ReadPass;

PRIVATE_NAMESPACE_END
