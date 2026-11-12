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

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/utils.h"
#include "libs/sha1/sha1.h"

#include "frontends/verific/verific.h"

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Woverloaded-virtual"
#endif

#include "Array.h"

#ifdef VERIFIC_VHDL_SUPPORT
#include "NameSpace.h"
#endif

#ifdef __clang__
#pragma clang diagnostic pop
#endif

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

YOSYS_NAMESPACE_BEGIN

static std::string format_src_location(DesignObj *obj)
{
	if (obj == nullptr || !obj->Linefile())
		return std::string();
#ifdef VERIFIC_LINEFILE_INCLUDES_COLUMNS
	return stringf("%s:%d.%d-%d.%d", LineFile::GetFileName(obj->Linefile()), obj->Linefile()->GetLeftLine(), obj->Linefile()->GetLeftCol(), obj->Linefile()->GetRightLine(), obj->Linefile()->GetRightCol());
#else
	return stringf("%s:%d", LineFile::GetFileName(obj->Linefile()), LineFile::GetLineNo(obj->Linefile()));
#endif
}

static std::string announce_src_location(DesignObj *obj)
{
	std::string loc = format_src_location(obj);
	if (loc.empty())
		return std::string();
	return loc + ": ";
}

VerificImporter::VerificImporter(bool mode_gates, bool mode_keep, bool mode_nosva, bool mode_sva_continue, bool mode_names, bool mode_verific, bool mode_autocover, bool mode_fullinit) :
		mode_gates(mode_gates), mode_keep(mode_keep), mode_nosva(mode_nosva), mode_sva_continue(mode_sva_continue),
		mode_names(mode_names), mode_verific(mode_verific), mode_autocover(mode_autocover),
		mode_fullinit(mode_fullinit)
{
}

RTLIL::SigBit VerificImporter::net_map_at(Net *net)
{
	if (net->IsExternalTo(netlist))
		log_error("Found external reference to '%s.%s' in netlist '%s', please use -flatten or -extnets.\n",
				get_full_netlist_name(net->Owner()), net->Name(), get_full_netlist_name(netlist));

	return net_map.at(net);
}

static bool is_blackbox(Netlist *nl)
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
		s += stringf("$%s:%d", RTLIL::encode_filename(Verific::LineFile::GetFileName(obj->Linefile())), Verific::LineFile::GetLineNo(obj->Linefile()));
	s += stringf("$%d", module->twines().next_autoidx());
	return module->twines().add(std::move(s));
}

static const RTLIL::Const extract_vhdl_boolean(std::string &val)
{
	if (val == "false")
		return RTLIL::Const::from_string("0");
	if (val == "true")
		return RTLIL::Const::from_string("1");
	log_error("Expecting VHDL boolean value.\n");
}

static const RTLIL::Const extract_vhdl_bit(std::string &val, std::string &typ)
{
	if (val.size()==3 && val[0]=='\'' && val.back()=='\'')
		return  RTLIL::Const::from_string(val.substr(1,val.size()-2));
	log_error("Error parsing VHDL %s.\n", typ);
}

static const RTLIL::Const extract_vhdl_bit_vector(std::string &val, std::string &typ)
{
	if (val.size()>1 && val[0]=='\"' && val.back()=='\"') {
		RTLIL::Const c = RTLIL::Const::from_string(val.substr(1,val.size()-2));
		if (typ == "signed")
			c.flags |= RTLIL::CONST_FLAG_SIGNED;
		return c;
	}
	log_error("Error parsing VHDL %s.\n", typ);
}

static const RTLIL::Const extract_vhdl_integer(std::string &val)
{
	char *end;
	return RTLIL::Const((int)std::strtol(val.c_str(), &end, 10));
}

static const RTLIL::Const extract_vhdl_char(std::string &val)
{
	if (val.size()==3 && val[0]=='\"' && val.back()=='\"')
		return RTLIL::Const((int)val[1]);
	log_error("Error parsing VHDL character.\n");
}

static const RTLIL::Const extract_real_value(std::string &val)
{
	RTLIL::Const c(val);
	c.flags |= RTLIL::CONST_FLAG_REAL;
	return c;
}

static const RTLIL::Const extract_vhdl_string(std::string &val)
{
	if (!(val.size()>1 && val[0]=='\"' && val.back()=='\"'))
		log_error("Error parsing VHDL string.\n");
	return RTLIL::Const(val.substr(1,val.size()-2));
}

static const  RTLIL::Const extract_vhdl_const(const char *value, bool output_signed)
{
	RTLIL::Const c;
	char *end;
	int decimal;
	bool is_signed = false;
	std::string val = std::string(value);

	if (val.size()>1 && val[0]=='\"' && val.back()=='\"') {
		std::string data = val.substr(1,val.size()-2);
		bool isBinary = std::all_of(data.begin(), data.end(), [](char c) {return c=='1' || c=='0'; });
		if (isBinary)
			c = RTLIL::Const::from_string(data);
		else
			c = RTLIL::Const(data);
	} else if (val.size()==3 && val[0]=='\'' && val.back()=='\'') {
		c = RTLIL::Const::from_string(val.substr(1,val.size()-2));
	} else if ((value[0] == '-' || (value[0] >= '0' && value[0] <= '9')) &&
			((decimal = std::strtol(value, &end, 10)), !end[0])) {
		is_signed = output_signed;
		c = RTLIL::Const((int)decimal);
	} else if (val == "false") {
		c = RTLIL::Const::from_string("0");
	} else if (val == "true") {
		c = RTLIL::Const::from_string("1");
	} else {
		c = RTLIL::Const(val);
		log_warning("encoding value '%s' as string.\n", value);
	}
	if (is_signed)
		c.flags |= RTLIL::CONST_FLAG_SIGNED;
	return c;
}

static const  RTLIL::Const extract_verilog_const(const char *value, bool allow_string, bool output_signed)
{
	RTLIL::Const c;
	char *end;
	int decimal;
	bool is_signed = false;
	size_t found;
	std::string val = std::string(value);

	if (allow_string && val.size()>1 && val[0]=='\"' && val.back()=='\"') {
		c = RTLIL::Const(val.substr(1,val.size()-2));
	} else if ((found = val.find("'sb")) != std::string::npos) {
		is_signed = output_signed;
		c = RTLIL::Const::from_string(val.substr(found + 3));
	} else if ((found = val.find("'b")) != std::string::npos) {
		c = RTLIL::Const::from_string(val.substr(found + 2));
	} else if ((value[0] == '-' || (value[0] >= '0' && value[0] <= '9')) &&
			((decimal = std::strtol(value, &end, 10)), !end[0])) {
		is_signed = output_signed;
		c = RTLIL::Const((int)decimal);
	} else if (allow_string) {
		c = RTLIL::Const(val);
	} else {
		c = RTLIL::Const(val);
		log_warning("encoding value '%s' as string.\n", value);
	}
	if (is_signed)
		c.flags |= RTLIL::CONST_FLAG_SIGNED;
	return c;
}

// When used as attributes or parameter values Verific constants come already processed.
// - Real string values are already under quotes
// - Numeric values with specified width are always converted to binary
// - Rest of user defined values are handled as 32bit integers
// - There could be some internal values that are strings without quotes
//   so we check if value is all digits or not
//
// Note: For signed values, verific uses <len>'sb<bits> and decimal values can
// also be negative.
static const RTLIL::Const verific_const(const char* type_name, const char *value, DesignObj *obj, bool allow_string = true, bool output_signed = false)
{
	std::string val = std::string(value);
	// VHDL
	if (obj->IsFromVhdl()) {
		if (type_name) {
			std::string typ = std::string(type_name);
			transform(typ.begin(), typ.end(), typ.begin(), ::tolower);
			if (typ ==  "integer" ||  typ == "natural" || typ=="positive") return extract_vhdl_integer(val);
			else if (typ =="boolean") return extract_vhdl_boolean(val);
			else if (typ == "bit" || typ =="std_logic" || typ == "std_ulogic") return extract_vhdl_bit(val,typ);
			else if (typ == "character") return extract_vhdl_char(val);
			else if (typ == "bit_vector" || typ == "std_logic_vector" || typ == "std_ulogic_vector" ||
					 typ == "unsigned" || typ == "signed") return extract_vhdl_bit_vector(val,typ);
			else if (typ == "real") return extract_real_value(val);
			else if (typ == "string") return extract_vhdl_string(val);
			else {
				if (val.size()>1 && val[0]=='\"' && val.back()=='\"')
					return RTLIL::Const(val.substr(1,val.size()-2));
				else if (val.size()==3 && val[0]=='\'' && val.back()=='\'')
					return RTLIL::Const(val.substr(1,val.size()-2));
				else
					return RTLIL::Const(val);
			}
		} else extract_vhdl_const(value, output_signed);
	}
	// SystemVerilog
	if (type_name && strcmp(type_name, "real")==0) {
		return extract_real_value(val);
	} else
		return extract_verilog_const(value, allow_string, output_signed);
}

#ifdef YOSYSHQ_VERIFIC_API_VERSION
static const std::string verific_unescape(const char *value)
{
	std::string val = std::string(value);
	if (val.size()>1 && val[0]=='\"' && val.back()=='\"')
		return val.substr(1,val.size()-2);
	return value;
}
#endif

void VerificImporter::import_attributes(dict<RTLIL::IdString, RTLIL::Const> &attributes, DesignObj *obj, Netlist *nl, int wire_width_hint)
{
	if (!obj)
		return;

	MapIter mi;
	Att *attr;

	if (obj->Linefile())
		attributes[ID::src] = format_src_location(obj);

	FOREACH_ATTRIBUTE(obj, mi, attr) {
		if (attr->Key()[0] == ' ' || attr->Value() == nullptr)
			continue;
		attributes[module->twines().add(RTLIL::escape_id(attr->Key()))] = verific_const(nullptr, attr->Value(), obj);
	}

	if (nl) {
		auto type_range = nl->GetTypeRange(obj->Name());
		if (!type_range)
			return;
		if (nl->IsFromVhdl() && type_range->IsTypeScalar()) {
			const long long bottom_bound = type_range->GetScalarRangeLeftBound();
			const long long top_bound = type_range->GetScalarRangeRightBound();
			int bit_width = type_range->LeftRangeBound()+1;
			if (bit_width <= 0) { // VHDL null range
				if (wire_width_hint >= 0)
					bit_width = wire_width_hint;
				else
					bit_width = 64; //fallback, currently largest integer width that verific will allow (in vhdl2019 mode)
			} else {
				if (wire_width_hint >= 0) log_assert(bit_width == wire_width_hint);
			}
			RTLIL::Const bottom_const(bottom_bound, bit_width);
			RTLIL::Const top_const(top_bound, bit_width);
			if (bottom_bound < 0 || top_bound < 0) {
				bottom_const.flags |= RTLIL::CONST_FLAG_SIGNED;
				top_const.flags |= RTLIL::CONST_FLAG_SIGNED;
			}
			attributes.emplace(ID(bottom_bound), bottom_const);
			attributes.emplace(ID(top_bound), top_const);
		}
		if (!type_range->IsTypeEnum())
			return;
#ifdef VERIFIC_VHDL_SUPPORT
		if (nl->IsFromVhdl() && strcmp(type_range->GetTypeName(), "STD_LOGIC") == 0)
			return;
#endif
		auto type_name = type_range->GetTypeName();
		if (!type_name)
			return;
		attributes.emplace(ID::wiretype, RTLIL::escape_id(type_name));

		MapIter mi;
		const char *k, *v;
		FOREACH_MAP_ITEM(type_range->GetEnumIdMap(), mi, &k, &v) {
			if (nl->IsFromVerilog()) {
				auto const value = verific_const(type_name, v, nl, false);

				attributes.emplace(module->twines().add(stringf("\\enum_value_%s", value.as_string())), RTLIL::escape_id(k));
			}
#ifdef VERIFIC_VHDL_SUPPORT
			else if (nl->IsFromVhdl()) {
				// Expect "<binary>" or plain <binary>
				auto p = v;
				if (p) {
					if (*p != '"') {
						auto l = strlen(p);
						auto q = (char*)malloc(l+1);
						strncpy(q, p, l);
						q[l] = '\0';
						for(char *ptr = q; *ptr; ++ptr )*ptr = tolower(*ptr);
						attributes.emplace(module->twines().add(stringf("\\enum_value_%s", q)), RTLIL::escape_id(k));
					} else {
						auto *q = p+1;
						for (; *q != '"'; q++)
							if (*q != '0' && *q != '1') {
								p = nullptr;
								break;
							}
						if (p && *(q+1) != '\0')
							p = nullptr;

						if (p != nullptr)
						{
							auto l = strlen(p);
							auto q = (char*)malloc(l+1-2);
							strncpy(q, p+1, l-2);
							q[l-2] = '\0';
							attributes.emplace(module->twines().add(stringf("\\enum_value_%s", q)), RTLIL::escape_id(k));
							free(q);
						}
					}
				}
				if (p == nullptr)
					log_error("%sExpected TypeRange value '%s' to be of form \"<binary>\" or <binary>.\n", announce_src_location(obj), v);
			}
#endif
		}
	}
}

RTLIL::SigBit VerificImporter::netToSigBit(Verific::Net *net) {
	if (net && net->IsGnd())
		return RTLIL::State::S0;
	else if (net && net->IsPwr())
		return RTLIL::State::S1;
	else if (net && net->IsX())
		return RTLIL::State::Sx;
	else if (net)
		return net_map_at(net);
	else
		return RTLIL::State::Sz;
}

RTLIL::SigSpec VerificImporter::operatorInput(Instance *inst)
{
	RTLIL::SigSpec sig;
	for (int i = int(inst->InputSize())-1; i >= 0; i--) {
		Net *net = inst->GetInputBit(i);
		sig.append(netToSigBit(net));
	}
	return sig;
}

RTLIL::SigSpec VerificImporter::operatorInput1(Instance *inst)
{
	RTLIL::SigSpec sig;
	for (int i = int(inst->Input1Size())-1; i >= 0; i--) {
		Net *net = inst->GetInput1Bit(i);
		sig.append(netToSigBit(net));
	}
	return sig;
}

RTLIL::SigSpec VerificImporter::operatorInput2(Instance *inst)
{
	RTLIL::SigSpec sig;
	for (int i = int(inst->Input2Size())-1; i >= 0; i--) {
		Net *net = inst->GetInput2Bit(i);
		sig.append(netToSigBit(net));
	}
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
				if (net->IsConstant()) {
					if (net->IsGnd())
						sig.append(RTLIL::State::S0);
					else if (net->IsPwr())
						sig.append(RTLIL::State::S1);
					else if (net->IsX())
						sig.append(RTLIL::State::Sx);
					else
						sig.append(RTLIL::State::Sz);
				}
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

RTLIL::SigSpec VerificImporter::operatorInportCase(Instance *inst, const char *portname)
{
	PortBus *portbus = inst->View()->GetPortBus(portname);
	if (portbus) {
		RTLIL::SigSpec sig;
		for (unsigned i = 0; i < portbus->Size(); i++) {
			Net *net = inst->GetNet(portbus->ElementAtIndex(i));
			if (net) {
				if (net->IsConstant()) {
					if (net->IsGnd())
						sig.append(RTLIL::State::S0);
					else if (net->IsPwr())
						sig.append(RTLIL::State::S1);
					else
						sig.append(RTLIL::State::Sa);
				}
				else
					sig.append(net_map_at(net));
			} else
				sig.append(RTLIL::State::Sa);
		}
		return sig;
	} else {
		Port *port = inst->View()->GetPort(portname);
		log_assert(port != NULL);
		Net *net = inst->GetNet(port);
		return net_map_at(net);
	}
}

RTLIL::SigSpec VerificImporter::operatorOutput(Instance *inst, const pool<Net*> *any_all_nets)
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

	if ((inst->Type() == PRIM_TRI) || (inst->Type() == PRIM_BUFIF1)) {
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

	if (inst->Type() == PRIM_DLATCHRS)
	{
		if (inst->GetSet()->IsGnd() && inst->GetReset()->IsGnd())
			module->addDlatch(inst_name, net_map_at(inst->GetControl()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		else
			module->addDlatchsr(inst_name, net_map_at(inst->GetControl()), net_map_at(inst->GetSet()), net_map_at(inst->GetReset()),
					net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		return true;
	}

	if (inst->Type() == PRIM_DFF)
	{
		VerificClocking clocking(this, inst->GetClock());
		log_assert(clocking.disable_sig == State::S0);
		log_assert(clocking.body_net == nullptr);

		if (inst->GetAsyncCond()->IsGnd())
			clocking.addDff(inst_name, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		else
			clocking.addAldff(inst_name, net_map_at(inst->GetAsyncCond()), net_map_at(inst->GetAsyncVal()),
					net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		return true;
	}

	if (inst->Type() == PRIM_DLATCH)
	{
		if (inst->GetAsyncCond()->IsGnd()) {
			module->addDlatch(inst_name, net_map_at(inst->GetControl()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		} else {
			RTLIL::SigSpec sig_set = module->And(NEW_ID, net_map_at(inst->GetAsyncCond()), net_map_at(inst->GetAsyncVal()));
			RTLIL::SigSpec sig_clr = module->And(NEW_ID, net_map_at(inst->GetAsyncCond()), module->Not(NEW_ID, net_map_at(inst->GetAsyncVal())));
			module->addDlatchsr(inst_name, net_map_at(inst->GetControl()), sig_set, sig_clr, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		}
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

	if ((inst->Type() == PRIM_TRI) || (inst->Type() == PRIM_BUFIF1)) {
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

	if (inst->Type() == PRIM_DFF)
	{
		VerificClocking clocking(this, inst->GetClock());
		log_assert(clocking.disable_sig == State::S0);
		log_assert(clocking.body_net == nullptr);

		if (inst->GetAsyncCond()->IsGnd())
			cell = clocking.addDff(inst_name, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		else
			cell = clocking.addAldff(inst_name, net_map_at(inst->GetAsyncCond()), net_map_at(inst->GetAsyncVal()),
					net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == PRIM_DLATCH)
	{
		if (inst->GetAsyncCond()->IsGnd()) {
			cell = module->addDlatch(inst_name, net_map_at(inst->GetControl()), net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		} else {
			RTLIL::SigSpec sig_set = module->And(NEW_ID, net_map_at(inst->GetAsyncCond()), net_map_at(inst->GetAsyncVal()));
			RTLIL::SigSpec sig_clr = module->And(NEW_ID, net_map_at(inst->GetAsyncCond()), module->Not(NEW_ID, net_map_at(inst->GetAsyncVal())));
			cell = module->addDlatchsr(inst_name, net_map_at(inst->GetControl()), sig_set, sig_clr, net_map_at(inst->GetInput()), net_map_at(inst->GetOutput()));
		}
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
			log_error("%sCan't import Verific OPER_SHIFT_RIGHT instance %s: carry_in is neither 0 nor msb of left input\n", announce_src_location(inst), inst->Name());
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
			log_error("%sCan't import Verific OPER_LESSTHAN instance %s: carry_in is neither 0 nor 1\n", announce_src_location(inst), inst->Name());
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
		cell = module->addBmux(inst_name, IN2, IN1, net_map_at(inst->GetOutput()));
		import_attributes(cell->attributes, inst);
		return true;
	}

	if (inst->Type() == OPER_WIDE_NTO1MUX)
	{
		cell = module->addBmux(inst_name, IN2, IN1, OUT);
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

	if (inst->Type() == OPER_WIDE_DLATCHRS)
	{
		RTLIL::SigSpec sig_set = operatorInport(inst, "set");
		RTLIL::SigSpec sig_reset = operatorInport(inst, "reset");

		if (sig_set.is_fully_const() && !sig_set.as_bool() && sig_reset.is_fully_const() && !sig_reset.as_bool())
			cell = module->addDlatch(inst_name, net_map_at(inst->GetControl()), IN, OUT);
		else
			cell = module->addDlatchsr(inst_name, net_map_at(inst->GetControl()), sig_set, sig_reset, IN, OUT);
		import_attributes(cell->attributes, inst);

		return true;
	}

	if (inst->Type() == OPER_WIDE_DFF)
	{
		VerificClocking clocking(this, inst->GetClock());
		log_assert(clocking.disable_sig == State::S0);
		log_assert(clocking.body_net == nullptr);

		RTLIL::SigSpec sig_d = IN;
		RTLIL::SigSpec sig_q = OUT;
		RTLIL::SigSpec sig_adata = IN1;
		RTLIL::SigSpec sig_acond = IN2;

		if (sig_acond.is_fully_const() && !sig_acond.as_bool()) {
			cell = clocking.addDff(inst_name, sig_d, sig_q);
			import_attributes(cell->attributes, inst);
		} else {
			int offset = 0, width = 0;
			for (offset = 0; offset < GetSize(sig_acond); offset += width) {
				for (width = 1; offset+width < GetSize(sig_acond); width++)
					if (sig_acond[offset] != sig_acond[offset+width]) break;
				cell = clocking.addAldff(module->uniquify(inst_name), sig_acond[offset], sig_adata.extract(offset, width),
						sig_d.extract(offset, width), sig_q.extract(offset, width));
				import_attributes(cell->attributes, inst);
			}
		}

		return true;
	}

	if (inst->Type() == OPER_WIDE_DLATCH)
	{
		RTLIL::SigSpec sig_d = IN;
		RTLIL::SigSpec sig_q = OUT;
		RTLIL::SigSpec sig_adata = IN1;
		RTLIL::SigSpec sig_acond = IN2;

		if (sig_acond.is_fully_const() && !sig_acond.as_bool()) {
			cell = module->addDlatch(inst_name, net_map_at(inst->GetControl()), sig_d, sig_q);
			import_attributes(cell->attributes, inst);
		} else {
			int offset = 0, width = 0;
			for (offset = 0; offset < GetSize(sig_acond); offset += width) {
				for (width = 1; offset+width < GetSize(sig_acond); width++)
					if (sig_acond[offset] != sig_acond[offset+width]) break;
				RTLIL::SigSpec sig_set = module->Mux(NEW_ID, RTLIL::SigSpec(0, width), sig_adata.extract(offset, width), sig_acond[offset]);
				RTLIL::SigSpec sig_clr = module->Mux(NEW_ID, RTLIL::SigSpec(0, width), module->Not(NEW_ID, sig_adata.extract(offset, width)), sig_acond[offset]);
				cell = module->addDlatchsr(module->uniquify(inst_name), net_map_at(inst->GetControl()), sig_set, sig_clr,
						sig_d.extract(offset, width), sig_q.extract(offset, width));
				import_attributes(cell->attributes, inst);
			}
		}

		return true;
	}

	if (inst->Type() == OPER_WIDE_CASE_SELECT_BOX)
	{
		RTLIL::SigSpec sig_out_val = operatorInport(inst, "out_value");
		RTLIL::SigSpec sig_select = operatorInport(inst, "select");
		RTLIL::SigSpec sig_select_values = operatorInportCase(inst, "select_values");
		RTLIL::SigSpec sig_data_values = operatorInport(inst, "data_values");
		RTLIL::SigSpec sig_data_default = operatorInport(inst, "default_value");

		RTLIL::Process *proc = module->addProcess(new_verific_id(inst));
		import_attributes(proc->attributes, inst);

		RTLIL::CaseRule *current_case = &proc->root_case;
		current_case = &proc->root_case;

		RTLIL::SwitchRule *sw = new RTLIL::SwitchRule;
		sw->signal = sig_select;
		current_case->switches.push_back(sw);

		unsigned select_width = inst->InputSize();
		unsigned data_width = inst->OutputSize();
		unsigned offset_data = 0;
		unsigned offset_select = 0;

		OperWideCaseSelector* selector = (OperWideCaseSelector*) inst->View();

		for (unsigned i = 0 ; i < selector->GetNumBranches() ; ++i) {

			SigSig action(sig_out_val, sig_data_values.extract(offset_data, data_width));
			offset_data += data_width;

			for (unsigned j = 0 ; j < selector->GetNumConditions(i) ; ++j) {
				Array left_bound, right_bound ;
				selector->GetCondition(i, j, &left_bound, &right_bound);

				SigSpec sel_left = sig_select_values.extract(offset_select, select_width);
				offset_select += select_width;

				if (right_bound.Size()) {
					SigSpec sel_right = sig_select_values.extract(offset_select, select_width);
					offset_select += select_width;

					log_assert(sel_right.is_fully_const() && sel_right.is_fully_def());
					log_assert(sel_left.is_fully_const() && sel_right.is_fully_def());

					int32_t left = sel_left.as_int();
					int32_t right = sel_right.as_int();
					int width = sel_left.size();

					for (int32_t i = right; i<left; i++) {
						RTLIL::CaseRule *cs = new RTLIL::CaseRule;
						cs->compare.push_back(RTLIL::Const(i,width));
						cs->actions.push_back(action);
						sw->cases.push_back(cs);
					}
				}

				RTLIL::CaseRule *cs = new RTLIL::CaseRule;
				cs->compare.push_back(sel_left);
				cs->actions.push_back(action);
				sw->cases.push_back(cs);
			}
		}
		RTLIL::CaseRule *cs_default = new RTLIL::CaseRule;
		cs_default->actions.push_back(SigSig(sig_out_val, sig_data_default));
		sw->cases.push_back(cs_default);

		return true;
	}

#ifdef YOSYSHQ_VERIFIC_API_VERSION
	if (inst->Type() == OPER_YOSYSHQ_SET_TAG)
	{
		RTLIL::SigSpec sig_expr = operatorInport(inst, "expr");
		RTLIL::SigSpec sig_set_mask = operatorInport(inst, "set_mask");
		RTLIL::SigSpec sig_clr_mask = operatorInport(inst, "clr_mask");
		RTLIL::SigSpec sig_o = operatorOutput(inst);
		std::string tag = inst->GetAtt("tag") ? verific_unescape(inst->GetAttValue("tag")) : "";
		module->connect(sig_o, module->SetTag(new_verific_id(inst), tag, sig_expr, sig_set_mask, sig_clr_mask));
		return true;
	}
	if (inst->Type() == OPER_YOSYSHQ_GET_TAG)
	{
		std::string tag = inst->GetAtt("tag") ? verific_unescape(inst->GetAttValue("tag")) : "";
		module->connect(operatorOutput(inst),module->GetTag(new_verific_id(inst), tag, operatorInput(inst)));
		return true;
	}
	if (inst->Type() == OPER_YOSYSHQ_OVERWRITE_TAG)
	{
		RTLIL::SigSpec sig_signal = operatorInport(inst, "signal");
		RTLIL::SigSpec sig_set_mask = operatorInport(inst, "set_mask");
		RTLIL::SigSpec sig_clr_mask = operatorInport(inst, "clr_mask");
		std::string tag = inst->GetAtt("tag") ? verific_unescape(inst->GetAttValue("tag")) : "";
		module->addOverwriteTag(new_verific_id(inst), tag, sig_signal, sig_set_mask, sig_clr_mask);
		return true;
	}
	if (inst->Type() == OPER_YOSYSHQ_ORIGINAL_TAG)
	{
		std::string tag = inst->GetAtt("tag") ? verific_unescape(inst->GetAttValue("tag")) : "";
		module->connect(operatorOutput(inst),module->OriginalTag(new_verific_id(inst), tag, operatorInput(inst)));
		return true;
	}
	if (inst->Type() == OPER_YOSYSHQ_FUTURE_FF)
	{
		module->connect(operatorOutput(inst),module->FutureFF(new_verific_id(inst), operatorInput(inst)));
		return true;
	}
#endif

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
			SigBit bit = sigmap(cell->getPort(ID::D));
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
				log("  merging single-bit past_ffs into new %d-bit ff %s.\n", GetSize(sig_d), new_ff);

			for (int i = 0; i < GetSize(sig_d); i++)
				for (auto old_ff : dbits_db[sig_d[i]])
				{
					if (verific_verbose)
						log("    replacing old ff %s on bit %d.\n", old_ff, i);

					SigBit old_q = old_ff->getPort(ID::Q);
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
		if (cell->type != ID($dff)) continue;
		SigBit clock = cell->getPort(ID::CLK);
		bool clock_pol = cell->getParam(ID::CLK_POLARITY).as_bool();
		database[make_pair(clock, int(clock_pol))].insert(cell);
	}

	for (auto it : database)
		merge_past_ffs_clock(it.second, it.first.first, it.first.second);
}

static std::string sha1_if_contain_spaces(std::string str)
{
	if(str.find_first_of(' ') != std::string::npos) {
		std::size_t open = str.find_first_of('(');
		std::size_t closed = str.find_last_of(')');
		if (open != std::string::npos && closed != std::string::npos) {
			std::string content = str.substr(open + 1, closed - open - 1);
			return str.substr(0, open + 1) + sha1(content) + str.substr(closed);
		} else {
			return sha1(str);
		}
	}
	return str;
}

void VerificImporter::recurse_mem_dimensions(RTLIL::Module *module, RTLIL::Memory *memory, Net *net, const char *&ascii_initdata, int max_bits_in_addr, const RTLIL::SigSpec &prefix, TypeRange *typeRange) {
	if (typeRange == nullptr)
		typeRange = net->GetOrigTypeRange();

	auto *nextRange = typeRange->GetNext();
	auto left = typeRange->LeftRangeBound();
	auto right = typeRange->RightRangeBound();
	bool is_up = left < right;
	for (auto i = left; is_up ? i <= right : i >= right; is_up ? i++ : i--) {
		// TODO verific can do u64
		auto max_bits = max_bits_in_addr - prefix.size();
		auto next_sig = SigSpec(Const(i, typeRange->NumBits()));
		auto extra_bits = next_sig.size() - max_bits;
		if (extra_bits > 0) {
			next_sig = next_sig.extract_end(extra_bits);
			auto extra_inc = (1 << extra_bits) - 1;
			i = is_up ? i + extra_inc : i - extra_inc;
		}
		next_sig.append(prefix);
		if (nextRange != nullptr && extra_bits < 0) {
			recurse_mem_dimensions(module, memory, net, ascii_initdata, max_bits_in_addr, next_sig, nextRange);
		} else {
			if (next_sig.size() != max_bits_in_addr) {
				// TODO verific can do u64
				log_error("Expected %d bits for addr but got %d!\n", max_bits_in_addr, next_sig.size());
			}
			Const initval = Const(State::Sx, memory->width);
			bool initval_valid = false;
			if (ascii_initdata) {
				for (int bit_idx = memory->width-1; bit_idx >= 0; bit_idx--) {
					if (*ascii_initdata == 0)
						break;
					if (*ascii_initdata == '0' || *ascii_initdata == '1') {
						initval.set(bit_idx, (*ascii_initdata == '0') ? State::S0 : State::S1);
						initval_valid = true;
					}
					ascii_initdata++;
				}
			}
			if (!next_sig.convertible_to_int())
				log_error("Address %s on RAM for identifier '%s' too wide!\n", log_signal(next_sig), net->Name());
			auto next_idx = next_sig.as_int();
			if (initval_valid) {
				RTLIL::Cell *cell = module->addCell(new_verific_id(net), ID($meminit));
				cell->parameters[ID::WORDS] = 1;
				cell->setPort(ID::ADDR, next_idx);
				cell->setPort(ID::DATA, initval);
				cell->parameters[ID::MEMID] = RTLIL::Const(memory->name.str());
				cell->parameters[ID::ABITS] = 32;
				cell->parameters[ID::WIDTH] = memory->width;
				cell->parameters[ID::PRIORITY] = RTLIL::Const(module->twines().autoidx()-1);
			}
			memory->start_offset = min(memory->start_offset, next_idx);
			memory->size = max(memory->size, next_idx);
		}
	}
}

void VerificImporter::import_netlist(RTLIL::Design *design, Netlist *nl, std::map<std::string,Netlist*> &nl_todo, bool norename)
{
	std::string netlist_name = nl->GetAtt(" \\top") || is_blackbox(nl) ? nl->CellBaseName() : nl->Owner()->Name();
	std::string module_name = netlist_name;

	if (nl->IsOperator() || nl->IsPrimitive()) {
		module_name = "$verific$" + module_name;
	} else {
		if (!norename && *nl->Name() && !is_blackbox(nl)) {
			module_name += "(";
			module_name += nl->Name();
			module_name += ")";
		}
		module_name = "\\" + sha1_if_contain_spaces(module_name);
	}

	{
		Array ram_nets ;
		MapIter mem_mi;
		Net *mem_net;
		FOREACH_NET_OF_NETLIST(nl, mem_mi, mem_net)
		{
			if (!mem_net->IsRamNet()) continue ;

			if (mem_net->GetAtt("mem2reg"))
				ram_nets.Insert(mem_net) ;
		}
		unsigned i ;
		FOREACH_ARRAY_ITEM(&ram_nets, i, mem_net) {
			log("Bit blasting RAM for identifier '%s'\n", mem_net->Name());
			mem_net->BlastNet();
		}
		nl->RemoveDanglingLogic(0);
	}

	netlist = nl;

	IdString module_id = design->twines().add(module_name);
	if (design->has(module_id)) {
		if (!nl->IsOperator() && !is_blackbox(nl))
			log_cmd_error("Re-definition of module `%s'.\n", netlist_name);
		return;
	}

	module = new RTLIL::Module(design);
	module->name = module_id;
	design->add(module);

	if (is_blackbox(nl)) {
		log("Importing blackbox module %s.\n", module);
		module->set_bool_attribute(ID::blackbox);
	} else {
		log("Importing module %s.\n", module);
	}
	import_attributes(module->attributes, nl, nl);
	if (module->name.isPublic())
		module->set_string_attribute(ID::hdlname, nl->CellBaseName());
	module->set_string_attribute(ID(library), nl->Owner()->Owner()->Name());
#ifdef VERIFIC_VHDL_SUPPORT
	if (nl->IsFromVhdl()) {
		NameSpace name_space(0);
		char *architecture_name = name_space.ReName(nl->Name()) ;
		module->set_string_attribute(ID(architecture), (architecture_name) ? architecture_name : nl->Name());
	}
#endif
	const char *param_name ;
	const char *param_value ;
	MapIter mi;
	FOREACH_PARAMETER_OF_NETLIST(nl, mi, param_name, param_value) {
		IdString param_id = design->twines().add(RTLIL::escape_id(param_name));
		module->avail_parameters(param_id);
		const TypeRange *tr = nl->GetTypeRange(param_name) ;
		const char* type_name = (tr) ? tr->GetTypeName() : nullptr;
		module->parameter_default_values[param_id] = verific_const(type_name, param_value, nl);
	}

	SetIter si;
	MapIter mi2;
	Port *port;
	PortBus *portbus;
	Net *net;
	NetBus *netbus;
	Instance *inst;
	PortRef *pr;
	Att *attr;

	FOREACH_ATTRIBUTE(nl, mi, attr) {
		if (!strcmp(attr->Key(), "noblackbox"))
			module->set_bool_attribute(ID::blackbox, false);
	}

	FOREACH_PORT_OF_NETLIST(nl, mi, port)
	{
		if (port->Bus())
			continue;

		if (verific_verbose)
			log("  importing port %s.\n", port->Name());

		RTLIL::Wire *wire = module->addWire(RTLIL::escape_id(port->Name()));
		import_attributes(wire->attributes, port, nl, 1);

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
		wire->upto = portbus->IsUp();
		import_attributes(wire->attributes, portbus, nl, portbus->Size());
		if (portbus->Size() == 1)
			wire->set_bool_attribute(ID::single_bit_vector);
		SetIter si ;
		Port *port ;
		FOREACH_PORT_OF_PORTBUS(portbus, si, port) {
			wire->port_id = nl->IndexOf(port) + 1;
			import_attributes(wire->attributes, port->GetNet(), nl, portbus->Size());
			break;
		}
		bool portbus_input = portbus->GetDir() == DIR_INOUT || portbus->GetDir() == DIR_IN;
		if (portbus_input)
			wire->port_input = true;
		if (portbus->GetDir() == DIR_INOUT || portbus->GetDir() == DIR_OUT)
			wire->port_output = true;

		for (int i = portbus->LeftIndex();; i += portbus->IsUp() ? +1 : -1) {
			if (portbus->ElementAtIndex(i) && portbus->ElementAtIndex(i)->GetNet()) {
				bool bit_input = portbus_input;
				if (portbus->GetDir() == DIR_NONE)  {
					Port *p = portbus->ElementAtIndex(i);
					bit_input = p->GetDir() == DIR_INOUT || p->GetDir() == DIR_IN;
					if (bit_input)
						wire->port_input = true;
					if (p->GetDir() == DIR_INOUT || p->GetDir() == DIR_OUT)
						wire->port_output = true;
				}
				net = portbus->ElementAtIndex(i)->GetNet();
				int bitidx = wire->upto ? (wire->width - 1 - (i - wire->start_offset)) : (i - wire->start_offset);
				RTLIL::SigBit bit(wire, bitidx);
				if (net_map.count(net) == 0)
					net_map[net] = bit;
				else if (bit_input)
					module->connect(net_map_at(net), bit);
				else
					module->connect(bit, net_map_at(net));
			}
			if (i == portbus->RightIndex())
				break;
		}
	}

	module->fixup_ports();

	dict<Net*, char> init_nets;
	pool<Net*> anyconst_nets, anyseq_nets;
	pool<Net*> allconst_nets, allseq_nets;
	any_all_nets.clear();

	FOREACH_NET_OF_NETLIST(nl, mi, net)
	{
		if (net->IsRamNet())
		{
			IdString memory_name = design->twines().add(RTLIL::escape_id(net->Name()));
			log_assert(module->count_id(memory_name) == 0);
			RTLIL::Memory *memory = module->addMemory(memory_name);
			import_attributes(memory->attributes, net, nl);

			int number_of_bits = net->Size();
			int min_bits_in_word = number_of_bits;
			int max_bits_in_addr = 0;

			// get the size of each memory access
			FOREACH_PORTREF_OF_NET(net, si, pr) {
				auto *inst = pr->GetInst();
				int bits_in_word;
				if (inst->Type() == OPER_READ_PORT)
					bits_in_word = inst->OutputSize();
				else if (inst->Type() == OPER_WRITE_PORT || inst->Type() == OPER_CLOCKED_WRITE_PORT)
					bits_in_word = inst->Input2Size();
				else
					log_error("%sVerific RamNet %s is connected to unsupported instance type %s (%s).\n", announce_src_location(inst),
							net->Name(), inst->View()->Owner()->Name(), inst->Name());

				if (bits_in_word < min_bits_in_word) {
					min_bits_in_word = bits_in_word;
					max_bits_in_addr = inst->Input1Size();
				}
			}

			int number_of_words = number_of_bits / min_bits_in_word;

			memory->width = min_bits_in_word;
			memory->size = 0;
			memory->start_offset = INT_MAX;

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
			}

			// process initdata and fixup min/max address
			auto prefix = SigSpec();
			recurse_mem_dimensions(module, memory, net, ascii_initdata, max_bits_in_addr, prefix);

			auto min_idx = memory->start_offset;
			auto max_idx = memory->size;
			memory->size = max_idx - min_idx + 1;

			// sanity check we haven't shrunk the memory
			if (memory->size < number_of_words)
				log_error("Expected memory of size %d words, but got %d for address range %d to %d (inclusive)\n", number_of_words, memory->size, min_idx, max_idx);

			// warn on oversize memories
			// TODO consider using a minimum ratio?
			if (memory->size > number_of_words) {
				float ratio = memory->size / (float)number_of_words;
				log_warning("RAM for identifier '%s' may be up to %.0f%% oversize due to addressing\n", net->Name(), (ratio-1)*100);
				log_debug("Expected memory of size %d words, but got %d for address range %d to %d (inclusive)\n", number_of_words, memory->size, min_idx, max_idx);
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

		RTLIL::IdString wire_name = module->uniquify(mode_names || net->IsUserDeclared() ? design->twines().add(RTLIL::escape_id(net->Name())) : new_verific_id(net));

		RTLIL::Wire *wire = module->addWire(wire_name);

		if (verific_verbose)
			log("  importing net %s as %s.\n", net->Name(), wire);
		import_attributes(wire->attributes, net, nl, 1);

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
			RTLIL::IdString wire_name = module->uniquify(mode_names || netbus->IsUserDeclared() ? design->twines().add(RTLIL::escape_id(netbus->Name())) : new_verific_id(netbus));

			RTLIL::Wire *wire = module->addWire(wire_name, netbus->Size());

			if (verific_verbose)
				log("  importing netbus %s as %s.\n", netbus->Name(), wire);
			wire->start_offset = min(netbus->LeftIndex(), netbus->RightIndex());
			wire->upto = netbus->IsUp();
			MapIter mibus;
			FOREACH_NET_OF_NETBUS(netbus, mibus, net) {
				if (net)
					import_attributes(wire->attributes, net, nl, netbus->Size());
				break;
			}
			import_attributes(wire->attributes, netbus, nl, netbus->Size());
			if (netbus->Size() == 1)
				wire->set_bool_attribute(ID::single_bit_vector);

			RTLIL::Const initval = Const(State::Sx, GetSize(wire));
			bool initval_valid = false;

			for (int i = netbus->LeftIndex();; i += netbus->IsUp() ? +1 : -1)
			{
				if (netbus->ElementAtIndex(i))
				{
					int bitidx = wire->upto ? (wire->width - 1 - (i - wire->start_offset)) : (i - wire->start_offset);
					net = netbus->ElementAtIndex(i);
					RTLIL::SigBit bit(wire, bitidx);

					if (init_nets.count(net)) {
						if (init_nets.at(net) == '0')
							initval.set(bitidx, State::S0);
						if (init_nets.at(net) == '1')
							initval.set(bitidx, State::S1);
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
				wire->attributes[ID::init] = initval;
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

		if (bit.wire->attributes.count(ID::init))
			initval = bit.wire->attributes.at(ID::init);

		if (GetSize(initval) < GetSize(bit.wire))
			initval.resize(GetSize(bit.wire), State::Sx);

		if (it.second == '0')
			initval.set(bit.offset, State::S0);
		if (it.second == '1')
			initval.set(bit.offset, State::S1);

		bit.wire->attributes[ID::init] = initval;
	}

	for (auto net : anyconst_nets)
		module->connect(net_map_at(net), module->Anyconst(new_verific_id(net)));

	for (auto net : anyseq_nets)
		module->connect(net_map_at(net), module->Anyseq(new_verific_id(net)));

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	pool<Instance*> sva_asserts;
	pool<Instance*> sva_assumes;
	pool<Instance*> sva_covers;
	pool<Instance*> sva_triggers;
	pool<RTLIL::Cell*> past_ffs;
#endif

	FOREACH_INSTANCE_OF_NETLIST(nl, mi, inst)
	{
		RTLIL::IdString inst_name = module->uniquify(mode_names || inst->IsUserDeclared() ? design->twines().add(RTLIL::escape_id(inst->Name())) : new_verific_id(inst));

		if (verific_verbose)
			log("  importing cell %s (%s) as %s.\n", inst->Name(), inst->View()->Owner()->Name(), PooledName(design, inst_name).unescape());

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
			RTLIL::Memory *memory = module->memories.at(module->twines().find(RTLIL::escape_id(inst->GetInput()->Name())), nullptr);
			if (!memory)
				log_error("%sMemory net '%s' missing, possibly no driver, use verific -flatten.\n", announce_src_location(inst), inst->GetInput()->Name());

			int numchunks = int(inst->OutputSize()) / memory->width;
			int chunksbits = ceil_log2(numchunks);

			for (int i = 0; i < numchunks; i++)
			{
				RTLIL::SigSpec addr = {operatorInput1(inst), RTLIL::Const(i, chunksbits)};
				RTLIL::SigSpec data = operatorOutput(inst).extract(i * memory->width, memory->width);

				RTLIL::Cell *cell = module->addCell(numchunks == 1 ? inst_name :
						module->twines().add(inst_name, stringf("_%d", i)), ID($memrd));
				cell->parameters[ID::MEMID] = memory->name.str();
				cell->parameters[ID::CLK_ENABLE] = false;
				cell->parameters[ID::CLK_POLARITY] = true;
				cell->parameters[ID::TRANSPARENT] = false;
				cell->parameters[ID::ABITS] = GetSize(addr);
				cell->parameters[ID::WIDTH] = GetSize(data);
				import_attributes(cell->attributes, inst);
				cell->setPort(ID::CLK, RTLIL::State::Sx);
				cell->setPort(ID::EN, RTLIL::State::Sx);
				cell->setPort(ID::ADDR, addr);
				cell->setPort(ID::DATA, data);
			}
			continue;
		}

		if (inst->Type() == OPER_WRITE_PORT || inst->Type() == OPER_CLOCKED_WRITE_PORT)
		{
			RTLIL::Memory *memory = module->memories.at(module->twines().find(RTLIL::escape_id(inst->GetOutput()->Name())), nullptr);
			if (!memory)
				log_error("%sMemory net '%s' missing, possibly no driver, use verific -flatten.\n", announce_src_location(inst), inst->GetInput()->Name());
			int numchunks = int(inst->Input2Size()) / memory->width;
			int chunksbits = ceil_log2(numchunks);

			for (int i = 0; i < numchunks; i++)
			{
				RTLIL::SigSpec addr = {operatorInput1(inst), RTLIL::Const(i, chunksbits)};
				RTLIL::SigSpec data = operatorInput2(inst).extract(i * memory->width, memory->width);

				RTLIL::Cell *cell = module->addCell(numchunks == 1 ? inst_name :
						module->twines().add(inst_name, stringf("_%d", i)), ID($memwr));
				cell->parameters[ID::MEMID] = memory->name.str();
				cell->parameters[ID::CLK_ENABLE] = false;
				cell->parameters[ID::CLK_POLARITY] = true;
				cell->parameters[ID::PRIORITY] = 0;
				cell->parameters[ID::ABITS] = GetSize(addr);
				cell->parameters[ID::WIDTH] = GetSize(data);
				import_attributes(cell->attributes, inst);
				cell->setPort(ID::EN, RTLIL::SigSpec(net_map_at(inst->GetControl())).repeat(GetSize(data)));
				cell->setPort(ID::CLK, RTLIL::State::S0);
				cell->setPort(ID::ADDR, addr);
				cell->setPort(ID::DATA, data);

				if (inst->Type() == OPER_CLOCKED_WRITE_PORT) {
					cell->parameters[ID::CLK_ENABLE] = true;
					cell->setPort(ID::CLK, net_map_at(inst->GetClock()));
				}
			}
			continue;
		}

		if (!mode_gates) {
			if (import_netlist_instance_cells(inst, inst_name))
				continue;
			if (inst->IsOperator() && !verific_sva_prims.count(inst->Type()))
				log_warning("%sUnsupported Verific operator: %s (fallback to gate level implementation provided by verific)\n", announce_src_location(inst), inst->View()->Owner()->Name());
		} else {
			if (import_netlist_instance_gates(inst, inst_name))
				continue;
		}

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
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

			unsigned width = inst->Input1Size();

			SigSpec sig_d, sig_dx, sig_qx, sig_o, sig_ox;
			sig_dx = module->addWire(new_verific_id(inst), width * 2);
			sig_qx = module->addWire(new_verific_id(inst), width * 2);
			sig_ox = module->addWire(new_verific_id(inst), width * 2);

			for (int i = int(width)-1; i >= 0; i--){
				sig_d.append(net_map_at(inst->GetInput1Bit(i)));
				sig_o.append(net_map_at(inst->GetOutputBit(i)));
			}

			if (verific_verbose) {
				for (unsigned i = 0; i < width; i++) {
					log("    NEX with A=%s, B=0, Y=%s.\n",
							log_signal(sig_d[i]), log_signal(sig_dx[i]));
					log("    EQX with A=%s, B=1, Y=%s.\n",
							log_signal(sig_d[i]), log_signal(sig_dx[i + width]));
				}
				log("    %sedge FF with D=%s, Q=%s, C=%s.\n", clocking.posedge ? "pos" : "neg",
						log_signal(sig_dx), log_signal(sig_qx), log_signal(clocking.clock_sig));
				log("    XNOR with A=%s, B=%s, Y=%s.\n",
						log_signal(sig_dx), log_signal(sig_qx), log_signal(sig_ox));
				log("    AND with A=%s, B=%s, Y=%s.\n",
						log_signal(sig_ox.extract(0, width)), log_signal(sig_ox.extract(width, width)), log_signal(sig_o));
			}

			for (unsigned i = 0; i < width; i++) {
				module->addNex(new_verific_id(inst), sig_d[i], State::S0, sig_dx[i]);
				module->addEqx(new_verific_id(inst), sig_d[i], State::S1, sig_dx[i + width]);
			}

			Const qx_init = Const(State::S1, width);
			qx_init.resize(2 * width, State::S0);

			clocking.addDff(new_verific_id(inst), sig_dx, sig_qx, qx_init);
			module->addXnor(new_verific_id(inst), sig_dx, sig_qx, sig_ox);

			module->addAnd(new_verific_id(inst), sig_ox.extract(0, width), sig_ox.extract(width, width), sig_o);

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
			SigSpec sig_dx = module->addWire(new_verific_id(inst), 2);
			SigSpec sig_qx = module->addWire(new_verific_id(inst), 2);

			if (verific_verbose) {
				log("    NEX with A=%s, B=0, Y=%s.\n",
						log_signal(sig_d), log_signal(sig_dx[0]));
				log("    EQX with A=%s, B=1, Y=%s.\n",
						log_signal(sig_d), log_signal(sig_dx[1]));
				log("    %sedge FF with D=%s, Q=%s, C=%s.\n", clocking.posedge ? "pos" : "neg",
						log_signal(sig_dx), log_signal(sig_qx), log_signal(clocking.clock_sig));
				log("    EQ with A=%s, B=%s, Y=%s.\n",
						log_signal(sig_dx), log_signal(sig_qx), log_signal(sig_o));
			}

			module->addNex(new_verific_id(inst), sig_d, State::S0, sig_dx[0]);
			module->addEqx(new_verific_id(inst), sig_d, State::S1, sig_dx[1]);

			clocking.addDff(new_verific_id(inst), sig_dx, sig_qx, Const(1, 2));
			module->addEq(new_verific_id(inst), sig_dx, sig_qx, sig_o);

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
			SigBit sig_d_no_x = module->addWire(new_verific_id(inst));

			if (verific_verbose) {
				log("    EQX with A=%s, B=%d, Y=%s.\n",
						log_signal(sig_d), inst->Type() == PRIM_SVA_ROSE, log_signal(sig_d_no_x));
				log("    %sedge FF with D=%s, Q=%s, C=%s.\n", clocking.posedge ? "pos" : "neg",
						log_signal(sig_d_no_x), log_signal(sig_q), log_signal(clocking.clock_sig));
				log("    EQ with A={%s, %s}, B={0, 1}, Y=%s.\n",
						log_signal(sig_q), log_signal(sig_d_no_x), log_signal(sig_o));
			}

			module->addEqx(new_verific_id(inst), sig_d, inst->Type() == PRIM_SVA_ROSE ? State::S1 : State::S0, sig_d_no_x);
			clocking.addDff(new_verific_id(inst), sig_d_no_x, sig_q, State::S0);
			module->addEq(new_verific_id(inst), {sig_q, sig_d_no_x}, Const(1, 2), sig_o);

			if (!mode_keep)
				continue;
		}
#endif

#ifdef YOSYSHQ_VERIFIC_API_VERSION
		if (inst->Type() == PRIM_YOSYSHQ_INITSTATE)
		{
			if (verific_verbose)
				log("   adding YosysHQ init state\n");
			SigBit initstate = module->Initstate(new_verific_id(inst));
			SigBit sig_o = net_map_at(inst->GetOutput());
			module->connect(sig_o, initstate);

			if (!mode_keep)
				continue;
		}
#endif

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

			Cell *cell = module->addAssert(new_verific_id(inst), cond, State::S1);
			import_attributes(cell->attributes, inst);
			continue;
		}

		if (inst->IsPrimitive())
		{
			if (!mode_keep)
				log_error("%sUnsupported Verific primitive %s of type %s\n", announce_src_location(inst), inst->Name(), inst->View()->Owner()->Name());

			if (!verific_sva_prims.count(inst->Type()))
				log_warning("%sUnsupported Verific primitive %s of type %s\n", announce_src_location(inst), inst->Name(), inst->View()->Owner()->Name());
		}

	import_verific_cells:
		std::string inst_type = is_blackbox(inst->View()) ? inst->View()->CellBaseName() : inst->View()->Owner()->Name();

		nl_todo[inst_type] = inst->View();

		if (inst->View()->IsOperator() || inst->View()->IsPrimitive()) {
			inst_type = "$verific$" + inst_type;
		} else {
			if (*inst->View()->Name() && !is_blackbox(inst->View())) {
				inst_type += "(";
				inst_type += inst->View()->Name();
				inst_type += ")";
			}
			inst_type = "\\" + sha1_if_contain_spaces(inst_type);
		}

		RTLIL::Cell *cell = module->addCell(inst_name, inst_type);
		import_attributes(cell->attributes, inst);

		if (inst->IsPrimitive() && mode_keep)
			cell->attributes[ID::keep] = 1;

		dict<IdString, vector<SigBit>> cell_port_conns;

		if (verific_verbose)
			log("    ports in verific db:\n");

		const char *param_name ;
		const char *param_value ;
		if (is_blackbox(inst->View())) {
			FOREACH_PARAMETER_OF_INST(inst, mi2, param_name, param_value) {
				const TypeRange *tr = inst->View()->GetTypeRange(param_name) ;
				const char* type_name = (tr) ? tr->GetTypeName() : nullptr;
				cell->setParam(RTLIL::escape_id(param_name), verific_const(type_name, param_value, inst->View()));
			}
		}

		FOREACH_PORTREF_OF_INST(inst, mi2, pr) {
			if (verific_verbose)
				log("      .%s(%s)\n", pr->GetPort()->Name(), pr->GetNet()->Name());
			const char *port_name = pr->GetPort()->Name();
			int port_offset = 0;
			if (pr->GetPort()->Bus()) {
				port_name = pr->GetPort()->Bus()->Name();
				int msb_index = pr->GetPort()->Bus()->LeftIndex();
				int lsb_index = pr->GetPort()->Bus()->RightIndex();
				int index_of_port = pr->GetPort()->Bus()->IndexOf(pr->GetPort());
				port_offset =  index_of_port - min(msb_index, lsb_index);
				// In cases where the msb order is flipped we need to make sure
				// that the indices match LSB = 0 order to match the std::vector
				// to SigSpec LSB = 0 precondition.
				if (lsb_index > msb_index) {
					port_offset = abs(port_offset - (lsb_index - min(msb_index, lsb_index)));
				}
			}
			IdString port_name_id = module->twines().add(RTLIL::escape_id(port_name));
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
				log("      .%s(%s)\n", PooledName(module, it.first).unescape(), log_signal(it.second));
			cell->setPort(it.first, it.second);
		}
	}

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
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
#endif

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
			if (!wire->attributes.count(ID::init))
				continue;

			Const &initval = wire->attributes.at(ID::init);
			for (int i = 0; i < GetSize(initval); i++)
			{
				if (initval[i] != State::S0 && initval[i] != State::S1)
					continue;

				if (non_ff_bits.count(SigBit(wire, i)))
					initval.set(i, State::Sx);
			}

			if (wire->port_input) {
				wire->attributes[ID::defaultvalue] = Const(initval);
				wire->attributes.erase(ID::init);
			} else if (initval.is_fully_undef())
				wire->attributes.erase(ID::init);
		}
	}

	if (num_sva_continue) {
		log_warning("Encountered %d items containing unsupported SVA!\n", num_sva_continue);
		log_warning("Unsupported SVA imported as 'x and marked using the `unsupported_sva' attribute due to -sva-continue-on-err.\n");
	}
	num_sva_continue = 0;
}

YOSYS_NAMESPACE_END
