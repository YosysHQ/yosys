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
#include "libs/sha1/sha1.h"
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

#include "Array.h"
#include "RuntimeFlags.h"
#ifdef VERIFIC_HIER_TREE_SUPPORT
#include "hier_tree.h"
#endif

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
#include "veri_file.h"
#include "VeriModule.h"
#include "VeriWrite.h"
#include "VeriLibrary.h"
#include "VeriExpression.h"
#endif

#ifdef VERIFIC_VHDL_SUPPORT
#include "vhdl_file.h"
#include "VhdlIdDef.h"
#include "VhdlUnits.h"
#include "NameSpace.h"
#endif

#ifdef VERIFIC_EDIF_SUPPORT
#include "edif_file.h"
#endif

#ifdef VERIFIC_LIBERTY_SUPPORT
#include "synlib_file.h"
#include "SynlibGroup.h"
#endif

#include "VerificStream.h"
#include "FileSystem.h"

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
#include "VerificExtensions.h"
#endif

#ifndef YOSYSHQ_VERIFIC_API_VERSION
#warning "Only YosysHQ flavored Verific is fully supported. Please contact office@yosyshq.com for commercial support for Yosys+Verific."
#else
#if YOSYSHQ_VERIFIC_API_VERSION < 20230901
#  error "Please update your version of YosysHQ flavored Verific."
#endif
#endif

#if !defined(VERIFIC_VHDL_SUPPORT) && !defined(VERIFIC_SYSTEMVERILOG_SUPPORT)
#error "At least one of HDL languages must be enabled."
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

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
vector<string> verific_incdirs, verific_libdirs, verific_libexts;
#endif

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

	if (log_verific_callback) {
		string full_message = stringf("%s%s\n", message_prefix.c_str(), message.c_str());
#ifdef VERIFIC_LINEFILE_INCLUDES_COLUMNS 
		log_verific_callback(int(msg_type), message_id, LineFile::GetFileName(linefile), 
			linefile ? linefile->GetLeftLine() : 0, linefile ? linefile->GetLeftCol() : 0, 
			linefile ? linefile->GetRightLine() : 0, linefile ? linefile->GetRightCol() : 0, full_message.c_str());
#else
		log_verific_callback(int(msg_type), message_id, LineFile::GetFileName(linefile), 
			linefile ? LineFile::GetLineNo(linefile) : 0, 0, 
			linefile ? LineFile::GetLineNo(linefile) : 0, 0, full_message.c_str());
#endif
	} else {
		if (msg_type == VERIFIC_ERROR || msg_type == VERIFIC_WARNING || msg_type == VERIFIC_PROGRAM_ERROR)
			log_warning_noprefix("%s%s\n", message_prefix.c_str(), message.c_str());
		else
			log("%s%s\n", message_prefix.c_str(), message.c_str());
	}
	if (verific_error_msg.empty() && (msg_type == VERIFIC_ERROR || msg_type == VERIFIC_PROGRAM_ERROR))
		verific_error_msg = message;
}

void set_verific_logging(void (*cb)(int msg_type, const char *message_id, const char* file_path, unsigned int left_line, unsigned int left_col, unsigned int right_line, unsigned int right_col, const char *msg))
{
	Message::SetConsoleOutput(0);
	Message::RegisterCallBackMsg(msg_func);
	log_verific_callback = cb;
}

string get_full_netlist_name(Netlist *nl)
{
	if (nl->NumOfRefs() == 1) {
		Instance *inst = (Instance*)nl->GetReferences()->GetLast();
		return get_full_netlist_name(inst->Owner()) + "." + inst->Name();
	}

	return nl->CellBaseName();
}

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
class YosysStreamCallBackHandler : public VerificStreamCallBackHandler
{
public:
	YosysStreamCallBackHandler() : VerificStreamCallBackHandler() { }
	virtual ~YosysStreamCallBackHandler() { }

	virtual verific_stream *GetSysCallStream(const char *file_path)
	{
		if (!file_path) return nullptr;

		linefile_type src_loc = GetFromLocation();

		char *this_file_name = nullptr;
		if (src_loc && !FileSystem::IsAbsolutePath(file_path)) {
			const char *src_file_name = LineFile::GetFileName(src_loc);
			char *dir_name = FileSystem::DirectoryPath(src_file_name);
			if (dir_name) {
				this_file_name = Strings::save(dir_name, "/", file_path);
				Strings::free(dir_name);
				file_path = this_file_name;
			}
		}
		verific_stream *strm = new verific_ifstream(file_path);
		Strings::free(this_file_name);
		return strm;
	}
};

YosysStreamCallBackHandler verific_read_cb;
#endif

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
		s += stringf("$%s:%d", RTLIL::encode_filename(Verific::LineFile::GetFileName(obj->Linefile())).c_str(), Verific::LineFile::GetLineNo(obj->Linefile()));
	s += stringf("$%d", autoidx++);
	return s;
}

RTLIL::Const mkconst_str(const std::string &str)
{
	RTLIL::Const val;
	std::vector<RTLIL::State> data;
	data.reserve(str.size() * 8);
	for (size_t i = 0; i < str.size(); i++) {
		unsigned char ch = str[str.size() - i - 1];
		for (int j = 0; j < 8; j++) {
			data.push_back((ch & 1) ? State::S1 : State::S0);
			ch = ch >> 1;
		}
	}
	val.bits = data;
	val.flags |= RTLIL::CONST_FLAG_STRING;
	return val;
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
	log_error("Error parsing VHDL %s.\n", typ.c_str());
}

static const RTLIL::Const extract_vhdl_bit_vector(std::string &val, std::string &typ)
{
	if (val.size()>1 && val[0]=='\"' && val.back()=='\"') {
		RTLIL::Const c = RTLIL::Const::from_string(val.substr(1,val.size()-2));
		if (typ == "signed")
			c.flags |= RTLIL::CONST_FLAG_SIGNED;
		return c;
	}
	log_error("Error parsing VHDL %s.\n", typ.c_str());
}

static const RTLIL::Const extract_vhdl_integer(std::string &val)
{
	char *end;
	return RTLIL::Const((int)std::strtol(val.c_str(), &end, 10), 32);
}

static const RTLIL::Const extract_vhdl_char(std::string &val)
{
	if (val.size()==3 && val[0]=='\"' && val.back()=='\"')
		return RTLIL::Const((int)val[1], 32);
	log_error("Error parsing VHDL character.\n");
}

static const RTLIL::Const extract_real_value(std::string &val)
{
	RTLIL::Const c = mkconst_str(val);
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
		c = RTLIL::Const((int)decimal, 32);
	} else if (val == "false") {
		c = RTLIL::Const::from_string("0");
	} else if (val == "true") {
		c = RTLIL::Const::from_string("1");
	} else {
		c = mkconst_str(val);
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
		c = RTLIL::Const((int)decimal, 32);
	} else if (allow_string) {
		c = RTLIL::Const(val);
	} else {
		c = mkconst_str(val);
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

void VerificImporter::import_attributes(dict<RTLIL::IdString, RTLIL::Const> &attributes, DesignObj *obj, Netlist *nl)
{
	if (!obj)
		return;

	MapIter mi;
	Att *attr;

#ifdef VERIFIC_LINEFILE_INCLUDES_COLUMNS 
	if (obj->Linefile())
		attributes[ID::src] = stringf("%s:%d.%d-%d.%d", LineFile::GetFileName(obj->Linefile()), obj->Linefile()->GetLeftLine(), obj->Linefile()->GetLeftCol(), obj->Linefile()->GetRightLine(), obj->Linefile()->GetRightCol());
#else
	if (obj->Linefile())
		attributes[ID::src] = stringf("%s:%d", LineFile::GetFileName(obj->Linefile()), LineFile::GetLineNo(obj->Linefile()));
#endif

	FOREACH_ATTRIBUTE(obj, mi, attr) {
		if (attr->Key()[0] == ' ' || attr->Value() == nullptr)
			continue;
		attributes[RTLIL::escape_id(attr->Key())] = verific_const(nullptr, attr->Value(), obj);
	}

	if (nl) {
		auto type_range = nl->GetTypeRange(obj->Name());
		if (!type_range)
			return;
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

				attributes.emplace(stringf("\\enum_value_%s", value.as_string().c_str()), RTLIL::escape_id(k));
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
						attributes.emplace(stringf("\\enum_value_%s", q), RTLIL::escape_id(k));
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
							attributes.emplace(stringf("\\enum_value_%s", q), RTLIL::escape_id(k));
							free(q);
						}
					}
				}
				if (p == nullptr)
					log_error("Expected TypeRange value '%s' to be of form \"<binary>\" or <binary>.\n", v);
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
				log("  merging single-bit past_ffs into new %d-bit ff %s.\n", GetSize(sig_d), log_id(new_ff));

			for (int i = 0; i < GetSize(sig_d); i++)
				for (auto old_ff : dbits_db[sig_d[i]])
				{
					if (verific_verbose)
						log("    replacing old ff %s on bit %d.\n", log_id(old_ff), i);

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
		module->set_bool_attribute(ID::blackbox);
	} else {
		log("Importing module %s.\n", RTLIL::id2cstr(module->name));
	}
	import_attributes(module->attributes, nl, nl);
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
		module->avail_parameters(RTLIL::escape_id(param_name));
		const TypeRange *tr = nl->GetTypeRange(param_name) ;
		module->parameter_default_values[RTLIL::escape_id(param_name)] = verific_const(tr->GetTypeName(), param_value, nl);
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
		import_attributes(wire->attributes, port, nl);

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
		import_attributes(wire->attributes, portbus, nl);
		SetIter si ;
		Port *port ;
		FOREACH_PORT_OF_PORTBUS(portbus, si, port) {
			import_attributes(wire->attributes, port->GetNet(), nl);
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
			import_attributes(memory->attributes, net, nl);

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
						RTLIL::Cell *cell = module->addCell(new_verific_id(net), ID($meminit));
						cell->parameters[ID::WORDS] = 1;
						if (net->GetOrigTypeRange()->LeftRangeBound() < net->GetOrigTypeRange()->RightRangeBound())
							cell->setPort(ID::ADDR, word_idx);
						else
							cell->setPort(ID::ADDR, memory->size - word_idx - 1);
						cell->setPort(ID::DATA, initval);
						cell->parameters[ID::MEMID] = RTLIL::Const(memory->name.str());
						cell->parameters[ID::ABITS] = 32;
						cell->parameters[ID::WIDTH] = memory->width;
						cell->parameters[ID::PRIORITY] = RTLIL::Const(autoidx-1);
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
		import_attributes(wire->attributes, net, nl);

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
			wire->upto = netbus->IsUp();
			MapIter mibus;
			FOREACH_NET_OF_NETBUS(netbus, mibus, net) {
				if (net)
					import_attributes(wire->attributes, net, nl);
				break;
			}
			import_attributes(wire->attributes, netbus, nl);

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

		while (GetSize(initval) < GetSize(bit.wire))
			initval.bits.push_back(State::Sx);

		if (it.second == '0')
			initval.bits.at(bit.offset) = State::S0;
		if (it.second == '1')
			initval.bits.at(bit.offset) = State::S1;

		bit.wire->attributes[ID::init] = initval;
	}

	for (auto net : anyconst_nets)
		module->connect(net_map_at(net), module->Anyconst(new_verific_id(net)));

	for (auto net : anyseq_nets)
		module->connect(net_map_at(net), module->Anyseq(new_verific_id(net)));

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	pool<Instance*, hash_ptr_ops> sva_asserts;
	pool<Instance*, hash_ptr_ops> sva_assumes;
	pool<Instance*, hash_ptr_ops> sva_covers;
	pool<Instance*, hash_ptr_ops> sva_triggers;
#endif

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
			RTLIL::Memory *memory = module->memories.at(RTLIL::escape_id(inst->GetInput()->Name()), nullptr);
			if (!memory)
				log_error("Memory net '%s' missing, possibly no driver, use verific -flatten.\n", inst->GetInput()->Name());

			int numchunks = int(inst->OutputSize()) / memory->width;
			int chunksbits = ceil_log2(numchunks);

			for (int i = 0; i < numchunks; i++)
			{
				RTLIL::SigSpec addr = {operatorInput1(inst), RTLIL::Const(i, chunksbits)};
				RTLIL::SigSpec data = operatorOutput(inst).extract(i * memory->width, memory->width);

				RTLIL::Cell *cell = module->addCell(numchunks == 1 ? inst_name :
						RTLIL::IdString(stringf("%s_%d", inst_name.c_str(), i)), ID($memrd));
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
			RTLIL::Memory *memory = module->memories.at(RTLIL::escape_id(inst->GetOutput()->Name()), nullptr);
			if (!memory)
				log_error("Memory net '%s' missing, possibly no driver, use verific -flatten.\n", inst->GetInput()->Name());
			int numchunks = int(inst->Input2Size()) / memory->width;
			int chunksbits = ceil_log2(numchunks);

			for (int i = 0; i < numchunks; i++)
			{
				RTLIL::SigSpec addr = {operatorInput1(inst), RTLIL::Const(i, chunksbits)};
				RTLIL::SigSpec data = operatorInput2(inst).extract(i * memory->width, memory->width);

				RTLIL::Cell *cell = module->addCell(numchunks == 1 ? inst_name :
						RTLIL::IdString(stringf("%s_%d", inst_name.c_str(), i)), ID($memwr));
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
				log_warning("Unsupported Verific operator: %s (fallback to gate level implementation provided by verific)\n", inst->View()->Owner()->Name());
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
			qx_init.bits.resize(2 * width, State::S0);

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
				cell->setParam(RTLIL::escape_id(param_name), verific_const(tr->GetTypeName(), param_value, inst->View()));
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
				// that the indicies match LSB = 0 order to match the std::vector
				// to SigSpec LSB = 0 precondition.
				if (lsb_index > msb_index) {
					port_offset = abs(port_offset - (lsb_index - min(msb_index, lsb_index)));
				}
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
					initval[i] = State::Sx;
			}

			if (wire->port_input) {
				wire->attributes[ID::defaultvalue] = Const(initval);
				wire->attributes.erase(ID::init);
			} else if (initval.is_fully_undef())
				wire->attributes.erase(ID::init);
		}
	}
}

// ==================================================================

VerificClocking::VerificClocking(VerificImporter *importer, Net *net, bool sva_at_only YS_MAYBE_UNUSED)
{
	module = importer->module;

	log_assert(importer != nullptr);
	log_assert(net != nullptr);

	Instance *inst = net->Driver();

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	// Detect condition expression in sva_at_only mode
	if (sva_at_only)
	do {
		Instance *inst_mux = net->Driver();
		if (inst_mux == nullptr || inst_mux->Type() != PRIM_MUX)
			break;

		bool pwr1 = inst_mux->GetInput1()->IsPwr();
		bool pwr2 = inst_mux->GetInput2()->IsPwr();

		if (!pwr1 && !pwr2)
			break;

		Net *sva_net = pwr1 ? inst_mux->GetInput2() : inst_mux->GetInput1();
		if (!verific_is_sva_net(importer, sva_net))
			break;

		inst = sva_net->Driver();
		cond_net = inst_mux->GetControl();
		cond_pol = pwr1;
	} while (0);

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
#endif
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

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	// Detect condition expression
	do {
		if (body_net == nullptr)
			break;

		Instance *inst_mux = body_net->Driver();

		if (inst_mux == nullptr || inst_mux->Type() != PRIM_MUX)
			break;

		bool pwr1 = inst_mux->GetInput1()->IsPwr();
		bool pwr2 = inst_mux->GetInput2()->IsPwr();

		if (!pwr1 && !pwr2)
			break;

		Net *sva_net = pwr1 ? inst_mux->GetInput2() : inst_mux->GetInput1();
		if (!verific_is_sva_net(importer, sva_net))
			break;

		body_net = sva_net;
		cond_net = inst_mux->GetControl();
		cond_pol = pwr1;
	} while (0);
#endif

	clock_net = net;
	clock_sig = importer->net_map_at(clock_net);

	const char *gclk_attr = clock_net->GetAttValue("gclk");
	if (gclk_attr != nullptr && (!strcmp(gclk_attr, "1") || !strcmp(gclk_attr, "'1'")))
		gclk = true;
}

Cell *VerificClocking::addDff(IdString name, SigSpec sig_d, SigSpec sig_q, Const init_value)
{
	log_assert(GetSize(sig_d) == GetSize(sig_q));

	auto set_init_attribute = [&](SigSpec &s) {
		if (GetSize(init_value) == 0)
			return;
		log_assert(GetSize(s) == GetSize(init_value));
		if (s.is_wire()) {
			s.as_wire()->attributes[ID::init] = init_value;
		} else {
			Wire *w = module->addWire(NEW_ID, GetSize(s));
			w->attributes[ID::init] = init_value;
			module->connect(s, w);
			s = w;
		}
	};

	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	if (disable_sig != State::S0) {
		log_assert(GetSize(sig_q) == GetSize(init_value));

		if (gclk) {
			Wire *pre_d = module->addWire(NEW_ID, GetSize(sig_d));
			Wire *post_q_w = module->addWire(NEW_ID, GetSize(sig_q));

			Const initval(State::Sx, GetSize(sig_q));
			int offset = 0;
			for (auto c : sig_q.chunks()) {
				if (c.wire && c.wire->attributes.count(ID::init)) {
					Const val = c.wire->attributes.at(ID::init);
					for (int i = 0; i < GetSize(c); i++)
						initval[offset+i] = val[c.offset+i];
				}
				offset += GetSize(c);
			}

			if (!initval.is_fully_undef())
				post_q_w->attributes[ID::init] = initval;

			module->addMux(NEW_ID, sig_d, init_value, disable_sig, pre_d);
			module->addMux(NEW_ID, post_q_w, init_value, disable_sig, sig_q);

			SigSpec post_q(post_q_w);
			set_init_attribute(post_q);
			return module->addFf(name, pre_d, post_q);
		}

		set_init_attribute(sig_q);
		return module->addAdff(name, clock_sig, disable_sig, sig_d, sig_q, init_value, posedge);
	}

	if (gclk) {
		set_init_attribute(sig_q);
		return module->addFf(name, sig_d, sig_q);
	}

	set_init_attribute(sig_q);
	return module->addDff(name, clock_sig, sig_d, sig_q, posedge);
}

Cell *VerificClocking::addAdff(IdString name, RTLIL::SigSpec sig_arst, SigSpec sig_d, SigSpec sig_q, Const arst_value)
{
	log_assert(gclk == false);
	log_assert(disable_sig == State::S0);

	// FIXME: Adffe
	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	return module->addAdff(name, clock_sig, sig_arst, sig_d, sig_q, arst_value, posedge);
}

Cell *VerificClocking::addDffsr(IdString name, RTLIL::SigSpec sig_set, RTLIL::SigSpec sig_clr, SigSpec sig_d, SigSpec sig_q)
{
	log_assert(gclk == false);
	log_assert(disable_sig == State::S0);

	// FIXME: Dffsre
	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	return module->addDffsr(name, clock_sig, sig_set, sig_clr, sig_d, sig_q, posedge);
}

Cell *VerificClocking::addAldff(IdString name, RTLIL::SigSpec sig_aload, RTLIL::SigSpec sig_adata, SigSpec sig_d, SigSpec sig_q)
{
	log_assert(disable_sig == State::S0);

	// FIXME: Aldffe
	if (enable_sig != State::S1)
		sig_d = module->Mux(NEW_ID, sig_q, sig_d, enable_sig);

	if (gclk) {
		Wire *pre_d = module->addWire(NEW_ID, GetSize(sig_d));
		Wire *post_q = module->addWire(NEW_ID, GetSize(sig_q));

		Const initval(State::Sx, GetSize(sig_q));
		int offset = 0;
		for (auto c : sig_q.chunks()) {
			if (c.wire && c.wire->attributes.count(ID::init)) {
				Const val = c.wire->attributes.at(ID::init);
				for (int i = 0; i < GetSize(c); i++)
					initval[offset+i] = val[c.offset+i];
			}
			offset += GetSize(c);
		}

		if (!initval.is_fully_undef())
			post_q->attributes[ID::init] = initval;

		module->addMux(NEW_ID, sig_d, sig_adata, sig_aload, pre_d);
		module->addMux(NEW_ID, post_q, sig_adata, sig_aload, sig_q);

		return module->addFf(name, pre_d, post_q);
	}

	return module->addAldff(name, clock_sig, sig_aload, sig_d, sig_q, sig_adata, posedge);
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
			nl->Buf(net)->Connect(new_port);

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

				Net *n = route_up(new_net, port->IsOutput(), ca_nl, ca_net);
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

void import_all(const char* work, std::map<std::string,Netlist*> *nl_todo, Map *parameters, bool show_message, std::string ppfile YS_MAYBE_UNUSED)
{
#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
	VerificExtensions::ElaborateAndRewrite(work, parameters);
	verific_error_msg.clear();
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	if (!ppfile.empty())
		veri_file::PrettyPrint(ppfile.c_str(), nullptr, work);
#endif

	Array vhdl_libs;
#ifdef VERIFIC_VHDL_SUPPORT
	VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work, 1);
	if (vhdl_lib) vhdl_libs.InsertLast(vhdl_lib);
#endif
	Array veri_libs;
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	VeriLibrary *veri_lib = veri_file::GetLibrary(work, 1);
	if (veri_lib) veri_libs.InsertLast(veri_lib);
#endif

#ifdef VERIFIC_HIER_TREE_SUPPORT
	if (show_message)
		log("Running hier_tree::ElaborateAll().\n");
	Array *netlists = hier_tree::ElaborateAll(&veri_libs, &vhdl_libs, parameters);
	Netlist *nl;
	int i;

	FOREACH_ARRAY_ITEM(netlists, i, nl)
		nl_todo->emplace(nl->CellBaseName(), nl);
	delete netlists;
#else
	if (parameters->Size())
		log_warning("Please note that parameters are not propagated during import.\n");
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	if (show_message)
		log("Running veri_file::ElaborateAll().\n");
	veri_file::ElaborateAll(work);
#endif
#ifdef VERIFIC_VHDL_SUPPORT
	if (show_message)
		log("Running vhdl_file::ElaborateAll().\n");
	vhdl_file::ElaborateAll(work);
#endif
	MapIter mi ;
	Verific::Cell *c ;
	MapIter it ;
	Library *l ;
	FOREACH_LIBRARY_OF_LIBSET(Libset::Global(),it,l) {
		if (l == Library::Primitives() || l == Library::Operators()) continue;
		FOREACH_CELL_OF_LIBRARY(l,mi,c) {
			MapIter ni ;
			Netlist *nl;
			FOREACH_NETLIST_OF_CELL(c, ni, nl) {
				if (nl)
					nl_todo->emplace(nl->CellBaseName(), nl);
			}
		}
	}
#endif
}

std::set<std::string> import_tops(const char* work, std::map<std::string,Netlist*> *nl_todo, Map *parameters, bool show_message, std::string ppfile YS_MAYBE_UNUSED, std::vector<std::string> &tops, std::string *top = nullptr)
{
	std::set<std::string> top_mod_names;
	Array *netlists = nullptr;

#ifdef VERIFIC_VHDL_SUPPORT
	VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work, 1);
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	VeriLibrary* veri_lib = veri_file::GetLibrary(work, 1);
#endif

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
	for (int static_elaborate = 1; static_elaborate >= 0; static_elaborate--)
#endif
	{
		Array vhdl_units;
		Array veri_modules;
		for (std::string n : tops)
		{
			const char *name = n.c_str();
			top_mod_names.insert(name);

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			VeriModule *veri_module = veri_lib ? veri_lib->GetModule(name, 1) : nullptr;
			if (veri_module) {
				if (veri_module->IsConfiguration()) {
					if (show_message)
						log("Adding Verilog configuration '%s' to elaboration queue.\n", name);
					veri_modules.InsertLast(veri_module);
					top_mod_names.erase(name);
					VeriConfiguration *cfg = (VeriConfiguration*)veri_module;
					VeriName *module_name;
					int i;
					FOREACH_ARRAY_ITEM(cfg->GetTopModuleNames(), i, module_name) {
						VeriLibrary *lib = veri_module->GetLibrary() ;
						if (module_name && module_name->IsHierName()) {
							VeriName *prefix = module_name->GetPrefix() ;
							const char *lib_name = (prefix) ? prefix->GetName() : 0 ;
							if (work != lib_name) lib = veri_file::GetLibrary(lib_name, 1) ;
						}
						if (lib && module_name)
							top_mod_names.insert(lib->GetModule(module_name->GetName(), 1)->GetName());
					}
				} else {
					if (show_message)
						log("Adding Verilog module '%s' to elaboration queue.\n", name);
					veri_modules.InsertLast(veri_module);
				}
			continue;
			}
#endif
#ifdef VERIFIC_VHDL_SUPPORT
			VhdlDesignUnit *vhdl_unit = vhdl_lib ? vhdl_lib->GetPrimUnit(name) : nullptr;
			if (vhdl_unit) {
				if (show_message)
					log("Adding VHDL unit '%s' to elaboration queue.\n", name);
				vhdl_units.InsertLast(vhdl_unit);
				if (strcmp(name, vhdl_unit->Id()->OrigName()) != 0) {
					top_mod_names.erase(name);
					top_mod_names.insert(vhdl_unit->Id()->OrigName());
					if (top && *top == name)
						*top = vhdl_unit->Id()->OrigName();
				}
				continue;
			}
#endif
			log_error("Can't find module/unit '%s'.\n", name);
		}

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
		if (static_elaborate) {
			VerificExtensions::ElaborateAndRewrite(work, &veri_modules, &vhdl_units, parameters);
			verific_error_msg.clear();
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			if (!ppfile.empty())
				veri_file::PrettyPrint(ppfile.c_str(), nullptr, work);
#endif
#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
			continue;
		}
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		const char *lib_name = nullptr;
		SetIter si;
		FOREACH_SET_ITEM(veri_file::GetAllLOptions(), si, &lib_name) {
			VeriLibrary* veri_lib = veri_file::GetLibrary(lib_name, 0);
			if (veri_lib) {
				// Also elaborate all root modules since they may contain bind statements
				MapIter mi;
				VeriModule *veri_module;
				FOREACH_VERILOG_MODULE_IN_LIBRARY(veri_lib, mi, veri_module) {
					if (!veri_module->IsRootModule()) continue;
					veri_modules.InsertLast(veri_module);
				}
			}
		}
#endif
#ifdef VERIFIC_HIER_TREE_SUPPORT
		if (show_message)
			log("Running hier_tree::Elaborate().\n");
		netlists = hier_tree::Elaborate(&veri_modules, &vhdl_units, parameters);
#else
#if defined(VERIFIC_SYSTEMVERILOG_SUPPORT) && !defined(VERIFIC_VHDL_SUPPORT)
		if (show_message)
			log("Running veri_file::ElaborateMultipleTop().\n");
		// SystemVerilog support only
		netlists = veri_file::ElaborateMultipleTop(&veri_modules, parameters);
#elif defined(VERIFIC_VHDL_SUPPORT) && !defined(VERIFIC_SYSTEMVERILOG_SUPPORT)
		if (show_message)
			log("Running vhdl_file::Elaborate().\n");
		// VHDL support	only
		netlists = new Array(top_mod_names.size());
		for (auto &name : top_mod_names) {
			vhdl_file::Elaborate(name.c_str(), work, 0, parameters);
			netlists->InsertLast(Netlist::PresentDesign());
		}
#elif defined(VERIFIC_SYSTEMVERILOG_SUPPORT) && defined(VERIFIC_VHDL_SUPPORT)
		// Both SystemVerilog and VHDL support
		if (veri_modules.Size()>0) {
			if (show_message)
				log("Running veri_file::ElaborateMultipleTop().\n");
			netlists = veri_file::ElaborateMultipleTop(&veri_modules, parameters);
		} else
			netlists = new Array(1);
		if (vhdl_units.Size()>0) {
			if (show_message)
				log("Running vhdl_file::Elaborate().\n");
			for (auto &name : top_mod_names) {
				vhdl_file::Elaborate(name.c_str(), work, 0, parameters);
				netlists->InsertLast(Netlist::PresentDesign());
			}
		}
#else
#endif
#endif
	}
	Netlist *nl;
	int i;

	FOREACH_ARRAY_ITEM(netlists, i, nl) {
		if (!nl) continue;
		if (!top_mod_names.count(nl->CellBaseName()))
			continue;
		nl->AddAtt(new Att(" \\top", NULL));
		nl_todo->emplace(nl->CellBaseName(), nl);
	}
	delete netlists;
	return top_mod_names;
}

void verific_cleanup()
{
#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
	VerificExtensions::Reset();
#endif
#ifdef VERIFIC_HIER_TREE_SUPPORT
	hier_tree::DeleteHierarchicalTree();
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	veri_file::Reset();
#endif
#ifdef VERIFIC_VHDL_SUPPORT
	vhdl_file::Reset();
#endif
#ifdef VERIFIC_EDIF_SUPPORT
	edif_file::Reset();
#endif
#ifdef VERIFIC_LIBERTY_SUPPORT
	synlib_file::Reset();
#endif
	Libset::Reset();
	Message::Reset();
	RuntimeFlags::DeleteAllFlags();
	LineFile::DeleteAllLineFiles();
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	verific_incdirs.clear();
	verific_libdirs.clear();
	verific_libexts.clear();
#endif
	verific_import_pending = false;
}

std::string verific_import(Design *design, const std::map<std::string,std::string> &parameters, std::string top)
{
	verific_sva_fsm_limit = 16;

	std::map<std::string,Netlist*> nl_todo, nl_done;

	Map verific_params(STRING_HASH);
	for (const auto &i : parameters)
		verific_params.Insert(i.first.c_str(), i.second.c_str());

	std::set<std::string> top_mod_names;
	if (top.empty()) {
		import_all("work", &nl_todo, &verific_params, false, "");
	} else {
		std::vector<std::string> tops;
		tops.push_back(top);
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		veri_file::RemoveAllLOptions();
		veri_file::AddLOption("work");
#endif
		top_mod_names = import_tops("work", &nl_todo, &verific_params, false, "", tops, &top) ;
	}

	if (!verific_error_msg.empty())
		log_error("%s\n", verific_error_msg.c_str());

	for (auto nl : nl_todo)
		nl.second->ChangePortBusStructures(1 /* hierarchical */);

	VerificExtNets worker;
	for (auto nl : nl_todo)
		worker.run(nl.second);

	while (!nl_todo.empty()) {
		auto it = nl_todo.begin();
		Netlist *nl = it->second;
		if (nl_done.count(it->first) == 0) {
			VerificImporter importer(false, false, false, false, false, false, false);
			nl_done[it->first] = it->second;
			importer.import_netlist(design, nl, nl_todo, top_mod_names.count(nl->CellBaseName()));
		}
		nl_todo.erase(it);
	}

	verific_cleanup();
	if (!verific_error_msg.empty())
		log_error("%s\n", verific_error_msg.c_str());
	return top;
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

#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
	void on_register() override	{ VerificExtensions::Reset(); }
#endif

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
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
		log("The macros YOSYS, SYNTHESIS, and VERIFIC are defined implicitly.\n");
		log("\n");
		log("\n");
		log("    verific -formal <verilog-file>..\n");
		log("\n");
		log("Like -sv, but define FORMAL instead of SYNTHESIS.\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_VHDL_SUPPORT
		log("    verific {-vhdl87|-vhdl93|-vhdl2k|-vhdl2008|-vhdl2019|-vhdl} <vhdl-file>..\n");
		log("\n");
		log("Load the specified VHDL files into Verific.\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_EDIF_SUPPORT
		log("    verific {-edif} <edif-file>..\n");
		log("\n");
		log("Load the specified EDIF files into Verific.\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_LIBERTY_SUPPORT
		log("    verific {-liberty} <liberty-file>..\n");
		log("\n");
		log("Load the specified Liberty files into Verific.\n");
		log("Default library when -work is not present is one specified in liberty file.\n");
		log("To use from SystemVerilog or VHDL use -L to specify liberty library.");
		log("\n");
		log("    -lib\n");
		log("        only create empty blackbox modules\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		log("    verific {-f|-F} [-vlog95|-vlog2k|-sv2005|-sv2009|\n");
		log("                     -sv2012|-sv|-formal] <command-file>\n");
		log("\n");
		log("Load and execute the specified command file.\n");
		log("Override verilog parsing mode can be set.\n");
		log("The macros YOSYS, SYNTHESIS/FORMAL, and VERIFIC are defined implicitly.\n");
		log("\n");
		log("Command file parser supports following commands in file:\n");
		log("    +define+<MACRO>=<VALUE> - defines macro\n");
		log("    -u                      - upper case all identifier (makes Verilog parser\n");
		log("                              case insensitive)\n");
		log("    -v <filepath>           - register library name (file)\n");
		log("    -y <filepath>           - register library name (directory)\n");
		log("    +incdir+<filepath>      - specify include dir\n");
		log("    +libext+<filepath>      - specify library extension\n");
		log("    +liborder+<id>          - add library in ordered list\n");
		log("    +librescan              - unresolved modules will be always searched\n");
		log("                              starting with the first library specified\n");
		log("                              by -y/-v options.\n");
		log("    -f/-file <filepath>     - nested -f option\n");
		log("    -F <filepath>           - nested -F option (relative path)\n");
		log("    parse files:\n");
		log("        <filepath>\n");
		log("        +systemverilogext+<filepath>\n");
		log("        +verilog1995ext+<filepath>\n");
		log("        +verilog2001ext+<filepath>\n");
		log("\n");
		log("    analysis mode:\n");
		log("        -ams\n");
		log("        +v2k\n");
		log("        -sverilog\n");
		log("\n");
		log("\n");
#endif
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
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
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
		log("    verific -vlog-libext <extension>..\n");
		log("\n");
		log("Add Verilog library extensions, used when searching in library directories.\n");
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
#endif
		log("    verific -set-error <msg_id>..\n");
		log("    verific -set-warning <msg_id>..\n");
		log("    verific -set-info <msg_id>..\n");
		log("    verific -set-ignore <msg_id>..\n");
		log("\n");
		log("Set message severity. <msg_id> is the string in square brackets when a message\n");
		log("is printed, such as VERI-1209.\n");
		log("Also errors, warnings, infos and comments could be used to set new severity for\n");
		log("all messages of certain type.\n");
		log("\n");
		log("\n");
		log("    verific -import [options] <top>..\n");
		log("\n");
		log("Elaborate the design for the specified top modules or configurations, import to\n");
		log("Yosys and reset the internal state of Verific.\n");
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
		log("  -no-split-complex-ports\n");
		log("    Complex ports (structs or arrays) are not split and remain packed as a single port.\n");
		log("\n");
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		log("  -autocover\n");
		log("    Generate automatic cover statements for all asserts\n");
		log("\n");
#endif
		log("  -fullinit\n");
		log("    Keep all register initializations, even those for non-FF registers.\n");
		log("\n");
		log("  -cells\n");
		log("    Import all cell definitions from Verific loaded libraries even if they are\n");
		log("    unused in design. Useful with \"-edif\" and \"-liberty\" option.\n");
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
		log("  -pp <filename>\n");
		log("    Pretty print design after elaboration to specified file.\n");
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
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		log("  -nosva\n");
		log("    Ignore SVA properties, do not infer checker logic.\n");
		log("\n");
		log("  -L <int>\n");
		log("    Maximum number of ctrl bits for SVA checker FSMs (default=16).\n");
		log("\n");
#endif
		log("  -n\n");
		log("    Keep all Verific names on instances and nets. By default only\n");
		log("    user-declared names are preserved.\n");
		log("\n");
		log("  -d <dump_file>\n");
		log("    Dump the Verific netlist as a verilog file.\n");
		log("\n");
		log("\n");
		log("    verific [-work <libname>] -pp [options] <filename> [<module>]..\n");
		log("\n");
		log("Pretty print design (or just module) to the specified file from the\n");
		log("specified library. (default library when -work is not present: \"work\")\n");
		log("\n");
		log("Pretty print options:\n");
		log("\n");
		log("  -verilog\n");
		log("    Save output for Verilog/SystemVerilog design modules (default).\n");
		log("\n");
		log("  -vhdl\n");
		log("    Save output for VHDL design units.\n");
		log("\n");
		log("\n");
		log("    verific -cfg [<name> [<value>]]\n");
		log("\n");
		log("Get/set Verific runtime flags.\n");
		log("\n");
		log("\n");
#if defined(YOSYS_ENABLE_VERIFIC) and defined(YOSYSHQ_VERIFIC_EXTENSIONS)
		VerificExtensions::Help();
#endif	
		log("Use YosysHQ Tabby CAD Suite if you need Yosys+Verific.\n");
		log("https://www.yosyshq.com/\n");
		log("\n");
		log("Contact office@yosyshq.com for free evaluation\n");
		log("binaries of YosysHQ Tabby CAD Suite.\n");
		log("\n");
	}
#ifdef YOSYS_ENABLE_VERIFIC
	std::string frontent_rewrite(std::vector<std::string> &args, int &argidx, std::vector<std::string> &tmp_files)
	{
		std::string filename = args[argidx++];
		//Accommodate heredocs with EOT marker spaced out from "<<", e.g. "<< EOT" vs. "<<EOT"
		if (filename == "<<" && (argidx < GetSize(args))) {
			filename += args[argidx++];
		}
		if (filename.compare(0, 2, "<<") == 0) {
			if (filename.size() <= 2)
				log_error("Missing EOT marker in here document!\n");
			std::string eot_marker = filename.substr(2);
			if (Frontend::current_script_file == nullptr)
				filename = "<stdin>";
			std::string last_here_document;
			while (1) {
				std::string buffer;
				char block[4096];
				while (1) {
					if (fgets(block, 4096, Frontend::current_script_file == nullptr? stdin : Frontend::current_script_file) == nullptr)
						log_error("Unexpected end of file in here document '%s'!\n", filename.c_str());
					buffer += block;
					if (buffer.size() > 0 && (buffer[buffer.size() - 1] == '\n' || buffer[buffer.size() - 1] == '\r'))
						break;
				}
				size_t indent = buffer.find_first_not_of(" \t\r\n");
				if (indent != std::string::npos && buffer.compare(indent, eot_marker.size(), eot_marker) == 0)
					break;
				last_here_document += buffer;
			}
			filename = make_temp_file();
			tmp_files.push_back(filename);
			std::ofstream file(filename);
			file << last_here_document;
		} else {
			rewrite_filename(filename);
		}
		return filename;
	}

#ifdef VERIFIC_VHDL_SUPPORT
	msg_type_t prev_1240 ;
	msg_type_t prev_1241 ;

	void add_units_to_map(Map &map, std::string work, bool flag_lib)
	{
		MapIter mi ;
		VhdlPrimaryUnit *unit ;
		if (!flag_lib) return;
		VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work.c_str(), 1);
		if (vhdl_lib) {					
			FOREACH_VHDL_PRIMARY_UNIT(vhdl_lib, mi, unit) {
				if (!unit) continue;
				map.Insert(unit,unit);
			}
		}

 		prev_1240 = Message::GetMessageType("VHDL-1240") ;
		prev_1241 = Message::GetMessageType("VHDL-1241") ;
		Message::SetMessageType("VHDL-1240", VERIFIC_INFO);
		Message::SetMessageType("VHDL-1241", VERIFIC_INFO);
	}

	void set_units_to_blackbox(Map &map, std::string work, bool flag_lib)
	{
		MapIter mi ;
		VhdlPrimaryUnit *unit ;
		if (!flag_lib) return;
		VhdlLibrary *vhdl_lib = vhdl_file::GetLibrary(work.c_str(), 1);
		FOREACH_VHDL_PRIMARY_UNIT(vhdl_lib, mi, unit) {
			if (!unit) continue;
			if (!map.GetValue(unit)) {
				unit->SetCompileAsBlackbox();
			}
		}
		Message::ClearMessageType("VHDL-1240") ; 
		Message::ClearMessageType("VHDL-1241") ; 
		if (Message::GetMessageType("VHDL-1240")!=prev_1240)
			Message::SetMessageType("VHDL-1240", prev_1240);
		if (Message::GetMessageType("VHDL-1241")!=prev_1241)
			Message::SetMessageType("VHDL-1241", prev_1241);

	}
#endif

	msg_type_t prev_1063;
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
	void add_modules_to_map(Map &map, std::string work, bool flag_lib)
	{
		MapIter mi ;
		VeriModule *veri_module ;
		if (!flag_lib) return;
		VeriLibrary *veri_lib = veri_file::GetLibrary(work.c_str(), 1);
		if (veri_lib) {					
			FOREACH_VERILOG_MODULE_IN_LIBRARY(veri_lib, mi, veri_module) {
				if (!veri_module) continue;
				map.Insert(veri_module,veri_module);
			}
		}

 		prev_1063 = Message::GetMessageType("VERI-1063") ;
		Message::SetMessageType("VERI-1063", VERIFIC_INFO);
	}

	void set_modules_to_blackbox(Map &map, std::string work, bool flag_lib)
	{
		MapIter mi ;
		VeriModule *veri_module ;
		if (!flag_lib) return;
		VeriLibrary *veri_lib = veri_file::GetLibrary(work.c_str(), 1);
		FOREACH_VERILOG_MODULE_IN_LIBRARY(veri_lib, mi, veri_module) {
			if (!veri_module) continue;
			if (!map.GetValue(veri_module)) {
				veri_module->SetCompileAsBlackbox();
			}
		}
		Message::ClearMessageType("VERI-1063") ; 
		if (Message::GetMessageType("VERI-1063")!=prev_1063)
			Message::SetMessageType("VERI-1063", prev_1063);
	}
#endif

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		static bool set_verific_global_flags = true;

		if (check_noverific_env())
			log_cmd_error("This version of Yosys is built without Verific support.\n"
					"\n"
					"Use YosysHQ Tabby CAD Suite if you need Yosys+Verific.\n"
					"https://www.yosyshq.com/\n"
					"\n"
					"Contact office@yosyshq.com for free evaluation\n"
					"binaries of YosysHQ Tabby CAD Suite.\n");

		log_header(design, "Executing VERIFIC (loading SystemVerilog and VHDL designs using Verific).\n");

		if (set_verific_global_flags)
		{
			Message::SetConsoleOutput(0);
			Message::RegisterCallBackMsg(msg_func);

			RuntimeFlags::SetVar("db_preserve_user_instances", 1);
			RuntimeFlags::SetVar("db_preserve_user_nets", 1);
			RuntimeFlags::SetVar("db_preserve_x", 1);

			RuntimeFlags::SetVar("db_allow_external_nets", 1);
			RuntimeFlags::SetVar("db_infer_wide_operators", 1);
			RuntimeFlags::SetVar("db_infer_set_reset_registers", 0);

			// Properly respect order of read and write for rams
			RuntimeFlags::SetVar("db_change_inplace_ram_blocking_write_before_read", 1);

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			RuntimeFlags::SetVar("veri_extract_dualport_rams", 0);
			RuntimeFlags::SetVar("veri_extract_multiport_rams", 1);
			RuntimeFlags::SetVar("veri_allow_any_ram_in_loop", 1);
#endif
#ifdef VERIFIC_VHDL_SUPPORT
			RuntimeFlags::SetVar("vhdl_extract_dualport_rams", 0);
			RuntimeFlags::SetVar("vhdl_extract_multiport_rams", 1);
			RuntimeFlags::SetVar("vhdl_allow_any_ram_in_loop", 1);

			RuntimeFlags::SetVar("vhdl_support_variable_slice", 1);
			RuntimeFlags::SetVar("vhdl_ignore_assertion_statements", 0);

			RuntimeFlags::SetVar("vhdl_preserve_assignments", 1);
			//RuntimeFlags::SetVar("vhdl_preserve_comments", 1);
			RuntimeFlags::SetVar("vhdl_preserve_drivers", 1);
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			RuntimeFlags::SetVar("veri_preserve_assignments", 1);
			RuntimeFlags::SetVar("veri_preserve_comments", 1);
			RuntimeFlags::SetVar("veri_preserve_drivers", 1);

			// Workaround for VIPER #13851
			RuntimeFlags::SetVar("veri_create_name_for_unnamed_gen_block", 1);

			// WARNING: instantiating unknown module 'XYZ' (VERI-1063)
			Message::SetMessageType("VERI-1063", VERIFIC_ERROR);

			// https://github.com/YosysHQ/yosys/issues/1055
			RuntimeFlags::SetVar("veri_elaborate_top_level_modules_having_interface_ports", 1) ;
#endif
			RuntimeFlags::SetVar("verific_produce_verbose_syntax_error_message", 1);

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
		std::vector<std::string> tmp_files;

		if (release_str == nullptr)
			release_str = "(no release string)";

		for (char *p = release_tmstr; *p; p++)
			if (*p == '\n') *p = 0;

		log("Built with Verific %s, released at %s.\n", release_str, release_tmstr);

		int argidx = 1;
		std::string work = "work";
		bool is_work_set = false;
		(void)is_work_set;
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		veri_file::RegisterCallBackVerificStream(&verific_read_cb);
#endif
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

			for (argidx++; argidx < GetSize(args); argidx++) {
				if (Strings::compare(args[argidx].c_str(), "errors")) {
					Message::SetMessageType("VERI-1063", new_type);
					Message::SetAllMessageType(VERIFIC_ERROR, new_type);
				} else if (Strings::compare(args[argidx].c_str(), "warnings")) {
					Message::SetAllMessageType(VERIFIC_WARNING, new_type);
				} else if (Strings::compare(args[argidx].c_str(), "infos")) {
					Message::SetAllMessageType(VERIFIC_INFO, new_type);
				} else if (Strings::compare(args[argidx].c_str(), "comments")) {
					Message::SetAllMessageType(VERIFIC_COMMENT, new_type);
				} else {
					Message::SetMessageType(args[argidx].c_str(), new_type);
				}
			}
			goto check_error;
		}

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
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

		if (GetSize(args) > argidx && args[argidx] == "-vlog-libext") {
			for (argidx++; argidx < GetSize(args); argidx++)
				verific_libexts.push_back(args[argidx]);
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
#endif
		for (int i = argidx; i < GetSize(args); i++)
		{
			if (args[i] == "-work" && i+1 < GetSize(args)) {
				work = args[++i];
				is_work_set = true;
				continue;
			}
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			if (args[i] == "-L" && i+1 < GetSize(args)) {
				++i;
				continue;
			}
#endif
			break;
		}
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		veri_file::AddLOption(work.c_str());
#endif
		for (int i = argidx; i < GetSize(args); i++)
		{
			if (args[i] == "-work" && i+1 < GetSize(args)) {
				++i;
				continue;
			}
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			if (args[i] == "-L" && i+1 < GetSize(args)) {
				if (args[++i] == work)
					veri_file::RemoveAllLOptions();
				continue;
			}
#endif
			break;
		}
		for (; argidx < GetSize(args); argidx++)
		{
			if (args[argidx] == "-work" && argidx+1 < GetSize(args)) {
				work = args[++argidx];
				is_work_set = true;
				continue;
			}
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			if (args[argidx] == "-L" && argidx+1 < GetSize(args)) {
				veri_file::AddLOption(args[++argidx].c_str());
				continue;
			}
#endif
			break;
		}

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
		if (GetSize(args) > argidx && (args[argidx] == "-f" || args[argidx] == "-F"))
		{
			unsigned verilog_mode = veri_file::UNDEFINED;
			bool is_formal = false;
			const char* filename = nullptr;

			Verific::veri_file::f_file_flags flags = (args[argidx] == "-f") ? veri_file::F_FILE_NONE : veri_file::F_FILE_CAPITAL;

			for (argidx++; argidx < GetSize(args); argidx++) {
				if (args[argidx] == "-vlog95") {
					verilog_mode = veri_file::VERILOG_95;
					continue;
				} else if (args[argidx] == "-vlog2k") {
					verilog_mode = veri_file::VERILOG_2K;
					continue;
				} else if (args[argidx] == "-sv2005") {
					verilog_mode = veri_file::SYSTEM_VERILOG_2005;
					continue;
				} else if (args[argidx] == "-sv2009") {
					verilog_mode = veri_file::SYSTEM_VERILOG_2009;
					continue;
				} else if (args[argidx] == "-sv2012" || args[argidx] == "-sv" || args[argidx] == "-formal") {
					verilog_mode = veri_file::SYSTEM_VERILOG;
					if (args[argidx] == "-formal") is_formal = true;
					continue;
				} else if (args[argidx].compare(0, 1, "-") == 0) {
					cmd_error(args, argidx, "unknown option");
					goto check_error;
				}

				if (!filename) {
					filename = args[argidx].c_str();
					continue;
				} else {
					log_cmd_error("Only one filename can be specified.\n");
				}
			}
			if (!filename)
				log_cmd_error("Filname must be specified.\n");

			unsigned analysis_mode = verilog_mode; // keep default as provided by user if not defined in file
			Array *file_names = veri_file::ProcessFFile(filename, flags, analysis_mode);
			if (analysis_mode != verilog_mode)
				log_warning("Provided verilog mode differs from one specified in file.\n");

			veri_file::DefineMacro("YOSYS");
			veri_file::DefineMacro("VERIFIC");
			veri_file::DefineMacro(is_formal ? "FORMAL" : "SYNTHESIS");

			if (!veri_file::AnalyzeMultipleFiles(file_names, analysis_mode, work.c_str(), veri_file::MFCU)) {
				verific_error_msg.clear();
				log_cmd_error("Reading Verilog/SystemVerilog sources failed.\n");
			}

			delete file_names;
			verific_import_pending = true;
			goto check_error;
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

			veri_file::DefineMacro("YOSYS");
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
			for (auto &ext : verific_libexts)
				veri_file::AddLibExt(ext.c_str());

			bool flag_lib = false;
			while (argidx < GetSize(args)) {
				if (args[argidx] == "-lib") {
					flag_lib = true;
					argidx++;
					continue;
				}
				if (args[argidx].compare(0, 1, "-") == 0) {
					cmd_error(args, argidx, "unknown option");
					goto check_error;
				}
				std::string filename = frontent_rewrite(args, argidx, tmp_files);
				file_names.Insert(strdup(filename.c_str()));
			}
			Map map(POINTER_HASH);
			add_modules_to_map(map, work, flag_lib);
			if (!veri_file::AnalyzeMultipleFiles(&file_names, verilog_mode, work.c_str(), veri_file::MFCU)) {
					verific_error_msg.clear();
					log_cmd_error("Reading Verilog/SystemVerilog sources failed.\n");
			}
			char* fn;
			int i = 0;

			FOREACH_ARRAY_ITEM(&file_names, i, fn) {
				free(fn);
			}
			set_modules_to_blackbox(map, work, flag_lib);
			verific_import_pending = true;
			goto check_error;
		}
#endif

#ifdef VERIFIC_VHDL_SUPPORT
		if (GetSize(args) > argidx && args[argidx] == "-vhdl87") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_1987").c_str());
			bool flag_lib = false;
			argidx++;
			while (argidx < GetSize(args)) {
				if (args[argidx] == "-lib") {
					flag_lib = true;
					argidx++;
					continue;
				}
				if (args[argidx].compare(0, 1, "-") == 0) {
					cmd_error(args, argidx, "unknown option");
					goto check_error;
				}
				Map map(POINTER_HASH);
				add_units_to_map(map, work, flag_lib);
				std::string filename = frontent_rewrite(args, argidx, tmp_files);
				if (!vhdl_file::Analyze(filename.c_str(), work.c_str(), vhdl_file::VHDL_87))
					log_cmd_error("Reading `%s' in VHDL_87 mode failed.\n", filename.c_str());
				set_units_to_blackbox(map, work, flag_lib);
			}
			verific_import_pending = true;
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdl93") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_1993").c_str());
			bool flag_lib = false;
			argidx++;
			while (argidx < GetSize(args)) {
				if (args[argidx] == "-lib") {
					flag_lib = true;
					argidx++;
					continue;
				}
				if (args[argidx].compare(0, 1, "-") == 0) {
					cmd_error(args, argidx, "unknown option");
					goto check_error;
				}
				Map map(POINTER_HASH);
				add_units_to_map(map, work, flag_lib);
				std::string filename = frontent_rewrite(args, argidx, tmp_files);
				if (!vhdl_file::Analyze(filename.c_str(), work.c_str(), vhdl_file::VHDL_93))
					log_cmd_error("Reading `%s' in VHDL_93 mode failed.\n", filename.c_str());
				set_units_to_blackbox(map, work, flag_lib);
			}
			verific_import_pending = true;
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-vhdl2k") {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_1993").c_str());
			bool flag_lib = false;
			argidx++;
			while (argidx < GetSize(args)) {
				if (args[argidx] == "-lib") {
					flag_lib = true;
					argidx++;
					continue;
				}
				if (args[argidx].compare(0, 1, "-") == 0) {
					cmd_error(args, argidx, "unknown option");
					goto check_error;
				}
				Map map(POINTER_HASH);
				add_units_to_map(map, work, flag_lib);
				std::string filename = frontent_rewrite(args, argidx, tmp_files);
				if (!vhdl_file::Analyze(filename.c_str(), work.c_str(), vhdl_file::VHDL_2K))
					log_cmd_error("Reading `%s' in VHDL_2K mode failed.\n", filename.c_str());
				set_units_to_blackbox(map, work, flag_lib);
			}
			verific_import_pending = true;
			goto check_error;
		}

		if (GetSize(args) > argidx && (args[argidx] == "-vhdl2019")) {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_2019").c_str());
			bool flag_lib = false;
			argidx++;
			while (argidx < GetSize(args)) {
				if (args[argidx] == "-lib") {
					flag_lib = true;
					argidx++;
					continue;
				}
				if (args[argidx].compare(0, 1, "-") == 0) {
					cmd_error(args, argidx, "unknown option");
					goto check_error;
				}
				Map map(POINTER_HASH);
				add_units_to_map(map, work, flag_lib);
				std::string filename = frontent_rewrite(args, argidx, tmp_files);
				if (!vhdl_file::Analyze(filename.c_str(), work.c_str(), vhdl_file::VHDL_2019))
					log_cmd_error("Reading `%s' in VHDL_2019 mode failed.\n", filename.c_str());
				set_units_to_blackbox(map, work, flag_lib);
			}
			verific_import_pending = true;
			goto check_error;
		}

		if (GetSize(args) > argidx && (args[argidx] == "-vhdl2008" || args[argidx] == "-vhdl")) {
			vhdl_file::SetDefaultLibraryPath((proc_share_dirname() + "verific/vhdl_vdbs_2008").c_str());
			bool flag_lib = false;
			argidx++;
			while (argidx < GetSize(args)) {
				if (args[argidx] == "-lib") {
					flag_lib = true;
					argidx++;
					continue;
				}
				if (args[argidx].compare(0, 1, "-") == 0) {
					cmd_error(args, argidx, "unknown option");
					goto check_error;
				}
				Map map(POINTER_HASH);
				add_units_to_map(map, work, flag_lib);
				std::string filename = frontent_rewrite(args, argidx, tmp_files);
				if (!vhdl_file::Analyze(filename.c_str(), work.c_str(), vhdl_file::VHDL_2008))
					log_cmd_error("Reading `%s' in VHDL_2008 mode failed.\n", filename.c_str());
				set_units_to_blackbox(map, work, flag_lib);
			}
			verific_import_pending = true;
			goto check_error;
		}
#endif
#ifdef VERIFIC_EDIF_SUPPORT
		if (GetSize(args) > argidx && args[argidx] == "-edif") {
			edif_file edif;
			argidx++;
			while (argidx < GetSize(args)) {
				std::string filename = frontent_rewrite(args, argidx, tmp_files);
				if (!edif.Read(filename.c_str()))
					log_cmd_error("Reading `%s' in EDIF mode failed.\n", filename.c_str());
			}
			goto check_error;
		}
#endif
#ifdef VERIFIC_LIBERTY_SUPPORT
		if (GetSize(args) > argidx && args[argidx] == "-liberty") {
			bool flag_lib = false;
			for (argidx++; argidx < GetSize(args); argidx++) {
				if (args[argidx] == "-lib") {
					flag_lib = true;
					continue;
				}
				if (args[argidx].compare(0, 1, "-") == 0) {
					cmd_error(args, argidx, "unknown option");
					goto check_error;
				}
				break;
			}

			while (argidx < GetSize(args)) {
				std::string filename = frontent_rewrite(args, argidx, tmp_files);
				if (!synlib_file::Read(filename.c_str(), is_work_set ? work.c_str() : nullptr))
					log_cmd_error("Reading `%s' in LIBERTY mode failed.\n", filename.c_str());
				SynlibLibrary *lib = synlib_file::GetLastLibraryAnalyzed();
				if (lib && flag_lib) {
					MapIter mi ;
					Verific::Cell *c ;
					FOREACH_CELL_OF_LIBRARY(lib->GetLibrary(),mi,c) {
						MapIter ni ;
						Netlist *nl;
						FOREACH_NETLIST_OF_CELL(c, ni, nl) {
							if (nl)
								nl->MakeBlackBox();
						}
					}
				}
			}
			goto check_error;
		}
#endif
		if (argidx < GetSize(args) && args[argidx] == "-pp")
		{
			const char* filename = nullptr;
			const char* module = nullptr;
			bool mode_vhdl = false;
			for (argidx++; argidx < GetSize(args); argidx++) {
#ifdef VERIFIC_VHDL_SUPPORT
				if (args[argidx] == "-vhdl") {
					mode_vhdl = true;
					continue;
				}
#endif
				if (args[argidx] == "-verilog") {
					mode_vhdl = false;
					continue;
				}

				if (args[argidx].compare(0, 1, "-") == 0) {
					cmd_error(args, argidx, "unknown option");
					goto check_error;
				}

				if (!filename) {
					filename = args[argidx].c_str();
					continue;
				}
				if (module)
					log_cmd_error("Only one module can be specified.\n");
				module = args[argidx].c_str();
			}

			if (argidx < GetSize(args))
				cmd_error(args, argidx, "unknown option/parameter");

			if (!filename)
				log_cmd_error("Filname must be specified.\n");

			if (mode_vhdl)
#ifdef VERIFIC_VHDL_SUPPORT
				vhdl_file::PrettyPrint(filename, module, work.c_str());
#else
				goto check_error;
#endif
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			else
				veri_file::PrettyPrint(filename, module, work.c_str());
#endif
			goto check_error;
		}

		if (GetSize(args) > argidx && args[argidx] == "-import")
		{
			std::map<std::string,Netlist*> nl_todo, nl_done;
			bool mode_all = false, mode_gates = false, mode_keep = false;
			bool mode_nosva = false, mode_names = false, mode_verific = false;
			bool mode_autocover = false, mode_fullinit = false;
			bool flatten = false, extnets = false, mode_cells = false;
			bool split_complex_ports = true;
			string dumpfile;
			string ppfile;
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
				if (args[argidx] == "-no-split-complex-ports") {
					split_complex_ports = false;
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
#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
				if (args[argidx] == "-nosva") {
					mode_nosva = true;
					continue;
				}
				if (args[argidx] == "-L" && argidx+1 < GetSize(args)) {
					verific_sva_fsm_limit = atoi(args[++argidx].c_str());
					continue;
				}
				if (args[argidx] == "-autocover") {
					mode_autocover = true;
					continue;
				}
#endif
				if (args[argidx] == "-n") {
					mode_names = true;
					continue;
				}
				if (args[argidx] == "-fullinit") {
					mode_fullinit = true;
					continue;
				}
				if (args[argidx] == "-cells") {
					mode_cells = true;
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
				if (args[argidx] == "-pp" && argidx+1 < GetSize(args)) {
					ppfile = args[++argidx];
					continue;
				}
				break;
			}

			if (argidx > GetSize(args) && args[argidx].compare(0, 1, "-") == 0)
				cmd_error(args, argidx, "unknown option");

			std::set<std::string> top_mod_names;

			if (mode_all)
			{
				import_all(work.c_str(), &nl_todo, &parameters, true, ppfile);
			}
			else
			{
				if (argidx == GetSize(args))
					cmd_error(args, argidx, "No top module specified.\n");

				std::vector<std::string> tops;
				for (int i = argidx; i < GetSize(args); i++)
					tops.push_back(args[i].c_str());
				top_mod_names = import_tops(work.c_str(), &nl_todo, &parameters, true, ppfile, tops) ;
			}
			if (mode_cells) {
				log("Importing all cells.\n");
				Libset *gls = Libset::Global() ;
				MapIter it ;
				Library *l ;
				FOREACH_LIBRARY_OF_LIBSET(gls,it,l) {
					MapIter mi ;
					Verific::Cell *c ;
					FOREACH_CELL_OF_LIBRARY(l,mi,c) {
						if (!mode_verific && (l == Library::Primitives() || l == Library::Operators())) continue;
						MapIter ni ;
						if (c->NumOfNetlists() == 1) {
							c->GetFirstNetlist()->SetName("");
						}
						Netlist *nl;
						FOREACH_NETLIST_OF_CELL(c, ni, nl) {
							if (nl)
								nl_todo.emplace(nl->CellBaseName(), nl);
						}
					}
				}
			}

			if (!verific_error_msg.empty())
				goto check_error;

			if (flatten) {
				for (auto nl : nl_todo)
					nl.second->Flatten();
			}

			if (extnets) {
				VerificExtNets worker;
				for (auto nl : nl_todo)
					worker.run(nl.second);
			}

			if (split_complex_ports) {
				for (auto nl : nl_todo)
					nl.second->ChangePortBusStructures(1 /* hierarchical */);
			}

#ifdef VERIFIC_SYSTEMVERILOG_SUPPORT
			if (!dumpfile.empty()) {
				VeriWrite veri_writer;
				veri_writer.WriteFile(dumpfile.c_str(), Netlist::PresentDesign());
			}
#endif
			while (!nl_todo.empty()) {
				auto it = nl_todo.begin();
				Netlist *nl = it->second;
				if (nl_done.count(it->first) == 0) {
					VerificImporter importer(mode_gates, mode_keep, mode_nosva,
							mode_names, mode_verific, mode_autocover, mode_fullinit);
					nl_done[it->first] = it->second;
					importer.import_netlist(design, nl, nl_todo, top_mod_names.count(nl->CellBaseName()));
				}
				nl_todo.erase(it);
			}

			verific_cleanup();
			goto check_error;
		}

		if (argidx < GetSize(args) && args[argidx] == "-cfg")
		{
			if (argidx+1 == GetSize(args)) {
				MapIter mi;
				const char *k, *s;
				unsigned long v;
				pool<std::string> lines;
				FOREACH_MAP_ITEM(RuntimeFlags::GetVarMap(), mi, &k, &v) {
					lines.insert(stringf("%s %lu", k, v));
				}
				FOREACH_MAP_ITEM(RuntimeFlags::GetStringVarMap(), mi, &k, &s) {
					if (s == nullptr)
						lines.insert(stringf("%s NULL", k));
					else
						lines.insert(stringf("%s \"%s\"", k, s));
				}
				lines.sort();
				for (auto &line : lines)
					log("verific -cfg %s\n", line.c_str());
				goto check_error;
			}

			if (argidx+2 == GetSize(args)) {
				const char *k = args[argidx+1].c_str();
				if (RuntimeFlags::HasUnsignedVar(k)) {
					log("verific -cfg %s %lu\n", k, RuntimeFlags::GetVar(k));
					goto check_error;
				}
				if (RuntimeFlags::HasStringVar(k)) {
					const char *s = RuntimeFlags::GetStringVar(k);
					if (s == nullptr)
						log("verific -cfg %s NULL\n", k);
					else
						log("verific -cfg %s \"%s\"\n", k, s);
					goto check_error;
				}
				log_cmd_error("Can't find Verific Runtime flag '%s'.\n", k);
			}

			if (argidx+3 == GetSize(args)) {
				const auto &k = args[argidx+1], &v = args[argidx+2];
				if (v == "NULL") {
					RuntimeFlags::SetStringVar(k.c_str(), nullptr);
					goto check_error;
				}
				if (v[0] == '"') {
					std::string s = v.substr(1, GetSize(v)-2);
					RuntimeFlags::SetStringVar(k.c_str(), v.c_str());
					goto check_error;
				}
				char *endptr;
				unsigned long n = strtol(v.c_str(), &endptr, 0);
				if (*endptr == 0) {
					RuntimeFlags::SetVar(k.c_str(), n);
					goto check_error;
				}
			}
		}
#ifdef YOSYSHQ_VERIFIC_EXTENSIONS
		if (VerificExtensions::Execute(args, argidx, work, 
			[this](const std::vector<std::string> &args, size_t argidx, std::string msg)
				{ cmd_error(args, argidx, msg); } )) {
			goto check_error;
		}
#endif	

		cmd_error(args, argidx, "Missing or unsupported mode parameter.\n");

	check_error:
		if (tmp_files.size()) {
			log("Removing temp files.\n");
			for(auto &fn : tmp_files) {
				remove(fn.c_str());
			}
		}

		if (!verific_error_msg.empty())
			log_error("%s\n", verific_error_msg.c_str());

	}
#else /* YOSYS_ENABLE_VERIFIC */
	void execute(std::vector<std::string>, RTLIL::Design *) override {
		log_cmd_error("This version of Yosys is built without Verific support.\n"
				"\n"
				"Use YosysHQ Tabby CAD Suite if you need Yosys+Verific.\n"
				"https://www.yosyshq.com/\n"
				"\n"
				"Contact office@yosyshq.com for free evaluation\n"
				"binaries of YosysHQ Tabby CAD Suite.\n");
	}
#endif
} VerificPass;

struct ReadPass : public Pass {
	ReadPass() : Pass("read", "load HDL designs") { }
	void help() override
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
#ifdef VERIFIC_VHDL_SUPPORT
		log("    read {-vhdl87|-vhdl93|-vhdl2k|-vhdl2008|-vhdl2019|-vhdl} <vhdl-file>..\n");
		log("\n");
		log("Load the specified VHDL files. (Requires Verific.)\n");
		log("\n");
		log("\n");
#endif
#ifdef VERIFIC_EDIF_SUPPORT
		log("    read {-edif} <edif-file>..\n");
		log("\n");
		log("Load the specified EDIF files. (Requires Verific.)\n");
		log("\n");
		log("\n");
#endif
		log("    read {-liberty} <liberty-file>..\n");
		log("\n");
		log("Load the specified Liberty files.\n");
		log("\n");
		log("    -lib\n");
		log("        only create empty blackbox modules\n");
		log("\n");
		log("\n");
		log("    read {-f|-F} <command-file>\n");
		log("\n");
		log("Load and execute the specified command file. (Requires Verific.)\n");
		log("Check verific command for more information about supported commands in file.\n");
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
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
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

#ifdef VERIFIC_VHDL_SUPPORT
		if (args[1] == "-vhdl87" || args[1] == "-vhdl93" || args[1] == "-vhdl2k" || args[1] == "-vhdl2008" || args[1] == "-vhdl2019" || args[1] == "-vhdl") {
			if (use_verific) {
				args[0] = "verific";
				Pass::call(design, args);
			} else {
				cmd_error(args, 1, "This version of Yosys is built without Verific support.\n");
			}
			return;
		}
#endif
#ifdef VERIFIC_EDIF_SUPPORT
		if (args[1] == "-edif") {
			if (use_verific) {
				args[0] = "verific";
				Pass::call(design, args);
			} else {
				cmd_error(args, 1, "This version of Yosys is built without Verific support.\n");
			}
			return;
		}
#endif
		if (args[1] == "-liberty") {
			if (use_verific) {
				args[0] = "verific";
			} else {
				args[0] = "read_liberty";
			}
			Pass::call(design, args);
			return;
		}
		if (args[1] == "-f" || args[1] == "-F") {
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
