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
#include "kernel/rtlil.h"
#include "libs/json11/json11.hpp"

#ifdef YOSYS_ENABLE_TCL
#include <tcl.h>
#include <tclTomMath.h>
#include <tclTomMathDecls.h>
#endif

YOSYS_NAMESPACE_BEGIN

#ifdef YOSYS_ENABLE_TCL
bool yosys_tcl_repl_active = false;

void yosys_tcl_activate_repl()
{
	yosys_tcl_repl_active = true;
}

static Tcl_Obj *json_to_tcl(Tcl_Interp *interp, const json11::Json &json)
{
	if (json.is_null())
		return Tcl_NewStringObj("null", 4);
	else if (json.is_string()) {
		auto string = json.string_value();
		return Tcl_NewStringObj(string.data(), string.size());
	} else if (json.is_number()) {
		double value = json.number_value();
		double round_val = std::nearbyint(value);
		if (std::isfinite(round_val) && value == round_val && value >= LONG_MIN && value < -double(LONG_MIN))
			return Tcl_NewLongObj((long)round_val);
		else
			return Tcl_NewDoubleObj(value);
	} else if (json.is_bool()) {
		return Tcl_NewBooleanObj(json.bool_value());
	} else if (json.is_array()) {
		auto list = json.array_items();
		Tcl_Obj *result = Tcl_NewListObj(list.size(), nullptr);
		for (auto &item : list)
			Tcl_ListObjAppendElement(interp, result, json_to_tcl(interp, item));
		return result;
	} else if (json.is_object()) {
		auto map = json.object_items();
		Tcl_Obj *result = Tcl_NewListObj(map.size() * 2, nullptr);
		for (auto &item : map) {
			Tcl_ListObjAppendElement(interp, result, Tcl_NewStringObj(item.first.data(), item.first.size()));
			Tcl_ListObjAppendElement(interp, result, json_to_tcl(interp, item.second));
		}
		return result;
	} else {
		log_abort();
	}
}

static int tcl_yosys_cmd(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	std::vector<std::string> args;
	for (int i = 1; i < argc; i++)
		args.push_back(argv[i]);

	if (args.size() >= 1 && args[0] == "-import") {
		for (auto &it : pass_register) {
			std::string tcl_command_name = it.first;
			if (tcl_command_name == "proc")
				tcl_command_name = "procs";
			else if (tcl_command_name == "rename")
				tcl_command_name = "renames";
			Tcl_CmdInfo info;
			if (Tcl_GetCommandInfo(interp, tcl_command_name.c_str(), &info) != 0) {
				log("[TCL: yosys -import] Command name collision: found pre-existing command `%s' -> skip.\n", it.first.c_str());
			} else {
				std::string tcl_script = stringf("proc %s args { yosys %s {*}$args }", tcl_command_name.c_str(), it.first.c_str());
				Tcl_Eval(interp, tcl_script.c_str());
			}
		}
		return TCL_OK;
	}

	yosys_get_design()->scratchpad_unset("result.json");
	yosys_get_design()->scratchpad_unset("result.string");

	bool in_repl = yosys_tcl_repl_active;
	bool restore_log_cmd_error_throw = log_cmd_error_throw;

	log_cmd_error_throw = true;

	try {
		if (args.size() == 1) {
			Pass::call(yosys_get_design(), args[0]);
		} else {
			Pass::call(yosys_get_design(), args);
		}
	} catch (log_cmd_error_exception) {
		if (in_repl) {
			auto design = yosys_get_design();
			while (design->selection_stack.size() > 1)
				design->pop_selection();
			log_reset_stack();
		}
		Tcl_SetResult(interp, (char *)"Yosys command produced an error", TCL_STATIC);

		yosys_tcl_repl_active = in_repl;
		log_cmd_error_throw = restore_log_cmd_error_throw;
		return TCL_ERROR;
	} catch (...) {
		log_error("uncaught exception during Yosys command invoked from TCL\n");
	}

	yosys_tcl_repl_active = in_repl;
	log_cmd_error_throw = restore_log_cmd_error_throw;

	auto &scratchpad = yosys_get_design()->scratchpad;
	auto result = scratchpad.find("result.json");
	if (result != scratchpad.end()) {
		std::string err;
		auto json = json11::Json::parse(result->second, err);
		if (err.empty()) {
			Tcl_SetObjResult(interp, json_to_tcl(interp, json));
		} else
			log_warning("Ignoring result.json scratchpad value due to parse error: %s\n", err.c_str());
	} else if ((result = scratchpad.find("result.string")) != scratchpad.end()) {
		Tcl_SetObjResult(interp, Tcl_NewStringObj(result->second.data(), result->second.size()));
	}

	return TCL_OK;
}

#define FLAG(name) \
	if (!strcmp(argv[i], "-" #name)) { \
		name##_flag = true; \
		continue; \
	} \

#define FLAG2(name) \
	if (!strcmp(Tcl_GetString(objv[i]), "-" #name)) { \
		name##_flag = true; \
		continue; \
	} \

#define ERROR(str) \
	{ \
		Tcl_SetResult(interp, (char *)(str), TCL_STATIC); \
		return TCL_ERROR; \
	}

bool const_to_mp_int(const Const &a, mp_int *b, bool force_signed, bool force_unsigned)
{
	if (!a.is_fully_def())
		return false;

	if (mp_init(b))
		return false;

	bool negative = ((a.flags & RTLIL::CONST_FLAG_SIGNED) || force_signed) &&
					!force_unsigned &&
					!a.empty() && (a.back() == RTLIL::S1);

	for (int i = a.size() - 1; i >= 0; i--) {
		if (mp_mul_2d(b, 1, b)) {
			mp_clear(b);
			return false;
		}

		if ((a[i] == RTLIL::S1) ^ negative) {
			if (mp_add_d(b, 1, b)) {
				mp_clear(b);
				return false;
			}
		}
	}

	if (negative) {
		if (mp_add_d(b, 1, b) || mp_neg(b, b)) {
			mp_clear(b);
			return false;
		}
	}

	return true;
}

bool mp_int_to_const(mp_int *a, Const &b, bool is_signed)
{
	bool negative = (mp_cmp_d(a, 0) == MP_LT);
	if (negative && !is_signed)
		return false;

	if (negative) {
		mp_neg(a, a);
		mp_sub_d(a, 1, a);
	}

	std::vector<unsigned char> buf;
	buf.resize(mp_unsigned_bin_size(a));
	mp_to_unsigned_bin(a, buf.data());

	b.bits().reserve(mp_count_bits(a) + is_signed);
	for (int i = 0; i < mp_count_bits(a);) {
		for (int j = 0; j < 8 && i < mp_count_bits(a); j++, i++) {
			bool bv = ((buf.back() & (1 << j)) != 0) ^ negative;
			b.bits().push_back(bv ? RTLIL::S1 : RTLIL::S0);
		}
		buf.pop_back();
	}

	if (is_signed) {
		b.bits().push_back(negative ? RTLIL::S1 : RTLIL::S0);
	}

	return true;
}

static int tcl_get_attr(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	int i;
	bool mod_flag = false, string_flag = false, bool_flag = false;
	bool int_flag = false, sint_flag = false, uint_flag = false;
	for (i = 1; i < argc; i++) {
		FLAG(mod)
		FLAG(string)
		FLAG(int)
		FLAG(sint)
		FLAG(uint)
		FLAG(bool)
		break;
	}

	if ((mod_flag && i != argc - 2) ||
			(!mod_flag && i != argc - 3) ||
			(string_flag + int_flag + sint_flag + uint_flag + bool_flag > 1))
		ERROR("bad usage: expected \"get_attr -mod [-string|-int|-sint|-uint|-bool] <module> <attrname>\""
			  " or \"get_attr [-string|-int|-sint|-uint|-bool] <module> <identifier> <attrname>\"")

	IdString mod_id, obj_id, attr_id;
	mod_id = RTLIL::escape_id(argv[i++]);
	if (!mod_flag)
		obj_id = RTLIL::escape_id(argv[i++]);
	attr_id = RTLIL::escape_id(argv[i++]);

	RTLIL::Module *mod = yosys_design->module(mod_id);
	if (!mod)
		ERROR("module not found")

	RTLIL::AttrObject *obj = nullptr;
	if (mod_flag) {
		obj = mod;
	} else {
		obj = mod->wire(obj_id);
		if (!obj)
			obj = mod->memories.at(obj_id, nullptr);
		if (!obj)
			obj = mod->cell(obj_id);
		if (!obj)
			obj = mod->processes.at(obj_id, nullptr);
	}

	if (!obj)
		ERROR("object not found")

	if (string_flag) {
		Tcl_SetResult(interp, (char *) obj->get_string_attribute(attr_id).c_str(), TCL_VOLATILE);
	} else if (int_flag || uint_flag || sint_flag) {
		if (!obj->has_attribute(attr_id))
			ERROR("attribute missing (required for -int)");
		RTLIL::Const &value = obj->attributes.at(attr_id);

		mp_int value_mp;
		if (!const_to_mp_int(value, &value_mp, sint_flag, uint_flag))
			ERROR("bignum manipulation failed");
		Tcl_SetObjResult(interp, Tcl_NewBignumObj(&value_mp));
	} else if (bool_flag) {
		Tcl_SetObjResult(interp, Tcl_NewBooleanObj(obj->get_bool_attribute(attr_id)));
	} else {
		if (!obj->has_attribute(attr_id))
			ERROR("attribute missing (required unless -bool or -string)")

		Tcl_SetResult(interp, (char *) obj->attributes.at(attr_id).as_string().c_str(), TCL_VOLATILE);
	}

	return TCL_OK;
}

static int tcl_has_attr(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	int i;
	bool mod_flag = false;
	for (i = 1; i < argc; i++) {
		FLAG(mod)
		break;
	}

	if ((mod_flag && i != argc - 2) ||
			(!mod_flag && i != argc - 3))
		ERROR("bad usage: expected \"has_attr -mod <module> <attrname>\""
			  " or \"has_attr <module> <identifier> <attrname>\"")

	IdString mod_id, obj_id, attr_id;
	mod_id = RTLIL::escape_id(argv[i++]);
	if (!mod_flag)
		obj_id = RTLIL::escape_id(argv[i++]);
	attr_id = RTLIL::escape_id(argv[i++]);

	RTLIL::Module *mod = yosys_design->module(mod_id);
	if (!mod)
		ERROR("module not found")

	RTLIL::AttrObject *obj = nullptr;
	if (mod_flag) {
		obj = mod;
	} else {
		obj = mod->wire(obj_id);
		if (!obj)
			obj = mod->memories.at(obj_id, nullptr);
		if (!obj)
			obj = mod->cell(obj_id);
		if (!obj)
			obj = mod->processes.at(obj_id, nullptr);
	}

	if (!obj)
		ERROR("object not found")

	Tcl_SetResult(interp, (char *) std::to_string(obj->has_attribute(attr_id)).c_str(), TCL_VOLATILE);
	return TCL_OK;
}

static int tcl_set_attr(ClientData, Tcl_Interp *interp, int objc, Tcl_Obj *const objv[])
{
	int i;
	bool mod_flag = false, string_flag = false, bool_flag = false;
	bool true_flag = false, false_flag = false, sint_flag = false, uint_flag = false;
	for (i = 1; i < objc; i++) {
		FLAG2(mod)
		FLAG2(string)
		FLAG2(true)
		FLAG2(false)
		FLAG2(sint)
		FLAG2(uint)
		FLAG2(bool)
		break;
	}

	if ((i != objc - (2 + !mod_flag + !(true_flag || false_flag))) ||
			(string_flag + sint_flag + uint_flag + bool_flag + true_flag + false_flag > 1))
		ERROR("bad usage: expected \"set_attr -mod [-string|-sint|-uint|-bool] <module> <attrname> <value>\""
			  " or \"set_attr [-string|-sint|-uint|-bool] <module> <identifier> <attrname> <value>\""
			  " or \"set_attr [-true|-false] <module> <identifier> <attrname>\""
			  " or \"set_attr -mod [-true|-false| <module> <attrname>\"")

	IdString mod_id, obj_id, attr_id;
	mod_id = RTLIL::escape_id(Tcl_GetString(objv[i++]));
	if (!mod_flag)
		obj_id = RTLIL::escape_id(Tcl_GetString(objv[i++]));
	attr_id = RTLIL::escape_id(Tcl_GetString(objv[i++]));

	RTLIL::Module *mod = yosys_design->module(mod_id);
	if (!mod)
		ERROR("module not found")

	RTLIL::AttrObject *obj = nullptr;
	if (mod_flag) {
		obj = mod;
	} else {
		obj = mod->wire(obj_id);
		if (!obj)
			obj = mod->memories.at(obj_id, nullptr);
		if (!obj)
			obj = mod->cell(obj_id);
		if (!obj)
			obj = mod->processes.at(obj_id, nullptr);
	}

	if (!obj)
		ERROR("object not found")

	if (string_flag) {
		obj->set_string_attribute(attr_id, Tcl_GetString(objv[i++]));
	} else if (sint_flag || uint_flag) {
		RTLIL::Const const_;
		mp_int value_mp;

		if (Tcl_TakeBignumFromObj(interp, objv[i++], &value_mp))
			ERROR("non-integral value")

		if (!mp_int_to_const(&value_mp, const_, sint_flag))
			ERROR("bignum manipulation failed");

		if (sint_flag) {
			const_.flags |= RTLIL::CONST_FLAG_SIGNED;
			if (const_.size() < 32)
				const_.exts(32);
		} else {
			if (const_.size() < 32)
				const_.extu(32);
		}

		obj->attributes[attr_id] = const_;
	} else if (bool_flag) {
		obj->set_bool_attribute(attr_id, atoi(Tcl_GetString(objv[i++])) != 0);
	} else if (true_flag) {
		obj->set_bool_attribute(attr_id, true);
	} else if (false_flag) {
		obj->set_bool_attribute(attr_id, false);
	} else {
		obj->attributes[attr_id] = Const::from_string(std::string(Tcl_GetString(objv[i++])));
	}

	return TCL_OK;
}

static int tcl_get_param(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	int i;
	bool string_flag = false;
	bool int_flag = false, sint_flag = false, uint_flag = false;
	for (i = 1; i < argc; i++) {
		FLAG(string)
		FLAG(int)
		FLAG(sint)
		FLAG(uint)
		break;
	}

	if ((i != argc - 3) ||
			(string_flag + int_flag > 1))
		ERROR("bad usage: expected \"get_param [-string|-int|-sint|-uint] <module> <cellid> <paramname>")

	IdString mod_id, cell_id, param_id;
	mod_id = RTLIL::escape_id(argv[i++]);
	cell_id = RTLIL::escape_id(argv[i++]);
	param_id = RTLIL::escape_id(argv[i++]);

	RTLIL::Module *mod = yosys_design->module(mod_id);
	if (!mod)
		ERROR("module not found")

	RTLIL::Cell *cell = mod->cell(cell_id);
	if (!cell)
		ERROR("object not found")

	if (!cell->hasParam(param_id))
		ERROR("parameter missing")

	const RTLIL::Const &value = cell->getParam(param_id);

	if (string_flag) {
		Tcl_SetResult(interp, (char *) value.decode_string().c_str(), TCL_VOLATILE);
	} else if (int_flag || uint_flag || sint_flag) {
		mp_int value_mp;
		if (!const_to_mp_int(value, &value_mp, sint_flag, uint_flag))
			ERROR("bignum manipulation failed");
		Tcl_SetObjResult(interp, Tcl_NewBignumObj(&value_mp));
	} else {
		Tcl_SetResult(interp, (char *) value.as_string().c_str(), TCL_VOLATILE);
	}
	return TCL_OK;
}

static int tcl_set_param(ClientData, Tcl_Interp *interp, int objc, Tcl_Obj *const objv[])
{
	int i;
	bool string_flag = false, sint_flag = false, uint_flag = false;
	for (i = 1; i < objc; i++) {
		FLAG2(string)
		FLAG2(sint)
		FLAG2(uint)
		break;
	}

	if ((i != objc - 4) ||
			(string_flag + sint_flag + uint_flag > 1))
		ERROR("bad usage: expected \"set_param [-string|-sint|-uint] <module> <cellid> <paramname> <value>")

	IdString mod_id, cell_id, param_id;
	mod_id = RTLIL::escape_id(Tcl_GetString(objv[i++]));
	cell_id = RTLIL::escape_id(Tcl_GetString(objv[i++]));
	param_id = RTLIL::escape_id(Tcl_GetString(objv[i++]));

	RTLIL::Module *mod = yosys_design->module(mod_id);
	if (!mod)
		ERROR("module not found")

	RTLIL::Cell *cell = mod->cell(cell_id);
	if (!cell)
		ERROR("object not found")

	if (string_flag) {
		cell->setParam(param_id, Const(std::string(Tcl_GetString(objv[i++]))));
	} else if (sint_flag || uint_flag) {
		RTLIL::Const const_;
		mp_int value_mp;

		if (Tcl_TakeBignumFromObj(interp, objv[i++], &value_mp))
			ERROR("non-integral value")

		if (!mp_int_to_const(&value_mp, const_, sint_flag))
			ERROR("bignum manipulation failed");

		if (sint_flag) {
			const_.flags |= RTLIL::CONST_FLAG_SIGNED;
			if (const_.size() < 32)
				const_.exts(32);
		} else {
			if (const_.size() < 32)
				const_.extu(32);
		}

		cell->setParam(param_id, const_);
	} else {
		cell->setParam(param_id, Const::from_string(std::string(Tcl_GetString(objv[i++]))));
	}
	return TCL_OK;
}

int yosys_tcl_iterp_init(Tcl_Interp *interp)
{
	if (Tcl_Init(interp)!=TCL_OK)
		log_warning("Tcl_Init() call failed - %s\n",Tcl_ErrnoMsg(Tcl_GetErrno()));
	Tcl_CreateCommand(interp, "yosys", tcl_yosys_cmd, NULL, NULL);
	Tcl_CreateCommand(interp, "rtlil::get_attr", tcl_get_attr, NULL, NULL);
	Tcl_CreateCommand(interp, "rtlil::has_attr", tcl_has_attr, NULL, NULL);
	Tcl_CreateObjCommand(interp, "rtlil::set_attr", tcl_set_attr, NULL, NULL);
	Tcl_CreateCommand(interp, "rtlil::get_param", tcl_get_param, NULL, NULL);
	Tcl_CreateObjCommand(interp, "rtlil::set_param", tcl_set_param, NULL, NULL);

	// TODO:
	//
	// port_list
	// wire_list
	// cell_list
	// wire_width
	//
	// add_wire
	// add_cell
	// rename_wire
	// rename_cell
	// remove
	//
	// SigSpec land
	//
	// get_conn
	// set_conn
	// unpack
	// pack

	// Note (dev jf 24-12-02): Make log_id escape everything that’s not a valid 
	// verilog identifier before adding any tcl API that returns IdString values
	// to avoid -option injection

	return TCL_OK ;
}
#endif

YOSYS_NAMESPACE_END
