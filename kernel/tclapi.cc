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
				design->selection_stack.pop_back();
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

#define ERROR(str) \
	{ \
		Tcl_SetResult(interp, (char *)(str), TCL_STATIC); \
		return TCL_ERROR; \
	}

static int tcl_get_attr(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	int i;
	bool mod_flag = false, string_flag = false, int_flag = false, bool_flag = false;
	for (i = 1; i < argc; i++) {
		FLAG(mod)
		FLAG(string)
		FLAG(int)
		FLAG(bool)
		break;
	}

	if ((mod_flag && i != argc - 2) ||
			(!mod_flag && i != argc - 3) ||
			(string_flag + int_flag + bool_flag > 1))
		ERROR("bad usage: expected \"get_attr -mod [-string|-int|-bool] <module> <attrname>\""
			  " or \"get_attr [-string|-int|-bool] <module> <identifier> <attrname>\"")

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
	} else if (int_flag) {
		if (!obj->has_attribute(attr_id))
			ERROR("attribute missing (required for -int)");

		RTLIL::Const &value = obj->attributes.at(attr_id);
		if (value.size() > 32)
			ERROR("value too large")

		// FIXME: 32'hffffffff will return as negative despite is_signed=false
		Tcl_SetResult(interp, (char *) std::to_string(value.as_int()).c_str(), TCL_VOLATILE);
	} else if (bool_flag) {
		bool value = obj->get_bool_attribute(attr_id);
		Tcl_SetResult(interp, (char *) std::to_string(value).c_str(), TCL_VOLATILE);
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

static int tcl_set_attr(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	int i;
	bool mod_flag = false, string_flag = false, int_flag = false, bool_flag = false;
	bool false_flag = false, true_flag = false;
	for (i = 1; i < argc; i++) {
		FLAG(mod)
		FLAG(string)
		FLAG(int)
		FLAG(bool)
		FLAG(false)
		FLAG(true)
		break;
	}

	if ((i != argc - (2 + !mod_flag + !(true_flag || false_flag))) ||
			(string_flag + int_flag + bool_flag + true_flag + false_flag > 1))
		ERROR("bad usage: expected \"set_attr -mod [-string|-int|-bool] <module> <attrname> <value>\""
			  " or \"set_attr [-string|-int|-bool] <module> <identifier> <attrname> <value>\""
			  " or \"set_attr [-true|-false] <module> <identifier> <attrname>\""
			  " or \"set_attr -mod [-true|-false| <module> <attrname>\"")

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
		obj->set_string_attribute(attr_id, argv[i++]);
	} else if (int_flag) {
		obj->attributes[attr_id] = atoi(argv[i++]);
	} else if (bool_flag) {
		obj->set_bool_attribute(attr_id, atoi(argv[i++]) != 0);
	} else if (true_flag) {
		obj->set_bool_attribute(attr_id, true);
	} else if (false_flag) {
		obj->set_bool_attribute(attr_id, false);
	} else {
		obj->attributes[attr_id] = Const::from_string(std::string(argv[i++]));
	}

	return TCL_OK;
}

static int tcl_get_param(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	int i;
	bool string_flag = false, int_flag = false;
	for (i = 1; i < argc; i++) {
		FLAG(string)
		FLAG(int)
		break;
	}

	if ((i != argc - 3) ||
			(string_flag + int_flag > 1))
		ERROR("bad usage: expected \"get_param [-string|-int] <module> <cellid> <paramname>")

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
	} else if (int_flag) {
		if (value.size() > 32)
			ERROR("value too large")

		Tcl_SetResult(interp, (char *) std::to_string(value.as_int()).c_str(), TCL_VOLATILE);
	} else {
		Tcl_SetResult(interp, (char *) value.as_string().c_str(), TCL_VOLATILE);
	}
	return TCL_OK;
}

static int tcl_set_param(ClientData, Tcl_Interp *interp, int argc, const char *argv[])
{
	int i;
	bool string_flag = false, int_flag = false;
	for (i = 1; i < argc; i++) {
		FLAG(string)
		FLAG(int)
		break;
	}

	if ((i != argc - 4) ||
			(string_flag + int_flag > 1))
		ERROR("bad usage: expected \"get_param [-string|-int] <module> <cellid> <paramname> <value>")

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

	if (string_flag) {
		cell->setParam(param_id, Const(std::string(argv[i++])));
	} else if (int_flag) {
		cell->setParam(param_id, Const(atoi(argv[i++])));
	} else {
		cell->setParam(param_id, Const::from_string(std::string(argv[i++])));
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
	Tcl_CreateCommand(interp, "rtlil::set_attr", tcl_set_attr, NULL, NULL);
	Tcl_CreateCommand(interp, "rtlil::get_param", tcl_get_param, NULL, NULL);
	Tcl_CreateCommand(interp, "rtlil::set_param", tcl_set_param, NULL, NULL);

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

	return TCL_OK ;
}
#endif

YOSYS_NAMESPACE_END
