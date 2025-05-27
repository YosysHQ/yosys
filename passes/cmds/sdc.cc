#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
#include <tcl.h>
#include <list>


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN


struct SdcObjects {
	std::vector<std::string> design_ports;
	std::vector<std::pair<std::string, Cell*>> design_cells;
	std::vector<std::pair<std::string, Cell*>> design_pins;
	std::vector<std::pair<std::string, Wire*>> design_nets;

	pool<std::string> constrained_ports;
	pool<std::pair<std::string, Cell*>> constrained_cells;
	pool<std::pair<std::string, Cell*>> constrained_pins;
	pool<std::pair<std::string, Wire*>> constrained_nets;

	void sniff_module(std::list<std::string>& hierarchy, Module* mod) {
		std::string prefix;
		for (auto mod_name : hierarchy) {
			if (prefix.length())
				prefix += "/"; // TODO seperator?
			prefix += mod_name;
		}

		for (auto* wire : mod->wires()) {
			std::string name = wire->name.str();
			log_assert(name.length());
			// TODO: really skip internal wires?
			if (name[0] == '$')
				continue;
			name = name.substr(1);
			std::string path = prefix;
			if (path.length())
				path += "/";
			path += name;
			design_nets.push_back(std::make_pair(path, wire));
		}

		for (auto* cell : mod->cells()) {
			std::string name = cell->name.str();
			// TODO: really skip internal cells?
			if (name[0] == '$')
				continue;
			name = name.substr(1);
			std::string path = prefix;
			if (path.length())
				path += "/";
			path += name;
			design_cells.push_back(std::make_pair(path, cell));
			for (auto pin : cell->connections()) {
				std::string pin_name = path + "/" + pin.first.str().substr(1);
				design_pins.push_back(std::make_pair(pin_name, cell));
			}
			if (auto sub_mod = mod->design->module(cell->type)) {
				hierarchy.push_back(name);
				sniff_module(hierarchy, sub_mod);
				hierarchy.pop_back();
			}
		}
	}
	SdcObjects(Design* design) {
		Module* top = design->top_module();
		if (!top)
			log_error("Top module couldn't be determined. Check 'top' attribute usage");
		for (auto port : top->ports) {
			design_ports.push_back(port.str().substr(1));
		}
		std::list<std::string> hierarchy{};
		sniff_module(hierarchy, top);
	}
	~SdcObjects() = default;
	void dump() {
		std::sort(design_ports.begin(), design_ports.end());
		std::sort(design_cells.begin(), design_cells.end());
		std::sort(design_pins.begin(), design_pins.end());
		std::sort(design_nets.begin(), design_nets.end());
		constrained_ports.sort();
		constrained_cells.sort();
		constrained_pins.sort();
		constrained_nets.sort();
		log("Design ports:\n");
		for (auto name : design_ports) {
			log("\t%s\n", name.c_str());
		}
		log("Design cells:\n");
		for (auto [name, cell] : design_cells) {
			(void)cell;
			log("\t%s\n", name.c_str());
		}
		log("Design pins:\n");
		for (auto [name, pin] : design_pins) {
			(void)pin;
			log("\t%s\n", name.c_str());
		}
		log("Design nets:\n");
		for (auto [name, net] : design_nets) {
			(void)net;
			log("\t%s\n", name.c_str());
		}
		log("\n");
		log("Constrained ports:\n");
		for (auto name : constrained_ports) {
			log("\t%s\n", name.c_str());
		}
		log("Constrained cells:\n");
		for (auto [name, cell] : constrained_cells) {
			(void)cell;
			log("\t%s\n", name.c_str());
		}
		log("Constrained pins:\n");
		for (auto [name, pin] : constrained_pins) {
			(void)pin;
			log("\t%s\n", name.c_str());
		}
		log("Constrained nets:\n");
		for (auto [name, net] : constrained_nets) {
			(void)net;
			log("\t%s\n", name.c_str());
		}
		log("\n");
	}
};

template<typename T>
static bool parse_flag(char* arg, const char* flag_name, T& flag_var) {
	std::string expected = std::string("-") + flag_name;
	if (expected == arg) {
		flag_var = true;
		return true;
	}
	return false;
}

// TODO vectors
// TODO cell arrays?

static int sdc_get_pins_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	(void)interp;
	auto* objects = (SdcObjects*)data;
	// When this flag is present, the search for the pattern is made in all positions in the hierarchy.
	bool hierarchical_flag = false;
	bool regexp_flag = false;
	bool nocase_flag = false;
	std::string separator = "/";
	Tcl_Obj* of_objects;
	std::vector<std::string> patterns;
	int i = 1;
	for (; i < objc; i++) {
		if (parse_flag(Tcl_GetString(objv[i]), "hierarchical", hierarchical_flag)) continue;
		if (parse_flag(Tcl_GetString(objv[i]), "hier", hierarchical_flag)) continue;
		if (parse_flag(Tcl_GetString(objv[i]), "regexp", regexp_flag)) continue;
		if (parse_flag(Tcl_GetString(objv[i]), "nocase", nocase_flag)) continue;
		if (!strcmp(Tcl_GetString(objv[i]), "-hsc")) {
			separator = Tcl_GetString(objv[++i]);
			continue;
		}
		if (!strcmp(Tcl_GetString(objv[i]), "-of_objects")) {
			of_objects = objv[++i];
			continue;
		}
		// Onto the next loop
		break;
	}
	for (; i < objc; i++) {
		patterns.push_back(Tcl_GetString(objv[i]));
	}
	std::vector<std::pair<std::string, Cell*>> resolved;
	for (auto pat : patterns) {
		bool found = false;
		for (auto [name, pin] : objects->design_pins) {
			if (name == pat) {
				found = true;
				resolved.push_back(std::make_pair(name, pin));
			}
		}
		if (!found)
			log_warning("No matches in design for pin %s\n", pat.c_str());
	}
	Tcl_Obj *result = Tcl_NewListObj(resolved.size(), nullptr);
	for (auto obj : resolved) {
		Tcl_ListObjAppendElement(interp, result, Tcl_NewStringObj(obj.first.c_str(), obj.first.size()));
		objects->constrained_pins.insert(obj);
	}
	(void)hierarchical_flag;
	(void)regexp_flag;
	(void)nocase_flag;
	(void)of_objects;

	if (separator != "/") {
		Tcl_SetResult(interp, (char *)"Only '/' accepted as separator", TCL_STATIC);
		return TCL_ERROR;
	}

	Tcl_SetObjResult(interp, result);
	return TCL_OK;
}

static int sdc_get_ports_cmd(ClientData data, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	(void)interp;
	auto* objects = (SdcObjects*)data;
	bool regexp_flag = false;
	bool nocase_flag = false;
	std::vector<std::string> patterns;
	int i = 1;
	for (; i < objc; i++) {
		if (parse_flag(Tcl_GetString(objv[i]), "regexp", regexp_flag)) continue;
		if (parse_flag(Tcl_GetString(objv[i]), "nocase", nocase_flag)) continue;
		// Onto the next loop
		break;
	}
	for (; i < objc; i++) {
		patterns.push_back(Tcl_GetString(objv[i]));
	}
	std::vector<std::string> resolved;
	for (auto pat : patterns) {
		bool found = false;
		for (auto name : objects->design_ports) {
			if (name == pat) {
				found = true;
				resolved.push_back(name);
			}
		}
		if (!found)
			log_warning("No matches in design for port %s\n", pat.c_str());
	}
	Tcl_Obj *result = Tcl_NewListObj(resolved.size(), nullptr);
	for (auto obj : resolved) {
		Tcl_ListObjAppendElement(interp, result, Tcl_NewStringObj(obj.c_str(), obj.size()));
		objects->constrained_ports.insert(obj);
	}
	(void)regexp_flag;
	(void)nocase_flag;
	Tcl_SetObjResult(interp, result);
	return TCL_OK;
}


class SDCInterpreter
{
private:
	Tcl_Interp* interp = nullptr;
public:
	std::unique_ptr<SdcObjects> objects;
	~SDCInterpreter() {
		if (interp)
			Tcl_DeleteInterp(interp);
	}
	static SDCInterpreter& get() {
		static SDCInterpreter instance;
		return instance;
	}
	Tcl_Interp* fresh_interp(Design* design) {
		if (interp)
			Tcl_DeleteInterp(interp);

		interp = Tcl_CreateInterp();
		if (Tcl_Init(interp)!=TCL_OK)
			log_error("Tcl_Init() call failed - %s\n",Tcl_ErrnoMsg(Tcl_GetErrno()));

		objects = std::make_unique<SdcObjects>(design);
		Tcl_CreateObjCommand(interp, "get_pins", sdc_get_pins_cmd, (ClientData) objects.get(), NULL);
		Tcl_CreateObjCommand(interp, "get_ports", sdc_get_ports_cmd, (ClientData) objects.get(), NULL);
		return interp;
	}
};

// Also see TclPass
struct SdcPass : public Pass {
	// TODO help
	SdcPass() : Pass("sdc", "sniff at some SDC") { }
	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		if (args.size() < 2)
			log_cmd_error("Missing SDC file.\n");
		// TODO optional extra stub file
		SDCInterpreter& sdc = SDCInterpreter::get();
		Tcl_Interp *interp = sdc.fresh_interp(design);
		Tcl_Preserve(interp);
		std::string stub_path = "+/sdc/stubs.sdc";
		rewrite_filename(stub_path);
		if (Tcl_EvalFile(interp, stub_path.c_str()) != TCL_OK)
			log_cmd_error("SDC interpreter returned an error in stub file: %s\n", Tcl_GetStringResult(interp));
		if (Tcl_EvalFile(interp, args[1].c_str()) != TCL_OK)
			log_cmd_error("SDC interpreter returned an error: %s\n", Tcl_GetStringResult(interp));
		sdc.objects->dump();
		Tcl_Release(interp);
	}
} SdcPass;

YOSYS_NAMESPACE_END
