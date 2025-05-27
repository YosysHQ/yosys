#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
#include <tcl.h>
#include <list>


USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

template<typename T>
static bool parse_flag(char* arg, const char* flag_name, T& flag_var) {
	std::string expected = std::string("-") + flag_name;
	if (expected == arg) {
		flag_var = true;
		return true;
	}
	return false;
}

// TODO return values like json_to_tcl on result.json?
// TODO vectors
// TODO cell arrays?

static int sdc_get_pins_cmd(ClientData, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	(void)interp;
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
	log("get_pins patterns:\n");
	for (auto pat : patterns) {
		log("\t%s\n", pat.c_str());
	}
	(void)hierarchical_flag;
	(void)regexp_flag;
	(void)nocase_flag;
	(void)of_objects;
	if (separator != "/") {
		Tcl_SetObjResult(interp, Tcl_NewStringObj("Only '/' accepted as separator", -1));
		return TCL_ERROR;
	}
	return TCL_OK;
}

static int sdc_get_ports_cmd(ClientData, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	(void)interp;
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
	log("get_ports patterns:\n");
	for (auto pat : patterns) {
		log("\t%s\n", pat.c_str());
	}
	(void)regexp_flag;
	(void)nocase_flag;
	return TCL_OK;
}

class SDCInterpreter
{
private:
	Tcl_Interp* interp = nullptr;
public:
	~SDCInterpreter() {
		if (interp)
			Tcl_DeleteInterp(interp);
	}
	static SDCInterpreter& get() {
		static SDCInterpreter instance;
		return instance;
	}
	Tcl_Interp* fresh_interp() {
		if (interp)
			Tcl_DeleteInterp(interp);
		interp = Tcl_CreateInterp();
		if (Tcl_Init(interp)!=TCL_OK)
			log_warning("Tcl_Init() call failed - %s\n",Tcl_ErrnoMsg(Tcl_GetErrno()));
		Tcl_CreateObjCommand(interp, "get_pins", sdc_get_pins_cmd, NULL, NULL);
		Tcl_CreateObjCommand(interp, "get_ports", sdc_get_ports_cmd, NULL, NULL);
		return interp;
	}
};

struct SdcObjects {
	std::vector<std::string> ports;
	std::vector<std::pair<std::string, Cell*>> cells;
	std::vector<std::pair<std::string, Cell*>> pins;
	std::vector<std::pair<std::string, Wire*>> nets;

	void sniff_module(std::list<std::string>& hierarchy, Module* mod) {
		log_debug("sniffing module %s\n", mod->name.c_str());

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
			nets.push_back(std::make_pair(path, wire));
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
			cells.push_back(std::make_pair(path, cell));
			for (auto pin : cell->connections()) {
				std::string pin_name = path + "/" + pin.first.str().substr(1);
				pins.push_back(std::make_pair(pin_name, cell));
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
			ports.push_back(port.str().substr(1));
		}
		std::list<std::string> hierarchy{};
		sniff_module(hierarchy, top);
	}
	void dump() {
		log("Dumping detected design objects visible to SDC constraints\n");
		log("Ports:\n");
		for (auto name : ports) {
			log("\t%s\n", name.c_str());
		}
		log("Cells:\n");
		for (auto [name, cell] : cells) {
			(void)cell;
			log("\t%s\n", name.c_str());
		}
		log("Pins:\n");
		for (auto [name, pin] : pins) {
			(void)pin;
			log("\t%s\n", name.c_str());
		}
		log("Nets:\n");
		for (auto [name, net] : nets) {
			(void)net;
			log("\t%s\n", name.c_str());
		}
		log("\n");
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
		Tcl_Interp *interp = SDCInterpreter::get().fresh_interp();
		Tcl_Preserve(interp);
		std::string stub_path = "+/sdc/stubs.sdc";
		rewrite_filename(stub_path);
		SdcObjects objects(design);
		objects.dump();
		if (Tcl_EvalFile(interp, stub_path.c_str()) != TCL_OK)
			log_cmd_error("SDC interpreter returned an error in stub file: %s\n", Tcl_GetStringResult(interp));
		if (Tcl_EvalFile(interp, args[1].c_str()) != TCL_OK)
			log_cmd_error("SDC interpreter returned an error: %s\n", Tcl_GetStringResult(interp));
		Tcl_Release(interp);
	}
} SdcPass;

YOSYS_NAMESPACE_END
