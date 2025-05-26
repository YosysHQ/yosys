#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"
#include <tcl.h>


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

static int sdc_get_pins_cmd(ClientData, Tcl_Interp *interp, int objc, Tcl_Obj* const objv[])
{
	(void)interp;
	bool hierarchical_flag = false;
	bool regexp_flag = false;
	bool nocase_flag = false;
	std::string separator = "/";
	Tcl_Obj* of_objects;
	std::vector<std::string> patterns;
	int i = 1;
	for (; i < objc; i++) {
        if (parse_flag(Tcl_GetString(objv[i]), "hierarchical", hierarchical_flag))
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
	(void)separator;
	(void)of_objects;
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
        return interp;
    }
};

// Also see TclPass
struct SdcPass : public Pass {
	SdcPass() : Pass("sdc", "sniff at some SDC") { }
	void execute(std::vector<std::string> args, RTLIL::Design *) override {
		if (args.size() < 2)
			log_cmd_error("Missing script file.\n");

		std::vector<Tcl_Obj*> script_args;
		for (auto it = args.begin() + 2; it != args.end(); ++it)
			script_args.push_back(Tcl_NewStringObj((*it).c_str(), (*it).size()));

		Tcl_Interp *interp = SDCInterpreter::get().fresh_interp();
		Tcl_Preserve(interp);
		Tcl_ObjSetVar2(interp, Tcl_NewStringObj("argc", 4), NULL, Tcl_NewIntObj(script_args.size()), 0);
		Tcl_ObjSetVar2(interp, Tcl_NewStringObj("argv", 4), NULL, Tcl_NewListObj(script_args.size(), script_args.data()), 0);
		Tcl_ObjSetVar2(interp, Tcl_NewStringObj("argv0", 5), NULL, Tcl_NewStringObj(args[1].c_str(), args[1].size()), 0);

        std::string stub_path = "+/sdc/stubs.sdc";
        rewrite_filename(stub_path);
		if (Tcl_EvalFile(interp, stub_path.c_str()) != TCL_OK)
            log_cmd_error("SDC interpreter returned an error in stub file: %s\n", Tcl_GetStringResult(interp));
		if (Tcl_EvalFile(interp, args[1].c_str()) != TCL_OK)
			log_cmd_error("SDC interpreter returned an error: %s\n", Tcl_GetStringResult(interp));
		Tcl_Release(interp);
	}
} SdcPass;

YOSYS_NAMESPACE_END
