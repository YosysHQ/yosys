#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct TestSelectPass : public Pass {
	TestSelectPass() : Pass("test_select", "call internal selection methods on design for testing purposes") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    test_select [options]\n");
		log("\n");
		log("Test semantics of internal 'RTLIL::Design::selected_modules()' by modifying the\n");
		log("current selection to only include the results of the call.\n");
		log("\n");
		log("Includes partially selected modules by default, use one of the following options\n");
		log("to remove them instead:\n");
		log("\n");
		log("    -whole_only\n");
		log("\n");
		log("    -whole_warn\n");
		log("    -whole_err\n");
		log("    -whole_cmderr\n");
		log("        remove partially selected modules, raising warning, error, or cmd error\n");
		log("\n");
		log("    test_select -unboxed_only [options]\n");
		log("\n");
		log("Remove boxed modules from selection.\n");
		log("\n");
		log("    -include_wb\n");
		log("        don't remove white boxes from selection\n");
		log("\n");
		log("    -warn_boxes\n");
		log("    -err_boxes\n");
		log("    -cmderr_boxes\n");
		log("        raise warning, error, or cmd error if a box is removed\n");
		log("\n");
	}
	void execute(vector<string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing TEST_SELECTION pass.\n");
		bool whole_only = false;
		bool whole_warn = false;
		bool whole_err = false;
		bool whole_cmderr = false;
		int whole_opts = 0;

		bool warn_boxes = false;
		bool err_boxes = false;
		bool cmderr_boxes = false;
		int box_level = 0;

		bool unboxed_only = false;
		bool include_wb = false;

		int argidx;
		for (argidx = 1; argidx < GetSize(args); argidx++)
		{
			if (args[argidx] == "-whole_only") {
				whole_only = true;
				whole_opts++;
				continue;
			}
			if (args[argidx] == "-whole_warn") {
				whole_warn = true;
				whole_opts++;
				continue;
			}
			if (args[argidx] == "-whole_err") {
				whole_err = true;
				whole_opts++;
				continue;
			}
			if (args[argidx] == "-whole_cmderr") {
				whole_cmderr = true;
				whole_opts++;
				continue;
			}
			if (args[argidx] == "-warn_boxes") {
				warn_boxes = true;
				box_level++;
				continue;
			}
			if (args[argidx] == "-err_boxes") {
				err_boxes = true;
				box_level++;
				continue;
			}
			if (args[argidx] == "-cmderr_boxes") {
				cmderr_boxes = true;
				box_level++;
				continue;
			}
			if (args[argidx] == "-unboxed_only") {
				unboxed_only = true;
				continue;
			}
			if (args[argidx] == "-include_wb") {
				include_wb = true;
				continue;
			}
			break;
		}

		if (whole_opts > 1)
			log_cmd_error("Only one of -whole_only, -whole_warn, -whole_err, or -whole_cmderr may be selected.\n");

		if (include_wb && !unboxed_only)
			log_cmd_error("-include_wb option requires -unboxed_only.\n");

		if (box_level > 0 && !unboxed_only)
			log_cmd_error("-*_boxes options require -unboxed_only.\n");

		if (box_level > 1)
			log_cmd_error("Only one of -warn_boxes, -err_boxes, or -cmderr_boxes may be selected.\n");

		extra_args(args, argidx, design, false);

		// construct enums
		RTLIL::SelectPartials partials;
		if (whole_only)
			partials = RTLIL::SELECT_WHOLE_ONLY;
		else if (whole_warn)
			partials = RTLIL::SELECT_WHOLE_WARN;
		else if (whole_err)
			partials = RTLIL::SELECT_WHOLE_ERR;
		else if (whole_cmderr)
			partials = RTLIL::SELECT_WHOLE_CMDERR;
		else
			partials = RTLIL::SELECT_ALL;

		char boxes = RTLIL::SB_ALL;
		if (warn_boxes)   boxes |= RTLIL::SB_WARN;
		if (err_boxes)    boxes |= RTLIL::SB_ERR;
		if (cmderr_boxes) boxes |= RTLIL::SB_CMDERR;
		if (unboxed_only) boxes |= RTLIL::SB_UNBOXED_ONLY;
		if (include_wb)    boxes |= RTLIL::SB_INCL_WB;

		// get sub selection and store the results
		auto sub_sel = design->selected_modules(partials, (RTLIL::SelectBoxes)boxes);
		pool<RTLIL::IdString> selected_modules;
		dict<RTLIL::IdString, pool<RTLIL::NamedObject*>> selected_members;

		for (auto *mod : sub_sel) {
			if (mod->is_selected_whole()) {
				log_debug("  Adding %s.\n", id2cstr(mod->name));
				selected_modules.insert(mod->name);
			} else for (auto *memb : mod->selected_members()) {
				log_debug("  Adding %s.%s.\n", id2cstr(mod->name), id2cstr(memb->name));
				selected_members[mod->name].insert(memb);
			}
		}

		// fully reset current selection
		design->selection() = RTLIL::Selection::EmptySelection(design);

		// add back sub selection
		for (auto modname : selected_modules)
			design->selection().select(design->module(modname));
		for (auto &it : selected_members) {
			auto mod = design->module(it.first);
			for (auto memb : it.second)
				design->selection().select(mod, memb);
		}

		// optimize
		design->selection().optimize(design);
	}
} TestSelectPass;

PRIVATE_NAMESPACE_END
