/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2018  whitequark <whitequark@whitequark.org>
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
#include "backends/rtlil/rtlil_backend.h"

USING_YOSYS_NAMESPACE
using namespace RTLIL_BACKEND;
PRIVATE_NAMESPACE_BEGIN

struct BugpointPass : public Pass {
	BugpointPass() : Pass("bugpoint", "minimize testcases") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    bugpoint [options] [-script <filename> | -command \"<command>\"]\n");
		log("\n");
		log("This command minimizes the current design that is known to crash Yosys with the\n");
		log("given script into a smaller testcase. It does this by removing an arbitrary part\n");
		log("of the design and recursively invokes a new Yosys process with this modified design\n");
		log("and the same script, repeating these steps while it can find a smaller design that\n");
		log("still causes a crash. Once this command finishes, it replaces the current design\n");
		log("with the smallest testcase it was able to produce.\n");
		log("In order to save the reduced testcase you must write this out to a file with\n");
		log("another command after `bugpoint` like `write_rtlil` or `write_verilog`.\n");
		log("\n");
		log("    -script <filename> | -command \"<command>\"\n");
		log("        use this script file or command to crash Yosys. required.\n");
		log("\n");
		log("    -yosys <filename>\n");
		log("        use this Yosys binary. if not specified, `yosys` is used.\n");
		log("\n");
		log("    -grep \"<string>\"\n");
		log("        only consider crashes that place this string in the log file.\n");
		log("\n");
		log("    -fast\n");
		log("        run `proc_clean; clean -purge` after each minimization step. converges\n");
		log("        faster, but produces larger testcases, and may fail to produce any\n");
		log("        testcase at all if the crash is related to dangling wires.\n");
		log("\n");
		log("    -clean\n");
		log("        run `proc_clean; clean -purge` before checking testcase and after\n");
		log("        finishing. produces smaller and more useful testcases, but may fail to\n");
		log("        produce any testcase at all if the crash is related to dangling wires.\n");
		log("\n");
		log("It is possible to constrain which parts of the design will be considered for\n");
		log("removal. Unless one or more of the following options are specified, all parts\n");
		log("will be considered.\n");
		log("\n");
		log("    -modules\n");
		log("        try to remove modules. modules with a (* bugpoint_keep *) attribute\n");
		log("        will be skipped.\n");
		log("\n");
		log("    -ports\n");
		log("        try to remove module ports. ports with a (* bugpoint_keep *) attribute\n");
		log("        will be skipped (useful for clocks, resets, etc.)\n");
		log("\n");
		log("    -cells\n");
		log("        try to remove cells. cells with a (* bugpoint_keep *) attribute will\n");
		log("        be skipped.\n");
		log("\n");
		log("    -connections\n");
		log("        try to reconnect ports to 'x.\n");
		log("\n");
		log("    -processes\n");
		log("        try to remove processes. processes with a (* bugpoint_keep *) attribute\n");
		log("        will be skipped.\n");
		log("\n");
		log("    -assigns\n");
		log("        try to remove process assigns from cases.\n");
		log("\n");
		log("    -updates\n");
		log("        try to remove process updates from syncs.\n");
		log("\n");
		log("    -runner \"<prefix>\"\n");
		log("        child process wrapping command, e.g., \"timeout 30\", or valgrind.\n");
		log("\n");
	}

	bool run_yosys(RTLIL::Design *design, string runner, string yosys_cmd, string yosys_arg)
	{
		design->sort();

		std::ofstream f("bugpoint-case.il");
		RTLIL_BACKEND::dump_design(f, design, /*only_selected=*/false, /*flag_m=*/true, /*flag_n=*/false);
		f.close();

		string yosys_cmdline = stringf("%s %s -qq -L bugpoint-case.log %s bugpoint-case.il", runner.c_str(), yosys_cmd.c_str(), yosys_arg.c_str());
		return run_command(yosys_cmdline) == 0;
	}

	bool check_logfile(string grep)
	{
		if (grep.empty())
			return true;

		if (grep.size() > 2 && grep.front() == '"' && grep.back() == '"')
			grep = grep.substr(1, grep.size() - 2);

		std::ifstream f("bugpoint-case.log");
		while (!f.eof())
		{
			string line;
			getline(f, line);
			if (line.find(grep) != std::string::npos)
				return true;
		}
		return false;
	}

	RTLIL::Design *clean_design(RTLIL::Design *design, bool do_clean = true, bool do_delete = false)
	{
		if (!do_clean)
			return design;

		RTLIL::Design *design_copy = new RTLIL::Design;
		for (auto module : design->modules())
			design_copy->add(module->clone());
		Pass::call(design_copy, "proc_clean -quiet");
		Pass::call(design_copy, "clean -purge");

		if (do_delete)
			delete design;
		return design_copy;
	}

	RTLIL::Design *simplify_something(RTLIL::Design *design, int &seed, bool stage2, bool modules, bool ports, bool cells, bool connections, bool processes, bool assigns, bool updates, bool wires)
	{
		RTLIL::Design *design_copy = new RTLIL::Design;
		for (auto module : design->modules())
			design_copy->add(module->clone());

		int index = 0;
		if (modules)
		{
			Module *removed_module = nullptr;
			for (auto module : design_copy->modules())
			{
				if (module->get_blackbox_attribute())
					continue;

				if (module->get_bool_attribute(ID::bugpoint_keep))
				    continue;

				if (index++ == seed)
				{
					log_header(design, "Trying to remove module %s.\n", log_id(module));
					removed_module = module;
					break;
				}
			}
			if (removed_module) {
				design_copy->remove(removed_module);
				return design_copy;
			}
		}
		if (ports)
		{
			for (auto mod : design_copy->modules())
			{
				if (mod->get_blackbox_attribute())
					continue;

				for (auto wire : mod->wires())
				{
					if (!wire->port_id)
						continue;

					if (!stage2 && wire->get_bool_attribute(ID($bugpoint)))
						continue;

					if (wire->get_bool_attribute(ID::bugpoint_keep))
						continue;

					if (index++ == seed)
					{
						log_header(design, "Trying to remove module port %s.\n", log_id(wire));
						wire->port_input = wire->port_output = false;
						mod->fixup_ports();
						return design_copy;
					}
				}
			}
		}
		if (cells)
		{
			for (auto mod : design_copy->modules())
			{
				if (mod->get_blackbox_attribute())
					continue;

				Cell *removed_cell = nullptr;
				for (auto cell : mod->cells())
				{
					if (cell->get_bool_attribute(ID::bugpoint_keep))
						continue;

					if (index++ == seed)
					{
						log_header(design, "Trying to remove cell %s.%s.\n", log_id(mod), log_id(cell));
						removed_cell = cell;
						break;
					}
				}
				if (removed_cell) {
					mod->remove(removed_cell);
					return design_copy;
				}
			}
		}
		if (connections)
		{
			for (auto mod : design_copy->modules())
			{
				if (mod->get_blackbox_attribute())
					continue;

				for (auto cell : mod->cells())
				{
					for (auto it : cell->connections_)
					{
						RTLIL::SigSpec port = cell->getPort(it.first);
						bool is_undef = port.is_fully_undef();
						bool is_port = port.is_wire() && (port.as_wire()->port_input || port.as_wire()->port_output);

						if(is_undef || (!stage2 && is_port))
							continue;

						if (index++ == seed)
						{
							log_header(design, "Trying to remove cell port %s.%s.%s.\n", log_id(mod), log_id(cell), log_id(it.first));
							RTLIL::SigSpec port_x(State::Sx, port.size());
							cell->unsetPort(it.first);
							cell->setPort(it.first, port_x);
							return design_copy;
						}

						if (!stage2 && (cell->input(it.first) || cell->output(it.first)) && index++ == seed)
						{
							log_header(design, "Trying to expose cell port %s.%s.%s as module port.\n", log_id(mod), log_id(cell), log_id(it.first));
							RTLIL::Wire *wire = mod->addWire(NEW_ID, port.size());
							wire->set_bool_attribute(ID($bugpoint));
							wire->port_input = cell->input(it.first);
							wire->port_output = cell->output(it.first);
							cell->unsetPort(it.first);
							cell->setPort(it.first, wire);
							mod->fixup_ports();
							return design_copy;
						}
					}
				}
			}
		}
		if (processes)
		{
			for (auto mod : design_copy->modules())
			{
				if (mod->get_blackbox_attribute())
					continue;

				RTLIL::IdString removed_process;
				for (auto process : mod->processes)
				{
					if (process.second->get_bool_attribute(ID::bugpoint_keep))
						continue;

					if (index++ == seed)
					{
						log_header(design, "Trying to remove process %s.%s.\n", log_id(mod), log_id(process.first));
						removed_process = process.first;
						break;
					}
				}
				if (!removed_process.empty()) {
					delete mod->processes[removed_process];
					mod->processes.erase(removed_process);
					return design_copy;
				}
			}
		}
		if (assigns)
		{
			for (auto mod : design_copy->modules())
			{
				if (mod->get_blackbox_attribute())
					continue;

				for (auto &pr : mod->processes)
				{
					vector<RTLIL::CaseRule*> cases = {&pr.second->root_case};
					while (!cases.empty())
					{
						RTLIL::CaseRule *cs = cases[0];
						cases.erase(cases.begin());
						for (auto it = cs->actions.begin(); it != cs->actions.end(); ++it)
						{
							if (index++ == seed)
							{
								log_header(design, "Trying to remove assign %s %s in %s.%s.\n", log_signal(it->first), log_signal(it->second), log_id(mod), log_id(pr.first));
								cs->actions.erase(it);
								return design_copy;
							}
						}
						for (auto &sw : cs->switches)
							cases.insert(cases.end(), sw->cases.begin(), sw->cases.end());
					}
				}
			}
		}
		if (updates)
		{
			for (auto mod : design_copy->modules())
			{
				if (mod->get_blackbox_attribute())
					continue;

				for (auto &pr : mod->processes)
				{
					for (auto &sy : pr.second->syncs)
					{
						for (auto it = sy->actions.begin(); it != sy->actions.end(); ++it)
						{
							if (index++ == seed)
							{
								log_header(design, "Trying to remove sync %s update %s %s in %s.%s.\n", log_signal(sy->signal), log_signal(it->first), log_signal(it->second), log_id(mod), log_id(pr.first));
								sy->actions.erase(it);
								return design_copy;
							}
						}
						int i = 0;
						for (auto it = sy->mem_write_actions.begin(); it != sy->mem_write_actions.end(); ++it, ++i)
						{
							if (index++ == seed)
							{
								log_header(design, "Trying to remove sync %s memwr %s %s %s %s in %s.%s.\n", log_signal(sy->signal), log_id(it->memid), log_signal(it->address), log_signal(it->data), log_signal(it->enable), log_id(mod), log_id(pr.first));
								sy->mem_write_actions.erase(it);
								// Remove the bit for removed action from other actions' priority masks.
								for (auto it2 = sy->mem_write_actions.begin(); it2 != sy->mem_write_actions.end(); ++it2) {
									auto &mask = it2->priority_mask;
									if (GetSize(mask) > i) {
										mask.bits.erase(mask.bits.begin() + i);
									}
								}
								return design_copy;
							}
						}
					}
				}
			}
		}
		if (wires)
		{
			for (auto mod : design_copy->modules())
			{
				if (mod->get_blackbox_attribute())
					continue;

				Wire *removed_wire = nullptr;
				for (auto wire : mod->wires())
				{
					if (wire->get_bool_attribute(ID::bugpoint_keep))
						continue;

					if (wire->name.begins_with("$delete_wire"))
						continue;

					if (index++ == seed)
					{
						log_header(design, "Trying to remove wire %s.%s.\n", log_id(mod), log_id(wire));
						removed_wire = wire;
						break;
					}
				}
				if (removed_wire) {
					mod->remove({removed_wire});
					return design_copy;
				}
			}
		}
		return nullptr;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		string yosys_cmd = "yosys", yosys_arg, grep, runner;
		bool fast = false, clean = false;
		bool modules = false, ports = false, cells = false, connections = false, processes = false, assigns = false, updates = false, wires = false, has_part = false;

		log_header(design, "Executing BUGPOINT pass (minimize testcases).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-yosys" && argidx + 1 < args.size()) {
				yosys_cmd = args[++argidx];
				continue;
			}
			if (args[argidx] == "-script" && argidx + 1 < args.size()) {
				if (!yosys_arg.empty())
					log_cmd_error("A -script or -command option can be only provided once!\n");
				yosys_arg = stringf("-s %s", args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-command" && argidx + 1 < args.size()) {
				if (!yosys_arg.empty())
					log_cmd_error("A -script or -command option can be only provided once!\n");
				yosys_arg = stringf("-p %s", args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-grep" && argidx + 1 < args.size()) {
				grep = args[++argidx];
				continue;
			}
			if (args[argidx] == "-fast") {
				fast = true;
				continue;
			}
			if (args[argidx] == "-clean") {
				clean = true;
				continue;
			}
			if (args[argidx] == "-modules") {
				modules = true;
				has_part = true;
				continue;
			}
			if (args[argidx] == "-ports") {
				ports = true;
				has_part = true;
				continue;
			}
			if (args[argidx] == "-cells") {
				cells = true;
				has_part = true;
				continue;
			}
			if (args[argidx] == "-connections") {
				connections = true;
				has_part = true;
				continue;
			}
			if (args[argidx] == "-processes") {
				processes = true;
				has_part = true;
				continue;
			}
			if (args[argidx] == "-assigns") {
				assigns = true;
				has_part = true;
				continue;
			}
			if (args[argidx] == "-updates") {
				updates = true;
				has_part = true;
				continue;
			}
			if (args[argidx] == "-wires") {
				wires = true;
				has_part = true;
				continue;
			}
			if (args[argidx] == "-runner" && argidx + 1 < args.size()) {
				runner = args[++argidx];
				if (runner.size() && runner.at(0) == '"') {
					log_assert(runner.back() == '"');
					runner = runner.substr(1, runner.size() - 2);
				}
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (yosys_arg.empty())
			log_cmd_error("Missing -script or -command option.\n");

		if (!has_part)
		{
			modules = true;
			ports = true;
			cells = true;
			connections = true;
			processes = true;
			assigns = true;
			updates = true;
			wires = true;
		}

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		RTLIL::Design *crashing_design = clean_design(design, clean);
		if (run_yosys(crashing_design, runner, yosys_cmd, yosys_arg))
			log_cmd_error("The provided script file or command and Yosys binary do not crash on this design!\n");
		if (!check_logfile(grep))
			log_cmd_error("The provided grep string is not found in the log file!\n");

		int seed = 0;
		bool found_something = false, stage2 = false;
		while (true)
		{
			if (RTLIL::Design *simplified = simplify_something(crashing_design, seed, stage2, modules, ports, cells, connections, processes, assigns, updates, wires))
			{
				simplified = clean_design(simplified, fast, /*do_delete=*/true);

				bool crashes;
				if (clean)
				{
					RTLIL::Design *testcase = clean_design(simplified);
					crashes = !run_yosys(testcase, runner, yosys_cmd, yosys_arg);
					delete testcase;
				}
				else
				{
					crashes = !run_yosys(simplified, runner, yosys_cmd, yosys_arg);
				}

				if (crashes && check_logfile(grep))
				{
					log("Testcase crashes.\n");
					if (crashing_design != design)
						delete crashing_design;
					crashing_design = simplified;
					found_something = true;
				}
				else
				{
					log("Testcase does not crash.\n");
					delete simplified;
					seed++;
				}
			}
			else
			{
				seed = 0;
				if (found_something)
					found_something = false;
				else
				{
					if (!stage2)
					{
						log("Demoting introduced module ports.\n");
						stage2 = true;
					}
					else
					{
						log("Simplifications exhausted.\n");
						break;
					}
				}
			}
		}

		if (crashing_design != design)
		{
			Pass::call(design, "design -reset");
			crashing_design = clean_design(crashing_design, clean, /*do_delete=*/true);
			for (auto module : crashing_design->modules())
				design->add(module->clone());
			delete crashing_design;
		}

		log_pop();
	}
} BugpointPass;

PRIVATE_NAMESPACE_END
