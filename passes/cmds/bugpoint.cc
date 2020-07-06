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
#include "backends/ilang/ilang_backend.h"

USING_YOSYS_NAMESPACE
using namespace ILANG_BACKEND;
PRIVATE_NAMESPACE_BEGIN

struct BugpointPass : public Pass {
	BugpointPass() : Pass("bugpoint", "minimize testcases") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    bugpoint [options]\n");
		log("\n");
		log("This command minimizes testcases that crash Yosys. It removes an arbitrary part\n");
		log("of the design and recursively invokes Yosys with a given script, repeating these\n");
		log("steps while it can find a smaller design that still causes a crash. Once this\n");
		log("command finishes, it replaces the current design with the smallest testcase it\n");
		log("was able to produce.\n");
		log("\n");
		log("It is possible to specify the kinds of design part that will be removed. If none\n");
		log("are specified, all parts of design will be removed.\n");
		log("\n");
		log("    -yosys <filename>\n");
		log("        use this Yosys binary. if not specified, `yosys` is used.\n");
		log("\n");
		log("    -script <filename>\n");
		log("        use this script to crash Yosys. required.\n");
		log("\n");
		log("    -grep <string>\n");
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
		log("    -modules\n");
		log("        try to remove modules.\n");
		log("\n");
		log("    -ports\n");
		log("        try to remove module ports.\n");
		log("\n");
		log("    -cells\n");
		log("        try to remove cells.\n");
		log("\n");
		log("    -connections\n");
		log("        try to reconnect ports to 'x.\n");
		log("\n");
		log("    -assigns\n");
		log("        try to remove process assigns from cases.\n");
		log("\n");
		log("    -updates\n");
		log("        try to remove process updates from syncs.\n");
		log("\n");
	}

	bool run_yosys(RTLIL::Design *design, string yosys_cmd, string script)
	{
		design->sort();

		std::ofstream f("bugpoint-case.il");
		ILANG_BACKEND::dump_design(f, design, /*only_selected=*/false, /*flag_m=*/true, /*flag_n=*/false);
		f.close();

		string yosys_cmdline = stringf("%s -qq -L bugpoint-case.log -s %s bugpoint-case.il", yosys_cmd.c_str(), script.c_str());
		return run_command(yosys_cmdline) == 0;
	}

	bool check_logfile(string grep)
	{
		if (grep.empty())
			return true;

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
		for (auto &it : design->modules_)
			design_copy->add(it.second->clone());
		Pass::call(design_copy, "proc_clean -quiet");
		Pass::call(design_copy, "clean -purge");

		if (do_delete)
			delete design;
		return design_copy;
	}

	RTLIL::Design *simplify_something(RTLIL::Design *design, int &seed, bool stage2, bool modules, bool ports, bool cells, bool connections, bool assigns, bool updates)
	{
		RTLIL::Design *design_copy = new RTLIL::Design;
		for (auto &it : design->modules_)
			design_copy->add(it.second->clone());

		int index = 0;
		if (modules)
		{
			for (auto &it : design_copy->modules_)
			{
				if (it.second->get_blackbox_attribute())
					continue;

				if (index++ == seed)
				{
					log("Trying to remove module %s.\n", it.first.c_str());
					design_copy->remove(it.second);
					return design_copy;
				}
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
					if (!stage2 && wire->get_bool_attribute("$bugpoint"))
						continue;

					if (wire->port_input || wire->port_output)
					{
						if (index++ == seed)
						{
							log("Trying to remove module port %s.\n", log_signal(wire));
							wire->port_input = wire->port_output = false;
							mod->fixup_ports();
							return design_copy;
						}
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

				for (auto &it : mod->cells_)
				{
					if (index++ == seed)
					{
						log("Trying to remove cell %s.%s.\n", mod->name.c_str(), it.first.c_str());
						mod->remove(it.second);
						return design_copy;
					}
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
							log("Trying to remove cell port %s.%s.%s.\n", mod->name.c_str(), cell->name.c_str(), it.first.c_str());
							RTLIL::SigSpec port_x(State::Sx, port.size());
							cell->unsetPort(it.first);
							cell->setPort(it.first, port_x);
							return design_copy;
						}

						if (!stage2 && (cell->input(it.first) || cell->output(it.first)) && index++ == seed)
						{
							log("Trying to expose cell port %s.%s.%s as module port.\n", mod->name.c_str(), cell->name.c_str(), it.first.c_str());
							RTLIL::Wire *wire = mod->addWire(NEW_ID, port.size());
							wire->set_bool_attribute("$bugpoint");
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
								log("Trying to remove assign %s %s in %s.%s.\n", log_signal((*it).first), log_signal((*it).second), mod->name.c_str(), pr.first.c_str());
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
								log("Trying to remove sync %s update %s %s in %s.%s.\n", log_signal(sy->signal), log_signal((*it).first), log_signal((*it).second), mod->name.c_str(), pr.first.c_str());
								sy->actions.erase(it);
								return design_copy;
							}
						}
					}
				}
			}
		}
		return NULL;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		string yosys_cmd = "yosys", script, grep;
		bool fast = false, clean = false;
		bool modules = false, ports = false, cells = false, connections = false, assigns = false, updates = false, has_part = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-yosys" && argidx + 1 < args.size()) {
				yosys_cmd = args[++argidx];
				continue;
			}
			if (args[argidx] == "-script" && argidx + 1 < args.size()) {
				script = args[++argidx];
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
			break;
		}
		extra_args(args, argidx, design);

		if (script.empty())
			log_cmd_error("Missing -script option.\n");

		if (!has_part)
		{
			modules = true;
			ports = true;
			cells = true;
			connections = true;
			assigns = true;
			updates = true;
		}

		if (!design->full_selection())
			log_cmd_error("This command only operates on fully selected designs!\n");

		RTLIL::Design *crashing_design = clean_design(design, clean);
		if (run_yosys(crashing_design, yosys_cmd, script))
			log_cmd_error("The provided script file and Yosys binary do not crash on this design!\n");
		if (!check_logfile(grep))
			log_cmd_error("The provided grep string is not found in the log file!\n");

		int seed = 0;
		bool found_something = false, stage2 = false;
		while (true)
		{
			if (RTLIL::Design *simplified = simplify_something(crashing_design, seed, stage2, modules, ports, cells, connections, assigns, updates))
			{
				simplified = clean_design(simplified, fast, /*do_delete=*/true);

				bool crashes;
				if (clean)
				{
					RTLIL::Design *testcase = clean_design(simplified);
					crashes = !run_yosys(testcase, yosys_cmd, script);
					delete testcase;
				}
				else
				{
					crashes = !run_yosys(simplified, yosys_cmd, script);
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
			for (auto &it : crashing_design->modules_)
				design->add(it.second->clone());
			delete crashing_design;
		}
	}
} BugpointPass;

PRIVATE_NAMESPACE_END
