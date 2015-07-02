/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct DeletePass : public Pass {
	DeletePass() : Pass("delete", "delete objects in the design") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    delete [selection]\n");
		log("\n");
		log("Deletes the selected objects. This will also remove entire modules, if the\n");
		log("whole module is selected.\n");
		log("\n");
		log("\n");
		log("    delete {-input|-output|-port} [selection]\n");
		log("\n");
		log("Does not delete any object but removes the input and/or output flag on the\n");
		log("selected wires, thus 'deleting' module ports.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_input = false;
		bool flag_output = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-input") {
				flag_input = true;
				continue;
			}
			if (args[argidx] == "-output") {
				flag_output = true;
				continue;
			}
			if (args[argidx] == "-port") {
				flag_input = true;
				flag_output = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		std::vector<RTLIL::IdString> delete_mods;

		for (auto &mod_it : design->modules_)
		{
			if (design->selected_whole_module(mod_it.first) && !flag_input && !flag_output) {
				delete_mods.push_back(mod_it.first);
				continue;
			}

			if (!design->selected_module(mod_it.first))
				continue;

			RTLIL::Module *module = mod_it.second;

			if (flag_input || flag_output) {
				for (auto &it : module->wires_)
					if (design->selected(module, it.second)) {
						if (flag_input)
							it.second->port_input = false;
						if (flag_output)
							it.second->port_output = false;
					}
				module->fixup_ports();
				continue;
			}

			pool<RTLIL::Wire*> delete_wires;
			pool<RTLIL::Cell*> delete_cells;
			pool<RTLIL::IdString> delete_procs;
			pool<RTLIL::IdString> delete_mems;

			for (auto &it : module->wires_)
				if (design->selected(module, it.second))
					delete_wires.insert(it.second);

			for (auto &it : module->memories)
				if (design->selected(module, it.second))
					delete_mems.insert(it.first);

			for (auto &it : module->cells_) {
				if (design->selected(module, it.second))
					delete_cells.insert(it.second);
				if ((it.second->type == "$memrd" || it.second->type == "$memwr") &&
						delete_mems.count(it.second->parameters.at("\\MEMID").decode_string()) != 0)
					delete_cells.insert(it.second);
			}

			for (auto &it : module->processes)
				if (design->selected(module, it.second))
					delete_procs.insert(it.first);

			for (auto &it : delete_mems) {
				delete module->memories.at(it);
				module->memories.erase(it);
			}

			for (auto &it : delete_cells)
				module->remove(it);

			for (auto &it : delete_procs) {
				delete module->processes.at(it);
				module->processes.erase(it);
			}

			module->remove(delete_wires);

			module->fixup_ports();
		}

		for (auto &it : delete_mods) {
			delete design->modules_.at(it);
			design->modules_.erase(it);
		}
	}
} DeletePass;

PRIVATE_NAMESPACE_END
