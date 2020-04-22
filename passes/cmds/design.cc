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
#include "frontends/verilog/preproc.h"
#include "frontends/ast/ast.h"

YOSYS_NAMESPACE_BEGIN

std::map<std::string, RTLIL::Design*> saved_designs;
std::vector<RTLIL::Design*> pushed_designs;

struct DesignPass : public Pass {
	DesignPass() : Pass("design", "save, restore and reset current design") { }
	~DesignPass() YS_OVERRIDE {
		for (auto &it : saved_designs)
			delete it.second;
		saved_designs.clear();
		for (auto &it : pushed_designs)
			delete it;
		pushed_designs.clear();
	}
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    design -reset\n");
		log("\n");
		log("Clear the current design.\n");
		log("\n");
		log("\n");
		log("    design -save <name>\n");
		log("\n");
		log("Save the current design under the given name.\n");
		log("\n");
		log("\n");
		log("    design -stash <name>\n");
		log("\n");
		log("Save the current design under the given name and then clear the current design.\n");
		log("\n");
		log("\n");
		log("    design -push\n");
		log("\n");
		log("Push the current design to the stack and then clear the current design.\n");
		log("\n");
		log("\n");
		log("    design -push-copy\n");
		log("\n");
		log("Push the current design to the stack without clearing the current design.\n");
		log("\n");
		log("\n");
		log("    design -pop\n");
		log("\n");
		log("Reset the current design and pop the last design from the stack.\n");
		log("\n");
		log("\n");
		log("    design -load <name>\n");
		log("\n");
		log("Reset the current design and load the design previously saved under the given\n");
		log("name.\n");
		log("\n");
		log("\n");
		log("    design -copy-from <name> [-as <new_mod_name>] <selection>\n");
		log("\n");
		log("Copy modules from the specified design into the current one. The selection is\n");
		log("evaluated in the other design.\n");
		log("\n");
		log("\n");
		log("    design -copy-to <name> [-as <new_mod_name>] [selection]\n");
		log("\n");
		log("Copy modules from the current design into the specified one.\n");
		log("\n");
		log("\n");
		log("    design -import <name> [-as <new_top_name>] [selection]\n");
		log("\n");
		log("Import the specified design into the current design. The source design must\n");
		log("either have a selected top module or the selection must contain exactly one\n");
		log("module that is then used as top module for this command.\n");
		log("\n");
		log("\n");
		log("    design -reset-vlog\n");
		log("\n");
		log("The Verilog front-end remembers defined macros and top-level declarations\n");
		log("between calls to 'read_verilog'. This command resets this memory.\n");
		log("\n");
		log("    design -delete <name>\n");
		log("\n");
		log("Delete the design previously saved under the given name.\n");
		log("\n");

	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool got_mode = false;
		bool reset_mode = false;
		bool reset_vlog_mode = false;
		bool push_mode = false;
		bool push_copy_mode = false;
		bool pop_mode = false;
		bool import_mode = false;
		RTLIL::Design *copy_from_design = NULL, *copy_to_design = NULL;
		std::string save_name, load_name, as_name, delete_name;
		std::vector<RTLIL::Module*> copy_src_modules;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (!got_mode && args[argidx] == "-reset") {
				got_mode = true;
				reset_mode = true;
				continue;
			}
			if (!got_mode && args[argidx] == "-reset-vlog") {
				got_mode = true;
				reset_vlog_mode = true;
				continue;
			}
			if (!got_mode && args[argidx] == "-push") {
				got_mode = true;
				push_mode = true;
				continue;
			}
			if (!got_mode && args[argidx] == "-push-copy") {
				got_mode = true;
				push_copy_mode = true;
				continue;
			}
			if (!got_mode && args[argidx] == "-pop") {
				got_mode = true;
				pop_mode = true;
				continue;
			}
			if (!got_mode && args[argidx] == "-save" && argidx+1 < args.size()) {
				got_mode = true;
				save_name = args[++argidx];
				continue;
			}
			if (!got_mode && args[argidx] == "-stash" && argidx+1 < args.size()) {
				got_mode = true;
				save_name = args[++argidx];
				reset_mode = true;
				continue;
			}
			if (!got_mode && args[argidx] == "-load" && argidx+1 < args.size()) {
				got_mode = true;
				load_name = args[++argidx];
				if (saved_designs.count(load_name) == 0)
					log_cmd_error("No saved design '%s' found!\n", load_name.c_str());
				continue;
			}
			if (!got_mode && args[argidx] == "-copy-from" && argidx+1 < args.size()) {
				got_mode = true;
				if (saved_designs.count(args[++argidx]) == 0)
					log_cmd_error("No saved design '%s' found!\n", args[argidx].c_str());
				copy_from_design = saved_designs.at(args[argidx]);
				copy_to_design = design;
				continue;
			}
			if (!got_mode && args[argidx] == "-copy-to" && argidx+1 < args.size()) {
				got_mode = true;
				if (saved_designs.count(args[++argidx]) == 0)
					saved_designs[args[argidx]] = new RTLIL::Design;
				copy_to_design = saved_designs.at(args[argidx]);
				copy_from_design = design;
				continue;
			}
			if (!got_mode && args[argidx] == "-import" && argidx+1 < args.size()) {
				got_mode = true;
				import_mode = true;
				if (saved_designs.count(args[++argidx]) == 0)
					log_cmd_error("No saved design '%s' found!\n", args[argidx].c_str());
				copy_from_design = saved_designs.at(args[argidx]);
				copy_to_design = design;
				as_name = args[argidx];
				continue;
			}
			if (copy_from_design != NULL && args[argidx] == "-as" && argidx+1 < args.size()) {
				as_name = args[++argidx];
				continue;
			}
			if (!got_mode && args[argidx] == "-delete" && argidx+1 < args.size()) {
				got_mode = true;
				delete_name = args[++argidx];
				if (saved_designs.count(delete_name) == 0)
					log_cmd_error("No saved design '%s' found!\n", delete_name.c_str());
				continue;
			}
			break;
		}

		if (copy_from_design != NULL)
		{
			if (copy_from_design != design && argidx == args.size() && !import_mode)
				cmd_error(args, argidx, "Missing selection.");

			RTLIL::Selection sel;
			if (argidx != args.size()) {
				handle_extra_select_args(this, args, argidx, args.size(), copy_from_design);
				sel = copy_from_design->selection_stack.back();
				copy_from_design->selection_stack.pop_back();
				argidx = args.size();
			}

			for (auto mod : copy_from_design->modules()) {
				if (sel.selected_whole_module(mod->name)) {
					copy_src_modules.push_back(mod);
					continue;
				}
				if (sel.selected_module(mod->name))
					log_cmd_error("Module %s is only partly selected.\n", log_id(mod->name));
			}

			if (import_mode) {
				std::vector<RTLIL::Module*> candidates;
				for (auto module : copy_src_modules)
				{
					if (module->get_bool_attribute(ID::top)) {
						candidates.clear();
						candidates.push_back(module);
						break;
					}
					if (!module->get_blackbox_attribute())
						candidates.push_back(module);
				}

				if (GetSize(candidates) == 1)
					copy_src_modules = std::move(candidates);
			}
		}

		extra_args(args, argidx, design, false);

		if (!got_mode)
			cmd_error(args, argidx, "Missing mode argument.");

		if (pop_mode && pushed_designs.empty())
			log_cmd_error("No pushed designs.\n");

		if (import_mode)
		{
			std::string prefix = RTLIL::escape_id(as_name);

			pool<Module*> queue;
			dict<IdString, IdString> done;

			if (copy_to_design->module(prefix) != nullptr)
				copy_to_design->remove(copy_to_design->module(prefix));

			if (GetSize(copy_src_modules) != 1)
				log_cmd_error("No top module found in source design.\n");

			for (auto mod : copy_src_modules)
			{
				log("Importing %s as %s.\n", log_id(mod), log_id(prefix));

				RTLIL::Module *t = mod->clone();
				t->name = prefix;
				t->design = copy_to_design;
				t->attributes.erase(ID::top);
				copy_to_design->add(t);

				queue.insert(t);
				done[mod->name] = prefix;
			}

			while (!queue.empty())
			{
				pool<Module*> old_queue;
				old_queue.swap(queue);

				for (auto mod : old_queue)
				for (auto cell : mod->cells())
				{
					Module *fmod = copy_from_design->module(cell->type);

					if (fmod == nullptr)
						continue;

					if (done.count(cell->type) == 0)
					{
						std::string trg_name = prefix + "." + (cell->type.c_str() + (*cell->type.c_str() == '\\'));

						log("Importing %s as %s.\n", log_id(fmod), log_id(trg_name));

						if (copy_to_design->module(trg_name) != nullptr)
							copy_to_design->remove(copy_to_design->module(trg_name));

						RTLIL::Module *t = fmod->clone();
						t->name = trg_name;
						t->design = copy_to_design;
						t->attributes.erase(ID::top);
						copy_to_design->add(t);

						queue.insert(t);
						done[cell->type] = trg_name;
					}

					cell->type = done.at(cell->type);
				}
			}
		}
		else
		if (copy_to_design != NULL)
		{
			if (!as_name.empty() && copy_src_modules.size() > 1)
				log_cmd_error("Only one module can be selected in combination with -as.\n");

			for (auto mod : copy_src_modules)
			{
				std::string trg_name = as_name.empty() ? mod->name.str() : RTLIL::escape_id(as_name);

				if (copy_to_design->module(trg_name) != nullptr)
					copy_to_design->remove(copy_to_design->module(trg_name));

				RTLIL::Module *t = mod->clone();
				t->name = trg_name;
				t->design = copy_to_design;
				copy_to_design->add(t);
			}
		}

		if (!save_name.empty() || push_mode || push_copy_mode)
		{
			RTLIL::Design *design_copy = new RTLIL::Design;

			for (auto mod : design->modules())
				design_copy->add(mod->clone());

			design_copy->selection_stack = design->selection_stack;
			design_copy->selection_vars = design->selection_vars;
			design_copy->selected_active_module = design->selected_active_module;

			if (saved_designs.count(save_name))
				delete saved_designs.at(save_name);

			if (push_mode || push_copy_mode)
				pushed_designs.push_back(design_copy);
			else
				saved_designs[save_name] = design_copy;
		}

		if (reset_mode || !load_name.empty() || push_mode || pop_mode)
		{
			for (auto mod : design->modules().to_vector())
				design->remove(mod);

			design->selection_stack.clear();
			design->selection_vars.clear();
			design->selected_active_module.clear();

			design->selection_stack.push_back(RTLIL::Selection());
		}

		if (reset_mode || reset_vlog_mode || !load_name.empty() || push_mode || pop_mode)
		{
			for (auto node : design->verilog_packages)
				delete node;
			design->verilog_packages.clear();

			for (auto node : design->verilog_globals)
				delete node;
			design->verilog_globals.clear();

			design->verilog_defines->clear();
		}

		if (!load_name.empty() || pop_mode)
		{
			RTLIL::Design *saved_design = pop_mode ? pushed_designs.back() : saved_designs.at(load_name);

			for (auto mod : saved_design->modules())
				design->add(mod->clone());

			design->selection_stack = saved_design->selection_stack;
			design->selection_vars = saved_design->selection_vars;
			design->selected_active_module = saved_design->selected_active_module;

			if (pop_mode) {
				delete saved_design;
				pushed_designs.pop_back();
			}
		}

		if (!delete_name.empty())
		{
			auto it = saved_designs.find(delete_name);
			log_assert(it != saved_designs.end());
			delete it->second;
			saved_designs.erase(it);
		}
	}
} DesignPass;

YOSYS_NAMESPACE_END

