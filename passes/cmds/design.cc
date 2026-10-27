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
#include "frontends/verilog/preproc.h"
#include "frontends/ast/ast.h"

YOSYS_NAMESPACE_BEGIN

std::map<std::string, std::unique_ptr<RTLIL::Design>> saved_designs;
std::vector<std::unique_ptr<RTLIL::Design>> pushed_designs;

static std::unique_ptr<RTLIL::Design> snapshot(RTLIL::Design *design)
{
	auto copy = std::make_unique<RTLIL::Design>();
	design->clone_into(copy.get());
	return copy;
}

static void copy_modules(RTLIL::Design *dst, const std::vector<RTLIL::Module*> &modules, const std::string &as_name)
{
	if (!as_name.empty() && modules.size() > 1)
		log_cmd_error("Only one module can be selected in combination with -as.\n");

	for (auto mod : modules)
	{
		std::string trg_name = as_name.empty() ? mod->name.str() : RTLIL::escape_id(as_name);
		IdString trg_ref = dst->twines().add(trg_name);

		if (dst->module(trg_ref) != nullptr)
			dst->remove(dst->module(trg_ref));

		mod->clone(dst, trg_ref);
	}
}

static void import_design(RTLIL::Design *src, RTLIL::Design *dst, std::vector<RTLIL::Module*> modules,
		const std::string &as_name)
{
	std::vector<RTLIL::Module*> candidates;
	for (auto module : modules)
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
		modules = std::move(candidates);

	std::string prefix = RTLIL::escape_id(as_name);
	IdString as_name_ref = dst->twines().add(prefix);

	pool<Module*> queue;
	dict<IdString, IdString> done;

	if (dst->module(as_name_ref) != nullptr)
		dst->remove(dst->module(as_name_ref));

	if (GetSize(modules) != 1)
		log_cmd_error("No top module found in source design.\n");

	for (auto mod : modules)
	{
		log("Importing %s as %s.\n", mod, PooledName(dst, as_name_ref).unescape());

		RTLIL::Module *t = mod->clone(dst, as_name_ref);
		t->attributes.erase(ID::top);

		queue.insert(t);
		done[mod->name] = as_name_ref;
	}

	while (!queue.empty())
	{
		pool<Module*> old_queue;
		old_queue.swap(queue);

		for (auto mod : old_queue)
		for (auto cell : mod->cells())
		{
			Module *fmod = src->module(src->twines().find(dst->twines().str(cell->type)));

			if (fmod == nullptr)
				continue;

			if (done.count(cell->type) == 0)
			{
				IdString trg_ref = dst->twines().add(
						TwineSpec::Suffix{as_name_ref, "." + cell->type.unescape()});

				log("Importing %s as %s.\n", fmod, PooledName(dst, trg_ref).unescape());

				if (dst->module(trg_ref) != nullptr)
					dst->remove(dst->module(trg_ref));

				RTLIL::Module *t = fmod->clone(dst, trg_ref);
				t->attributes.erase(ID::top);

				queue.insert(t);
				done[cell->type] = trg_ref;
			}

			cell->type = done.at(cell->type);
		}
	}
}

struct DesignPass : public Pass {
	DesignPass() : Pass("design", "save, restore and reset current design") { }
	void on_shutdown() override {
		saved_designs.clear();
		pushed_designs.clear();
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    design -reset\n");
		log("\n");
		log("Clear the current design. This also restarts the numbering of generated\n");
		log("names.\n");
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
	enum class Mode { None, Reset, ResetVlog, Push, PushCopy, Pop, Save, Stash, Load, CopyFrom, CopyTo, Import, Delete };

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		static const std::map<std::string, Mode> flag_modes = {
			{"-reset", Mode::Reset}, {"-reset-vlog", Mode::ResetVlog},
			{"-push", Mode::Push}, {"-push-copy", Mode::PushCopy}, {"-pop", Mode::Pop},
		};
		static const std::map<std::string, Mode> named_modes = {
			{"-save", Mode::Save}, {"-stash", Mode::Stash}, {"-load", Mode::Load},
			{"-copy-from", Mode::CopyFrom}, {"-copy-to", Mode::CopyTo},
			{"-import", Mode::Import}, {"-delete", Mode::Delete},
		};

		Mode mode = Mode::None;
		std::string name, as_name;

		if (!design)
			log_cmd_error("No default design.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			const std::string &arg = args[argidx];
			bool has_value = argidx+1 < args.size();
			if (mode == Mode::None && flag_modes.count(arg)) {
				mode = flag_modes.at(arg);
				continue;
			}
			if (mode == Mode::None && named_modes.count(arg) && has_value) {
				mode = named_modes.at(arg);
				name = args[++argidx];
				continue;
			}
			bool copying = mode == Mode::CopyFrom || mode == Mode::CopyTo || mode == Mode::Import;
			if (copying && arg == "-as" && has_value) {
				as_name = args[++argidx];
				continue;
			}
			break;
		}

		bool reads_saved = mode == Mode::Load || mode == Mode::CopyFrom || mode == Mode::Import || mode == Mode::Delete;
		if (reads_saved && saved_designs.count(name) == 0)
			log_cmd_error("No saved design '%s' found!\n", name);

		RTLIL::Design *copy_from_design = nullptr, *copy_to_design = nullptr;
		if (mode == Mode::CopyFrom || mode == Mode::Import) {
			copy_from_design = saved_designs.at(name).get();
			copy_to_design = design;
		}
		if (mode == Mode::CopyTo) {
			auto &saved = saved_designs[name];
			if (!saved)
				saved = std::make_unique<RTLIL::Design>();
			copy_from_design = design;
			copy_to_design = saved.get();
		}
		if (mode == Mode::Import && as_name.empty())
			as_name = name;

		std::vector<RTLIL::Module*> copy_src_modules;
		if (copy_from_design != nullptr)
		{
			if (copy_from_design != design && argidx == args.size() && mode != Mode::Import)
				cmd_error(args, argidx, "Missing selection.");

			if (argidx != args.size()) {
				handle_extra_select_args(this, args, argidx, args.size(), copy_from_design);
				argidx = args.size();
			} else {
				copy_from_design->push_complete_selection();
			}

			for (auto mod : copy_from_design->selected_modules(RTLIL::SELECT_WHOLE_CMDERR, RTLIL::SB_ALL))
				copy_src_modules.push_back(mod);

			copy_from_design->pop_selection();
		}

		extra_args(args, argidx, design, false);

		if (mode == Mode::None)
			cmd_error(args, argidx, "Missing mode argument.");

		if (mode == Mode::Pop && pushed_designs.empty())
			log_cmd_error("No pushed designs.\n");

		switch (mode) {
		case Mode::Reset:
			design->reset();
			break;
		case Mode::ResetVlog:
			design->reset_verilog_state();
			break;
		case Mode::Push:
			pushed_designs.push_back(snapshot(design));
			design->reset();
			break;
		case Mode::PushCopy:
			pushed_designs.push_back(snapshot(design));
			break;
		case Mode::Pop:
			design->reset();
			pushed_designs.back()->clone_into(design);
			pushed_designs.pop_back();
			break;
		case Mode::Save:
			saved_designs[name] = snapshot(design);
			break;
		case Mode::Stash:
			saved_designs[name] = snapshot(design);
			design->reset();
			break;
		case Mode::Load:
			design->reset();
			saved_designs.at(name)->clone_into(design);
			break;
		case Mode::CopyFrom:
		case Mode::CopyTo:
			copy_modules(copy_to_design, copy_src_modules, as_name);
			break;
		case Mode::Import:
			import_design(copy_from_design, copy_to_design, copy_src_modules, as_name);
			break;
		case Mode::Delete:
			saved_designs.erase(name);
			break;
		case Mode::None:
			log_abort();
		}
	}
} DesignPass;

YOSYS_NAMESPACE_END
