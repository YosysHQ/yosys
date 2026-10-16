/*
Equivalence Checking with Yosys (eqy)

Copyright (C) 2020 Claire Xenia Wolf <claire@yosyshq.com>
Copyright (C) 2020 N. Engelhardt <nak@yosyshq.com>

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

#include "kernel/yosys.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct EqyCombinePass : public Pass
{
	EqyCombinePass() : Pass("eqy_combine", "combine gate and gold designs for eqy") { }

	void help() override
	{
	//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
	log("\n");
	log("    eqy_combine -gold_ids file -gate_ids file\n");
	log("\n");
	log("Combine gate and gold designs, partially flattening each design until their\n");
	log("hierarchies match. Designs \"gate\" and \"gold\" need to have been previously\n");
	log("saved under these names. For use by EQY.\n");
	log("\n");
	log("    -gold_ids <filename>\n");
	log("        Dump IDs of public cells and wires in gold module to file\n");
	log("\n");
	log("    -gate_ids <filename>\n");
	log("        Dump IDs of public cells and wires in gate module to file\n");
	log("\n");
	log("    -nocombine\n");
	log("        Skip generating miter, just generate IDs\n");
	log("\n");
}

	void co_flatten_worker(RTLIL::Selection &sel, Design *work, Design *other, Module *mod)
	{
		// TODO: check that the interfaces of both modules are compatible
		// recoding should be done before this so the interfaces match already
		for (auto cell : mod->cells())
		{
			Module *work_submod = work->module(cell->type);
			Module *other_submod = other->module(cell->type);
			if (work_submod)
			{
				if(other_submod)
					co_flatten_worker(sel, work, other, work_submod);
				else
					sel.select(mod, cell);
			}
		}
	}

	bool co_flatten(Design *work, Design *other)
	{
		RTLIL::Selection sel(false);
		co_flatten_worker(sel, work, other, work->top_module());
		if (sel.empty())
			return false;
		Pass::call_on_selection(work, sel, "flatten");
		Pass::call(work, "hierarchy");
		return true;
	}

	void print_ids(FILE *file, Module *m)
	{
		fprintf(file, "%s .", m->twines().unescaped_str(m->name).c_str());
		for (string name : m->get_hdlname_attribute())
			if (m->twines().unescaped_str(m->name) != name)
				fprintf(file, " N=%s", name.c_str());
		for (auto &a : m->attributes) {
			if (a.first == ID::hdlname)
				continue;
			if (a.second.flags == RTLIL::CONST_FLAG_STRING)
				fprintf(file, " A:%s=\"%s\"", m->twines().unescaped_str(a.first).c_str(), a.second.decode_string().c_str());
			else
				fprintf(file, " A:%s=%d", m->twines().unescaped_str(a.first).c_str(), a.second.as_int());
		}
		fprintf(file, "\n");

		for (auto c : m->cells())
			if (c->name.isPublic())
			{
				fprintf(file, "%s %s c=%s", m->twines().unescaped_str(m->name).c_str(), m->twines().unescaped_str(c->name).c_str(), m->twines().unescaped_str(c->type).c_str());
				for (string name : c->get_hdlname_attribute())
					if (m->twines().unescaped_str(c->name) != name)
						fprintf(file, " N=%s", name.c_str());
				for (auto &a : c->attributes) {
					if (a.first == ID::hdlname)
						continue;
					if (a.second.flags == RTLIL::CONST_FLAG_STRING)
						fprintf(file, " A:%s=\"%s\"", m->twines().unescaped_str(a.first).c_str(), a.second.decode_string().c_str());
					else
						fprintf(file, " A:%s=%d", m->twines().unescaped_str(a.first).c_str(), a.second.as_int());
				}
				fprintf(file, "\n");
			}

		for (auto w : m->wires())
			if (w->name.isPublic())
			{
				fprintf(file, "%s %s w=%d:%d", m->twines().unescaped_str(m->name).c_str(), m->twines().unescaped_str(w->name).c_str(), w->width - 1 + w->start_offset, w->start_offset);
				for (string name : w->get_hdlname_attribute())
					if (m->twines().unescaped_str(w->name) != name)
						fprintf(file, " N=%s", name.c_str());
				for (auto &a : w->attributes) {
					if (a.first == ID::hdlname)
						continue;
					if (a.second.flags == RTLIL::CONST_FLAG_STRING)
						fprintf(file, " A:%s=\"%s\"", m->twines().unescaped_str(a.first).c_str(), a.second.decode_string().c_str());
					else
						fprintf(file, " A:%s=%d", m->twines().unescaped_str(a.first).c_str(), a.second.as_int());
				}
				if (w->port_id)
					fprintf(file, " P=%s%s", w->port_input ? "I" : "", w->port_output ? "O" : "");
				fprintf(file, "\n");
			}
		//fclose(file);
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		FILE *gold_ids = nullptr;
		FILE *gate_ids = nullptr;

		size_t argidx;
		bool nocombine = false;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if ((args[argidx] == "-gold_ids") && argidx+1 < args.size()) {
				gold_ids = stdout;
				std::string fn = args[++argidx].c_str();
				if (!gold_ids)
					log_cmd_error("Can't create file %s.\n", args[argidx].c_str());
				continue;
			}
			if ((args[argidx] == "-gate_ids") && argidx+1 < args.size()) {
				gate_ids = stdout;
				std::string fn = args[++argidx].c_str();
				if (!gate_ids)
					log_cmd_error("Can't create file %s.\n", args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-nocombine") {
				nocombine = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);

		if (saved_designs.find("gold") == saved_designs.end())
			log_error("Design \"gold\" not found in saved designs.\n");
		if (saved_designs.find("gate") == saved_designs.end())
			log_error("Design \"gate\" not found in saved designs.\n");
		Design *gold_design = saved_designs.at("gold");
		Design *gate_design = saved_designs.at("gate");

		if (gold_design->top_module() == nullptr)
			log_cmd_error("No \"gold\" top module found!\n");
		if (gate_design->top_module() == nullptr)
			log_cmd_error("No \"gate\" top module found!\n");
		std::string gold_top = gold_design->top_module()->name.unescape();
		std::string gate_top = gate_design->top_module()->name.unescape();
		if (gold_top != gate_top)
			log_error("Top modules of gold and gate do not have the same name.\n");

		Pass::call(gold_design, "setattr -unset keep_hierarchy");
		Pass::call(gate_design, "setattr -unset keep_hierarchy");
		Pass::call(gold_design, "setattr -unset keep_hierarchy -mod");
		Pass::call(gate_design, "setattr -unset keep_hierarchy -mod");

		bool did_something = true;
		while (did_something)
		{
			did_something = co_flatten(gold_design, gate_design);
			did_something |= co_flatten(gate_design, gold_design);
		}

		for (auto m : gold_design->modules())
		{
			Module *gold_m = m->clone(design, design->twines().add("\\gold." + m->name.unescape()));
			gold_m->attributes.erase(ID(top));
			if (!gate_design->module(m->name))
				log_error("Unmatched module exists in gold that does not exist in gate. This should not happen. Please report this bug.\n");
			Module *gate_m = gate_design->module(m->name)->clone(design, design->twines().add("\\gate." + m->name.unescape()));
			gate_m->attributes.erase(ID(top));
			if (gold_ids) print_ids(gold_ids, m);
		}

		for (auto m : gate_design->modules())
		{
			if (!gold_design->module(m->name))
				log_error("Unmatched module exists in gate that does not exist in gold. This should not happen. Please report this bug.\n");
			if (gate_ids)
				print_ids(gate_ids, m);
		}

		if (nocombine)
			return;

		for (auto mod : design->modules())
		{
			for (auto cell : mod->cells())
			{
				auto new_type = design->twines().add(mod->name.substr(0, 6) + design->twines().unescaped_str(cell->type)); //no comment
				if (mod->design->module(new_type))
					cell->type = new_type;
			}
		}

		//Pass::call(design, std::vector<std::string>({"miter", "-equiv", "-ignore_gold_x", "-make_assert", "\\gold." + gold_top, "\\gate." + gold_top, "miter"}));

		//design->module("\\miter")->set_bool_attribute(ID(top));

	}
} EqyCombinePass;

PRIVATE_NAMESPACE_END
