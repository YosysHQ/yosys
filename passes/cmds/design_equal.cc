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
#include "kernel/rtlil.h"

YOSYS_NAMESPACE_BEGIN

class ModuleComparator
{
	RTLIL::Module *mod_a;
	RTLIL::Module *mod_b;

public:
	ModuleComparator(RTLIL::Module *mod_a, RTLIL::Module *mod_b) : mod_a(mod_a), mod_b(mod_b) {}

	template <typename... Args>
	[[noreturn]] void error(FmtString<TypeIdentity<Args>...> fmt, const Args &... args)
	{
		formatted_error(fmt.format(args...));
	}
	[[noreturn]]
	void formatted_error(std::string err)
	{
		log("Module A: %s\n", log_id(mod_a->name));
		log_module(mod_a, "  ");
		log("Module B: %s\n", log_id(mod_b->name));
		log_module(mod_b, "  ");
		log_cmd_error("Designs are different: %s\n", err);
	}

	bool compare_sigbit(const RTLIL::SigBit &a, const RTLIL::SigBit &b)
	{
		if (a.wire == nullptr && b.wire == nullptr)
			return a.data == b.data;
		if (a.wire != nullptr && b.wire != nullptr)
			return a.wire->name == b.wire->name && a.offset == b.offset;
		return false;
	}

	bool compare_sigspec(const RTLIL::SigSpec &a, const RTLIL::SigSpec &b)
	{
		if (a.size() != b.size()) return false;
		auto it_a = a.begin(), it_b = b.begin();
		for (; it_a != a.end(); ++it_a, ++it_b) {
			if (!compare_sigbit(*it_a, *it_b)) return false;
		}
		return true;
	}

	std::string compare_attributes(const RTLIL::AttrObject *a, const RTLIL::AttrObject *b)
	{
		for (const auto &it : a->attributes) {
			if (b->attributes.count(it.first) == 0)
				return "missing attribute " + std::string(log_id(it.first)) + " in second design";
			if (it.second != b->attributes.at(it.first))
				return "attribute " + std::string(log_id(it.first)) + " mismatch: " + log_const(it.second) + " != " + log_const(b->attributes.at(it.first));
		}
		for (const auto &it : b->attributes)
			if (a->attributes.count(it.first) == 0)
				return "missing attribute " + std::string(log_id(it.first)) + " in first design";
		return "";
	}

	std::string compare_wires(const RTLIL::Wire *a, const RTLIL::Wire *b)
	{
		if (a->name != b->name)
			return "name mismatch: " + std::string(log_id(a->name)) + " != " + log_id(b->name);
		if (a->width != b->width)
			return "width mismatch: " + std::to_string(a->width) + " != " + std::to_string(b->width);
		if (a->start_offset != b->start_offset)
			return "start_offset mismatch: " + std::to_string(a->start_offset) + " != " + std::to_string(b->start_offset);
		if (a->port_id != b->port_id)
			return "port_id mismatch: " + std::to_string(a->port_id) + " != " + std::to_string(b->port_id);
		if (a->port_input != b->port_input)
			return "port_input mismatch: " + std::to_string(a->port_input) + " != " + std::to_string(b->port_input);
		if (a->port_output != b->port_output)
			return "port_output mismatch: " + std::to_string(a->port_output) + " != " + std::to_string(b->port_output);
		if (a->upto != b->upto)
			return "upto mismatch: " + std::to_string(a->upto) + " != " + std::to_string(b->upto);
		if (a->is_signed != b->is_signed)
			return "is_signed mismatch: " + std::to_string(a->is_signed) + " != " + std::to_string(b->is_signed);
		if (std::string mismatch = compare_attributes(a, b); !mismatch.empty())
			return mismatch;
		return "";
	}

	void check_wires()
	{
		for (const auto &it : mod_a->wires_) {
			if (mod_b->wires_.count(it.first) == 0)
				error("Module %s missing wire %s in second design.\n", log_id(mod_a->name), log_id(it.first));
			if (std::string mismatch = compare_wires(it.second, mod_b->wires_.at(it.first)); !mismatch.empty())
				error("Module %s wire %s %s.\n", log_id(mod_a->name), log_id(it.first), mismatch);
		}
		for (const auto &it : mod_b->wires_)
			if (mod_a->wires_.count(it.first) == 0)
				error("Module %s missing wire %s in first design.\n", log_id(mod_b->name), log_id(it.first));
	}

	std::string compare_memories(const RTLIL::Memory *a, const RTLIL::Memory *b)
	{
		if (a->name != b->name)
			return "name mismatch: " + std::string(log_id(a->name)) + " != " + log_id(b->name);
		if (a->width != b->width)
			return "width mismatch: " + std::to_string(a->width) + " != " + std::to_string(b->width);
		if (a->start_offset != b->start_offset)
			return "start_offset mismatch: " + std::to_string(a->start_offset) + " != " + std::to_string(b->start_offset);
		if (a->size != b->size)
			return "size mismatch: " + std::to_string(a->size) + " != " + std::to_string(b->size);
		if (std::string mismatch = compare_attributes(a, b); !mismatch.empty())
			return mismatch;
		return "";
	}

	std::string compare_cells(const RTLIL::Cell *a, const RTLIL::Cell *b)
	{
		if (a->name != b->name)
			return "name mismatch: " + std::string(log_id(a->name)) + " != " + log_id(b->name);
		if (a->type != b->type)
			return "type mismatch: " + std::string(log_id(a->type)) + " != " + log_id(b->type);
		if (std::string mismatch = compare_attributes(a, b); !mismatch.empty())
			return mismatch;

		for (const auto &it : a->parameters) {
			if (b->parameters.count(it.first) == 0)
				return "parameter mismatch: missing parameter " + std::string(log_id(it.first)) + " in second design";
			if (it.second != b->parameters.at(it.first))
				return "parameter mismatch: " + std::string(log_id(it.first)) + " mismatch: " + log_const(it.second) + " != " + log_const(b->parameters.at(it.first));
		}
		for (const auto &it : b->parameters)
			if (a->parameters.count(it.first) == 0)
				return "parameter mismatch: missing parameter " + std::string(log_id(it.first)) + " in first design";

		for (const auto &it : a->connections()) {
			if (b->connections().count(it.first) == 0)
				return "connection mismatch: missing connection " + std::string(log_id(it.first)) + " in second design";
			if (!compare_sigspec(it.second, b->connections().at(it.first)))
				return "connection " + std::string(log_id(it.first)) + " mismatch: " + log_signal(it.second) + " != " + log_signal(b->connections().at(it.first));
		}
		for (const auto &it : b->connections())
			if (a->connections().count(it.first) == 0)
				return "connection mismatch: missing connection " + std::string(log_id(it.first)) + " in first design";

		return "";
	}

	void check_cells()
	{
		for (const auto &it : mod_a->cells_) {
			if (mod_b->cells_.count(it.first) == 0)
				error("Module %s missing cell %s in second design.\n", log_id(mod_a->name), log_id(it.first));
			if (std::string mismatch = compare_cells(it.second, mod_b->cells_.at(it.first)); !mismatch.empty())
				error("Module %s cell %s %s.\n", log_id(mod_a->name), log_id(it.first), mismatch);
		}
		for (const auto &it : mod_b->cells_)
			if (mod_a->cells_.count(it.first) == 0)
				error("Module %s missing cell %s in first design.\n", log_id(mod_b->name), log_id(it.first));
	}

	void check_memories()
	{
		for (const auto &it : mod_a->memories) {
			if (mod_b->memories.count(it.first) == 0)
				error("Module %s missing memory %s in second design.\n", log_id(mod_a->name), log_id(it.first));
			if (std::string mismatch = compare_memories(it.second, mod_b->memories.at(it.first)); !mismatch.empty())
				error("Module %s memory %s %s.\n", log_id(mod_a->name), log_id(it.first), mismatch);
		}
		for (const auto &it : mod_b->memories)
			if (mod_a->memories.count(it.first) == 0)
				error("Module %s missing memory %s in first design.\n", log_id(mod_b->name), log_id(it.first));
	}

	std::string compare_case_rules(const RTLIL::CaseRule *a, const RTLIL::CaseRule *b)
	{
		if (std::string mismatch = compare_attributes(a, b); !mismatch.empty()) return mismatch;

		if (a->compare.size() != b->compare.size())
			return "compare size mismatch: " + std::to_string(a->compare.size()) + " != " + std::to_string(b->compare.size());
		for (size_t i = 0; i < a->compare.size(); i++)
			if (!compare_sigspec(a->compare[i], b->compare[i]))
				return "compare " + std::to_string(i) + " mismatch: " + log_signal(a->compare[i]) + " != " + log_signal(b->compare[i]);

		if (a->actions.size() != b->actions.size())
			return "actions size mismatch: " + std::to_string(a->actions.size()) + " != " + std::to_string(b->actions.size());
		for (size_t i = 0; i < a->actions.size(); i++) {
			if (!compare_sigspec(a->actions[i].first, b->actions[i].first))
				return "action " + std::to_string(i) + " first mismatch: " + log_signal(a->actions[i].first) + " != " + log_signal(b->actions[i].first);
			if (!compare_sigspec(a->actions[i].second, b->actions[i].second))
				return "action " + std::to_string(i) + " second mismatch: " + log_signal(a->actions[i].second) + " != " + log_signal(b->actions[i].second);
		}

		if (a->switches.size() != b->switches.size())
			return "switches size mismatch: " + std::to_string(a->switches.size()) + " != " + std::to_string(b->switches.size());
		for (size_t i = 0; i < a->switches.size(); i++)
			if (std::string mismatch = compare_switch_rules(a->switches[i], b->switches[i]); !mismatch.empty())
				return "switch " + std::to_string(i) + " " + mismatch;

		return "";
	}

	std::string compare_switch_rules(const RTLIL::SwitchRule *a, const RTLIL::SwitchRule *b)
	{
		if (std::string mismatch = compare_attributes(a, b); !mismatch.empty())
			return mismatch;
		if (!compare_sigspec(a->signal, b->signal))
			return "signal mismatch: " + log_signal(a->signal) + " != " + log_signal(b->signal);

		if (a->cases.size() != b->cases.size())
			return "cases size mismatch: " + std::to_string(a->cases.size()) + " != " + std::to_string(b->cases.size());
		for (size_t i = 0; i < a->cases.size(); i++)
			if (std::string mismatch = compare_case_rules(a->cases[i], b->cases[i]); !mismatch.empty())
				return "case " + std::to_string(i) + " " + mismatch;

		return "";
	}

	std::string compare_sync_rules(const RTLIL::SyncRule *a, const RTLIL::SyncRule *b)
	{
		if (a->type != b->type)
			return "type mismatch: " + std::to_string(a->type) + " != " + std::to_string(b->type);
		if (!compare_sigspec(a->signal, b->signal))
			return "signal mismatch: " + log_signal(a->signal) + " != " + log_signal(b->signal);
		if (a->actions.size() != b->actions.size())
			return "actions size mismatch: " + std::to_string(a->actions.size()) + " != " + std::to_string(b->actions.size());
		for (size_t i = 0; i < a->actions.size(); i++) {
			if (!compare_sigspec(a->actions[i].first, b->actions[i].first))
				return "action " + std::to_string(i) + " first mismatch: " + log_signal(a->actions[i].first) + " != " + log_signal(b->actions[i].first);
			if (!compare_sigspec(a->actions[i].second, b->actions[i].second))
				return "action " + std::to_string(i) + " second mismatch: " + log_signal(a->actions[i].second) + " != " + log_signal(b->actions[i].second);
		}
		if (a->mem_write_actions.size() != b->mem_write_actions.size())
			return "mem_write_actions size mismatch: " + std::to_string(a->mem_write_actions.size()) + " != " + std::to_string(b->mem_write_actions.size());
		for (size_t i = 0; i < a->mem_write_actions.size(); i++) {
			const auto &ma = a->mem_write_actions[i];
			const auto &mb = b->mem_write_actions[i];
			if (ma.memid != mb.memid)
				return "mem_write_actions " + std::to_string(i) + " memid mismatch: " + log_id(ma.memid) + " != " + log_id(mb.memid);
			if (!compare_sigspec(ma.address, mb.address))
				return "mem_write_actions " + std::to_string(i) + " address mismatch: " + log_signal(ma.address) + " != " + log_signal(mb.address);
			if (!compare_sigspec(ma.data, mb.data))
				return "mem_write_actions " + std::to_string(i) + " data mismatch: " + log_signal(ma.data) + " != " + log_signal(mb.data);
			if (!compare_sigspec(ma.enable, mb.enable))
				return "mem_write_actions " + std::to_string(i) + " enable mismatch: " + log_signal(ma.enable) + " != " + log_signal(mb.enable);
			if (ma.priority_mask != mb.priority_mask)
				return "mem_write_actions " + std::to_string(i) + " priority_mask mismatch: " + log_const(ma.priority_mask) + " != " + log_const(mb.priority_mask);
			if (std::string mismatch = compare_attributes(&ma, &mb); !mismatch.empty())
				return "mem_write_actions " + std::to_string(i) + " " + mismatch;
		}
		return "";
	}

	std::string compare_processes(const RTLIL::Process *a, const RTLIL::Process *b)
	{
		if (a->name != b->name) return "name mismatch: " + std::string(log_id(a->name)) + " != " + log_id(b->name);
		if (std::string mismatch = compare_attributes(a, b); !mismatch.empty())
			return mismatch;
		if (std::string mismatch = compare_case_rules(&a->root_case, &b->root_case); !mismatch.empty())
			return "case rule " + mismatch;
		if (a->syncs.size() != b->syncs.size())
			return "sync count mismatch: " + std::to_string(a->syncs.size()) + " != " + std::to_string(b->syncs.size());
		for (size_t i = 0; i < a->syncs.size(); i++)
			if (std::string mismatch = compare_sync_rules(a->syncs[i], b->syncs[i]); !mismatch.empty())
				return "sync " + std::to_string(i) + " " + mismatch;
		return "";
	}

	void check_processes()
	{
		for (auto &it : mod_a->processes) {
			if (mod_b->processes.count(it.first) == 0)
				error("Module %s missing process %s in second design.\n", log_id(mod_a->name), log_id(it.first));
			if (std::string mismatch = compare_processes(it.second, mod_b->processes.at(it.first)); !mismatch.empty())
				error("Module %s process %s %s.\n", log_id(mod_a->name), log_id(it.first), mismatch.c_str());
		}
		for (auto &it : mod_b->processes)
			if (mod_a->processes.count(it.first) == 0)
				error("Module %s missing process %s in first design.\n", log_id(mod_b->name), log_id(it.first));
	}

	void check_connections()
	{
		const auto &conns_a = mod_a->connections();
		const auto &conns_b = mod_b->connections();
		if (conns_a.size() != conns_b.size()) {
			error("Module %s connection count differs: %zu != %zu\n", log_id(mod_a->name), conns_a.size(), conns_b.size());
		} else {
			for (size_t i = 0; i < conns_a.size(); i++) {
				if (!compare_sigspec(conns_a[i].first, conns_b[i].first))
					error("Module %s connection %zu LHS %s != %s.\n", log_id(mod_a->name), i, log_signal(conns_a[i].first), log_signal(conns_b[i].first));
				if (!compare_sigspec(conns_a[i].second, conns_b[i].second))
					error("Module %s connection %zu RHS %s != %s.\n", log_id(mod_a->name), i, log_signal(conns_a[i].second), log_signal(conns_b[i].second));
			}
		}
	}

	void check()
	{
		if (mod_a->name != mod_b->name)
			error("Modules have different names: %s != %s\n", log_id(mod_a->name), log_id(mod_b->name));
		if (std::string mismatch = compare_attributes(mod_a, mod_b); !mismatch.empty())
			error("Module %s %s.\n", log_id(mod_a->name), mismatch);
		check_wires();
		check_cells();
		check_memories();
		check_connections();
		check_processes();
	}
};

struct DesignEqualPass : public Pass {
	DesignEqualPass() : Pass("design_equal", "check if two designs are the same") { }
	void help() override
	{
		log("\n");
		log("    design_equal <name>\n");
		log("\n");
		log("Compare the current design with the design previously saved under the given\n");
		log("name. Abort with an error if the designs are different.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		if (args.size() != 2)
			log_cmd_error("Missing argument.\n");

		std::string check_name = args[1];
		if (saved_designs.count(check_name) == 0)
			log_cmd_error("No saved design '%s' found!\n", check_name.c_str());

		RTLIL::Design *other = saved_designs.at(check_name);

		for (auto &it : design->modules_) {
			RTLIL::Module *mod = it.second;
			if (!other->has(mod->name))
				log_error("Second design missing module %s.\n", log_id(mod->name));

			ModuleComparator cmp(mod, other->module(mod->name));
			cmp.check();
		}
		for (auto &it : other->modules_) {
			RTLIL::Module *mod = it.second;
			if (!design->has(mod->name))
				log_error("First design missing module %s.\n", log_id(mod->name));
		}

		log("Designs are identical.\n");
	}
} DesignEqualPass;

YOSYS_NAMESPACE_END
