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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/log.h"

namespace
{
	struct statdata_t
	{
		#define STAT_INT_MEMBERS X(num_wires) X(num_wire_bits) X(num_pub_wires) X(num_pub_wire_bits) \
				X(num_memories) X(num_memory_bits) X(num_cells) X(num_processes)

		#define X(_name) int _name;
		STAT_INT_MEMBERS
		#undef X

		std::map<RTLIL::IdString, int> num_cells_by_type;

		statdata_t operator+(const statdata_t &other) const
		{
			statdata_t sum = other;
		#define X(_name) sum._name += _name;
			STAT_INT_MEMBERS
		#undef X
			for (auto &it : num_cells_by_type)
				sum.num_cells_by_type[it.first] += it.second;
			return sum;
		}

		statdata_t operator*(int other) const
		{
			statdata_t sum = *this;
		#define X(_name) sum._name *= other;
			STAT_INT_MEMBERS
		#undef X
			for (auto &it : sum.num_cells_by_type)
				it.second *= other;
			return sum;
		}

		statdata_t()
		{
		#define X(_name) _name = 0;
			STAT_INT_MEMBERS
		#undef X
		}

		statdata_t(RTLIL::Design *design, RTLIL::Module *mod)
		{
		#define X(_name) _name = 0;
			STAT_INT_MEMBERS
		#undef X

			for (auto &it : mod->wires_)
			{
				if (!design->selected(mod, it.second))
					continue;

				if (it.first[0] == '\\') {
					num_pub_wires++;
					num_pub_wire_bits += it.second->width;
				}

				num_wires++;
				num_wire_bits += it.second->width;
			}

			for (auto &it : mod->memories) {
				if (!design->selected(mod, it.second))
					continue;
				num_memories++;
				num_memory_bits += it.second->width * it.second->size;
			}

			for (auto &it : mod->cells_) {
				if (!design->selected(mod, it.second))
					continue;
				num_cells++;
				num_cells_by_type[it.second->type]++;
			}

			for (auto &it : mod->processes) {
				if (!design->selected(mod, it.second))
					continue;
				num_processes++;
			}
		}

		void log_data()
		{
			log("   Number of wires:             %6d\n", num_wires);
			log("   Number of wire bits:         %6d\n", num_wire_bits);
			log("   Number of public wires:      %6d\n", num_pub_wires);
			log("   Number of public wire bits:  %6d\n", num_pub_wire_bits);
			log("   Number of memories:          %6d\n", num_memories);
			log("   Number of memory bits:       %6d\n", num_memory_bits);
			log("   Number of processes:         %6d\n", num_processes);
			log("   Number of cells:             %6d\n", num_cells);
			for (auto &it : num_cells_by_type)
				log("     %-26s %6d\n", RTLIL::id2cstr(it.first), it.second);
		}
	};

	statdata_t hierarchy_worker(std::map<RTLIL::IdString, statdata_t> &mod_stat, RTLIL::IdString mod, int level)
	{
		statdata_t mod_data = mod_stat.at(mod);
		std::map<RTLIL::IdString, int> num_cells_by_type;
		num_cells_by_type.swap(mod_data.num_cells_by_type);

		for (auto &it : num_cells_by_type)
			if (mod_stat.count(it.first) > 0) {
				log("     %*s%-*s %6d\n", 2*level, "", 26-2*level, RTLIL::id2cstr(it.first), it.second);
				mod_data = mod_data + hierarchy_worker(mod_stat, it.first, level+1) * it.second;
				mod_data.num_cells -= it.second;
			} else {
				mod_data.num_cells_by_type[it.first] += it.second;
			}

		return mod_data;
	}
}

struct StatPass : public Pass {
	StatPass() : Pass("stat", "print some statistics") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    stat [options] [selection]\n");
		log("\n");
		log("Print some statistics (number of objects) on the selected portion of the\n");
		log("design.\n");
		log("\n");
		log("    -top <module>\n");
		log("        print design hierarchy with this module as top. if the design is fully\n");
		log("        selected and a module has the 'top' attribute set, this module is used\n");
		log("        default value for this option.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header("Printing statistics.\n");

		RTLIL::Module *top_mod = NULL;
		std::map<RTLIL::IdString, statdata_t> mod_stat;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				if (design->modules.count(RTLIL::escape_id(args[argidx+1])) == 0)
					log_cmd_error("Can't find module %s.\n", args[argidx+1].c_str());
				top_mod = design->modules.at(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &it : design->modules)
		{
			if (!design->selected_module(it.first))
				continue;

			if (!top_mod && design->full_selection())
				if (it.second->get_bool_attribute("\\top"))
					top_mod = it.second;

			statdata_t data(design, it.second);
			mod_stat[it.first] = data;

			log("\n");
			log("=== %s%s ===\n", RTLIL::id2cstr(it.first), design->selected_whole_module(it.first) ? "" : " (partially selected)");
			log("\n");
			data.log_data();
		}

		if (top_mod != NULL)
		{
			log("\n");
			log("=== design hierarchy ===\n");
			log("\n");

			log("   %-28s %6d\n", RTLIL::id2cstr(top_mod->name), 1);
			statdata_t data = hierarchy_worker(mod_stat, top_mod->name, 0);

			log("\n");
			data.log_data();
		}

		log("\n");
	}
} StatPass;
 
