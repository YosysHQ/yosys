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
#include "passes/techmap/libparse.h"

#include "kernel/log.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct statdata_t
{
	#define STAT_INT_MEMBERS X(num_wires) X(num_wire_bits) X(num_pub_wires) X(num_pub_wire_bits) \
			X(num_memories) X(num_memory_bits) X(num_cells) X(num_processes)

	#define STAT_NUMERIC_MEMBERS STAT_INT_MEMBERS X(area)

	#define X(_name) int _name;
	STAT_INT_MEMBERS
	#undef X
	double area;

	std::map<RTLIL::IdString, int, RTLIL::sort_by_id_str> num_cells_by_type;
	std::set<RTLIL::IdString> unknown_cell_area;

	statdata_t operator+(const statdata_t &other) const
	{
		statdata_t sum = other;
	#define X(_name) sum._name += _name;
		STAT_NUMERIC_MEMBERS
	#undef X
		for (auto &it : num_cells_by_type)
			sum.num_cells_by_type[it.first] += it.second;
		return sum;
	}

	statdata_t operator*(int other) const
	{
		statdata_t sum = *this;
	#define X(_name) sum._name *= other;
		STAT_NUMERIC_MEMBERS
	#undef X
		for (auto &it : sum.num_cells_by_type)
			it.second *= other;
		return sum;
	}

	statdata_t()
	{
	#define X(_name) _name = 0;
		STAT_NUMERIC_MEMBERS
	#undef X
	}

	statdata_t(RTLIL::Design *design, RTLIL::Module *mod, bool width_mode, const dict<IdString, double> &cell_area)
	{
	#define X(_name) _name = 0;
		STAT_NUMERIC_MEMBERS
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

		for (auto &it : mod->cells_)
		{
			if (!design->selected(mod, it.second))
				continue;

			RTLIL::IdString cell_type = it.second->type;

			if (width_mode)
			{
				if (cell_type.in("$not", "$pos", "$neg",
						"$logic_not", "$logic_and", "$logic_or",
						"$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor", "$reduce_bool",
						"$lut", "$and", "$or", "$xor", "$xnor",
						"$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx",
						"$lt", "$le", "$eq", "$ne", "$eqx", "$nex", "$ge", "$gt",
						"$add", "$sub", "$mul", "$div", "$mod", "$pow")) {
					int width_a = it.second->hasPort("\\A") ? GetSize(it.second->getPort("\\A")) : 0;
					int width_b = it.second->hasPort("\\B") ? GetSize(it.second->getPort("\\B")) : 0;
					int width_y = it.second->hasPort("\\Y") ? GetSize(it.second->getPort("\\Y")) : 0;
					cell_type = stringf("%s_%d", cell_type.c_str(), max<int>({width_a, width_b, width_y}));
				}
				else if (cell_type.in("$mux", "$pmux"))
					cell_type = stringf("%s_%d", cell_type.c_str(), GetSize(it.second->getPort("\\Y")));
				else if (cell_type.in("$sr", "$dff", "$dffsr", "$adff", "$dlatch", "$dlatchsr"))
					cell_type = stringf("%s_%d", cell_type.c_str(), GetSize(it.second->getPort("\\Q")));
			}

			if (!cell_area.empty()) {
				if (cell_area.count(cell_type))
					area += cell_area.at(cell_type);
				else
					unknown_cell_area.insert(cell_type);
			}

			num_cells++;
			num_cells_by_type[cell_type]++;
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

		if (!unknown_cell_area.empty()) {
			log("\n");
			for (auto cell_type : unknown_cell_area)
				log("   Area for cell type %s is unknown!\n", cell_type.c_str());
		}

		if (area != 0) {
			log("\n");
			log("   Chip area for this module: %f\n", area);
		}
	}
};

statdata_t hierarchy_worker(std::map<RTLIL::IdString, statdata_t> &mod_stat, RTLIL::IdString mod, int level)
{
	statdata_t mod_data = mod_stat.at(mod);
	std::map<RTLIL::IdString, int, RTLIL::sort_by_id_str> num_cells_by_type;
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

void read_liberty_cellarea(dict<IdString, double> &cell_area, string liberty_file)
{
	std::ifstream f;
	f.open(liberty_file.c_str());
	if (f.fail())
		log_cmd_error("Can't open liberty file `%s': %s\n", liberty_file.c_str(), strerror(errno));
	LibertyParser libparser(f);
	f.close();

	for (auto cell : libparser.ast->children)
	{
		if (cell->id != "cell" || cell->args.size() != 1)
			continue;

		LibertyAst *ar = cell->find("area");
		if (ar != NULL && !ar->value.empty())
			cell_area["\\" + cell->args[0]] = atof(ar->value.c_str());
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
		log("    -liberty <liberty_file>\n");
		log("        use cell area information from the provided liberty file\n");
		log("\n");
		log("    -width\n");
		log("        annotate internal cell types with their word width.\n");
		log("        e.g. $add_8 for an 8 bit wide $add cell.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		log_header(design, "Printing statistics.\n");

		bool width_mode = false;
		RTLIL::Module *top_mod = NULL;
		std::map<RTLIL::IdString, statdata_t> mod_stat;
		dict<IdString, double> cell_area;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-width") {
				width_mode = true;
				continue;
			}
			if (args[argidx] == "-liberty" && argidx+1 < args.size()) {
				string liberty_file = args[++argidx];
				rewrite_filename(liberty_file);
				read_liberty_cellarea(cell_area, liberty_file);
				continue;
			}
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				if (design->modules_.count(RTLIL::escape_id(args[argidx+1])) == 0)
					log_cmd_error("Can't find module %s.\n", args[argidx+1].c_str());
				top_mod = design->modules_.at(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules())
		{
			if (!top_mod && design->full_selection())
				if (mod->get_bool_attribute("\\top"))
					top_mod = mod;

			statdata_t data(design, mod, width_mode, cell_area);
			mod_stat[mod->name] = data;

			log("\n");
			log("=== %s%s ===\n", RTLIL::id2cstr(mod->name), design->selected_whole_module(mod->name) ? "" : " (partially selected)");
			log("\n");
			data.log_data();
		}

		if (top_mod != NULL && GetSize(mod_stat) > 1)
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

PRIVATE_NAMESPACE_END
