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

#include <iterator>

#include "kernel/yosys.h"
#include "kernel/celltypes.h"
#include "passes/techmap/libparse.h"
#include "kernel/cost.h"
#include "libs/json11/json11.hpp"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct cell_area_t {
	double area;
	bool is_sequential;
};

struct statdata_t
{
	#define STAT_INT_MEMBERS X(num_wires) X(num_wire_bits) X(num_pub_wires) X(num_pub_wire_bits) \
			X(num_ports) X(num_port_bits) X(num_memories) X(num_memory_bits) X(num_cells) \
			X(num_processes)

	#define STAT_NUMERIC_MEMBERS STAT_INT_MEMBERS X(area)

	#define X(_name) unsigned int _name;
	STAT_INT_MEMBERS
	#undef X
	double area;
	double sequential_area;
	string tech;

	std::map<RTLIL::IdString, int> techinfo;
	std::map<RTLIL::IdString, unsigned int, RTLIL::sort_by_id_str> num_cells_by_type;
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

	statdata_t operator*(unsigned int other) const
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

	statdata_t(RTLIL::Design *design, RTLIL::Module *mod, bool width_mode, const dict<IdString, cell_area_t> &cell_area, string techname)
	{
		tech = techname;

	#define X(_name) _name = 0;
		STAT_NUMERIC_MEMBERS
	#undef X

		for (auto wire : mod->selected_wires())
		{
			if (wire->port_input || wire->port_output) {
				num_ports++;
				num_port_bits += wire->width;
			}

			if (wire->name.isPublic()) {
				num_pub_wires++;
				num_pub_wire_bits += wire->width;
			}

			num_wires++;
			num_wire_bits += wire->width;
		}

		for (auto &it : mod->memories) {
			if (!design->selected(mod, it.second))
				continue;
			num_memories++;
			num_memory_bits += it.second->width * it.second->size;
		}

		for (auto cell : mod->selected_cells())
		{
			RTLIL::IdString cell_type = cell->type;

			if (width_mode)
			{
				if (cell_type.in(ID($not), ID($pos), ID($neg),
						ID($logic_not), ID($logic_and), ID($logic_or),
						ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool),
						ID($lut), ID($and), ID($or), ID($xor), ID($xnor),
						ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx),
						ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt),
						ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($pow), ID($alu))) {
					int width_a = cell->hasPort(ID::A) ? GetSize(cell->getPort(ID::A)) : 0;
					int width_b = cell->hasPort(ID::B) ? GetSize(cell->getPort(ID::B)) : 0;
					int width_y = cell->hasPort(ID::Y) ? GetSize(cell->getPort(ID::Y)) : 0;
					cell_type = stringf("%s_%d", cell_type.c_str(), max<int>({width_a, width_b, width_y}));
				}
				else if (cell_type.in(ID($mux), ID($pmux)))
					cell_type = stringf("%s_%d", cell_type.c_str(), GetSize(cell->getPort(ID::Y)));
				else if (cell_type == ID($bmux))
					cell_type = stringf("%s_%d_%d", cell_type.c_str(), GetSize(cell->getPort(ID::Y)), GetSize(cell->getPort(ID::S)));
				else if (cell_type == ID($demux))
					cell_type = stringf("%s_%d_%d", cell_type.c_str(), GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::S)));
				else if (cell_type.in(
						ID($sr), ID($ff), ID($dff), ID($dffe), ID($dffsr), ID($dffsre),
						ID($adff), ID($adffe), ID($sdff), ID($sdffe), ID($sdffce),
						ID($aldff), ID($aldffe), ID($dlatch), ID($adlatch), ID($dlatchsr)))
					cell_type = stringf("%s_%d", cell_type.c_str(), GetSize(cell->getPort(ID::Q)));
			}

			if (!cell_area.empty()) {
				if (cell_area.count(cell_type)) {
					cell_area_t cell_data = cell_area.at(cell_type);
					if (cell_data.is_sequential) {
						sequential_area += cell_data.area;
					}
					area += cell_data.area;
				}
				else {
					unknown_cell_area.insert(cell_type);
				}
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

	unsigned int estimate_xilinx_lc()
	{
		unsigned int lut6_cnt = num_cells_by_type[ID(LUT6)];
		unsigned int lut5_cnt = num_cells_by_type[ID(LUT5)];
		unsigned int lut4_cnt = num_cells_by_type[ID(LUT4)];
		unsigned int lut3_cnt = num_cells_by_type[ID(LUT3)];
		unsigned int lut2_cnt = num_cells_by_type[ID(LUT2)];
		unsigned int lut1_cnt = num_cells_by_type[ID(LUT1)];
		unsigned int lc_cnt = 0;

		lc_cnt += lut6_cnt;

		lc_cnt += lut5_cnt;
		if (lut1_cnt) {
			int cnt = std::min(lut5_cnt, lut1_cnt);
			lut5_cnt -= cnt;
			lut1_cnt -= cnt;
		}

		lc_cnt += lut4_cnt;
		if (lut1_cnt) {
			int cnt = std::min(lut4_cnt, lut1_cnt);
			lut4_cnt -= cnt;
			lut1_cnt -= cnt;
		}
		if (lut2_cnt) {
			int cnt = std::min(lut4_cnt, lut2_cnt);
			lut4_cnt -= cnt;
			lut2_cnt -= cnt;
		}

		lc_cnt += lut3_cnt;
		if (lut1_cnt) {
			int cnt = std::min(lut3_cnt, lut1_cnt);
			lut3_cnt -= cnt;
			lut1_cnt -= cnt;
		}
		if (lut2_cnt) {
			int cnt = std::min(lut3_cnt, lut2_cnt);
			lut3_cnt -= cnt;
			lut2_cnt -= cnt;
		}
		if (lut3_cnt) {
			int cnt = (lut3_cnt + 1) / 2;
			lut3_cnt -= cnt;
		}

		lc_cnt += (lut2_cnt + lut1_cnt + 1) / 2;

		return lc_cnt;
	}

	unsigned int cmos_transistor_count(bool *tran_cnt_exact)
	{
		unsigned int tran_cnt = 0;
		auto &gate_costs = CellCosts::cmos_gate_cost();

		for (auto it : num_cells_by_type) {
			auto ctype = it.first;
			auto cnum = it.second;

			if (gate_costs.count(ctype))
				tran_cnt += cnum * gate_costs.at(ctype);
			else
				*tran_cnt_exact = false;
		}

		return tran_cnt;
	}

	void log_data(RTLIL::IdString mod_name, bool top_mod)
	{
		log("   Number of wires:             %6u\n", num_wires);
		log("   Number of wire bits:         %6u\n", num_wire_bits);
		log("   Number of public wires:      %6u\n", num_pub_wires);
		log("   Number of public wire bits:  %6u\n", num_pub_wire_bits);
		log("   Number of ports:             %6u\n", num_ports);
		log("   Number of port bits:         %6u\n", num_port_bits);
		log("   Number of memories:          %6u\n", num_memories);
		log("   Number of memory bits:       %6u\n", num_memory_bits);
		log("   Number of processes:         %6u\n", num_processes);
		log("   Number of cells:             %6u\n", num_cells);
		for (auto &it : num_cells_by_type)
			if (it.second)
				log("     %-26s %6u\n", log_id(it.first), it.second);

		if (!unknown_cell_area.empty()) {
			log("\n");
			for (auto cell_type : unknown_cell_area)
				log("   Area for cell type %s is unknown!\n", cell_type.c_str());
		}

		if (area != 0) {
			log("\n");
			log("   Chip area for %smodule '%s': %f\n", (top_mod) ? "top " : "", mod_name.c_str(), area);
			log("     of which used for sequential elements: %f (%.2f%%)\n", sequential_area, 100.0*sequential_area/area);
		}

		if (tech == "xilinx")
		{
			log("\n");
			log("   Estimated number of LCs: %10u\n", estimate_xilinx_lc());
		}

		if (tech == "cmos")
		{
			bool tran_cnt_exact = true;
			unsigned int tran_cnt = cmos_transistor_count(&tran_cnt_exact);

			log("\n");
			log("   Estimated number of transistors: %10u%s\n", tran_cnt, tran_cnt_exact ? "" : "+");
		}
	}

	void log_data_json(const char *mod_name, bool first_module)
	{
		if (!first_module)
			log(",\n");
		log("      %s: {\n", json11::Json(mod_name).dump().c_str());
		log("         \"num_wires\":         %u,\n", num_wires);
		log("         \"num_wire_bits\":     %u,\n", num_wire_bits);
		log("         \"num_pub_wires\":     %u,\n", num_pub_wires);
		log("         \"num_pub_wire_bits\": %u,\n", num_pub_wire_bits);
		log("         \"num_ports\":         %u,\n", num_ports);
		log("         \"num_port_bits\":     %u,\n", num_port_bits);
		log("         \"num_memories\":      %u,\n", num_memories);
		log("         \"num_memory_bits\":   %u,\n", num_memory_bits);
		log("         \"num_processes\":     %u,\n", num_processes);
		log("         \"num_cells\":         %u,\n", num_cells);
		if (area != 0) {
			log("         \"area\":              %f,\n", area);
		}
		log("         \"num_cells_by_type\": {\n");
		bool first_line = true;
		for (auto &it : num_cells_by_type)
			if (it.second) {
				if (!first_line)
					log(",\n");
				log("            %s: %u", json11::Json(log_id(it.first)).dump().c_str(), it.second);
				first_line = false;
			}
		log("\n");
		log("         }");
		if (tech == "xilinx")
		{
			log(",\n");
			log("         \"estimated_num_lc\": %u", estimate_xilinx_lc());
		}
		if (tech == "cmos")
		{
			bool tran_cnt_exact = true;
			unsigned int tran_cnt = cmos_transistor_count(&tran_cnt_exact);
			log(",\n");
			log("         \"estimated_num_transistors\": \"%u%s\"", tran_cnt, tran_cnt_exact ? "" : "+");
		}
		log("\n");
		log("      }");
	}
};

statdata_t hierarchy_worker(std::map<RTLIL::IdString, statdata_t> &mod_stat, RTLIL::IdString mod, int level, bool quiet = false)
{
	statdata_t mod_data = mod_stat.at(mod);
	std::map<RTLIL::IdString, unsigned int, RTLIL::sort_by_id_str> num_cells_by_type;
	num_cells_by_type.swap(mod_data.num_cells_by_type);

	for (auto &it : num_cells_by_type)
		if (mod_stat.count(it.first) > 0) {
			if (!quiet)
				log("     %*s%-*s %6u\n", 2*level, "", 26-2*level, log_id(it.first), it.second);
			mod_data = mod_data + hierarchy_worker(mod_stat, it.first, level+1, quiet) * it.second;
			mod_data.num_cells -= it.second;
		} else {
			mod_data.num_cells_by_type[it.first] += it.second;
		}

	return mod_data;
}

void read_liberty_cellarea(dict<IdString, cell_area_t> &cell_area, string liberty_file)
{
	std::ifstream f;
	f.open(liberty_file.c_str());
	yosys_input_files.insert(liberty_file);
	if (f.fail())
		log_cmd_error("Can't open liberty file `%s': %s\n", liberty_file.c_str(), strerror(errno));
	LibertyParser libparser(f);
	f.close();

	for (auto cell : libparser.ast->children)
	{
		if (cell->id != "cell" || cell->args.size() != 1)
			continue;

		LibertyAst *ar = cell->find("area");
		bool is_flip_flop = cell->find("ff") != nullptr;
		if (ar != nullptr && !ar->value.empty())
			cell_area["\\" + cell->args[0]] = {/*area=*/atof(ar->value.c_str()), is_flip_flop};
	}
}

struct StatPass : public Pass {
	StatPass() : Pass("stat", "print some statistics") { }
	void help() override
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
		log("    -tech <technology>\n");
		log("        print area estimate for the specified technology. Currently supported\n");
		log("        values for <technology>: xilinx, cmos\n");
		log("\n");
		log("    -width\n");
		log("        annotate internal cell types with their word width.\n");
		log("        e.g. $add_8 for an 8 bit wide $add cell.\n");
		log("\n");
		log("    -json\n");
		log("        output the statistics in a machine-readable JSON format.\n");
		log("        this is output to the console; use \"tee\" to output to a file.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool width_mode = false, json_mode = false;
		RTLIL::Module *top_mod = nullptr;
		std::map<RTLIL::IdString, statdata_t> mod_stat;
		dict<IdString, cell_area_t> cell_area;
		string techname;

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
			if (args[argidx] == "-tech" && argidx+1 < args.size()) {
				techname = args[++argidx];
				continue;
			}
			if (args[argidx] == "-top" && argidx+1 < args.size()) {
				if (design->module(RTLIL::escape_id(args[argidx+1])) == nullptr)
					log_cmd_error("Can't find module %s.\n", args[argidx+1].c_str());
				top_mod = design->module(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-json") {
				json_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if(!json_mode)
			log_header(design, "Printing statistics.\n");

		if (techname != "" && techname != "xilinx" && techname != "cmos" && !json_mode)
			log_cmd_error("Unsupported technology: '%s'\n", techname.c_str());

		if (json_mode) {
			log("{\n");
			log("   \"creator\": %s,\n", json11::Json(yosys_version_str).dump().c_str());
			std::stringstream invocation;
			std::copy(args.begin(), args.end(), std::ostream_iterator<std::string>(invocation, " "));
			log("   \"invocation\": %s,\n", json11::Json(invocation.str()).dump().c_str());
			log("   \"modules\": {\n");
		}

		bool first_module = true;
		for (auto mod : design->selected_modules())
		{
			if (!top_mod && design->full_selection())
				if (mod->get_bool_attribute(ID::top))
					top_mod = mod;

			statdata_t data(design, mod, width_mode, cell_area, techname);
			mod_stat[mod->name] = data;

			if (json_mode) {
				data.log_data_json(mod->name.c_str(), first_module);
				first_module = false;
			} else {
				log("\n");
				log("=== %s%s ===\n", log_id(mod->name), design->selected_whole_module(mod->name) ? "" : " (partially selected)");
				log("\n");
				data.log_data(mod->name, false);
			}
		}

		if (json_mode) {
			log("\n");
			log(top_mod == nullptr ? "   }\n" : "   },\n");
		}

		if (top_mod != nullptr)
		{
			if (!json_mode && GetSize(mod_stat) > 1) {
				log("\n");
				log("=== design hierarchy ===\n");
				log("\n");
				log("   %-28s %6d\n", log_id(top_mod->name), 1);
			}

			statdata_t data = hierarchy_worker(mod_stat, top_mod->name, 0, /*quiet=*/json_mode);

			if (json_mode)
				data.log_data_json("design", true);
			else if (GetSize(mod_stat) > 1) {
				log("\n");
				data.log_data(top_mod->name, true);
			}

			design->scratchpad_set_int("stat.num_wires", data.num_wires);
			design->scratchpad_set_int("stat.num_wire_bits", data.num_wire_bits);
			design->scratchpad_set_int("stat.num_pub_wires", data.num_pub_wires);
			design->scratchpad_set_int("stat.num_pub_wire_bits", data.num_pub_wire_bits);
			design->scratchpad_set_int("stat.num_ports", data.num_ports);
			design->scratchpad_set_int("stat.num_port_bits", data.num_port_bits);
			design->scratchpad_set_int("stat.num_memories", data.num_memories);
			design->scratchpad_set_int("stat.num_memory_bits", data.num_memory_bits);
			design->scratchpad_set_int("stat.num_processes", data.num_processes);
			design->scratchpad_set_int("stat.num_cells", data.num_cells);
			design->scratchpad_set_int("stat.area", data.area);
		}

		if (json_mode) {
			log("\n");
			log("}\n");
		}

		log("\n");
	}
} StatPass;

PRIVATE_NAMESPACE_END
