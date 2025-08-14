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

#include "kernel/celltypes.h"
#include "kernel/cost.h"
#include "kernel/gzip.h"
#include "kernel/log_help.h"
#include "kernel/yosys.h"
#include "libs/json11/json11.hpp"
#include "passes/techmap/libparse.h"
#include <charconv>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct cell_area_t {
	double area;
	bool is_sequential;
	vector<double> single_parameter_area;
	vector<vector<double>> double_parameter_area;
	vector<string> parameter_names;
};

struct statdata_t {
#define STAT_INT_MEMBERS                                                                                                                             \
	X(num_wires)                                                                                                                                 \
	X(num_wire_bits)                                                                                                                             \
	X(num_pub_wires) X(num_pub_wire_bits) X(num_ports) X(num_port_bits) X(num_memories) X(num_memory_bits) X(num_cells) X(num_processes)

#define STAT_NUMERIC_MEMBERS STAT_INT_MEMBERS X(area) X(sequential_area)

#define X(_name) unsigned int _name;
	STAT_INT_MEMBERS
#undef X
#define X(_name) unsigned int local_##_name;
	STAT_INT_MEMBERS
#undef X
	double area = 0;
	double sequential_area = 0;
	double local_area = 0;
	double local_sequential_area = 0;
	double submodule_area = 0;
	int num_submodules = 0;
	std::map<RTLIL::IdString, unsigned int, RTLIL::sort_by_id_str> num_submodules_by_type;
	std::map<RTLIL::IdString, double, RTLIL::sort_by_id_str> submodules_area_by_type;

	std::map<RTLIL::IdString, unsigned int, RTLIL::sort_by_id_str> local_num_cells_by_type;
	std::map<RTLIL::IdString, double, RTLIL::sort_by_id_str> local_area_cells_by_type;
	std::map<RTLIL::IdString, double, RTLIL::sort_by_id_str> local_seq_area_cells_by_type;
	string tech;

	std::map<RTLIL::IdString, unsigned int, RTLIL::sort_by_id_str> num_cells_by_type;
	std::map<RTLIL::IdString, double, RTLIL::sort_by_id_str> area_cells_by_type;
	std::map<RTLIL::IdString, double, RTLIL::sort_by_id_str> seq_area_cells_by_type;
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
	statdata_t add(const statdata_t &other)
	{
#define X(_name) _name += other._name;
		STAT_NUMERIC_MEMBERS
#undef X
		for (auto &it : other.num_cells_by_type) {
			if (num_cells_by_type.count(it.first))
				num_cells_by_type[it.first] += it.second;
			else
				num_cells_by_type[it.first] = it.second;
		}
		for (auto &it : other.submodules_area_by_type) {
			if (submodules_area_by_type.count(it.first))
				submodules_area_by_type[it.first] += it.second;
			else
				submodules_area_by_type[it.first] = it.second;
		}
		for (auto &it : other.area_cells_by_type) {
			if (area_cells_by_type.count(it.first))
				area_cells_by_type[it.first] += it.second;
			else
				area_cells_by_type[it.first] = it.second;
		}
		for (auto &it : other.seq_area_cells_by_type) {
			if (seq_area_cells_by_type.count(it.first))
				seq_area_cells_by_type[it.first] += it.second;
			else
				seq_area_cells_by_type[it.first] = it.second;
		}
		unknown_cell_area.insert(other.unknown_cell_area.begin(), other.unknown_cell_area.end());
		return *this;
	}

	statdata_t()
	{
#define X(_name) _name = 0;
		STAT_NUMERIC_MEMBERS
#undef X
	}

	statdata_t(cell_area_t &cell_data, string techname)
	{
		tech = techname;
		area = cell_data.area;
		if (cell_data.is_sequential) {
			sequential_area = cell_data.area;
		}
	}

	statdata_t(const RTLIL::Design *design, const RTLIL::Module *mod, bool width_mode, dict<IdString, cell_area_t> &cell_area, string techname)
	{
		tech = techname;

#define X(_name) _name = 0;
		STAT_NUMERIC_MEMBERS
#undef X
#define X(_name) local_##_name = 0;
		STAT_NUMERIC_MEMBERS
#undef X
		// additional_cell_area

		for (auto wire : mod->selected_wires()) {
			if (wire->port_input || wire->port_output) {
				num_ports++;
				local_num_ports++;
				num_port_bits += wire->width;
				local_num_port_bits += wire->width;
			}

			if (wire->name.isPublic()) {
				num_pub_wires++;
				local_num_pub_wires++;
				num_pub_wire_bits += wire->width;
				local_num_pub_wire_bits += wire->width;
			}

			num_wires++;
			local_num_wires++;
			num_wire_bits += wire->width;
			local_num_wire_bits += wire->width;
		}

		for (auto &it : mod->memories) {
			if (!design->selected(mod, it.second))
				continue;
			num_memories++;
			local_num_memories++;
			num_memory_bits += it.second->width * it.second->size;
			local_num_memory_bits += it.second->width * it.second->size;
		}
		for (auto cell : mod->selected_cells()) {
			RTLIL::IdString cell_type = cell->type;
			if (width_mode) {
				if (cell_type.in(ID($not), ID($pos), ID($neg), ID($logic_not), ID($logic_and), ID($logic_or), ID($reduce_and),
						 ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool), ID($lut), ID($and), ID($or),
						 ID($xor), ID($xnor), ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx), ID($lt),
						 ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt), ID($add), ID($sub), ID($mul),
						 ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($pow), ID($alu))) {
					int width_a = cell->hasPort(ID::A) ? GetSize(cell->getPort(ID::A)) : 0;
					int width_b = cell->hasPort(ID::B) ? GetSize(cell->getPort(ID::B)) : 0;
					int width_y = cell->hasPort(ID::Y) ? GetSize(cell->getPort(ID::Y)) : 0;
					cell_type = stringf("%s_%d", cell_type.c_str(), max<int>({width_a, width_b, width_y}));
				} else if (cell_type.in(ID($mux)))
					cell_type = stringf("%s_%d", cell_type.c_str(), GetSize(cell->getPort(ID::Y)));
				else if (cell_type.in(ID($bmux), ID($pmux)))
					cell_type =
					  stringf("%s_%d_%d", cell_type.c_str(), GetSize(cell->getPort(ID::Y)), GetSize(cell->getPort(ID::S)));
				else if (cell_type == ID($demux))
					cell_type =
					  stringf("%s_%d_%d", cell_type.c_str(), GetSize(cell->getPort(ID::A)), GetSize(cell->getPort(ID::S)));
				else if (cell_type.in(ID($sr), ID($ff), ID($dff), ID($dffe), ID($dffsr), ID($dffsre), ID($adff), ID($adffe),
						      ID($sdff), ID($sdffe), ID($sdffce), ID($aldff), ID($aldffe), ID($dlatch), ID($adlatch),
						      ID($dlatchsr)))
					cell_type = stringf("%s_%d", cell_type.c_str(), GetSize(cell->getPort(ID::Q)));
			}

			if (!cell_area.empty()) {
				// check if cell_area provides a area calculator
				if (cell_area.count(cell->type)) {
					cell_area_t cell_data = cell_area.at(cell->type);
					if (cell_data.single_parameter_area.size() > 0) {
						// assume that we just take the max of the A,B,Y ports

						int width_a = cell->hasPort(ID::A) ? GetSize(cell->getPort(ID::A)) : 0;
						int width_b = cell->hasPort(ID::B) ? GetSize(cell->getPort(ID::B)) : 0;
						int width_y = cell->hasPort(ID::Y) ? GetSize(cell->getPort(ID::Y)) : 0;
						int width_q = cell->hasPort(ID::Q) ? GetSize(cell->getPort(ID::Q)) : 0;
						int max_width = max<int>({width_a, width_b, width_y, width_q});
						if (!cell_area.count(cell_type)) {
							cell_area[cell_type] = cell_data;
						}
						if (cell_data.single_parameter_area.size() > max_width - 1u) {
							cell_area.at(cell_type).area = cell_data.single_parameter_area.at(max_width - 1);
							cell_area.at(cell_type).is_sequential = cell_data.is_sequential;

						} else {
							log_warning("too small single_parameter_area %s width: %d size: %d\n", cell_type.c_str(), max_width,
							       (int)cell_data.single_parameter_area.size());
							cell_area.at(cell_type).area = cell_data.single_parameter_area.back();
							cell_area.at(cell_type).is_sequential = cell_data.is_sequential;
						}
					}
					vector<double> widths;
					if (cell_data.parameter_names.size() > 0) {
						for (auto &it : cell_data.parameter_names) {
							RTLIL::IdString port_name;
							if (it == "A") {
								port_name = ID::A;
							} else if (it == "B") {
								port_name = ID::B;
							} else if (it == "Y") {
								port_name = ID::Y;
							} else if (it == "Q") {
								port_name = ID::Q;
							} else if (it == "S") {
								port_name = ID::S;
							} else {
								port_name = ID(it);
							}
							if (cell->hasPort(port_name)) {
								int width = GetSize(cell->getPort(port_name));
								widths.push_back(width);
							} else {
								widths.push_back(0);
							}
						}
					}

					if (cell_data.double_parameter_area.size() > 0) {
						if (!cell_area.count(cell_type)) {
							cell_area[cell_type] = cell_data;
						}
						if (widths.size() == 2) {
							unsigned int width_a = widths.at(0);
							unsigned int width_b = widths.at(1);
							if (width_a > 0 && width_b > 0) {
								if (cell_data.double_parameter_area.size() > width_a - 1 &&
								    cell_data.double_parameter_area.at(width_a - 1).size() > width_b - 1) {
									cell_area.at(cell_type).area =
									  cell_data.double_parameter_area.at(width_a - 1).at(width_b - 1);
									cell_area.at(cell_type).is_sequential = cell_data.is_sequential;
								} else {
									log_warning("too small double_parameter_area %s, width_a: %d, width_b: %d, size_a: %d, size_b: %d\n", cell_type.c_str(),
									       width_a, width_b, (int)cell_data.double_parameter_area.size(),
									       (int)cell_data.double_parameter_area.at(width_a - 1).size());
									cell_area.at(cell_type).area = cell_data.double_parameter_area.back().back();
									cell_area.at(cell_type).is_sequential = cell_data.is_sequential;
								}
							} else {
								cell_area.at(cell_type).area = cell_data.area;
								cell_area.at(cell_type).is_sequential = cell_data.is_sequential;
							}
						} else {
							log_error("double_parameter_area for %s has %d parameters, but only 2 are expected.\n", cell_type.c_str(),
							       (int)cell_data.double_parameter_area.size());
						}
					}
				}

				if (cell_area.count(cell_type)) {
					cell_area_t cell_data = cell_area.at(cell_type);
					if (cell_data.is_sequential) {
						sequential_area += cell_data.area;
						local_sequential_area += cell_data.area;
					}
					area += cell_data.area;
					num_cells++;
					num_cells_by_type[cell_type]++;
					area_cells_by_type[cell_type] += cell_data.area;
					seq_area_cells_by_type[cell_type] += cell_data.is_sequential ? cell_data.area : 0;
					local_area_cells_by_type[cell_type] += cell_data.area;
					local_seq_area_cells_by_type[cell_type] += cell_data.is_sequential ? cell_data.area : 0;
					local_area += cell_data.area;
					local_num_cells++;
					local_num_cells_by_type[cell_type]++;

				} else {
					unknown_cell_area.insert(cell_type);
					num_cells++;
					num_cells_by_type[cell_type]++;
					local_num_cells++;
					local_num_cells_by_type[cell_type]++;
					area_cells_by_type[cell_type] = 0;
					seq_area_cells_by_type[cell_type] = 0;
					local_area_cells_by_type[cell_type] = 0;
					local_seq_area_cells_by_type[cell_type] = 0;
				}
			} else {
				num_cells++;
				num_cells_by_type[cell_type]++;
				area_cells_by_type[cell_type] = 0;
				seq_area_cells_by_type[cell_type] = 0;
				local_num_cells++;
				local_num_cells_by_type[cell_type]++;
				local_area_cells_by_type[cell_type] = 0;
				local_seq_area_cells_by_type[cell_type] = 0;
			}
		}

		for (auto &it : mod->processes) {
			if (!design->selected(mod, it.second))
				continue;
			num_processes++;
			local_num_processes++;
		}
		RTLIL::IdString cell_name = mod->name;
		auto s = cell_name.str();
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

	/*
	format a floating point value to a of 8 characters, with at most 7 digits or scientific notation
	uses - to mark zero or very small values
	*/
	std::string f_val(double value)
	{
		if (std::abs(value) < 1e-12)
			return "       -";

		char buf[16];

		int len = snprintf(buf, sizeof(buf), "%.3f", value);

		while (len > 0 && buf[len - 1] == '0')
			--len;
		if (len > 0 && buf[len - 1] == '.')
			--len;
		buf[len] = '\0';

		if (len <= 7) {
			return std::string(8 - len, ' ') + std::string(buf);
		}

		// use scientific notation, this should always fit in 8 characters
		snprintf(buf, sizeof(buf), "%8.3G", value);

		return std::string(buf);
	}

	void print_log_line(const std::string &name, unsigned int count_local, double area_local, unsigned int count_global, double area_global,
			    int spacer = 0, bool print_area = true, bool print_hierarchical = true, bool print_global_only = false)
	{
		const std::string indent(2 * spacer, ' ');

		std::string count_local_str = f_val(static_cast<double>(count_local));
		std::string count_global_str = f_val(static_cast<double>(count_global));
		std::string area_local_str = f_val(area_local);
		std::string area_global_str = f_val(area_global);

		if (print_area) {
			if (print_hierarchical) {
				log(" %s %s %s %s %s%s\n", count_global_str.c_str(), area_global_str.c_str(), count_local_str.c_str(),
				    area_local_str.c_str(), indent.c_str(), name.c_str());
			} else if (print_global_only) {
				log(" %s %s %s%s\n", count_global_str.c_str(), area_global_str.c_str(), indent.c_str(), name.c_str());
			} else {
				if (count_local > 0)
					log(" %s %s %s%s\n", count_local_str.c_str(), area_local_str.c_str(), indent.c_str(), name.c_str());
			}
		} else {
			if (print_hierarchical) {
				log(" %s %s %s%s\n", count_global_str.c_str(), count_local_str.c_str(), indent.c_str(), name.c_str());
			} else if (print_global_only) {
				log(" %s %s%s\n", count_global_str.c_str(), indent.c_str(), name.c_str());
			} else {
				if (count_local > 0)
					log(" %s %s%s\n", count_local_str.c_str(), indent.c_str(), name.c_str());
			}
		}
	}

	void print_log_header(bool print_area = true, bool print_hierarchical = true, bool print_global_only = false)
	{
		if (print_area) {
			if (print_hierarchical) {
				log(" %8s-%8s-%8s-%8s-%s\n", "+", "--------", "--------", "--------", "Count including submodules.");
				log(" %8s %8s-%8s-%8s-%s\n", "|", "+", "--------", "--------", "Area including submodules.");
				log(" %8s %8s %8s-%8s-%s\n", "|", "|", "+", "--------", "Local count, excluding submodules.");
				log(" %8s %8s %8s %8s-%s\n", "|", "|", "|", "+", "Local area, excluding submodules.");
				log(" %8s %8s %8s %8s \n", "|", "|", "|", "|");
			} else if (print_global_only) {
				log(" %8s-%8s-%s\n", "+", "--------", "Count including submodules.");
				log(" %8s %8s-%s\n", "|", "+", "Area including submodules.");
				log(" %8s %8s \n", "|", "|");
			} else {
				log(" %8s-%8s-%s\n", "+", "--------", "Local Count, excluding submodules.");
				log(" %8s %8s-%s\n", "|", "+", "Local Area, excluding submodules.");
				log(" %8s %8s \n", "|", "|");
			}
		} else {
			if (print_hierarchical) {
				log(" %8s-%8s-%8s-%s\n", "+", "--------", "--------", "Count including submodules.");
				log(" %8s %8s-%8s-%s\n", "|", "+", "--------", "Local count, excluding submodules.");
				log(" %8s %8s \n", "|", "|");
			} else if (print_global_only) {
				log(" %8s-%8s-%s\n", "+", "--------", "Count including submodules.");
				log(" %8s \n", "|");
			} else {
				log(" %8s-%8s-%s\n", "+", "--------", "Local Count, excluding submodules.");
				log(" %8s \n", "|");
			}
		}
	}

	void log_data(RTLIL::IdString mod_name, bool top_mod, bool print_area = true, bool print_hierarchical = true, bool print_global_only = false)
	{

		print_log_header(print_area, print_hierarchical, print_global_only);

		print_log_line("wires", local_num_wires, 0, num_wires, 0, 0, print_area, print_hierarchical, print_global_only);
		print_log_line("wire bits", local_num_wire_bits, 0, num_wire_bits, 0, 0, print_area, print_hierarchical, print_global_only);
		print_log_line("public wires", local_num_pub_wires, 0, num_pub_wires, 0, 0, print_area, print_hierarchical, print_global_only);
		print_log_line("public wire bits", local_num_pub_wire_bits, 0, num_pub_wire_bits, 0, 0, print_area, print_hierarchical,
			       print_global_only);
		print_log_line("ports", local_num_ports, 0, num_ports, 0, 0, print_area, print_hierarchical, print_global_only);
		print_log_line("port bits", local_num_port_bits, 0, num_port_bits, 0, 0, print_area, print_hierarchical, print_global_only);
		print_log_line("memories", local_num_memories, 0, num_memories, 0, 0, print_area, print_hierarchical, print_global_only);
		print_log_line("memory bits", local_num_memory_bits, 0, num_memory_bits, 0, 0, print_area, print_hierarchical, print_global_only);
		print_log_line("processes", local_num_processes, 0, num_processes, 0, 0, print_area, print_hierarchical, print_global_only);
		print_log_line("cells", local_num_cells, local_area, num_cells, area, 0, print_area, print_hierarchical, print_global_only);
		for (auto &it : num_cells_by_type)
			if (it.second) {
				auto name = string(log_id(it.first));
				print_log_line(name, local_num_cells_by_type.count(it.first) ? local_num_cells_by_type.at(it.first) : 0,
					       local_area_cells_by_type.count(it.first) ? local_area_cells_by_type.at(it.first) : 0, it.second,
					       area_cells_by_type.at(it.first), 1, print_area, print_hierarchical, print_global_only);
			}
		if (num_submodules > 0) {
			print_log_line("submodules", num_submodules, 0, num_submodules, submodule_area, 0, print_area, print_hierarchical,
				       print_global_only);
			for (auto &it : num_submodules_by_type)
				if (it.second)
					print_log_line(string(log_id(it.first)), it.second, 0, it.second,
						       submodules_area_by_type.count(it.first) ? submodules_area_by_type.at(it.first) : 0, 1,
						       print_area, print_hierarchical, print_global_only);
		}
		if (!unknown_cell_area.empty()) {
			log("\n");
			for (auto cell_type : unknown_cell_area)
				log("   Area for cell type %s is unknown!\n", cell_type.c_str());
		}

		if (area != 0) {
			log("\n");
			if (print_hierarchical || print_global_only) {
				log("   Chip area for %smodule '%s': %f\n", (top_mod) ? "top " : "", mod_name.c_str(), area);
				log("     of which used for sequential elements: %f (%.2f%%)\n", sequential_area, 100.0 * sequential_area / area);
			} else {
				double local_area = 0;
				for (auto &it : local_area_cells_by_type)
					local_area += it.second;
				double local_sequential_area = 0;
				for (auto &it : local_seq_area_cells_by_type)
					local_sequential_area += it.second;
				log("   Chip area for %smodule '%s': %f\n", (top_mod) ? "top " : "", mod_name.c_str(), local_area);
				log("     of which used for sequential elements: %f (%.2f%%)\n", local_sequential_area,
				    100.0 * local_sequential_area / local_area);
			}
		}

		if (tech == "xilinx") {
			log("\n");
			log("   Estimated number of LCs: %10u\n", estimate_xilinx_lc());
		}

		if (tech == "cmos") {
			bool tran_cnt_exact = true;
			unsigned int tran_cnt = cmos_transistor_count(&tran_cnt_exact);

			log("\n");
			log("   Estimated number of transistors: %10u%s\n", tran_cnt, tran_cnt_exact ? "" : "+");
		}
	}

	string json_line(unsigned int count_local, double area_local, unsigned int count_global, double area_global)
	{

		return stringf("{ \"count\": \"%u\", \"area\": \"%f\", \"local_count\": \"%u\", \"local_area\": \"%f\" }", count_global, area_global,
			       count_local, area_local);
	}

	void log_data_json(const char *mod_name, bool first_module, bool hierarchical = false, bool global_only = false)
	{
		if (!first_module)
			log(",\n");
		if (hierarchical) {
			log("      %s: {\n", json11::Json(mod_name).dump().c_str());
			log("         \"num_wires\":         %s,\n", json_line(local_num_wires, 0, num_wires, 0).c_str());
			log("         \"num_wire_bits\":     %s,\n", json_line(local_num_wire_bits, 0, num_wire_bits, 0).c_str());
			log("         \"num_pub_wires\":     %s,\n", json_line(local_num_pub_wires, 0, num_pub_wires, 0).c_str());
			log("         \"num_pub_wire_bits\": %s,\n", json_line(local_num_pub_wire_bits, 0, num_pub_wire_bits, 0).c_str());
			log("         \"num_ports\":         %s,\n", json_line(local_num_ports, 0, num_ports, 0).c_str());
			log("         \"num_port_bits\":     %s,\n", json_line(local_num_port_bits, 0, num_port_bits, 0).c_str());
			log("         \"num_memories\":      %s,\n", json_line(local_num_memories, 0, num_memories, 0).c_str());
			log("         \"num_memory_bits\":   %s,\n", json_line(local_num_memory_bits, 0, num_memory_bits, 0).c_str());
			log("         \"num_processes\":     %s,\n", json_line(local_num_processes, 0, num_processes, 0).c_str());
			log("         \"num_cells\":         %s,\n", json_line(local_num_cells, local_area, num_cells, area).c_str());
			log("         \"num_submodules\":       %s,\n", json_line(0, 0, num_submodules, submodule_area).c_str());
			log("         \"sequential_area\":    %s,\n", json_line(0, local_sequential_area, 0, sequential_area).c_str());

			log("         \"num_cells_by_type\": {\n");
			bool first_line = true;
			for (auto &it : num_cells_by_type)
				if (it.second) {
					if (!first_line)
						log(",\n");
					log("            %s: %s", json11::Json(log_id(it.first)).dump().c_str(),
					    json_line(local_num_cells_by_type.count(it.first) ? local_num_cells_by_type.at(it.first) : 0,
						      local_area_cells_by_type.count(it.first) ? local_area_cells_by_type.at(it.first) : 0, it.second,
						      area_cells_by_type.at(it.first))
					      .c_str());
					first_line = false;
				}
			log("\n      },\n");
			log("         \"num_submodules_by_type\": {\n");
			first_line = true;
			for (auto &it : num_submodules_by_type)
				if (it.second) {
					if (!first_line)
						log(",\n");
					log("            %s: %s", json11::Json(log_id(it.first)).dump().c_str(),
					    json_line(0, 0, it.second,
						      submodules_area_by_type.count(it.first) ? submodules_area_by_type.at(it.first) : 0)
					      .c_str());
					first_line = false;
				}
			log("\n      }\n");
			if (tech == "xilinx") {
				log("         \"estimated_num_lc\": %u,\n", estimate_xilinx_lc());
			}
			if (tech == "cmos") {
				bool tran_cnt_exact = true;
				unsigned int tran_cnt = cmos_transistor_count(&tran_cnt_exact);
				log("		 \"estimated_num_transistors\": \"%u%s\"\n", tran_cnt, tran_cnt_exact ? "" : "+");
			}
			log("      }");

		} else {
			if (global_only) {
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
				log("         \"num_submodules\":       %u,\n", num_submodules);
				if (area != 0) {
					log("         \"area\":              %f,\n", area);
					log("         \"sequential_area\":    %f,\n", sequential_area);
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
				for (auto &it : num_submodules_by_type)
					if (it.second) {
						if (!first_line)
							log(",\n");
						log("            %s: %u", json11::Json(log_id(it.first)).dump().c_str(), it.second);
						first_line = false;
					}
				log("\n");
				log("         }");
			} else {
				log("      %s: {\n", json11::Json(mod_name).dump().c_str());
				log("         \"num_wires\":         %u,\n", local_num_wires);
				log("         \"num_wire_bits\":     %u,\n", local_num_wire_bits);
				log("         \"num_pub_wires\":     %u,\n", local_num_pub_wires);
				log("         \"num_pub_wire_bits\": %u,\n", local_num_pub_wire_bits);
				log("         \"num_ports\":         %u,\n", local_num_ports);
				log("         \"num_port_bits\":     %u,\n", local_num_port_bits);
				log("         \"num_memories\":      %u,\n", local_num_memories);
				log("         \"num_memory_bits\":   %u,\n", local_num_memory_bits);
				log("         \"num_processes\":     %u,\n", local_num_processes);
				log("         \"num_cells\":         %u,\n", local_num_cells);
				log("         \"num_submodules\":       %u,\n", num_submodules);
				if (area != 0) {
					log("         \"area\":              %f,\n", area);
					log("         \"sequential_area\":    %f,\n", sequential_area);
				}
				log("         \"num_cells_by_type\": {\n");
				bool first_line = true;
				for (auto &it : local_num_cells_by_type)
					if (it.second) {
						if (!first_line)
							log(",\n");
						log("            %s: %u", json11::Json(log_id(it.first)).dump().c_str(), it.second);
						first_line = false;
					}
				for (auto &it : num_submodules_by_type)
					if (it.second) {
						if (!first_line)
							log(",\n");
						log("            %s: %u", json11::Json(log_id(it.first)).dump().c_str(), it.second);
						first_line = false;
					}
				log("\n");
				log("         }");
			}
			if (tech == "xilinx") {
				log(",\n");
				log("         \"estimated_num_lc\": %u", estimate_xilinx_lc());
			}
			if (tech == "cmos") {
				bool tran_cnt_exact = true;
				unsigned int tran_cnt = cmos_transistor_count(&tran_cnt_exact);
				log(",\n");
				log("         \"estimated_num_transistors\": \"%u%s\"", tran_cnt, tran_cnt_exact ? "" : "+");
			}
			log("\n");
			log("      }");
		}
	}
};

statdata_t hierarchy_worker(std::map<RTLIL::IdString, statdata_t> &mod_stat, RTLIL::IdString mod, int level, bool quiet = false, bool has_area = true,
			    bool hierarchy_mode = true)
{
	statdata_t mod_data = mod_stat.at(mod);

	for (auto &it : mod_data.num_submodules_by_type) {
		if (mod_stat.count(it.first) > 0) {
			if (!quiet)
				mod_data.print_log_line(string(log_id(it.first)), mod_stat.at(it.first).local_num_cells,
							mod_stat.at(it.first).local_area, mod_stat.at(it.first).num_cells, mod_stat.at(it.first).area,
							level, has_area, hierarchy_mode);
			hierarchy_worker(mod_stat, it.first, level + 1, quiet, has_area, hierarchy_mode) * it.second;
		}
	}

	return mod_data;
}

statdata_t hierarchy_builder(const RTLIL::Design *design, const RTLIL::Module *top_mod, std::map<RTLIL::IdString, statdata_t> &mod_stat,
			     bool width_mode, dict<IdString, cell_area_t> &cell_area, string techname)
{
	if (top_mod == nullptr)
		top_mod = design->top_module();
	statdata_t mod_data(design, top_mod, width_mode, cell_area, techname);
	for (auto cell : top_mod->selected_cells()) {
		if (cell_area.count(cell->type) == 0) {
			if (design->has(cell->type)) {
				if (!(design->module(cell->type)->attributes.count(ID::blackbox))) {
					// deal with modules
					mod_data.add(
					  hierarchy_builder(design, design->module(cell->type), mod_stat, width_mode, cell_area, techname));
					mod_data.num_submodules_by_type[cell->type]++;
					mod_data.submodules_area_by_type[cell->type] += mod_stat.at(cell->type).area;
					mod_data.submodule_area += mod_stat.at(cell->type).area;
					mod_data.num_submodules++;
					mod_data.unknown_cell_area.erase(cell->type);
					mod_data.num_cells -=
					  (mod_data.num_cells_by_type.count(cell->type) != 0) ? mod_data.num_cells_by_type.at(cell->type) : 0;
					mod_data.num_cells_by_type.erase(cell->type);
					mod_data.local_num_cells -= (mod_data.local_num_cells_by_type.count(cell->type) != 0)
								      ? mod_data.local_num_cells_by_type.at(cell->type)
								      : 0;
					mod_data.local_num_cells_by_type.erase(cell->type);
					mod_data.local_area_cells_by_type.erase(cell->type);
				} else {
					// deal with blackbox cells
					if (design->module(cell->type)->attributes.count(ID::area) &&
					    design->module(cell->type)->attributes.at(ID::area).size() == 0) {
						mod_data.num_submodules_by_type[cell->type]++;
						mod_data.num_submodules++;
						mod_data.submodules_area_by_type[cell->type] +=
						  double(design->module(cell->type)->attributes.at(ID::area).as_int());
						mod_data.area += double(design->module(cell->type)->attributes.at(ID::area).as_int());
						mod_data.unknown_cell_area.erase(cell->type);
						mod_data.num_cells -=
						  (mod_data.num_cells_by_type.count(cell->type) != 0) ? mod_data.num_cells_by_type.at(cell->type) : 0;
						mod_data.num_cells_by_type.erase(cell->type);
						mod_data.local_num_cells -= (mod_data.local_num_cells_by_type.count(cell->type) != 0)
									      ? mod_data.local_num_cells_by_type.at(cell->type)
									      : 0;
						mod_data.local_num_cells_by_type.erase(cell->type);
						mod_data.local_area_cells_by_type.erase(cell->type);
					}
				}
			}
		}
	}
	mod_stat[top_mod->name] = mod_data;
	return mod_data;
}

void read_liberty_cellarea(dict<IdString, cell_area_t> &cell_area, string liberty_file)
{
	std::istream *f = uncompressed(liberty_file.c_str());
	yosys_input_files.insert(liberty_file);
	LibertyParser libparser(*f, liberty_file);
	delete f;

	for (auto cell : libparser.ast->children) {
		if (cell->id != "cell" || cell->args.size() != 1)
			continue;

		const LibertyAst *ar = cell->find("area");
		bool is_flip_flop = cell->find("ff") != nullptr;
		vector<double> single_parameter_area;
		vector<vector<double>> double_parameter_area;
		vector<string> port_names;
		const LibertyAst *sar = cell->find("single_area_parameterised");
		if (sar != nullptr) {
			for (const auto &s : sar->args) {
				if (s.empty()) {
					//catches trailing commas
					continue;
				}
				try {
					double value = std::stod(s);
					single_parameter_area.push_back(value);
				} catch (const std::exception &e) {
					log_error("Failed to parse single parameter area value '%s': %s\n", s.c_str(), e.what());
				}
			}
			if (single_parameter_area.size() == 0)
				log_error("single parameter area has size 0: %s\n", sar->args[single_parameter_area.size() - 1].c_str());
			// check if it is a double parameterised area
		}
		const LibertyAst *dar = cell->find("double_area_parameterised");
		if (dar != nullptr) {
			for (const auto &s : dar->args) {


				vector<string> sub_array;
				std::string::size_type start = 0;
				std::string::size_type end = s.find_first_of(",", start);
				while (end != std::string::npos) {
					sub_array.push_back(s.substr(start, end - start));
					start = end + 1;
					end = s.find_first_of(",", start);
				}
				sub_array.push_back(s.substr(start, end));

				vector<double> cast_sub_array;
				for (const auto &s : sub_array) {
					double value = 0;
					if (s.empty()) {
						//catches trailing commas
						continue;
					}
					try {
						value = std::stod(s);
						cast_sub_array.push_back(value);
					} catch (const std::exception &e) {
						log_error("Failed to parse double parameter area value for  '%s': %s\n", s.c_str(), e.what());
					}
				}
				double_parameter_area.push_back(cast_sub_array);
				if (cast_sub_array.size() == 0)
					log_error("double paramter array has size 0: %s\n", s.c_str());
			}
		}
		const LibertyAst *par = cell->find("port_names");
		if (par != nullptr) {
			for (const auto &s : par->args) {
				port_names.push_back(s);
			}
		}

		if (ar != nullptr && !ar->value.empty()) {
			string prefix = cell->args[0].substr(0, 1) == "$" ? "" : "\\";
			cell_area[prefix + cell->args[0]] = {atof(ar->value.c_str()), is_flip_flop, single_parameter_area, double_parameter_area,
							     port_names};
		}
	}
}

struct StatPass : public Pass {
	StatPass() : Pass("stat", "print some statistics") {}
	bool formatted_help() override
	{
		auto *help = PrettyHelp::get_current();
		help->set_group("passes/status");
		return false;
	}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    stat [options] [selection]\n");
		log("\n");
		log("Print some statistics (number of objects) on the selected portion of the\n");
		log("design.\n");
		log("Extracts the area of cells from a liberty file, if provided.\n");
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
		log("    -hierarchy\n");
		log("        print hierarchical statistics, i.e. The area and number of cells include submodules.\n");
		log(" 	     this changes the format of the json output.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool width_mode = false, json_mode = false, hierarchy_mode = false;
		RTLIL::Module *top_mod = nullptr;
		std::map<RTLIL::IdString, statdata_t> mod_stat;
		dict<IdString, cell_area_t> cell_area;
		string techname;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-width") {
				width_mode = true;
				continue;
			}
			if (args[argidx] == "-liberty" && argidx + 1 < args.size()) {
				string liberty_file = args[++argidx];
				rewrite_filename(liberty_file);
				read_liberty_cellarea(cell_area, liberty_file);
				continue;
			}
			if (args[argidx] == "-tech" && argidx + 1 < args.size()) {
				techname = args[++argidx];
				continue;
			}
			if (args[argidx] == "-top" && argidx + 1 < args.size()) {
				if (design->module(RTLIL::escape_id(args[argidx + 1])) == nullptr)
					log_cmd_error("Can't find module %s.\n", args[argidx + 1].c_str());
				top_mod = design->module(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-json") {
				json_mode = true;
				continue;
			}
			if (args[argidx] == "-hierarchy") {
				hierarchy_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!json_mode)
			log_header(design, "Printing statistics.\n");

		if (techname != "" && techname != "xilinx" && techname != "cmos" && !json_mode)
			log_cmd_error("Unsupported technology: '%s'\n", techname.c_str());

		if (json_mode) {
			log("{\n");
			log("   \"creator\": %s,\n", json11::Json(yosys_maybe_version()).dump().c_str());
			std::stringstream invocation;
			std::copy(args.begin(), args.end(), std::ostream_iterator<std::string>(invocation, " "));
			log("   \"invocation\": %s,\n", json11::Json(invocation.str()).dump().c_str());
			log("   \"modules\": {\n");
		}

		if (top_mod != nullptr) {
			hierarchy_builder(design, top_mod, mod_stat, width_mode, cell_area, techname);
		} else {
			for (auto mod : design->selected_modules()) {
				if (mod_stat.count(mod->name) == 0) {
					hierarchy_builder(design, mod, mod_stat, width_mode, cell_area, techname);
				}
			}
		}

		bool first_module = true;
		// determine if anything has a area.
		bool has_area = false;
		for (auto &it : mod_stat) {
			if (it.second.area > 0 || it.second.sequential_area > 0) {
				has_area = true;
				break;
			}
		}
		for (auto mod : design->selected_modules()) {
			if (!top_mod && design->full_selection())
				if (mod->get_bool_attribute(ID::top))
					top_mod = mod;
			statdata_t data = mod_stat.at(mod->name);
			if (json_mode) {
				data.log_data_json(mod->name.c_str(), first_module, hierarchy_mode);
				first_module = false;
			} else {
				log("\n");
				log("=== %s%s ===\n", log_id(mod->name), mod->is_selected_whole() ? "" : " (partially selected)");
				log("\n");
				data.log_data(mod->name, false, has_area, hierarchy_mode);
			}
		}

		if (json_mode) {
			log("\n");
			log(top_mod == nullptr ? "   }\n" : "   },\n");
		}

		if (top_mod != nullptr) {
			if (!json_mode && GetSize(mod_stat) > 1) {
				log("\n");
				log("=== design hierarchy ===\n");
				log("\n");
				mod_stat[top_mod->name].print_log_header(has_area, hierarchy_mode, true);
				mod_stat[top_mod->name].print_log_line(log_id(top_mod->name), mod_stat[top_mod->name].local_num_cells,
								       mod_stat[top_mod->name].local_area, mod_stat[top_mod->name].num_cells,
								       mod_stat[top_mod->name].area, 0, has_area, hierarchy_mode, true);
			}

			statdata_t data = hierarchy_worker(mod_stat, top_mod->name, 0, /*quiet=*/json_mode, has_area, hierarchy_mode);

			if (json_mode)
				data.log_data_json("design", true, hierarchy_mode, true);
			else if (GetSize(mod_stat) > 1) {
				log("\n");
				data.log_data(top_mod->name, true, has_area, hierarchy_mode, true);
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
