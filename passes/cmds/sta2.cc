/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *            (C) 2019  Eddie Hung <eddie@fpgeh.com>
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

#include "kernel/cost.h"
#include "kernel/ff.h"
#include "kernel/gzip.h"
#include "kernel/modtools.h"
#include "kernel/sigtools.h"
#include "kernel/timinginfo.h"
#include "kernel/yosys.h"
#include "libs/json11/json11.hpp"
#include "passes/techmap/libparse.h"
#include <charconv>
#include <deque>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct cell_delay_t {
	double delay;
	bool is_flipflop;
	vector<double> single_parameter_delay;
	vector<vector<double>> double_parameter_delay;
	vector<string> parameter_names;
};

struct Sta_Path {
	double delay;
	RTLIL::IdString wire;
	vector<Cell *> cells;
	vector<double> delays; // delays of the cells in the path, used for debugging and analysis.
	Sta_Path(double d, RTLIL::IdString p, vector<Cell *> c, vector<double> ds) : delay(d), wire(p), cells(c), delays(ds) {}
	Sta_Path() : delay(0), wire(), cells(), delays() {}
	Sta_Path(const Sta_Path &other) : delay(other.delay), wire(other.wire), cells(other.cells), delays(other.delays) {}
	Hasher hash_into(Hasher h) const
	{
		// the delay is not required for the hash, as it's a result of the cells.

		for (auto &cell : cells)
			h.eat(cell->name);
		return h;
	}
	void add_delay(Cell *cell, dict<IdString, cell_delay_t> cell_delays)
	{
		if (cell == nullptr) {
			log_error("Cell is null, cannot add delay.\n");
		}
		if (!cell_delays.count(cell->type)) {
			return; // return current delay if cell type not found
		}
		auto cell_delay = cell_delays.at(cell->type);
		// deal with parameterized delays.
		// extract width of ports from the cells:
		vector<double> widths;
		if (cell_delay.parameter_names.size() > 0) {
			for (auto &it : cell_delay.parameter_names) {
				RTLIL::IdString port_name;
				// TODO: there has to be a better way to do this
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
		} else {
			int width_a = cell->hasPort(ID::A) ? GetSize(cell->getPort(ID::A)) : 0;
			int width_b = cell->hasPort(ID::B) ? GetSize(cell->getPort(ID::B)) : 0;
			int width_y = cell->hasPort(ID::Y) ? GetSize(cell->getPort(ID::Y)) : 0;
			int width_q = cell->hasPort(ID::Q) ? GetSize(cell->getPort(ID::Q)) : 0;
			int max_width = max<int>({width_a, width_b, width_y, width_q});
			widths.push_back(max_width);
		}
		if (cell_delay.single_parameter_delay.size() > 0) {
			if (widths.size() != 1) {
				// we need to have exactly one parameter for single parameter delay.
				log_error("Cell %s has single parameter delay, but has %d parameters.\n", cell->name.c_str(), widths.size());
			}
			if (cell_delay.single_parameter_delay.size() > widths.at(0) - 1) {
				delay += cell_delay.single_parameter_delay.at(widths.at(0) - 1);
				delays.push_back(cell_delay.single_parameter_delay.at(widths.at(0) - 1));
			} else {
				delay += cell_delay.single_parameter_delay.back();
				delays.push_back(cell_delay.single_parameter_delay.back());
			}
		} else if (cell_delay.double_parameter_delay.size() > 0) {
			if (widths.size() != 2) {
				// we need to have exactly two parameters for double parameter delay.
				log_error("Cell %s has double parameter delay, but has %d parameters.\n", cell->name.c_str(), widths.size());
			}
			int width_a = widths.at(1);
			int width_b = widths.at(0);
			if (width_a > 0 && width_b > 0) {
				if (cell_delay.double_parameter_delay.size() > width_a - 1 &&
				    cell_delay.double_parameter_delay.at(width_a - 1).size() > width_b - 1) {
					delay += cell_delay.double_parameter_delay.at(width_a - 1).at(width_b - 1);
					delays.push_back(cell_delay.double_parameter_delay.at(width_a - 1).at(width_b - 1));
				} else {
					delay += cell_delay.double_parameter_delay.back().back();
					delays.push_back(cell_delay.double_parameter_delay.back().back());
				}
			} else {
				log_error("Cell %s has double parameter delay, but has zero width parameters.\n", cell->name.c_str());
			}
		} else {
			delay += cell_delay.delay;
			delays.push_back(cell_delay.delay);
		}

		return;
	}
	bool operator==(const Sta_Path &other) const { return delay == other.delay && wire == other.wire && cells == other.cells; }
};

struct Sta2Worker {
	Design *design;
	std::deque<Sta_Path> queue;
	dict<IdString, cell_delay_t> cell_delays;
	std::map<RTLIL::IdString, std::pair<Sta_Path, Sta_Path>> analysed;
	pool<Sta_Path> analysed_max_paths;
	pool<Sta_Path> analysed_min_paths;
	std::map<RTLIL::IdString, double> cell_max_analysed;
	std::map<RTLIL::IdString, double> cell_min_analysed;
	std::map<RTLIL::Module *, ModWalker> modwalkers;

	Sta2Worker(RTLIL::Design *design, dict<IdString, cell_delay_t> cell_delay) : design(design), cell_delays(cell_delay) {}

	void run(RTLIL::Module *module, bool hold_violations, bool setup_violations)
	{
		auto modules = design->modules().to_vector();
		if (module != nullptr) {
			modules = {module};
		}
		for (auto module : modules) {
			SigMap sigmap(module);
			ModWalker modwalker(design);
			modwalker.setup(module);
			for (auto port : module->ports) {
				auto wire = module->wire(port);
				if (wire->port_input) {
					for (auto &bit : sigmap(wire)) {

						auto first_cells = modwalker.signal_consumers[bit];
						for (auto &f_cell : first_cells) {
							if (f_cell.cell == nullptr) {
								continue;
							}

							vector<Cell *> new_vector = {f_cell.cell};
							Sta_Path p(0, f_cell.cell->name, new_vector, vector<double>());
							p.add_delay(f_cell.cell, cell_delays);
							queue.push_back(p);
						}
					}
				}
			}
			for (auto cell : module->cells()) {
				if (RTLIL::builtin_ff_cell_types().count(cell->type) ||
				    (cell_delays.count(cell->type) && cell_delays.at(cell->type).is_flipflop)) {
					vector<Cell *> new_vector;
					new_vector.push_back(cell);
					Sta_Path p(0, cell->name, new_vector, vector<double>());
					p.add_delay(cell, cell_delays);
					queue.push_back(p);
				} else {
					continue;
				}

				while (queue.size() > 0) {
					auto entry = queue.back();
					queue.pop_back();
					auto cell = entry.cells.back();

					if (design->module(cell->type) == nullptr) {

					} else if (design->module(cell->type)->get_blackbox_attribute()) {

						if (!cell_delays.count(cell->type)) {
							continue;
						}
					}
					pool<RTLIL::IdString> analysed_cells;
					auto signals = modwalker.cell_outputs[cell];
					for (auto sig : signals) {
						auto consumers = modwalker.signal_consumers[sig];

						// figure out if we have reached a output cell.
						if (sig.wire->port_output) {
							// if we have reached a output port, print it.
							if (analysed.count(sig.wire->name)) {
								if (analysed[sig.wire->name].second.delay < entry.delay) {
									// reached new maximum delay for this cell.
									analysed[sig.wire->name].second = entry;
								} else if (analysed[sig.wire->name].first.delay > entry.delay) {
									// reached new minimum delay for this cell.
									analysed[sig.wire->name].first = entry;
								}
							} else {
								analysed[sig.wire->name] = pair<Sta_Path, Sta_Path>(entry, entry);
							}
						}

						if (consumers.empty()) {

							continue;
						}
						Yosys::RTLIL::Cell *last_consumer = nullptr;
						for (auto &consumer_bit : consumers) {
							auto consumer = consumer_bit.cell;
							if (analysed_cells.count(consumer->name)) {
								continue;
							}

							analysed_cells.insert(consumer->name);
							Sta_Path new_entry(entry.delay, entry.wire, entry.cells, entry.delays);
							new_entry.cells.push_back(consumer);
							new_entry.add_delay(consumer, cell_delays);
							double delay = new_entry.delays.back();
							// if we have already reached this cell skip it if between max or min.
							if (cell_max_analysed.count(consumer->name) &&
							    cell_max_analysed[consumer->name] > entry.delay) {
								if (!hold_violations)
									continue; // if we are not looking for hold violations, skip this.
								if (cell_min_analysed.count(consumer->name) &&
								    cell_min_analysed[consumer->name] < entry.delay) {
									continue;
								} else {
									cell_min_analysed[consumer->name] = delay;
								}
							} else {
								cell_max_analysed[consumer->name] = delay;
							}

							// we have found a cell that is connected.
							if (RTLIL::builtin_ff_cell_types().count(consumer->type) ||
							    (cell_delays.count(consumer->type) && cell_delays.at(consumer->type).is_flipflop)) {
								// We have a flip-flop. This is the end of this path.
								// check that we don't have a clk or rst port. In that case we don't want to include
								// this.
								if (RTLIL::builtin_ff_cell_types().count(consumer->type)) {
									FfData ff(nullptr, consumer);
									if (sigmap(sig) == sigmap(ff.sig_clk)) {
										continue;
									}
									if (sigmap(ff.sig_clr).size() == 1 && sigmap(sig) == sigmap(ff.sig_clr)) {
										continue;
									}
								}
								if (analysed.count(entry.cells.front()->name)) {

									if (analysed[consumer->name].second.delay < new_entry.delay) {
										// reached new maximum delay for this cell.
										analysed[consumer->name].second = new_entry;
										continue;
									} else if (analysed[consumer->name].first.delay > new_entry.delay) {
										// reached new minimum delay for this cell.
										analysed[consumer->name].first = new_entry;
										continue;
									}
								} else {

									analysed[consumer->name] = pair<Sta_Path, Sta_Path>(new_entry, new_entry);
								}
							} else {
								// check for loops.
								// a loop here does not mean a loop in the circuit.
								// therefore we just print a warning.
								auto loop = false;
								for (auto &it : entry.cells) {
									if (it->name == consumer->name) {
										log_warning("warning: potential loop detected: %s %s \n",
											    cell->name.c_str(), consumer->name.c_str());
										loop = true;
										break;
									}
								}
								if (loop)
									continue;

								queue.push_back(new_entry);
							}
						}
					}
				}
			}
		}
	}
};

void read_liberty_celldelay(dict<IdString, cell_delay_t> &cell_delay, string liberty_file)
{
	std::istream *f = uncompressed(liberty_file.c_str());
	yosys_input_files.insert(liberty_file);
	LibertyParser libparser(*f, liberty_file);
	delete f;

	for (auto cell : libparser.ast->children) {
		if (cell->id != "cell" || cell->args.size() != 1)
			continue;

		const LibertyAst *ar = cell->find("delay");
		bool is_flip_flop = cell->find("ff") != nullptr;
		vector<double> single_parameter_delay;
		vector<vector<double>> double_parameter_delay;
		vector<string> port_names;
		const LibertyAst *sar = cell->find("single_delay_parameterised");
		if (sar != nullptr) {
			for (const auto &s : sar->args) {
				double value = 0;
				auto [ptr, ec] = std::from_chars(s.data(), s.data() + s.size(), value);
				// ec != std::errc() means parse error, or ptr didn't consume entire string
				if (ec != std::errc() || ptr != s.data() + s.size())
					break;
				single_parameter_delay.push_back(value);
			}
			if (single_parameter_delay.size() == 0)
				log_error("single delay parameterisation array does not contain values: %s\n",
					  sar->args[single_parameter_delay.size() - 1].c_str());
			// check if it is a double parameterised delay
		}
		const LibertyAst *dar = cell->find("double_delay_parameterised");
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
					auto [ptr, ec] = std::from_chars(s.data() + 1, s.data() + s.size(), value);
					if (ec != std::errc() || ptr != s.data() + s.size())
						break;
					cast_sub_array.push_back(value);
				}
				double_parameter_delay.push_back(cast_sub_array);
				if (cast_sub_array.size() == 0)
					log_error("double delay parameterisation array does not contain values: %s\n",
						  dar->args[double_parameter_delay.size() - 1].c_str());
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
			cell_delay[prefix + cell->args[0]] = {atof(ar->value.c_str()), is_flip_flop, single_parameter_delay, double_parameter_delay,
							      port_names};
		}
	}
}

void generate_timing_report(const pool<Sta_Path> &max_paths, const pool<Sta_Path> &min_paths, double max_delay, double min_delay, bool names,
			    bool paths)
{
	log("Number of paths longer than max delay %f: %d \n", max_delay, max_paths.size());
	log("Number of paths shorter than min delay %f: %d \n", min_delay, min_paths.size());

	// Create ordered versions of max_delays and min_delays
	auto ordered_max_paths = vector<Sta_Path>(max_paths.begin(), max_paths.end());
	auto ordered_min_paths = vector<Sta_Path>(min_paths.begin(), min_paths.end());
	std::sort(ordered_max_paths.begin(), ordered_max_paths.end(), [](const Sta_Path &a, const Sta_Path &b) { return a.delay > b.delay; });
	std::sort(ordered_min_paths.begin(), ordered_min_paths.end(), [](const Sta_Path &a, const Sta_Path &b) { return a.delay < b.delay; });

	if (names) {
		for (auto &it : ordered_max_paths) {
			log("max_path: start: %s, end: %s, delay: %f, cells: %u \n", it.cells.front()->name.c_str(), it.cells.back()->name.c_str(),
			    it.delay, it.cells.size());
		}
		for (auto &it : ordered_min_paths) {
			log("min_path: start: %s, end: %s, delay: %f, cells: %u \n", it.cells.front()->name.c_str(), it.cells.back()->name.c_str(),
			    it.delay, it.cells.size());
		}
	}

	if (paths) {
		for (auto &it : ordered_max_paths) {
			log("max_path: start: %s, end: %s, delay: %f, cells: %u , delays_length: %u\n", it.cells.front()->name.c_str(),
			    it.cells.back()->name.c_str(), it.delay, it.cells.size(), it.delays.size());
			int i = 0;
			for (auto &cell : it.cells) {
				if (i < 0 || i >= it.delays.size()) {
					log("  cell: %s , delay: %d-> \n", cell->name.c_str(), 0);
				} else {
					log("  cell: %s , delay: %f -> \n", cell->name.c_str(), it.delays.at(i));
				}
				i++;
			}
		}
		for (auto &it : ordered_min_paths) {
			log("min_path: start: %s, end: %s, delay: %f, cells: %u \n", it.cells.front()->name.c_str(), it.cells.back()->name.c_str(),
			    it.delay, it.cells.size());
			for (auto &cell : it.cells) {
				log("  cell: %s -> \n", cell->name.c_str());
			}
		}
	}
}
struct Sta2Pass : public Pass {
	Sta2Pass() : Pass("sta2", "perform static timing analysis") {}

	void help() override
{
    // |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
    log("\n");
    log(" sta2 [options] [selection]\n");
    log("\n");
    log("This command performs static timing analysis on the design.\n\n");
    log("config file content: \n\n");
    log("It needs a config file to read the cell delay information.\n");
    log("The config file should be in the same format as the liberty file.\n");
    log("each cell needs to have a delay parameter.\n");
    log("It cannot parse the timing() section of the liberty file.\n");
    log("there is the option to use parameterised delays. This allows STA to run early on in the flow.\n");
    log("the delay can be parameterised by the width of the ports of the cells.\n");
    log("There is the option to use single parameter delays, which are indexed by max port width of a cell.\n");
    log("There is the option to use double parameter delays, here the two ports that are used for indexing can be specified.\n");
    log("\n");
    log("Extended liberty file fields for STA:\n");
    log(" ff: true;                           - marks cells that terminate timing paths\n");
    log(" delay: <value>;      				  - basic delay for non-parameterized cells\n");
    log(" single_delay_parameterised(...);    - delay values indexed by max port width\n");
    log(" port_names(\"A\", \"B\");           - specifies ports for multi-dimensional arrays\n");
    log(" double_delay_parameterised(...);    - 2D delay array (requires port_names)\n");
    log("   Format: (\"val1,val2,val3,\", \"val4,val5,val6,\", ...) - strings delimit dimensions\n");
    log("\n");
	log("\n");
	log("    -config <file>\n");
	log("        read cell delay information from config file\n");
	log("\n");
	log("    -top <module>\n");
	log("        use the specified module as the top level module\n");
	log("\n");
	log("    -max_delay <delay>\n");
	log("        report paths longer than the specified maximum delay\n");
	log("\n");
	log("    -min_delay <delay>\n");
	log("        report paths shorter than the specified minimum delay\n");
	log("\n");
	log("    -v\n");
	log("        verbose mode - show path start/end names and basic statistics\n");
	log("\n");
	log("    -vv\n");
	log("        very verbose mode - show detailed path information including\n");
	log("        individual cell delays\n");
	log("\n");
}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing STA pass (static timing analysis).\n");
		RTLIL::Module *top_mod = design->top_module();
		dict<IdString, cell_delay_t> cell_delay;
		bool names = false;
		bool paths = false;
		double max_delay = 0;
		double min_delay = 0;
		size_t argidx;

		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-config" && argidx + 1 < args.size()) {
				string liberty_file = args[++argidx];
				rewrite_filename(liberty_file);
				read_liberty_celldelay(cell_delay, liberty_file);
				continue;
			}
			if (args[argidx] == "-top" && argidx + 1 < args.size()) {
				if (design->module(RTLIL::escape_id(args[argidx + 1])) == nullptr)
					log_cmd_error("Can't find module %s.\n", args[argidx + 1].c_str());
				top_mod = design->module(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-max_delay" && argidx + 1 < args.size()) {
				argidx++;
				max_delay = atof(args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-min_delay" && argidx + 1 < args.size()) {
				argidx++;
				min_delay = atof(args[argidx].c_str());
				continue;
			}
			if (args[argidx] == "-v") {
				log("verbose mode enabled.\n");
				names = true;
				continue;
			}
			if (args[argidx] == "-vv") {
				log("very verbose mode enabled.\n");
				names = true;
				paths = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Design *new_design = new RTLIL::Design;
		auto modules = design->modules().to_vector();
		for (auto &mod : modules) {
			new_design->add(mod->clone());
			auto cells = new_design->module(mod->name)->cells().to_vector();
			for (auto &cell : cells) {
				cell->set_bool_attribute(ID::keep_hierarchy, false);
			}
		}
		Pass::call(new_design, "hierarchy -check -top " + top_mod->name.str());
		Pass::call(new_design, "flatten");
		Pass::call(new_design, "dump -m -o \"out/poststa.dump\"");

		Sta2Worker sta(new_design, cell_delay);
		sta.run(new_design->module(top_mod->name), min_delay, 1);

		// Extract all the paths longer than max_delay and shorter than min_delay
		auto max_paths = pool<Sta_Path>();
		auto min_paths = pool<Sta_Path>();
		for (auto &it : sta.analysed) {
			if (it.second.second.delay > max_delay) {
				max_paths.insert(it.second.second);
			}
			if (it.second.first.delay < min_delay) {
				min_paths.insert(it.second.first);
			}
		}

		// Generate the timing analysis report
		generate_timing_report(max_paths, min_paths, max_delay, min_delay, names, paths);
	}
} Sta2Pass;

PRIVATE_NAMESPACE_END
