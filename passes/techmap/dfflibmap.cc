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
#include "kernel/sigtools.h"
#include "kernel/gzip.h"
#include "kernel/ff.h"
#include "libparse.h"
#include <cstddef>
#include <string.h>
#include <errno.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct cell_mapping {
	IdString cell_name;
	std::map<std::string, char> ports;
};
static std::map<RTLIL::IdString, cell_mapping> cell_mappings;

static void strip_chars(std::string &s, const char *chars)
{
	for (size_t pos = s.find_first_of(chars); pos != std::string::npos; pos = s.find_first_of(chars))
		s.erase(pos, 1);
}

static bool is_dont_use(const LibertyAst *cell, std::vector<std::string> &dont_use_cells)
{
	const LibertyAst *dn = cell->find("dont_use");
	if (dn != nullptr && dn->value == "true")
		return true;
	for (auto &pat : dont_use_cells)
		if (patmatch(pat.c_str(), cell->args[0].c_str()))
			return true;
	return false;
}

// State for evaluating a candidate library cell
struct CellMatch {
	std::map<std::string, char> ports;
	int num_pins = 0;
	bool has_noninv_output = false;

	enum ScanResult {
		REJECT,    // cell has unconnected inputs
		NO_OUTPUT, // cell is valid but has no Q/QN output
		OK         // cell is valid with output found
	};

	// Scan cell pins to count them, check inputs, and identify Q/QN outputs.
	ScanResult scan_outputs(const LibertyAst *cell, const LibertyAst *ff, bool cell_next_pol)
	{
		bool found_output = false;
		for (auto pin : cell->children) {
			if (pin->id != "pin" || pin->args.size() != 1)
				continue;
			const LibertyAst *dir = pin->find("direction");
			if (dir == nullptr || dir->value == "internal")
				continue;
			num_pins++;
			if (dir->value == "input" && ports.count(pin->args[0]) == 0)
				return REJECT;
			const LibertyAst *func = pin->find("function");
			if (dir->value == "output" && func != nullptr) {
				std::string value = func->value;
				strip_chars(value, "\" \t");
				// next_state negation propagated to output
				if (value == ff->args[0]) {
					ports[pin->args[0]] = cell_next_pol ? 'Q' : 'q';
					if (cell_next_pol) has_noninv_output = true;
					found_output = true;
				} else if (value == ff->args[1]) {
					ports[pin->args[0]] = cell_next_pol ? 'q' : 'Q';
					if (!cell_next_pol) has_noninv_output = true;
					found_output = true;
				}
			}
			if (ports.count(pin->args[0]) == 0)
				ports[pin->args[0]] = 0;
		}
		return found_output ? OK : NO_OUTPUT;
	}
};

// State for tracking the best matching library cell found so far
struct BestCell : CellMatch {
	const LibertyAst *cell = nullptr;
	double area = 0;

	// Update best cell if candidate is better (fewer pins, has noninv output, smaller area)
	void update(const LibertyAst *candidate, CellMatch &match)
	{
		if (cell != nullptr && (match.num_pins > num_pins || (has_noninv_output && !match.has_noninv_output)))
			return;
		double candidate_area = 0;
		const LibertyAst *ar = candidate->find("area");
		if (ar != nullptr && !ar->value.empty())
			candidate_area = atof(ar->value.c_str());
		if (cell != nullptr && match.num_pins == num_pins && candidate_area > area)
			return;
		cell = candidate;
		num_pins = match.num_pins;
		area = candidate_area;
		has_noninv_output = match.has_noninv_output;
		ports.swap(match.ports);
	}

	void record_mapping(IdString cell_type)
	{
		if (cell != nullptr) {
			log("  cell %s (%sinv, pins=%d, area=%.2f) is a direct match for cell type %s.\n",
				cell->args[0].c_str(), has_noninv_output ? "non" : "", num_pins, area, cell_type.c_str());
			cell_mappings[cell_type].cell_name = RTLIL::escape_id(cell->args[0]);
			cell_mappings[cell_type].ports = ports;
		}
	}
};

static void logmap(IdString dff)
{
	if (cell_mappings.count(dff) == 0) {
		log("    unmapped dff cell: %s\n", dff);
	} else {
		log("    %s %s (", cell_mappings[dff].cell_name, dff.substr(1));
		bool first = true;
		for (auto &port : cell_mappings[dff].ports) {
			char arg[3] = { port.second, 0, 0 };
			if ('a' <= arg[0] && arg[0] <= 'z')
				arg[1] = arg[0] - ('a' - 'A'), arg[0] = '~';
			else
				arg[1] = arg[0], arg[0] = ' ';
			log("%s.%s(%s)", first ? "" : ", ", port.first, arg);
			first = false;
		}
		log(");\n");
	}
}

static bool is_supported_ff(const FfTypeData &ff)
{
	// only support fine cells with clk, no aload/srst/gclk
	if (!ff.is_fine || !ff.has_clk || ff.has_aload || ff.has_srst || ff.has_gclk)
		return false;
	// no combined enable with reset/sr
	if (ff.has_ce && (ff.has_arst || ff.has_sr))
		return false;
	return true;
}

static void logmap_all()
{
	for (auto type : RTLIL::builtin_ff_cell_types()) {
		FfTypeData ff(type);
		if (is_supported_ff(ff))
			logmap(type);
	}
}

static bool parse_next_state(const LibertyAst *cell, const LibertyAst *attr, std::string &data_name, bool &data_not_inverted, std::string &enable_name, bool &enable_not_inverted)
{
	static pool<std::string> warned_cells{};

	if (cell == nullptr || attr == nullptr || attr->value.empty())
		return false;

	auto expr = attr->value;
	auto cell_name = cell->args[0];

	strip_chars(expr, "\"\t");

	// if this isn't an enable flop, the next_state variable is usually just the input pin name.
	if (expr[expr.size()-1] == '\'') {
		data_name = expr.substr(0, expr.size()-1);
		data_not_inverted = false;
	} else if (expr[0] == '!') {
		data_name = expr.substr(1, expr.size()-1);
		data_not_inverted = false;
	} else if (expr[0] == '(' && expr[expr.size() - 1] == ')') {
		data_name = expr.substr(1, expr.size() - 2);
		data_not_inverted = true;
	} else {
		data_name = expr;
		data_not_inverted = true;
	}

	for (auto child : cell->children)
		if (child->id == "pin" && child->args.size() == 1 && child->args[0] == data_name)
			return true;

	// the next_state variable isn't just a pin name; perhaps this is an enable?
	auto helper = LibertyExpression::Lexer(expr);
	auto tree = LibertyExpression::parse(helper);
	// log_debug("liberty expression:\n%s\n", tree.str());

	if (tree.kind == LibertyExpression::Kind::EMPTY) {
		if (!warned_cells.count(cell_name)) {
			log_debug("Invalid expression '%s' in next_state attribute of cell '%s' - skipping.\n", expr, cell_name);
			warned_cells.insert(cell_name);
		}
		return false;
	}

	auto pin_names = std::unordered_set<std::string>{};
	tree.get_pin_names(pin_names);

	// from the `ff` block, we know the flop output signal name for loopback.
	auto ff = cell->find("ff");
	if (ff == nullptr || ff->args.size() != 2)
		return false;
	auto ff_output = ff->args.at(0);

	// This test is redundant with the one in enable_pin, but we're in a
	// position that gives better diagnostics here.
	if (!pin_names.count(ff_output)) {
		if (!warned_cells.count(cell_name)) {
			log_debug("Inference failed on expression '%s' in next_state attribute of cell '%s' because it does not contain ff output '%s' - skipping.\n", expr, cell_name, ff_output);
			warned_cells.insert(cell_name);
		}
		return false;
	}

	data_not_inverted = true;
	data_name = "";
	enable_not_inverted = true;
	enable_name = "";

	if (pin_names.size() == 3 && pin_names.count(ff_output)) {
		pin_names.erase(ff_output);
		auto pins = std::vector<std::string>(pin_names.begin(), pin_names.end());
		int lut = 0;
		for (int n = 0; n < 8; n++) {
			auto values = std::unordered_map<std::string, bool>{};
			values.insert(std::make_pair(pins[0], (n & 1) == 1));
			values.insert(std::make_pair(pins[1], (n & 2) == 2));
			values.insert(std::make_pair(ff_output, (n & 4) == 4));
			if (tree.eval(values))
				lut |= 1 << n;
		}
		// the ff output Q is in a known bit location, so we now just have to compare the LUT mask to known values to find the enable pin and polarity.
		if (lut == 0xD8) {
			data_name = pins[1];
			enable_name = pins[0];
			return true;
		}
		if (lut == 0xB8) {
			data_name = pins[0];
			enable_name = pins[1];
			return true;
		}
		enable_not_inverted = false;
		if (lut == 0xE4) {
			data_name = pins[1];
			enable_name = pins[0];
			return true;
		}
		if (lut == 0xE2) {
			data_name = pins[0];
			enable_name = pins[1];
			return true;
		}
		// this does not match an enable flop.
	}

	if (!warned_cells.count(cell_name)) {
		log_debug("Inference failed on expression '%s' in next_state attribute of cell '%s' because it does not evaluate to an enable flop - skipping.\n", expr, cell_name);
		warned_cells.insert(cell_name);
	}
	return false;
}

static bool parse_pin(const LibertyAst *cell, const LibertyAst *attr, std::string &pin_name, bool &pin_pol)
{
	if (cell == nullptr || attr == nullptr || attr->value.empty())
		return false;

	std::string value = attr->value;
	strip_chars(value, "\" \t()");

	if (value[value.size()-1] == '\'') {
		pin_name = value.substr(0, value.size()-1);
		pin_pol = false;
	} else if (value[0] == '!') {
		pin_name = value.substr(1, value.size()-1);
		pin_pol = false;
	} else {
		pin_name = value;
		pin_pol = true;
	}

	for (auto child : cell->children)
		if (child->id == "pin" && child->args.size() == 1 && child->args[0] == pin_name)
			return true;

	/* If we end up here, the pin specified in the attribute does not exist, which is an error,
	   or, the attribute contains an expression which we do not yet support.
       For now, we'll simply produce a warning to let the user know something is up.
	*/
	if (pin_name.find_first_of("^*|&") == std::string::npos) {
		log_debug("Malformed liberty file - cannot find pin '%s' in cell '%s' - skipping.\n", pin_name, cell->args[0]);
	}
	else {
		log_debug("Found unsupported expression '%s' in pin attribute of cell '%s' - skipping.\n", pin_name, cell->args[0]);
	}

	return false;
}

struct DffFinder {
	std::vector<const LibertyAst *> &cells;
	std::vector<std::string> &dont_use_cells;

	void find(IdString cell_type, const FfTypeData &ff)
	{
		BestCell best;

		for (auto cell : cells) {
			if (is_dont_use(cell, dont_use_cells))
				continue;
			const LibertyAst *cell_ff = cell->find("ff");
			if (cell_ff == nullptr)
				continue;

			std::string cell_clk_pin, cell_rst_pin, cell_next_pin, cell_enable_pin;
			bool cell_clk_pol, cell_rst_pol, cell_next_pol, cell_enable_pol;

			if (!parse_pin(cell, cell_ff->find("clocked_on"), cell_clk_pin, cell_clk_pol) || cell_clk_pol != ff.pol_clk)
				continue;
			if (!parse_next_state(cell, cell_ff->find("next_state"), cell_next_pin, cell_next_pol, cell_enable_pin, cell_enable_pol) || (ff.has_ce && (cell_enable_pin.empty() || cell_enable_pol != ff.pol_ce)))
				continue;

			// next_state is negated, we later propagate this inversion to the output,
			// which requires the negation of the reset value
			if (ff.has_arst) {
				bool rstval = ff.val_arst[0] == State::S1;
				if (!cell_next_pol)
					rstval = !rstval;
				if (!parse_pin(cell, cell_ff->find(rstval ? "preset" : "clear"), cell_rst_pin, cell_rst_pol) || cell_rst_pol != ff.pol_arst)
					continue;
			}

			CellMatch match;
			match.ports[cell_clk_pin] = 'C';
			if (ff.has_arst) match.ports[cell_rst_pin] = 'R';
			if (ff.has_ce) match.ports[cell_enable_pin] = 'E';
			match.ports[cell_next_pin] = 'D';

			if (match.scan_outputs(cell, cell_ff, cell_next_pol) != CellMatch::OK)
				continue;
			best.update(cell, match);
		}
		best.record_mapping(cell_type);
	}

	void find_sr(IdString cell_type, const FfTypeData &ff)
	{
		BestCell best;

		log_assert(!ff.has_ce && "set/reset cell with enable is unimplemented due to lack of cells for testing");

		for (auto cell : cells) {
			if (is_dont_use(cell, dont_use_cells))
				continue;
			const LibertyAst *cell_ff = cell->find("ff");
			if (cell_ff == nullptr)
				continue;

			std::string cell_clk_pin, cell_set_pin, cell_clr_pin, cell_next_pin, cell_enable_pin;
			bool cell_clk_pol, cell_set_pol, cell_clr_pol, cell_next_pol, cell_enable_pol;

			if (!parse_pin(cell, cell_ff->find("clocked_on"), cell_clk_pin, cell_clk_pol) || cell_clk_pol != ff.pol_clk)
				continue;
			if (!parse_next_state(cell, cell_ff->find("next_state"), cell_next_pin, cell_next_pol, cell_enable_pin, cell_enable_pol))
				continue;
			if (!parse_pin(cell, cell_ff->find("preset"), cell_set_pin, cell_set_pol) ||
			    !parse_pin(cell, cell_ff->find("clear"), cell_clr_pin, cell_clr_pol))
				continue;
			// next_state is negated, we later propagate this inversion to the output,
			// which requires the swap of set and reset
			if (!cell_next_pol) {
				std::swap(cell_set_pin, cell_clr_pin);
				std::swap(cell_set_pol, cell_clr_pol);
			}
			if (cell_set_pol != ff.pol_set || cell_clr_pol != ff.pol_clr)
				continue;

			CellMatch match;
			match.ports[cell_clk_pin] = 'C';
			match.ports[cell_set_pin] = 'S';
			match.ports[cell_clr_pin] = 'R';
			if (ff.has_ce) match.ports[cell_enable_pin] = 'E';
			match.ports[cell_next_pin] = 'D';

			if (match.scan_outputs(cell, cell_ff, cell_next_pol) != CellMatch::OK)
				continue;
			best.update(cell, match);
		}
		best.record_mapping(cell_type);
	}
};

static void dfflibmap(RTLIL::Design *design, RTLIL::Module *module)
{
	log("Mapping DFF cells in module `%s':\n", module->name);

	dict<SigBit, pool<Cell*>> notmap;
	SigMap sigmap(module);

	std::vector<RTLIL::Cell*> cell_list;
	for (auto cell : module->cells()) {
		if (design->selected(module, cell) && cell_mappings.count(cell->type) > 0)
			cell_list.push_back(cell);
		if (cell->type == ID($_NOT_))
			notmap[sigmap(cell->getPort(ID::A))].insert(cell);
	}

	std::map<std::string, int> stats;
	for (auto cell : cell_list)
	{
		auto cell_type = cell->type;
		auto cell_name = cell->name;
		auto cell_connections = cell->connections();
		std::string src = cell->get_src_attribute();

		module->remove(cell);

		cell_mapping &cm = cell_mappings[cell_type];
		RTLIL::Cell *new_cell = module->addCell(cell_name, cm.cell_name);

		new_cell->set_src_attribute(src);

		bool has_q = false, has_qn = false;
		for (auto &port : cm.ports) {
			if (port.second == 'Q') has_q = true;
			if (port.second == 'q') has_qn = true;
		}

		for (auto &port : cm.ports) {
			RTLIL::SigSpec sig;
			if ('A' <= port.second && port.second <= 'Z') {
				sig = cell_connections[std::string("\\") + port.second];
			} else if (port.second == 'q') {
				RTLIL::SigSpec old_sig = cell_connections[std::string("\\") + char(port.second - ('a' - 'A'))];
				sig = module->addWire(NEW_ID, GetSize(old_sig));
				if (has_q && has_qn) {
					for (auto &it : notmap[sigmap(old_sig)]) {
						module->connect(it->getPort(ID::Y), sig);
						it->setPort(ID::Y, module->addWire(NEW_ID, GetSize(old_sig)));
					}
				} else {
					module->addNotGate(NEW_ID, sig, old_sig);
				}
			} else if ('a' <= port.second && port.second <= 'z') {
				sig = cell_connections[std::string("\\") + char(port.second - ('a' - 'A'))];
				sig = module->NotGate(NEW_ID, sig);
			} else if (port.second == '0' || port.second == '1') {
				sig = RTLIL::SigSpec(port.second == '0' ? 0 : 1, 1);
			} else if (port.second == 0) {
				sig = module->addWire(NEW_ID);
			} else {
				log_abort();
			}
			new_cell->setPort("\\" + port.first, sig);
		}

		stats[stringf("%s cells to %s cells", cell_type, new_cell->type)]++;
	}

	for (auto &stat: stats)
		log("  mapped %d %s.\n", stat.second, stat.first);
}

struct DfflibmapPass : public Pass {
	DfflibmapPass() : Pass("dfflibmap", "technology mapping of flip-flops") { }
	void help() override
	{
		log("\n");
		log("    dfflibmap [-prepare] [-map-only] [-info] [-dont_use <cell_name>] -liberty <file> [selection]\n");
		log("\n");
		log("Map internal flip-flop cells to the flip-flop cells in the technology\n");
		log("library specified in the given liberty files.\n");
		log("\n");
		log("This pass may add inverters as needed. Therefore it is recommended to\n");
		log("first run this pass and then map the logic paths to the target technology.\n");
		log("\n");
		log("When called with -prepare, this command will convert the internal FF cells\n");
		log("to the internal cell types that best match the cells found in the given\n");
		log("liberty file, but won't actually map them to the target cells.\n");
		log("\n");
		log("When called with -map-only, this command will only map internal cell\n");
		log("types that are already of exactly the right type to match the target\n");
		log("cells, leaving remaining internal cells untouched.\n");
		log("\n");
		log("When called with -info, this command will only print the target cell\n");
		log("list, along with their associated internal cell types, and the arguments\n");
		log("that would be passed to the dfflegalize pass.  The design will not be\n");
		log("changed.\n");
		log("\n");
		log("When called with -dont_use, this command will not map to the specified cell\n");
		log("name as an alternative to setting the dont_use property in the Liberty file.\n");
		log("This argument can be called multiple times with different cell names. This\n");
		log("argument also supports simple glob patterns in the cell name.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing DFFLIBMAP pass (mapping DFF cells to sequential cells from liberty file).\n");
		log_push();

		bool prepare_mode = false;
		bool map_only_mode = false;
		bool info_mode = false;

		std::vector<std::string> liberty_files;
		std::vector<std::string> dont_use_cells;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-liberty" && argidx+1 < args.size()) {
				append_globbed(liberty_files, args[++argidx]);
				continue;
			}
			if (arg == "-prepare") {
				prepare_mode = true;
				continue;
			}
			if (arg == "-map-only") {
				map_only_mode = true;
				continue;
			}
			if (arg == "-info") {
				info_mode = true;
				continue;
			}
			if (arg == "-dont_use" && argidx+1 < args.size()) {
				dont_use_cells.push_back(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (prepare_mode + map_only_mode + info_mode > 1)
			log_cmd_error("Only one of -prepare, -map-only, or -info options should be given!\n");

		if (liberty_files.empty())
			log_cmd_error("Missing `-liberty liberty_file' option!\n");

		LibertyMergedCells merged;
		for (auto path : liberty_files) {
			std::istream* f = uncompressed(path);
			LibertyParser p(*f, path);
			merged.merge(p);
			delete f;
		}

		DffFinder finder{merged.cells, dont_use_cells};
		for (auto type : RTLIL::builtin_ff_cell_types()) {
			FfTypeData ff(type);
			if (!is_supported_ff(ff))
				continue;
			if (ff.has_sr)
				finder.find_sr(type, ff);
			else
				finder.find(type, ff);
		}

		log("  final dff cell mappings:\n");
		logmap_all();

		if (!map_only_mode) {
			std::string dfflegalize_cmd = "dfflegalize";
			for (auto it : cell_mappings)
				dfflegalize_cmd += stringf(" -cell %s 01", it.first);
			dfflegalize_cmd += " t:$_DFF* t:$_SDFF*";
			if (info_mode) {
				log("dfflegalize command line: %s\n", dfflegalize_cmd);
			} else {
				Pass::call(design, dfflegalize_cmd);
			}
		}

		if (!prepare_mode && !info_mode) {
			for (auto module : design->selected_modules())
				if (!module->get_blackbox_attribute())
					dfflibmap(design, module);
		}

		log_pop();
		cell_mappings.clear();
	}
} DfflibmapPass;

PRIVATE_NAMESPACE_END
